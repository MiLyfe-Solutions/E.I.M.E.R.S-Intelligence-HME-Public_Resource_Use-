import V185TrunkScan23Chunk0510

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3022394 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2]
def baseStart_3022394 : Nat := 118140960795 + 3022394 * 2 ^ 59
def prefixEnd_3022394 : Nat := 4983230072969 + 3 ^ 40 * 3022394 * 2
def baseEnd_3022394 : Nat := 1551940849265153103275269

theorem tailTrace_3022394 : CollatzResearch.WordTrace tailWord_3022394 prefixEnd_3022394 1551940849265153103275269 := by
  unfold tailWord_3022394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558941353097549161204559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73490510274926797763212157 27558941353097549161204559)
  ·
    refine ⟨41338412029646323741806839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27558941353097549161204559 41338412029646323741806839)
    ·
      refine ⟨62007618044469485612710259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41338412029646323741806839 62007618044469485612710259)
      ·
        refine ⟨93011427066704228419065389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62007618044469485612710259 93011427066704228419065389)
        ·
          refine ⟨34879285150014085657149521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93011427066704228419065389 34879285150014085657149521)
          ·
            refine ⟨26159463862510564242862141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34879285150014085657149521 26159463862510564242862141)
            ·
              refine ⟨9809798948441461591073303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26159463862510564242862141 9809798948441461591073303)
              ·
                refine ⟨14714698422662192386609955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809798948441461591073303 14714698422662192386609955)
                ·
                  refine ⟨22072047633993288579914933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14714698422662192386609955 22072047633993288579914933)
                  ·
                    refine ⟨2069254465686870804367025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22072047633993288579914933 2069254465686870804367025)
                    ·
                      refine ⟨1551940849265153103275269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069254465686870804367025 1551940849265153103275269)
                      ·
                        rfl

theorem cell23_3022394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_3022394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022394 prefixEnd_3022394 := by exact prefixLift 3022394
  have htrace : WordTrace (prefixWord ++ tailWord_3022394) baseStart_3022394 baseEnd_3022394 := by
    simpa [prefixWord, tailWord_3022394, baseEnd_3022394] using wordTrace_append hprefix tailTrace_3022394
  have hstable : (prefixWord ++ tailWord_3022394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022394).length < 2 ^ (prefixWord ++ tailWord_3022394).sum := by decide
  have hdescent : baseEnd_3022394 < baseStart_3022394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022418 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_3022418 : Nat := 118140960795 + 3022418 * 2 ^ 59
def prefixEnd_3022418 : Nat := 4983230072969 + 3 ^ 40 * 3022418 * 2
def baseEnd_3022418 : Nat := 1551953172800861009375159

theorem tailTrace_3022418 : CollatzResearch.WordTrace tailWord_3022418 prefixEnd_3022418 1551953172800861009375159 := by
  unfold tailWord_3022418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27559160191075812185922977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73491093842868832495794605 27559160191075812185922977)
  ·
    refine ⟨20669370143306859139442233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27559160191075812185922977 20669370143306859139442233)
    ·
      refine ⟨15502027607480144354581675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20669370143306859139442233 15502027607480144354581675)
      ·
        refine ⟨23253041411220216531872513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15502027607480144354581675 23253041411220216531872513)
        ·
          refine ⟨17439781058415162398904385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23253041411220216531872513 17439781058415162398904385)
          ·
            refine ⟨13079835793811371799178289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17439781058415162398904385 13079835793811371799178289)
            ·
              refine ⟨9809876845358528849383717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13079835793811371799178289 9809876845358528849383717)
              ·
                refine ⟨1839351908504724159259447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9809876845358528849383717 1839351908504724159259447)
                ·
                  refine ⟨2759027862757086238889171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839351908504724159259447 2759027862757086238889171)
                  ·
                    refine ⟨4138541794135629358333757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759027862757086238889171 4138541794135629358333757)
                    ·
                      refine ⟨1551953172800861009375159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138541794135629358333757 1551953172800861009375159)
                      ·
                        rfl

theorem cell23_3022418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_3022418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022418 prefixEnd_3022418 := by exact prefixLift 3022418
  have htrace : WordTrace (prefixWord ++ tailWord_3022418) baseStart_3022418 baseEnd_3022418 := by
    simpa [prefixWord, tailWord_3022418, baseEnd_3022418] using wordTrace_append hprefix tailTrace_3022418
  have hstable : (prefixWord ++ tailWord_3022418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022418).length < 2 ^ (prefixWord ++ tailWord_3022418).sum := by decide
  have hdescent : baseEnd_3022418 < baseStart_3022418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022441 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 3, 2, 2]
def baseStart_3022441 : Nat := 118140960795 + 3022441 * 2 ^ 59
def prefixEnd_3022441 : Nat := 4983230072969 + 3 ^ 40 * 3022441 * 2
def baseEnd_3022441 : Nat := 1551964982855914419387553

theorem tailTrace_3022441 : CollatzResearch.WordTrace tailWord_3022441 prefixEnd_3022441 1551964982855914419387553 := by
  unfold tailWord_3022441
  simp only [CollatzResearch.WordTrace]
  refine ⟨110237479643219923671779177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73491653095479949114519451 110237479643219923671779177)
  ·
    refine ⟨82678109732414942753834383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110237479643219923671779177 82678109732414942753834383)
    ·
      refine ⟨124017164598622414130751575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82678109732414942753834383 124017164598622414130751575)
      ·
        refine ⟨186025746897933621196127363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124017164598622414130751575 186025746897933621196127363)
        ·
          refine ⟨279038620346900431794191045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186025746897933621196127363 279038620346900431794191045)
          ·
            refine ⟨52319741315043830961410821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279038620346900431794191045 52319741315043830961410821)
            ·
              refine ⟨9809951496570718305264529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52319741315043830961410821 9809951496570718305264529)
              ·
                refine ⟨7357463622428038728948397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9809951496570718305264529 7357463622428038728948397)
                ·
                  refine ⟨2759048858410514523355649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7357463622428038728948397 2759048858410514523355649)
                  ·
                    refine ⟨2069286643807885892516737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759048858410514523355649 2069286643807885892516737)
                    ·
                      refine ⟨1551964982855914419387553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069286643807885892516737 1551964982855914419387553)
                      ·
                        rfl

theorem cell23_3022441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 2, 2].length) (baseStart_3022441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022441 prefixEnd_3022441 := by exact prefixLift 3022441
  have htrace : WordTrace (prefixWord ++ tailWord_3022441) baseStart_3022441 baseEnd_3022441 := by
    simpa [prefixWord, tailWord_3022441, baseEnd_3022441] using wordTrace_append hprefix tailTrace_3022441
  have hstable : (prefixWord ++ tailWord_3022441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022441).length < 2 ^ (prefixWord ++ tailWord_3022441).sum := by decide
  have hdescent : baseEnd_3022441 < baseStart_3022441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022458 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2]
def baseStart_3022458 : Nat := 118140960795 + 3022458 * 2 ^ 59
def prefixEnd_3022458 : Nat := 4983230072969 + 3 ^ 40 * 3022458 * 2
def baseEnd_3022458 : Nat := 1551973712027040852874975

theorem tailTrace_3022458 : CollatzResearch.WordTrace tailWord_3022458 prefixEnd_3022458 1551973712027040852874975 := by
  unfold tailWord_3022458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27559524921039583893787007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73492066456105557050098685 27559524921039583893787007)
  ·
    refine ⟨41339287381559375840680511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27559524921039583893787007 41339287381559375840680511)
    ·
      refine ⟨62008931072339063761020767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41339287381559375840680511 62008931072339063761020767)
      ·
        refine ⟨93013396608508595641531151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62008931072339063761020767 93013396608508595641531151)
        ·
          refine ⟨139520094912762893462296727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93013396608508595641531151 139520094912762893462296727)
          ·
            refine ⟨209280142369144340193445091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139520094912762893462296727 209280142369144340193445091)
            ·
              refine ⟨313920213553716510290167637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209280142369144340193445091 313920213553716510290167637)
              ·
                refine ⟨1839376251291307677481451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 313920213553716510290167637 1839376251291307677481451)
                ·
                  refine ⟨2759064376936961516222177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839376251291307677481451 2759064376936961516222177)
                  ·
                    refine ⟨2069298282702721137166633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759064376936961516222177 2069298282702721137166633)
                    ·
                      refine ⟨1551973712027040852874975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069298282702721137166633 1551973712027040852874975)
                      ·
                        rfl

theorem cell23_3022458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_3022458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022458 prefixEnd_3022458 := by exact prefixLift 3022458
  have htrace : WordTrace (prefixWord ++ tailWord_3022458) baseStart_3022458 baseEnd_3022458 := by
    simpa [prefixWord, tailWord_3022458, baseEnd_3022458] using wordTrace_append hprefix tailTrace_3022458
  have hstable : (prefixWord ++ tailWord_3022458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022458).length < 2 ^ (prefixWord ++ tailWord_3022458).sum := by decide
  have hdescent : baseEnd_3022458 < baseStart_3022458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022461 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_3022461 : Nat := 118140960795 + 3022461 * 2 ^ 59
def prefixEnd_3022461 : Nat := 4983230072969 + 3 ^ 40 * 3022461 * 2
def baseEnd_3022461 : Nat := 1551975252469004341137461

theorem tailTrace_3022461 : CollatzResearch.WordTrace tailWord_3022461 prefixEnd_3022461 1551975252469004341137461 := by
  unfold tailWord_3022461
  simp only [CollatzResearch.WordTrace]
  refine ⟨110238209103147467087507237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73492139402098311391671491 110238209103147467087507237)
  ·
    refine ⟨20669664206840150078907607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110238209103147467087507237 20669664206840150078907607)
    ·
      refine ⟨31004496310260225118361411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20669664206840150078907607 31004496310260225118361411)
      ·
        refine ⟨46506744465390337677542117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31004496310260225118361411 46506744465390337677542117)
        ·
          refine ⟨8720014587260688314539147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46506744465390337677542117 8720014587260688314539147)
          ·
            refine ⟨13080021880891032471808721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8720014587260688314539147 13080021880891032471808721)
            ·
              refine ⟨9810016410668274353856541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13080021880891032471808721 9810016410668274353856541)
              ·
                refine ⟨3678756154000602882696203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9810016410668274353856541 3678756154000602882696203)
                ·
                  refine ⟨5518134231000904324044305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678756154000602882696203 5518134231000904324044305)
                  ·
                    refine ⟨4138600673250678243033229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5518134231000904324044305 4138600673250678243033229)
                    ·
                      refine ⟨1551975252469004341137461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138600673250678243033229 1551975252469004341137461)
                      ·
                        rfl

theorem cell23_3022461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_3022461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022461 prefixEnd_3022461 := by exact prefixLift 3022461
  have htrace : WordTrace (prefixWord ++ tailWord_3022461) baseStart_3022461 baseEnd_3022461 := by
    simpa [prefixWord, tailWord_3022461, baseEnd_3022461] using wordTrace_append hprefix tailTrace_3022461
  have hstable : (prefixWord ++ tailWord_3022461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022461).length < 2 ^ (prefixWord ++ tailWord_3022461).sum := by decide
  have hdescent : baseEnd_3022461 < baseStart_3022461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022475 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 1, 2, 2]
def baseStart_3022475 : Nat := 118140960795 + 3022475 * 2 ^ 59
def prefixEnd_3022475 : Nat := 4983230072969 + 3 ^ 40 * 3022475 * 2
def baseEnd_3022475 : Nat := 1551982441198167286362397

theorem tailTrace_3022475 : CollatzResearch.WordTrace tailWord_3022475 prefixEnd_3022475 1551982441198167286362397 := by
  unfold tailWord_3022475
  simp only [CollatzResearch.WordTrace]
  refine ⟨110238719725096747478516879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73492479816731164985677919 110238719725096747478516879)
  ·
    refine ⟨165358079587645121217775319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110238719725096747478516879 165358079587645121217775319)
    ·
      refine ⟨248037119381467681826662979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165358079587645121217775319 248037119381467681826662979)
      ·
        refine ⟨372055679072201522739994469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248037119381467681826662979 372055679072201522739994469)
        ·
          refine ⟨69760439826037785513748963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372055679072201522739994469 69760439826037785513748963)
          ·
            refine ⟨104640659739056678270623445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69760439826037785513748963 104640659739056678270623445)
            ·
              refine ⟨2452515462634140896967737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 104640659739056678270623445 2452515462634140896967737)
              ·
                refine ⟨1839386596975605672725803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452515462634140896967737 1839386596975605672725803)
                ·
                  refine ⟨2759079895463408509088705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839386596975605672725803 2759079895463408509088705)
                  ·
                    refine ⟨2069309921597556381816529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759079895463408509088705 2069309921597556381816529)
                    ·
                      refine ⟨1551982441198167286362397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069309921597556381816529 1551982441198167286362397)
                      ·
                        rfl

theorem cell23_3022475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 2, 2].length) (baseStart_3022475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022475 prefixEnd_3022475 := by exact prefixLift 3022475
  have htrace : WordTrace (prefixWord ++ tailWord_3022475) baseStart_3022475 baseEnd_3022475 := by
    simpa [prefixWord, tailWord_3022475, baseEnd_3022475] using wordTrace_append hprefix tailTrace_3022475
  have hstable : (prefixWord ++ tailWord_3022475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022475).length < 2 ^ (prefixWord ++ tailWord_3022475).sum := by decide
  have hdescent : baseEnd_3022475 < baseStart_3022475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022495 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3022495 : Nat := 118140960795 + 3022495 * 2 ^ 59
def prefixEnd_3022495 : Nat := 4983230072969 + 3 ^ 40 * 3022495 * 2
def baseEnd_3022495 : Nat := 1551992710811257208112305

theorem tailTrace_3022495 : CollatzResearch.WordTrace tailWord_3022495 prefixEnd_3022495 1551992710811257208112305 := by
  unfold tailWord_3022495
  simp only [CollatzResearch.WordTrace]
  refine ⟨110239449185024290894244939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73492966123349527262829959 110239449185024290894244939)
  ·
    refine ⟨165359173777536436341367409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110239449185024290894244939 165359173777536436341367409)
    ·
      refine ⟨124019380333152327256025557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165359173777536436341367409 124019380333152327256025557)
      ·
        refine ⟨2906704226558257670063099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 124019380333152327256025557 2906704226558257670063099)
        ·
          refine ⟨4360056339837386505094649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906704226558257670063099 4360056339837386505094649)
          ·
            refine ⟨3270042254878039878820987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360056339837386505094649 3270042254878039878820987)
            ·
              refine ⟨4905063382317059818231481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270042254878039878820987 4905063382317059818231481)
              ·
                refine ⟨3678797536737794863673611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4905063382317059818231481 3678797536737794863673611)
                ·
                  refine ⟨5518196305106692295510417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678797536737794863673611 5518196305106692295510417)
                  ·
                    refine ⟨4138647228830019221632813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5518196305106692295510417 4138647228830019221632813)
                    ·
                      refine ⟨1551992710811257208112305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138647228830019221632813 1551992710811257208112305)
                      ·
                        rfl

theorem cell23_3022495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3022495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022495 prefixEnd_3022495 := by exact prefixLift 3022495
  have htrace : WordTrace (prefixWord ++ tailWord_3022495) baseStart_3022495 baseEnd_3022495 := by
    simpa [prefixWord, tailWord_3022495, baseEnd_3022495] using wordTrace_append hprefix tailTrace_3022495
  have hstable : (prefixWord ++ tailWord_3022495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022495).length < 2 ^ (prefixWord ++ tailWord_3022495).sum := by decide
  have hdescent : baseEnd_3022495 < baseStart_3022495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022541 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3022541 : Nat := 118140960795 + 3022541 * 2 ^ 59
def prefixEnd_3022541 : Nat := 4983230072969 + 3 ^ 40 * 3022541 * 2
def baseEnd_3022541 : Nat := 517338776973788009379031

theorem tailTrace_3022541 : CollatzResearch.WordTrace tailWord_3022541 prefixEnd_3022541 517338776973788009379031 := by
  unfold tailWord_3022541
  simp only [CollatzResearch.WordTrace]
  refine ⟨110241126942857640750419477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73494084628571760500279651 110241126942857640750419477)
  ·
    refine ⟨5167552825446451910175913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110241126942857640750419477 5167552825446451910175913)
    ·
      refine ⟨3875664619084838932631935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5167552825446451910175913 3875664619084838932631935)
      ·
        refine ⟨5813496928627258398947903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3875664619084838932631935 5813496928627258398947903)
        ·
          refine ⟨8720245392940887598421855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5813496928627258398947903 8720245392940887598421855)
          ·
            refine ⟨13080368089411331397632783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8720245392940887598421855 13080368089411331397632783)
            ·
              refine ⟨19620552134116997096449175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13080368089411331397632783 19620552134116997096449175)
              ·
                refine ⟨29430828201175495644673763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19620552134116997096449175 29430828201175495644673763)
                ·
                  refine ⟨44146242301763243467010645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29430828201175495644673763 44146242301763243467010645)
                  ·
                    refine ⟨517338776973788009379031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44146242301763243467010645 517338776973788009379031)
                    ·
                      rfl

theorem cell23_3022541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3022541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022541 prefixEnd_3022541 := by exact prefixLift 3022541
  have htrace : WordTrace (prefixWord ++ tailWord_3022541) baseStart_3022541 baseEnd_3022541 := by
    simpa [prefixWord, tailWord_3022541, baseEnd_3022541] using wordTrace_append hprefix tailTrace_3022541
  have hstable : (prefixWord ++ tailWord_3022541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022541).length < 2 ^ (prefixWord ++ tailWord_3022541).sum := by decide
  have hdescent : baseEnd_3022541 < baseStart_3022541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022548 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3022548 : Nat := 118140960795 + 3022548 * 2 ^ 59
def prefixEnd_3022548 : Nat := 4983230072969 + 3 ^ 40 * 3022548 * 2
def baseEnd_3022548 : Nat := 1552019925285945500749561

theorem tailTrace_3022548 : CollatzResearch.WordTrace tailWord_3022548 prefixEnd_3022548 1552019925285945500749561 := by
  unfold tailWord_3022548
  simp only [CollatzResearch.WordTrace]
  refine ⟨55120691126916140472962149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73494254835888187297282865 55120691126916140472962149)
  ·
    refine ⟨10335129586296776338680403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55120691126916140472962149 10335129586296776338680403)
    ·
      refine ⟨15502694379445164508020605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10335129586296776338680403 15502694379445164508020605)
      ·
        refine ⟨5813510392291936690507727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15502694379445164508020605 5813510392291936690507727)
        ·
          refine ⟨8720265588437905035761591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5813510392291936690507727 8720265588437905035761591)
          ·
            refine ⟨13080398382656857553642387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8720265588437905035761591 13080398382656857553642387)
            ·
              refine ⟨19620597573985286330463581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13080398382656857553642387 19620597573985286330463581)
              ·
                refine ⟨7357724090244482373923843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19620597573985286330463581 7357724090244482373923843)
                ·
                  refine ⟨11036586135366723560885765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357724090244482373923843 11036586135366723560885765)
                  ·
                    refine ⟨2069359900381260667666081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11036586135366723560885765 2069359900381260667666081)
                    ·
                      refine ⟨1552019925285945500749561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069359900381260667666081 1552019925285945500749561)
                      ·
                        rfl

theorem cell23_3022548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3022548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022548 prefixEnd_3022548 := by exact prefixLift 3022548
  have htrace : WordTrace (prefixWord ++ tailWord_3022548) baseStart_3022548 baseEnd_3022548 := by
    simpa [prefixWord, tailWord_3022548, baseEnd_3022548] using wordTrace_append hprefix tailTrace_3022548
  have hstable : (prefixWord ++ tailWord_3022548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022548).length < 2 ^ (prefixWord ++ tailWord_3022548).sum := by decide
  have hdescent : baseEnd_3022548 < baseStart_3022548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022554 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_3022554 : Nat := 118140960795 + 3022554 * 2 ^ 59
def prefixEnd_3022554 : Nat := 4983230072969 + 3 ^ 40 * 3022554 * 2
def baseEnd_3022554 : Nat := 172447000685541386363837

theorem tailTrace_3022554 : CollatzResearch.WordTrace tailWord_3022554 prefixEnd_3022554 172447000685541386363837 := by
  unfold tailWord_3022554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27560400272952635992660679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73494400727873695980428477 27560400272952635992660679)
  ·
    refine ⟨41340600409428953988991019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27560400272952635992660679 41340600409428953988991019)
    ·
      refine ⟨62010900614143430983486529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41340600409428953988991019 62010900614143430983486529)
      ·
        refine ⟨46508175460607573237614897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62010900614143430983486529 46508175460607573237614897)
        ·
          refine ⟨34881131595455679928211173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46508175460607573237614897 34881131595455679928211173)
          ·
            refine ⟨6540212174147939986539595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34881131595455679928211173 6540212174147939986539595)
            ·
              refine ⟨9810318261221909979809393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540212174147939986539595 9810318261221909979809393)
              ·
                refine ⟨7357738695916432484857045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9810318261221909979809393 7357738695916432484857045)
                ·
                  refine ⟨172447000685541386363837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7357738695916432484857045 172447000685541386363837)
                  ·
                    rfl

theorem cell23_3022554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_3022554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022554 prefixEnd_3022554 := by exact prefixLift 3022554
  have htrace : WordTrace (prefixWord ++ tailWord_3022554) baseStart_3022554 baseEnd_3022554 := by
    simpa [prefixWord, tailWord_3022554, baseEnd_3022554] using wordTrace_append hprefix tailTrace_3022554
  have hstable : (prefixWord ++ tailWord_3022554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022554).length < 2 ^ (prefixWord ++ tailWord_3022554).sum := by decide
  have hdescent : baseEnd_3022554 < baseStart_3022554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022564 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_3022564 : Nat := 118140960795 + 3022564 * 2 ^ 59
def prefixEnd_3022564 : Nat := 4983230072969 + 3 ^ 40 * 3022564 * 2
def baseEnd_3022564 : Nat := 1552028140976417438149487

theorem tailTrace_3022564 : CollatzResearch.WordTrace tailWord_3022564 prefixEnd_3022564 1552028140976417438149487 := by
  unfold tailWord_3022564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55120982910887157839253373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73494643881182877119004497 55120982910887157839253373)
  ·
    refine ⟨20670368591582684189720015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55120982910887157839253373 20670368591582684189720015)
    ·
      refine ⟨31005552887374026284580023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20670368591582684189720015 31005552887374026284580023)
      ·
        refine ⟨46508329331061039426870035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31005552887374026284580023 46508329331061039426870035)
        ·
          refine ⟨69762493996591559140305053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46508329331061039426870035 69762493996591559140305053)
          ·
            refine ⟨26160935248721834677614395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69762493996591559140305053 26160935248721834677614395)
            ·
              refine ⟨39241402873082752016421593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26160935248721834677614395 39241402873082752016421593)
              ·
                refine ⟨29431052154812064012316195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39241402873082752016421593 29431052154812064012316195)
                ·
                  refine ⟨44146578232218096018474293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29431052154812064012316195 44146578232218096018474293)
                  ·
                    refine ⟨4138741709270446501731965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44146578232218096018474293 4138741709270446501731965)
                    ·
                      refine ⟨1552028140976417438149487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138741709270446501731965 1552028140976417438149487)
                      ·
                        rfl

theorem cell23_3022564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_3022564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022564 prefixEnd_3022564 := by exact prefixLift 3022564
  have htrace : WordTrace (prefixWord ++ tailWord_3022564) baseStart_3022564 baseEnd_3022564 := by
    simpa [prefixWord, tailWord_3022564, baseEnd_3022564] using wordTrace_append hprefix tailTrace_3022564
  have hstable : (prefixWord ++ tailWord_3022564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022564).length < 2 ^ (prefixWord ++ tailWord_3022564).sum := by decide
  have hdescent : baseEnd_3022564 < baseStart_3022564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022582 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_3022582 : Nat := 118140960795 + 3022582 * 2 ^ 59
def prefixEnd_3022582 : Nat := 4983230072969 + 3 ^ 40 * 3022582 * 2
def baseEnd_3022582 : Nat := 1552037383628198367724405

theorem tailTrace_3022582 : CollatzResearch.WordTrace tailWord_3022582 prefixEnd_3022582 1552037383628198367724405 := by
  unfold tailWord_3022582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890163895981819047041375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73495081557139403168441333 6890163895981819047041375)
  ·
    refine ⟨10335245843972728570562063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6890163895981819047041375 10335245843972728570562063)
    ·
      refine ⟨15502868765959092855843095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10335245843972728570562063 15502868765959092855843095)
      ·
        refine ⟨23254303148938639283764643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15502868765959092855843095 23254303148938639283764643)
        ·
          refine ⟨34881454723407958925646965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23254303148938639283764643 34881454723407958925646965)
          ·
            refine ⟨3270136380319496149279403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34881454723407958925646965 3270136380319496149279403)
            ·
              refine ⟨4905204570479244223919105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270136380319496149279403 4905204570479244223919105)
              ·
                refine ⟨3678903427859433167939329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4905204570479244223919105 3678903427859433167939329)
                ·
                  refine ⟨2759177570894574875954497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3678903427859433167939329 2759177570894574875954497)
                  ·
                    refine ⟨2069383178170931156965873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759177570894574875954497 2069383178170931156965873)
                    ·
                      refine ⟨1552037383628198367724405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069383178170931156965873 1552037383628198367724405)
                      ·
                        rfl

theorem cell23_3022582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_3022582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022582 prefixEnd_3022582 := by exact prefixLift 3022582
  have htrace : WordTrace (prefixWord ++ tailWord_3022582) baseStart_3022582 baseEnd_3022582 := by
    simpa [prefixWord, tailWord_3022582, baseEnd_3022582] using wordTrace_append hprefix tailTrace_3022582
  have hstable : (prefixWord ++ tailWord_3022582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022582).length < 2 ^ (prefixWord ++ tailWord_3022582).sum := by decide
  have hdescent : baseEnd_3022582 < baseStart_3022582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022604 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3022604 : Nat := 118140960795 + 3022604 * 2 ^ 59
def prefixEnd_3022604 : Nat := 4983230072969 + 3 ^ 40 * 3022604 * 2
def baseEnd_3022604 : Nat := 1552048680202597281649303

theorem tailTrace_3022604 : CollatzResearch.WordTrace tailWord_3022604 prefixEnd_3022604 1552048680202597281649303 := by
  unfold tailWord_3022604
  simp only [CollatzResearch.WordTrace]
  refine ⟨55121712370814701254981433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73495616494419601673308577 55121712370814701254981433)
  ·
    refine ⟨41341284278111025941236075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55121712370814701254981433 41341284278111025941236075)
    ·
      refine ⟨62011926417166538911854113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41341284278111025941236075 62011926417166538911854113)
      ·
        refine ⟨46508944812874904183890585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62011926417166538911854113 46508944812874904183890585)
        ·
          refine ⟨34881708609656178137917939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46508944812874904183890585 34881708609656178137917939)
          ·
            refine ⟨52322562914484267206876909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34881708609656178137917939 52322562914484267206876909)
            ·
              refine ⟨19620961092931600202578841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52322562914484267206876909 19620961092931600202578841)
              ·
                refine ⟨14715720819698700151934131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19620961092931600202578841 14715720819698700151934131)
                ·
                  refine ⟨22073581229548050227901197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14715720819698700151934131 22073581229548050227901197)
                  ·
                    refine ⟨8277592961080518835462949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22073581229548050227901197 8277592961080518835462949)
                    ·
                      refine ⟨1552048680202597281649303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8277592961080518835462949 1552048680202597281649303)
                      ·
                        rfl

theorem cell23_3022604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3022604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022604 prefixEnd_3022604 := by exact prefixLift 3022604
  have htrace : WordTrace (prefixWord ++ tailWord_3022604) baseStart_3022604 baseEnd_3022604 := by
    simpa [prefixWord, tailWord_3022604, baseEnd_3022604] using wordTrace_append hprefix tailTrace_3022604
  have hstable : (prefixWord ++ tailWord_3022604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022604).length < 2 ^ (prefixWord ++ tailWord_3022604).sum := by decide
  have hdescent : baseEnd_3022604 < baseStart_3022604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022641 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_3022641 : Nat := 118140960795 + 3022641 * 2 ^ 59
def prefixEnd_3022641 : Nat := 4983230072969 + 3 ^ 40 * 3022641 * 2
def baseEnd_3022641 : Nat := 1552067678986813636886633

theorem tailTrace_3022641 : CollatzResearch.WordTrace tailWord_3022641 prefixEnd_3022641 1552067678986813636886633 := by
  unfold tailWord_3022641
  simp only [CollatzResearch.WordTrace]
  refine ⟨110244774242495357829059777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73496516161663571886039851 110244774242495357829059777)
  ·
    refine ⟨82683580681871518371794833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110244774242495357829059777 82683580681871518371794833)
    ·
      refine ⟨62012685511403638778846125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82683580681871518371794833 62012685511403638778846125)
      ·
        refine ⟨23254757066776364542067297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62012685511403638778846125 23254757066776364542067297)
        ·
          refine ⟨17441067800082273406550473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23254757066776364542067297 17441067800082273406550473)
          ·
            refine ⟨13080800850061705054912855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17441067800082273406550473 13080800850061705054912855)
            ·
              refine ⟨19621201275092557582369283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13080800850061705054912855 19621201275092557582369283)
              ·
                refine ⟨29431801912638836373553925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19621201275092557582369283 29431801912638836373553925)
                ·
                  refine ⟨5518462858619781820041361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29431801912638836373553925 5518462858619781820041361)
                  ·
                    refine ⟨4138847143964836365031021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5518462858619781820041361 4138847143964836365031021)
                    ·
                      refine ⟨1552067678986813636886633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138847143964836365031021 1552067678986813636886633)
                      ·
                        rfl

theorem cell23_3022641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_3022641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022641 prefixEnd_3022641 := by exact prefixLift 3022641
  have htrace : WordTrace (prefixWord ++ tailWord_3022641) baseStart_3022641 baseEnd_3022641 := by
    simpa [prefixWord, tailWord_3022641, baseEnd_3022641] using wordTrace_append hprefix tailTrace_3022641
  have hstable : (prefixWord ++ tailWord_3022641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022641).length < 2 ^ (prefixWord ++ tailWord_3022641).sum := by decide
  have hdescent : baseEnd_3022641 < baseStart_3022641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022648 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 3, 4]
def baseStart_3022648 : Nat := 118140960795 + 3022648 * 2 ^ 59
def prefixEnd_3022648 : Nat := 4983230072969 + 3 ^ 40 * 3022648 * 2
def baseEnd_3022648 : Nat := 517357091117131703166367

theorem tailTrace_3022648 : CollatzResearch.WordTrace tailWord_3022648 prefixEnd_3022648 517357091117131703166367 := by
  unfold tailWord_3022648
  simp only [CollatzResearch.WordTrace]
  refine ⟨55122514776734999012282299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73496686368979998683043065 55122514776734999012282299)
  ·
    refine ⟨82683772165102498518423449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55122514776734999012282299 82683772165102498518423449)
    ·
      refine ⟨62012829123826873888817587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82683772165102498518423449 62012829123826873888817587)
      ·
        refine ⟨93019243685740310833226381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62012829123826873888817587 93019243685740310833226381)
        ·
          refine ⟨34882216382152616562459893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93019243685740310833226381 34882216382152616562459893)
          ·
            refine ⟨3270207785826807802730615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34882216382152616562459893 3270207785826807802730615)
            ·
              refine ⟨4905311678740211704095923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270207785826807802730615 4905311678740211704095923)
              ·
                refine ⟨7357967518110317556143885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905311678740211704095923 7357967518110317556143885)
                ·
                  refine ⟨2759237819291369083553957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7357967518110317556143885 2759237819291369083553957)
                  ·
                    refine ⟨517357091117131703166367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2759237819291369083553957 517357091117131703166367)
                    ·
                      rfl

theorem cell23_3022648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_3022648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022648 prefixEnd_3022648 := by exact prefixLift 3022648
  have htrace : WordTrace (prefixWord ++ tailWord_3022648) baseStart_3022648 baseEnd_3022648 := by
    simpa [prefixWord, tailWord_3022648, baseEnd_3022648] using wordTrace_append hprefix tailTrace_3022648
  have hstable : (prefixWord ++ tailWord_3022648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022648).length < 2 ^ (prefixWord ++ tailWord_3022648).sum := by decide
  have hdescent : baseEnd_3022648 < baseStart_3022648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022704 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_3022704 : Nat := 118140960795 + 3022704 * 2 ^ 59
def prefixEnd_3022704 : Nat := 4983230072969 + 3 ^ 40 * 3022704 * 2
def baseEnd_3022704 : Nat := 517366676089348963466281

theorem tailTrace_3022704 : CollatzResearch.WordTrace tailWord_3022704 prefixEnd_3022704 517366676089348963466281 := by
  unfold tailWord_3022704
  simp only [CollatzResearch.WordTrace]
  refine ⟨55123536020633559794301583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73498048027511413059068777 55123536020633559794301583)
  ·
    refine ⟨82685304030950339691452375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55123536020633559794301583 82685304030950339691452375)
    ·
      refine ⟨124027956046425509537178563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82685304030950339691452375 124027956046425509537178563)
      ·
        refine ⟨186041934069638264305767845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124027956046425509537178563 186041934069638264305767845)
        ·
          refine ⟨34882862638057174557331471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186041934069638264305767845 34882862638057174557331471)
          ·
            refine ⟨52324293957085761835997207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34882862638057174557331471 52324293957085761835997207)
            ·
              refine ⟨78486440935628642753995811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52324293957085761835997207 78486440935628642753995811)
              ·
                refine ⟨117729661403442964130993717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78486440935628642753995811 117729661403442964130993717)
                ·
                  refine ⟨11037155756572777887280661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117729661403442964130993717 11037155756572777887280661)
                  ·
                    refine ⟨517366676089348963466281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11037155756572777887280661 517366676089348963466281)
                    ·
                      rfl

theorem cell23_3022704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_3022704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022704 prefixEnd_3022704 := by exact prefixLift 3022704
  have htrace : WordTrace (prefixWord ++ tailWord_3022704) baseStart_3022704 baseEnd_3022704 := by
    simpa [prefixWord, tailWord_3022704, baseEnd_3022704] using wordTrace_append hprefix tailTrace_3022704
  have hstable : (prefixWord ++ tailWord_3022704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022704).length < 2 ^ (prefixWord ++ tailWord_3022704).sum := by decide
  have hdescent : baseEnd_3022704 < baseStart_3022704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022705 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 1, 1, 3]
def baseStart_3022705 : Nat := 118140960795 + 3022705 * 2 ^ 59
def prefixEnd_3022705 : Nat := 4983230072969 + 3 ^ 40 * 3022705 * 2
def baseEnd_3022705 : Nat := 1552100541748701386486339

theorem tailTrace_3022705 : CollatzResearch.WordTrace tailWord_3022705 prefixEnd_3022705 1552100541748701386486339 := by
  unfold tailWord_3022705
  simp only [CollatzResearch.WordTrace]
  refine ⟨110247108514263496759389569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73498072342842331172926379 110247108514263496759389569)
  ·
    refine ⟨82685331385697622569542177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110247108514263496759389569 82685331385697622569542177)
    ·
      refine ⟨62013998539273216927156633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82685331385697622569542177 62013998539273216927156633)
      ·
        refine ⟨46510498904454912695367475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62013998539273216927156633 46510498904454912695367475)
        ·
          refine ⟨69765748356682369043051213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46510498904454912695367475 69765748356682369043051213)
          ·
            refine ⟨26162155633755888391144205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69765748356682369043051213 26162155633755888391144205)
            ·
              refine ⟨9810808362658458146679077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26162155633755888391144205 9810808362658458146679077)
              ·
                refine ⟨1839526567998460902502327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9810808362658458146679077 1839526567998460902502327)
                ·
                  refine ⟨2759289851997691353753491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839526567998460902502327 2759289851997691353753491)
                  ·
                    refine ⟨4138934777996537030630237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759289851997691353753491 4138934777996537030630237)
                    ·
                      refine ⟨1552100541748701386486339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138934777996537030630237 1552100541748701386486339)
                      ·
                        rfl

theorem cell23_3022705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_3022705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022705 prefixEnd_3022705 := by exact prefixLift 3022705
  have htrace : WordTrace (prefixWord ++ tailWord_3022705) baseStart_3022705 baseEnd_3022705 := by
    simpa [prefixWord, tailWord_3022705, baseEnd_3022705] using wordTrace_append hprefix tailTrace_3022705
  have hstable : (prefixWord ++ tailWord_3022705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022705).length < 2 ^ (prefixWord ++ tailWord_3022705).sum := by decide
  have hdescent : baseEnd_3022705 < baseStart_3022705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022711 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 6, 2]
def baseStart_3022711 : Nat := 118140960795 + 3022711 * 2 ^ 59
def prefixEnd_3022711 : Nat := 4983230072969 + 3 ^ 40 * 3022711 * 2
def baseEnd_3022711 : Nat := 1552103622632628363011311

theorem tailTrace_3022711 : CollatzResearch.WordTrace tailWord_3022711 prefixEnd_3022711 1552103622632628363011311 := by
  unfold tailWord_3022711
  simp only [CollatzResearch.WordTrace]
  refine ⟨110247327352241759784107987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73498218234827839856071991 110247327352241759784107987)
  ·
    refine ⟨165370991028362639676161981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110247327352241759784107987 165370991028362639676161981)
    ·
      refine ⟨62014121635635989878560743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165370991028362639676161981 62014121635635989878560743)
      ·
        refine ⟨93021182453453984817841115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62014121635635989878560743 93021182453453984817841115)
        ·
          refine ⟨139531773680180977226761673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93021182453453984817841115 139531773680180977226761673)
          ·
            refine ⟨104648830260135732920071255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139531773680180977226761673 104648830260135732920071255)
            ·
              refine ⟨156973245390203599380106883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104648830260135732920071255 156973245390203599380106883)
              ·
                refine ⟨235459868085305399070160325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156973245390203599380106883 235459868085305399070160325)
                ·
                  refine ⟨44148725265994762325655061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235459868085305399070160325 44148725265994762325655061)
                  ·
                    refine ⟨2069471496843504484015081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44148725265994762325655061 2069471496843504484015081)
                    ·
                      refine ⟨1552103622632628363011311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069471496843504484015081 1552103622632628363011311)
                      ·
                        rfl

theorem cell23_3022711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_3022711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022711 prefixEnd_3022711 := by exact prefixLift 3022711
  have htrace : WordTrace (prefixWord ++ tailWord_3022711) baseStart_3022711 baseEnd_3022711 := by
    simpa [prefixWord, tailWord_3022711, baseEnd_3022711] using wordTrace_append hprefix tailTrace_3022711
  have hstable : (prefixWord ++ tailWord_3022711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022711).length < 2 ^ (prefixWord ++ tailWord_3022711).sum := by decide
  have hdescent : baseEnd_3022711 < baseStart_3022711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022738 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3022738 : Nat := 118140960795 + 3022738 * 2 ^ 59
def prefixEnd_3022738 : Nat := 4983230072969 + 3 ^ 40 * 3022738 * 2
def baseEnd_3022738 : Nat := 517372495536766585791229

theorem tailTrace_3022738 : CollatzResearch.WordTrace tailWord_3022738 prefixEnd_3022738 517372495536766585791229 := by
  unfold tailWord_3022738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27562078030785985848835217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73498874748762628930227245 27562078030785985848835217)
  ·
    refine ⟨20671558523089489386626413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27562078030785985848835217 20671558523089489386626413)
    ·
      refine ⟨7751834446158558519984905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20671558523089489386626413 7751834446158558519984905)
      ·
        refine ⟨5813875834618918889988679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7751834446158558519984905 5813875834618918889988679)
        ·
          refine ⟨8720813751928378334983019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5813875834618918889988679 8720813751928378334983019)
          ·
            refine ⟨13081220627892567502474529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8720813751928378334983019 13081220627892567502474529)
            ·
              refine ⟨9810915470919425626855897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13081220627892567502474529 9810915470919425626855897)
              ·
                refine ⟨7358186603189569220141923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9810915470919425626855897 7358186603189569220141923)
                ·
                  refine ⟨11037279904784353830212885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7358186603189569220141923 11037279904784353830212885)
                  ·
                    refine ⟨517372495536766585791229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11037279904784353830212885 517372495536766585791229)
                    ·
                      rfl

theorem cell23_3022738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3022738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022738 prefixEnd_3022738 := by exact prefixLift 3022738
  have htrace : WordTrace (prefixWord ++ tailWord_3022738) baseStart_3022738 baseEnd_3022738 := by
    simpa [prefixWord, tailWord_3022738, baseEnd_3022738] using wordTrace_append hprefix tailTrace_3022738
  have hstable : (prefixWord ++ tailWord_3022738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022738).length < 2 ^ (prefixWord ++ tailWord_3022738).sum := by decide
  have hdescent : baseEnd_3022738 < baseStart_3022738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022741 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_3022741 : Nat := 118140960795 + 3022741 * 2 ^ 59
def prefixEnd_3022741 : Nat := 4983230072969 + 3 ^ 40 * 3022741 * 2
def baseEnd_3022741 : Nat := 1552119027052263245636173

theorem tailTrace_3022741 : CollatzResearch.WordTrace tailWord_3022741 prefixEnd_3022741 1552119027052263245636173 := by
  unfold tailWord_3022741
  simp only [CollatzResearch.WordTrace]
  refine ⟨110248421542133074907700077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73498947694755383271800051 110248421542133074907700077)
  ·
    refine ⟨41343158078299903090387529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110248421542133074907700077 41343158078299903090387529)
    ·
      refine ⟨31007368558724927317790647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41343158078299903090387529 31007368558724927317790647)
      ·
        refine ⟨46511052838087390976685971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31007368558724927317790647 46511052838087390976685971)
        ·
          refine ⟨69766579257131086465028957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46511052838087390976685971 69766579257131086465028957)
          ·
            refine ⟨26162467221424157424385859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69766579257131086465028957 26162467221424157424385859)
            ·
              refine ⟨39243700832136236136578789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26162467221424157424385859 39243700832136236136578789)
              ·
                refine ⟨7358193906025544275608523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39243700832136236136578789 7358193906025544275608523)
                ·
                  refine ⟨11037290859038316413412785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7358193906025544275608523 11037290859038316413412785)
                  ·
                    refine ⟨8277968144278737310059589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11037290859038316413412785 8277968144278737310059589)
                    ·
                      refine ⟨1552119027052263245636173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8277968144278737310059589 1552119027052263245636173)
                      ·
                        rfl

theorem cell23_3022741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_3022741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022741 prefixEnd_3022741 := by exact prefixLift 3022741
  have htrace : WordTrace (prefixWord ++ tailWord_3022741) baseStart_3022741 baseEnd_3022741 := by
    simpa [prefixWord, tailWord_3022741, baseEnd_3022741] using wordTrace_append hprefix tailTrace_3022741
  have hstable : (prefixWord ++ tailWord_3022741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022741).length < 2 ^ (prefixWord ++ tailWord_3022741).sum := by decide
  have hdescent : baseEnd_3022741 < baseStart_3022741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022751 : List Nat := [1, 1, 2, 5, 3, 1, 10]
def baseStart_3022751 : Nat := 118140960795 + 3022751 * 2 ^ 59
def prefixEnd_3022751 : Nat := 4983230072969 + 3 ^ 40 * 3022751 * 2
def baseEnd_3022751 : Nat := 19162026689614916129767

theorem tailTrace_3022751 : CollatzResearch.WordTrace tailWord_3022751 prefixEnd_3022751 19162026689614916129767 := by
  unfold tailWord_3022751
  simp only [CollatzResearch.WordTrace]
  refine ⟨110248786272096846615564107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73499190848064564410376071 110248786272096846615564107)
  ·
    refine ⟨165373179408145269923346161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110248786272096846615564107 165373179408145269923346161)
    ·
      refine ⟨124029884556108952442509621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165373179408145269923346161 124029884556108952442509621)
      ·
        refine ⟨11627801677135214291485277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124029884556108952442509621 11627801677135214291485277)
        ·
          refine ⟨4360425628925705359306979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11627801677135214291485277 4360425628925705359306979)
          ·
            refine ⟨6540638443388558038960469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360425628925705359306979 6540638443388558038960469)
            ·
              refine ⟨19162026689614916129767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6540638443388558038960469 19162026689614916129767)
              ·
                rfl

theorem cell23_3022751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 10].length) (baseStart_3022751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022751 prefixEnd_3022751 := by exact prefixLift 3022751
  have htrace : WordTrace (prefixWord ++ tailWord_3022751) baseStart_3022751 baseEnd_3022751 := by
    simpa [prefixWord, tailWord_3022751, baseEnd_3022751] using wordTrace_append hprefix tailTrace_3022751
  have hstable : (prefixWord ++ tailWord_3022751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022751).length < 2 ^ (prefixWord ++ tailWord_3022751).sum := by decide
  have hdescent : baseEnd_3022751 < baseStart_3022751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022772 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3022772 : Nat := 118140960795 + 3022772 * 2 ^ 59
def prefixEnd_3022772 : Nat := 4983230072969 + 3 ^ 40 * 3022772 * 2
def baseEnd_3022772 : Nat := 517378314984184208116177

theorem tailTrace_3022772 : CollatzResearch.WordTrace tailWord_3022772 prefixEnd_3022772 517378314984184208116177 := by
  unfold tailWord_3022772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55124776102510383601039285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73499701470013844801385713 55124776102510383601039285)
  ·
    refine ⟨5167947759610348462597433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55124776102510383601039285 5167947759610348462597433)
    ·
      refine ⟨3875960819707761346948075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5167947759610348462597433 3875960819707761346948075)
      ·
        refine ⟨5813941229561642020422113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3875960819707761346948075 5813941229561642020422113)
        ·
          refine ⟨4360455922171231515316585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5813941229561642020422113 4360455922171231515316585)
          ·
            refine ⟨3270341941628423636487439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360455922171231515316585 3270341941628423636487439)
            ·
              refine ⟨4905512912442635454731159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270341941628423636487439 4905512912442635454731159)
              ·
                refine ⟨7358269368663953182096739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905512912442635454731159 7358269368663953182096739)
                ·
                  refine ⟨11037404052995929773145109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7358269368663953182096739 11037404052995929773145109)
                  ·
                    refine ⟨517378314984184208116177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11037404052995929773145109 517378314984184208116177)
                    ·
                      rfl

theorem cell23_3022772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3022772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022772 prefixEnd_3022772 := by exact prefixLift 3022772
  have htrace : WordTrace (prefixWord ++ tailWord_3022772) baseStart_3022772 baseEnd_3022772 := by
    simpa [prefixWord, tailWord_3022772, baseEnd_3022772] using wordTrace_append hprefix tailTrace_3022772
  have hstable : (prefixWord ++ tailWord_3022772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022772).length < 2 ^ (prefixWord ++ tailWord_3022772).sum := by decide
  have hdescent : baseEnd_3022772 < baseStart_3022772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022829 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3022829 : Nat := 118140960795 + 3022829 * 2 ^ 59
def prefixEnd_3022829 : Nat := 4983230072969 + 3 ^ 40 * 3022829 * 2
def baseEnd_3022829 : Nat := 1552164213349858901335769

theorem tailTrace_3022829 : CollatzResearch.WordTrace tailWord_3022829 prefixEnd_3022829 1552164213349858901335769 := by
  unfold tailWord_3022829
  simp only [CollatzResearch.WordTrace]
  refine ⟨110251631165814265936903541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73501087443876177291269027 110251631165814265936903541)
  ·
    refine ⟨10336090421795087431584707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110251631165814265936903541 10336090421795087431584707)
    ·
      refine ⟨15504135632692631147377061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336090421795087431584707 15504135632692631147377061)
      ·
        refine ⟨2907025431129868340133199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15504135632692631147377061 2907025431129868340133199)
        ·
          refine ⟨4360538146694802510199799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907025431129868340133199 4360538146694802510199799)
          ·
            refine ⟨6540807220042203765299699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360538146694802510199799 6540807220042203765299699)
            ·
              refine ⟨9811210830063305647949549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540807220042203765299699 9811210830063305647949549)
              ·
                refine ⟨3679204061273739617981081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9811210830063305647949549 3679204061273739617981081)
                ·
                  refine ⟨2759403045955304713485811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679204061273739617981081 2759403045955304713485811)
                  ·
                    refine ⟨4139104568932957070228717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759403045955304713485811 4139104568932957070228717)
                    ·
                      refine ⟨1552164213349858901335769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139104568932957070228717 1552164213349858901335769)
                      ·
                        rfl

theorem cell23_3022829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3022829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022829 prefixEnd_3022829 := by exact prefixLift 3022829
  have htrace : WordTrace (prefixWord ++ tailWord_3022829) baseStart_3022829 baseEnd_3022829 := by
    simpa [prefixWord, tailWord_3022829, baseEnd_3022829] using wordTrace_append hprefix tailTrace_3022829
  have hstable : (prefixWord ++ tailWord_3022829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022829).length < 2 ^ (prefixWord ++ tailWord_3022829).sum := by decide
  have hdescent : baseEnd_3022829 < baseStart_3022829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022831 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_3022831 : Nat := 118140960795 + 3022831 * 2 ^ 59
def prefixEnd_3022831 : Nat := 4983230072969 + 3 ^ 40 * 3022831 * 2
def baseEnd_3022831 : Nat := 1552165240311167893510759

theorem tailTrace_3022831 : CollatzResearch.WordTrace tailWord_3022831 prefixEnd_3022831 1552165240311167893510759 := by
  unfold tailWord_3022831
  simp only [CollatzResearch.WordTrace]
  refine ⟨110251704111807020278476347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73501136074538013518984231 110251704111807020278476347)
  ·
    refine ⟨165377556167710530417714521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110251704111807020278476347 165377556167710530417714521)
    ·
      refine ⟨124033167125782897813285891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165377556167710530417714521 124033167125782897813285891)
      ·
        refine ⟨186049750688674346719928837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124033167125782897813285891 186049750688674346719928837)
        ·
          refine ⟨34884328254126440009986657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186049750688674346719928837 34884328254126440009986657)
          ·
            refine ⟨26163246190594830007489993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34884328254126440009986657 26163246190594830007489993)
            ·
              refine ⟨19622434642946122505617495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26163246190594830007489993 19622434642946122505617495)
              ·
                refine ⟨29433651964419183758426243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19622434642946122505617495 29433651964419183758426243)
                ·
                  refine ⟨44150477946628775637639365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29433651964419183758426243 44150477946628775637639365)
                  ·
                    refine ⟨8278214614992895432057381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44150477946628775637639365 8278214614992895432057381)
                    ·
                      refine ⟨1552165240311167893510759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8278214614992895432057381 1552165240311167893510759)
                      ·
                        rfl

theorem cell23_3022831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_3022831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022831 prefixEnd_3022831 := by exact prefixLift 3022831
  have htrace : WordTrace (prefixWord ++ tailWord_3022831) baseStart_3022831 baseEnd_3022831 := by
    simpa [prefixWord, tailWord_3022831, baseEnd_3022831] using wordTrace_append hprefix tailTrace_3022831
  have hstable : (prefixWord ++ tailWord_3022831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022831).length < 2 ^ (prefixWord ++ tailWord_3022831).sum := by decide
  have hdescent : baseEnd_3022831 < baseStart_3022831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022869 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_3022869 : Nat := 118140960795 + 3022869 * 2 ^ 59
def prefixEnd_3022869 : Nat := 4983230072969 + 3 ^ 40 * 3022869 * 2
def baseEnd_3022869 : Nat := 1552184752576038744835585

theorem tailTrace_3022869 : CollatzResearch.WordTrace tailWord_3022869 prefixEnd_3022869 1552184752576038744835585 := by
  unfold tailWord_3022869
  simp only [CollatzResearch.WordTrace]
  refine ⟨110253090085669352768359661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73502060057112901845573107 110253090085669352768359661)
  ·
    refine ⟨41344908782126007288134873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110253090085669352768359661 41344908782126007288134873)
    ·
      refine ⟨31008681586594505466101155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41344908782126007288134873 31008681586594505466101155)
      ·
        refine ⟨46513022379891758199151733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31008681586594505466101155 46513022379891758199151733)
        ·
          refine ⟨4360595848114852331170475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46513022379891758199151733 4360595848114852331170475)
          ·
            refine ⟨6540893772172278496755713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360595848114852331170475 6540893772172278496755713)
            ·
              refine ⟨4905670329129208872566785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6540893772172278496755713 4905670329129208872566785)
              ·
                refine ⟨3679252746846906654425089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4905670329129208872566785 3679252746846906654425089)
                ·
                  refine ⟨2759439560135179990818817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679252746846906654425089 2759439560135179990818817)
                  ·
                    refine ⟨2069579670101384993114113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759439560135179990818817 2069579670101384993114113)
                    ·
                      refine ⟨1552184752576038744835585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069579670101384993114113 1552184752576038744835585)
                      ·
                        rfl

theorem cell23_3022869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_3022869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022869 prefixEnd_3022869 := by exact prefixLift 3022869
  have htrace : WordTrace (prefixWord ++ tailWord_3022869) baseStart_3022869 baseEnd_3022869 := by
    simpa [prefixWord, tailWord_3022869, baseEnd_3022869] using wordTrace_append hprefix tailTrace_3022869
  have hstable : (prefixWord ++ tailWord_3022869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022869).length < 2 ^ (prefixWord ++ tailWord_3022869).sum := by decide
  have hdescent : baseEnd_3022869 < baseStart_3022869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022908 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_3022908 : Nat := 118140960795 + 3022908 * 2 ^ 59
def prefixEnd_3022908 : Nat := 4983230072969 + 3 ^ 40 * 3022908 * 2
def baseEnd_3022908 : Nat := 1552204778321564092247905

theorem tailTrace_3022908 : CollatzResearch.WordTrace tailWord_3022908 prefixEnd_3022908 1552204778321564092247905 := by
  unfold tailWord_3022908
  simp only [CollatzResearch.WordTrace]
  refine ⟨55127256266264031214514689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73503008355018708286019585 55127256266264031214514689)
  ·
    refine ⟨41345442199698023410886017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55127256266264031214514689 41345442199698023410886017)
    ·
      refine ⟨31009081649773517558164513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41345442199698023410886017 31009081649773517558164513)
      ·
        refine ⟨23256811237330138168623385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31009081649773517558164513 23256811237330138168623385)
        ·
          refine ⟨17442608427997603626467539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23256811237330138168623385 17442608427997603626467539)
          ·
            refine ⟨26163912641996405439701309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17442608427997603626467539 26163912641996405439701309)
            ·
              refine ⟨9811467240748652039887991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26163912641996405439701309 9811467240748652039887991)
              ·
                refine ⟨14717200861122978059831987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9811467240748652039887991 14717200861122978059831987)
                ·
                  refine ⟨22075801291684467089747981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14717200861122978059831987 22075801291684467089747981)
                  ·
                    refine ⟨8278425484381675158655493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22075801291684467089747981 8278425484381675158655493)
                    ·
                      refine ⟨1552204778321564092247905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8278425484381675158655493 1552204778321564092247905)
                      ·
                        rfl

theorem cell23_3022908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_3022908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022908 prefixEnd_3022908 := by exact prefixLift 3022908
  have htrace : WordTrace (prefixWord ++ tailWord_3022908) baseStart_3022908 baseEnd_3022908 := by
    simpa [prefixWord, tailWord_3022908, baseEnd_3022908] using wordTrace_append hprefix tailTrace_3022908
  have hstable : (prefixWord ++ tailWord_3022908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022908).length < 2 ^ (prefixWord ++ tailWord_3022908).sum := by decide
  have hdescent : baseEnd_3022908 < baseStart_3022908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022921 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_3022921 : Nat := 118140960795 + 3022921 * 2 ^ 59
def prefixEnd_3022921 : Nat := 4983230072969 + 3 ^ 40 * 3022921 * 2
def baseEnd_3022921 : Nat := 1552211453570072541385345

theorem tailTrace_3022921 : CollatzResearch.WordTrace tailWord_3022921 prefixEnd_3022921 1552211453570072541385345 := by
  unfold tailWord_3022921
  simp only [CollatzResearch.WordTrace]
  refine ⟨110254986681480965649252617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73503324454320643766168411 110254986681480965649252617)
  ·
    refine ⟨82691240011110724236939463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110254986681480965649252617 82691240011110724236939463)
    ·
      refine ⟨124036860016666086355409195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82691240011110724236939463 124036860016666086355409195)
      ·
        refine ⟨186055290024999129533113793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124036860016666086355409195 186055290024999129533113793)
        ·
          refine ⟨139541467518749347149835345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186055290024999129533113793 139541467518749347149835345)
          ·
            refine ⟨104656100639062010362376509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139541467518749347149835345 104656100639062010362376509)
            ·
              refine ⟨39246037739648253885891191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104656100639062010362376509 39246037739648253885891191)
              ·
                refine ⟨58869056609472380828836787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39246037739648253885891191 58869056609472380828836787)
                ·
                  refine ⟨88303584914208571243255181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58869056609472380828836787 88303584914208571243255181)
                  ·
                    refine ⟨33113844342828214216220693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88303584914208571243255181 33113844342828214216220693)
                    ·
                      refine ⟨1552211453570072541385345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33113844342828214216220693 1552211453570072541385345)
                      ·
                        rfl

theorem cell23_3022921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_3022921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022921 prefixEnd_3022921 := by exact prefixLift 3022921
  have htrace : WordTrace (prefixWord ++ tailWord_3022921) baseStart_3022921 baseEnd_3022921 := by
    simpa [prefixWord, tailWord_3022921, baseEnd_3022921] using wordTrace_append hprefix tailTrace_3022921
  have hstable : (prefixWord ++ tailWord_3022921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022921).length < 2 ^ (prefixWord ++ tailWord_3022921).sum := by decide
  have hdescent : baseEnd_3022921 < baseStart_3022921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022925 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3022925 : Nat := 118140960795 + 3022925 * 2 ^ 59
def prefixEnd_3022925 : Nat := 4983230072969 + 3 ^ 40 * 3022925 * 2
def baseEnd_3022925 : Nat := 1552213507492690525735327

theorem tailTrace_3022925 : CollatzResearch.WordTrace tailWord_3022925 prefixEnd_3022925 1552213507492690525735327 := by
  unfold tailWord_3022925
  simp only [CollatzResearch.WordTrace]
  refine ⟨110255132573466474332398229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73503421715644316221598819 110255132573466474332398229)
  ·
    refine ⟨5168209339381240984331167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110255132573466474332398229 5168209339381240984331167)
    ·
      refine ⟨7752314009071861476496751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5168209339381240984331167 7752314009071861476496751)
      ·
        refine ⟨11628471013607792214745127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7752314009071861476496751 11628471013607792214745127)
        ·
          refine ⟨17442706520411688322117691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11628471013607792214745127 17442706520411688322117691)
          ·
            refine ⟨26164059780617532483176537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17442706520411688322117691 26164059780617532483176537)
            ·
              refine ⟨19623044835463149362382403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26164059780617532483176537 19623044835463149362382403)
              ·
                refine ⟨29434567253194724043573605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19623044835463149362382403 29434567253194724043573605)
                ·
                  refine ⟨5518981359974010758170051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29434567253194724043573605 5518981359974010758170051)
                  ·
                    refine ⟨8278472039961016137255077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5518981359974010758170051 8278472039961016137255077)
                    ·
                      refine ⟨1552213507492690525735327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8278472039961016137255077 1552213507492690525735327)
                      ·
                        rfl

theorem cell23_3022925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3022925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022925 prefixEnd_3022925 := by exact prefixLift 3022925
  have htrace : WordTrace (prefixWord ++ tailWord_3022925) baseStart_3022925 baseEnd_3022925 := by
    simpa [prefixWord, tailWord_3022925, baseEnd_3022925] using wordTrace_append hprefix tailTrace_3022925
  have hstable : (prefixWord ++ tailWord_3022925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022925).length < 2 ^ (prefixWord ++ tailWord_3022925).sum := by decide
  have hdescent : baseEnd_3022925 < baseStart_3022925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022948 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 6]
def baseStart_3022948 : Nat := 118140960795 + 3022948 * 2 ^ 59
def prefixEnd_3022948 : Nat := 4983230072969 + 3 ^ 40 * 3022948 * 2
def baseEnd_3022948 : Nat := 172469479727527103971969

theorem tailTrace_3022948 : CollatzResearch.WordTrace tailWord_3022948 prefixEnd_3022948 172469479727527103971969 := by
  unfold tailWord_3022948
  simp only [CollatzResearch.WordTrace]
  refine ⟨55127985726191574630242749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73503980968255432840323665 55127985726191574630242749)
  ·
    refine ⟨20672994647321840486341031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55127985726191574630242749 20672994647321840486341031)
    ·
      refine ⟨31009491970982760729511547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20672994647321840486341031 31009491970982760729511547)
      ·
        refine ⟨46514237956474141094267321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31009491970982760729511547 46514237956474141094267321)
        ·
          refine ⟨34885678467355605820700491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46514237956474141094267321 34885678467355605820700491)
          ·
            refine ⟨52328517701033408731050737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34885678467355605820700491 52328517701033408731050737)
            ·
              refine ⟨39246388275775056548288053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52328517701033408731050737 39246388275775056548288053)
              ·
                refine ⟨3679348900853911551402005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39246388275775056548288053 3679348900853911551402005)
                ·
                  refine ⟨172469479727527103971969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3679348900853911551402005 172469479727527103971969)
                  ·
                    rfl

theorem cell23_3022948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_3022948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022948 prefixEnd_3022948 := by exact prefixLift 3022948
  have htrace : WordTrace (prefixWord ++ tailWord_3022948) baseStart_3022948 baseEnd_3022948 := by
    simpa [prefixWord, tailWord_3022948, baseEnd_3022948] using wordTrace_append hprefix tailTrace_3022948
  have hstable : (prefixWord ++ tailWord_3022948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022948).length < 2 ^ (prefixWord ++ tailWord_3022948).sum := by decide
  have hdescent : baseEnd_3022948 < baseStart_3022948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022969 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 1, 4]
def baseStart_3022969 : Nat := 118140960795 + 3022969 * 2 ^ 59
def prefixEnd_3022969 : Nat := 4983230072969 + 3 ^ 40 * 3022969 * 2
def baseEnd_3022969 : Nat := 517412033547162784528375

theorem tailTrace_3022969 : CollatzResearch.WordTrace tailWord_3022969 prefixEnd_3022969 517412033547162784528375 := by
  unfold tailWord_3022969
  simp only [CollatzResearch.WordTrace]
  refine ⟨110256737385307069846999961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73504491590204713231333307 110256737385307069846999961)
  ·
    refine ⟨82692553038980302385249971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110256737385307069846999961 82692553038980302385249971)
    ·
      refine ⟨124038829558470453577874957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82692553038980302385249971 124038829558470453577874957)
      ·
        refine ⟨46514561084426420091703109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124038829558470453577874957 46514561084426420091703109)
        ·
          refine ⟨8721480203329953767194333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46514561084426420091703109 8721480203329953767194333)
          ·
            refine ⟨3270555076248732662697875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8721480203329953767194333 3270555076248732662697875)
            ·
              refine ⟨4905832614373098994046813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270555076248732662697875 4905832614373098994046813)
              ·
                refine ⟨1839687230389912122767555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4905832614373098994046813 1839687230389912122767555)
                ·
                  refine ⟨2759530845584868184151333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839687230389912122767555 2759530845584868184151333)
                  ·
                    refine ⟨517412033547162784528375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2759530845584868184151333 517412033547162784528375)
                    ·
                      rfl

theorem cell23_3022969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 4].length) (baseStart_3022969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022969 prefixEnd_3022969 := by exact prefixLift 3022969
  have htrace : WordTrace (prefixWord ++ tailWord_3022969) baseStart_3022969 baseEnd_3022969 := by
    simpa [prefixWord, tailWord_3022969, baseEnd_3022969] using wordTrace_append hprefix tailTrace_3022969
  have hstable : (prefixWord ++ tailWord_3022969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022969).length < 2 ^ (prefixWord ++ tailWord_3022969).sum := by decide
  have hdescent : baseEnd_3022969 < baseStart_3022969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022999 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 6]
def baseStart_3022999 : Nat := 118140960795 + 3022999 * 2 ^ 59
def prefixEnd_3022999 : Nat := 4983230072969 + 3 ^ 40 * 3022999 * 2
def baseEnd_3022999 : Nat := 172472389451235915134443

theorem tailTrace_3022999 : CollatzResearch.WordTrace tailWord_3022999 prefixEnd_3022999 172472389451235915134443 := by
  unfold tailWord_3022999
  simp only [CollatzResearch.WordTrace]
  refine ⟨110257831575198384970592051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73505221050132256647061367 110257831575198384970592051)
  ·
    refine ⟨165386747362797577455888077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110257831575198384970592051 165386747362797577455888077)
    ·
      refine ⟨62020030261049091545958029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165386747362797577455888077 62020030261049091545958029)
      ·
        refine ⟨23257511347893409329734261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62020030261049091545958029 23257511347893409329734261)
        ·
          refine ⟨2180391688865007124662587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23257511347893409329734261 2180391688865007124662587)
          ·
            refine ⟨3270587533297510686993881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180391688865007124662587 3270587533297510686993881)
            ·
              refine ⟨2452940649973133015245411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270587533297510686993881 2452940649973133015245411)
              ·
                refine ⟨3679410974959699522868117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452940649973133015245411 3679410974959699522868117)
                ·
                  refine ⟨172472389451235915134443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3679410974959699522868117 172472389451235915134443)
                  ·
                    rfl

theorem cell23_3022999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 6].length) (baseStart_3022999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022999 prefixEnd_3022999 := by exact prefixLift 3022999
  have htrace : WordTrace (prefixWord ++ tailWord_3022999) baseStart_3022999 baseEnd_3022999 := by
    simpa [prefixWord, tailWord_3022999, baseEnd_3022999] using wordTrace_append hprefix tailTrace_3022999
  have hstable : (prefixWord ++ tailWord_3022999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022999).length < 2 ^ (prefixWord ++ tailWord_3022999).sum := by decide
  have hdescent : baseEnd_3022999 < baseStart_3022999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023032 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 1, 1, 4]
def baseStart_3023032 : Nat := 118140960795 + 3023032 * 2 ^ 59
def prefixEnd_3023032 : Nat := 4983230072969 + 3 ^ 40 * 3023032 * 2
def baseEnd_3023032 : Nat := 1552268449922721607097335

theorem tailTrace_3023032 : CollatzResearch.WordTrace tailWord_3023032 prefixEnd_3023032 1552268449922721607097335 := by
  unfold tailWord_3023032
  simp only [CollatzResearch.WordTrace]
  refine ⟨55129517592039415803271675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73506023456052554404362233 55129517592039415803271675)
  ·
    refine ⟨82694276388059123704907513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55129517592039415803271675 82694276388059123704907513)
    ·
      refine ⟨62020707291044342778680635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82694276388059123704907513 62020707291044342778680635)
      ·
        refine ⟨93031060936566514168020953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62020707291044342778680635 93031060936566514168020953)
        ·
          refine ⟨69773295702424885626015715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93031060936566514168020953 69773295702424885626015715)
          ·
            refine ⟨104659943553637328439023573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69773295702424885626015715 104659943553637328439023573)
            ·
              refine ⟨2452967427038374885289615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 104659943553637328439023573 2452967427038374885289615)
              ·
                refine ⟨3679451140557562327934423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452967427038374885289615 3679451140557562327934423)
                ·
                  refine ⟨5519176710836343491901635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679451140557562327934423 5519176710836343491901635)
                  ·
                    refine ⟨8278765066254515237852453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5519176710836343491901635 8278765066254515237852453)
                    ·
                      refine ⟨1552268449922721607097335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8278765066254515237852453 1552268449922721607097335)
                      ·
                        rfl

theorem cell23_3023032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_3023032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023032 prefixEnd_3023032 := by exact prefixLift 3023032
  have htrace : WordTrace (prefixWord ++ tailWord_3023032) baseStart_3023032 baseEnd_3023032 := by
    simpa [prefixWord, tailWord_3023032, baseEnd_3023032] using wordTrace_append hprefix tailTrace_3023032
  have hstable : (prefixWord ++ tailWord_3023032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023032).length < 2 ^ (prefixWord ++ tailWord_3023032).sum := by decide
  have hdescent : baseEnd_3023032 < baseStart_3023032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023038 : List Nat := [4, 2, 1, 1, 15]
def baseStart_3023038 : Nat := 118140960795 + 3023038 * 2 ^ 59
def prefixEnd_3023038 : Nat := 4983230072969 + 3 ^ 40 * 3023038 * 2
def baseEnd_3023038 : Nat := 2129316228815704504283

theorem tailTrace_3023038 : CollatzResearch.WordTrace tailWord_3023038 prefixEnd_3023038 2129316228815704504283 := by
  unfold tailWord_3023038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13782406752757136828907721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73506169348038063087507845 13782406752757136828907721)
  ·
    refine ⟨10336805064567852621680791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13782406752757136828907721 10336805064567852621680791)
    ·
      refine ⟨15505207596851778932521187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336805064567852621680791 15505207596851778932521187)
      ·
        refine ⟨23257811395277668398781781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15505207596851778932521187 23257811395277668398781781)
        ·
          refine ⟨2129316228815704504283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 23257811395277668398781781 2129316228815704504283)
          ·
            rfl

theorem cell23_3023038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 15].length) (baseStart_3023038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023038 prefixEnd_3023038 := by exact prefixLift 3023038
  have htrace : WordTrace (prefixWord ++ tailWord_3023038) baseStart_3023038 baseEnd_3023038 := by
    simpa [prefixWord, tailWord_3023038, baseEnd_3023038] using wordTrace_append hprefix tailTrace_3023038
  have hstable : (prefixWord ++ tailWord_3023038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023038).length < 2 ^ (prefixWord ++ tailWord_3023038).sum := by decide
  have hdescent : baseEnd_3023038 < baseStart_3023038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023065 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_3023065 : Nat := 118140960795 + 3023065 * 2 ^ 59
def prefixEnd_3023065 : Nat := 4983230072969 + 3 ^ 40 * 3023065 * 2
def baseEnd_3023065 : Nat := 1552285394784319977984683

theorem tailTrace_3023065 : CollatzResearch.WordTrace tailWord_3023065 prefixEnd_3023065 1552285394784319977984683 := by
  unfold tailWord_3023065
  simp only [CollatzResearch.WordTrace]
  refine ⟨110260238792959278242494649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73506825861972852161663099 110260238792959278242494649)
  ·
    refine ⟨82695179094719458681870987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110260238792959278242494649 82695179094719458681870987)
    ·
      refine ⟨124042768642079188022806481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82695179094719458681870987 124042768642079188022806481)
      ·
        refine ⟨93032076481559391017104861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124042768642079188022806481 93032076481559391017104861)
        ·
          refine ⟨34887028680584771631414323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93032076481559391017104861 34887028680584771631414323)
          ·
            refine ⟨52330543020877157447121485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34887028680584771631414323 52330543020877157447121485)
            ·
              refine ⟨19623953632828934042670557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52330543020877157447121485 19623953632828934042670557)
              ·
                refine ⟨7358982612310850266001459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19623953632828934042670557 7358982612310850266001459)
                ·
                  refine ⟨11038473918466275399002189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7358982612310850266001459 11038473918466275399002189)
                  ·
                    refine ⟨4139427719424853274625821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11038473918466275399002189 4139427719424853274625821)
                    ·
                      refine ⟨1552285394784319977984683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139427719424853274625821 1552285394784319977984683)
                      ·
                        rfl

theorem cell23_3023065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_3023065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023065 prefixEnd_3023065 := by exact prefixLift 3023065
  have htrace : WordTrace (prefixWord ++ tailWord_3023065) baseStart_3023065 baseEnd_3023065 := by
    simpa [prefixWord, tailWord_3023065, baseEnd_3023065] using wordTrace_append hprefix tailTrace_3023065
  have hstable : (prefixWord ++ tailWord_3023065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023065).length < 2 ^ (prefixWord ++ tailWord_3023065).sum := by decide
  have hdescent : baseEnd_3023065 < baseStart_3023065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023082 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3023082 : Nat := 118140960795 + 3023082 * 2 ^ 59
def prefixEnd_3023082 : Nat := 4983230072969 + 3 ^ 40 * 3023082 * 2
def baseEnd_3023082 : Nat := 1552294123955446411472105

theorem tailTrace_3023082 : CollatzResearch.WordTrace tailWord_3023082 prefixEnd_3023082 1552294123955446411472105 := by
  unfold tailWord_3023082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27565214708474422536465875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73507239222598460097242333 27565214708474422536465875)
  ·
    refine ⟨41347822062711633804698813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27565214708474422536465875 41347822062711633804698813)
    ·
      refine ⟨15505433273516862676762055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41347822062711633804698813 15505433273516862676762055)
      ·
        refine ⟨23258149910275294015143083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15505433273516862676762055 23258149910275294015143083)
        ·
          refine ⟨34887224865412941022714625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23258149910275294015143083 34887224865412941022714625)
          ·
            refine ⟨26165418649059705767035969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34887224865412941022714625 26165418649059705767035969)
            ·
              refine ⟨19624063986794779325276977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26165418649059705767035969 19624063986794779325276977)
              ·
                refine ⟨14718047990096084493957733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19624063986794779325276977 14718047990096084493957733)
                ·
                  refine ⟨2759633998143015842617075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14718047990096084493957733 2759633998143015842617075)
                  ·
                    refine ⟨4139450997214523763925613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759633998143015842617075 4139450997214523763925613)
                    ·
                      refine ⟨1552294123955446411472105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139450997214523763925613 1552294123955446411472105)
                      ·
                        rfl

theorem cell23_3023082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3023082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023082 prefixEnd_3023082 := by exact prefixLift 3023082
  have htrace : WordTrace (prefixWord ++ tailWord_3023082) baseStart_3023082 baseEnd_3023082 := by
    simpa [prefixWord, tailWord_3023082, baseEnd_3023082] using wordTrace_append hprefix tailTrace_3023082
  have hstable : (prefixWord ++ tailWord_3023082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023082).length < 2 ^ (prefixWord ++ tailWord_3023082).sum := by decide
  have hdescent : baseEnd_3023082 < baseStart_3023082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023125 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_3023125 : Nat := 118140960795 + 3023125 * 2 ^ 59
def prefixEnd_3023125 : Nat := 4983230072969 + 3 ^ 40 * 3023125 * 2
def baseEnd_3023125 : Nat := 1552316203623589743234407

theorem tailTrace_3023125 : CollatzResearch.WordTrace tailWord_3023125 prefixEnd_3023125 1552316203623589743234407 := by
  unfold tailWord_3023125
  simp only [CollatzResearch.WordTrace]
  refine ⟨110262427172741908489678829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73508284781827938993119219 110262427172741908489678829)
  ·
    refine ⟨41348410189778215683629561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110262427172741908489678829 41348410189778215683629561)
    ·
      refine ⟨31011307642333661762722171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41348410189778215683629561 31011307642333661762722171)
      ·
        refine ⟨46516961463500492644083257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31011307642333661762722171 46516961463500492644083257)
        ·
          refine ⟨34887721097625369483062443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46516961463500492644083257 34887721097625369483062443)
          ·
            refine ⟨52331581646438054224593665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34887721097625369483062443 52331581646438054224593665)
            ·
              refine ⟨39248686234828540668445249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52331581646438054224593665 39248686234828540668445249)
              ·
                refine ⟨29436514676121405501333937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39248686234828540668445249 29436514676121405501333937)
                ·
                  refine ⟨22077386007091054126000453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29436514676121405501333937 22077386007091054126000453)
                  ·
                    refine ⟨4139509876329572648625085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22077386007091054126000453 4139509876329572648625085)
                    ·
                      refine ⟨1552316203623589743234407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139509876329572648625085 1552316203623589743234407)
                      ·
                        rfl

theorem cell23_3023125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_3023125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023125 prefixEnd_3023125 := by exact prefixLift 3023125
  have htrace : WordTrace (prefixWord ++ tailWord_3023125) baseStart_3023125 baseEnd_3023125 := by
    simpa [prefixWord, tailWord_3023125, baseEnd_3023125] using wordTrace_append hprefix tailTrace_3023125
  have hstable : (prefixWord ++ tailWord_3023125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023125).length < 2 ^ (prefixWord ++ tailWord_3023125).sum := by decide
  have hdescent : baseEnd_3023125 < baseStart_3023125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023156 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3023156 : Nat := 118140960795 + 3023156 * 2 ^ 59
def prefixEnd_3023156 : Nat := 4983230072969 + 3 ^ 40 * 3023156 * 2
def baseEnd_3023156 : Nat := 1552332121523879121946765

theorem tailTrace_3023156 : CollatzResearch.WordTrace tailWord_3023156 prefixEnd_3023156 1552332121523879121946765 := by
  unfold tailWord_3023156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55131778917814800392028661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73509038557086400522704881 55131778917814800392028661)
  ·
    refine ⟨5168604273545137536752687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55131778917814800392028661 5168604273545137536752687)
    ·
      refine ⟨7752906410317706305129031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5168604273545137536752687 7752906410317706305129031)
      ·
        refine ⟨11629359615476559457693547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7752906410317706305129031 11629359615476559457693547)
        ·
          refine ⟨17444039423214839186540321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11629359615476559457693547 17444039423214839186540321)
          ·
            refine ⟨13083029567411129389905241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17444039423214839186540321 13083029567411129389905241)
            ·
              refine ⟨9812272175558347042428931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13083029567411129389905241 9812272175558347042428931)
              ·
                refine ⟨14718408263337520563643397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9812272175558347042428931 14718408263337520563643397)
                ·
                  refine ⟨2759701549375785105683137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14718408263337520563643397 2759701549375785105683137)
                  ·
                    refine ⟨2069776162031838829262353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759701549375785105683137 2069776162031838829262353)
                    ·
                      refine ⟨1552332121523879121946765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069776162031838829262353 1552332121523879121946765)
                      ·
                        rfl

theorem cell23_3023156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3023156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023156 prefixEnd_3023156 := by exact prefixLift 3023156
  have htrace : WordTrace (prefixWord ++ tailWord_3023156) baseStart_3023156 baseEnd_3023156 := by
    simpa [prefixWord, tailWord_3023156, baseEnd_3023156] using wordTrace_append hprefix tailTrace_3023156
  have hstable : (prefixWord ++ tailWord_3023156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023156).length < 2 ^ (prefixWord ++ tailWord_3023156).sum := by decide
  have hdescent : baseEnd_3023156 < baseStart_3023156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023162 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_3023162 : Nat := 118140960795 + 3023162 * 2 ^ 59
def prefixEnd_3023162 : Nat := 4983230072969 + 3 ^ 40 * 3023162 * 2
def baseEnd_3023162 : Nat := 172481689156422899830193

theorem tailTrace_3023162 : CollatzResearch.WordTrace tailWord_3023162 prefixEnd_3023162 172481689156422899830193 := by
  unfold tailWord_3023162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27565944168401965952193935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73509184449071909205850493 27565944168401965952193935)
  ·
    refine ⟨41348916252602948928290903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27565944168401965952193935 41348916252602948928290903)
    ·
      refine ⟨62023374378904423392436355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41348916252602948928290903 62023374378904423392436355)
      ·
        refine ⟨93035061568356635088654533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62023374378904423392436355 93035061568356635088654533)
        ·
          refine ⟨17444074044066869079122725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93035061568356635088654533 17444074044066869079122725)
          ·
            refine ⟨3270763883262537952335511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17444074044066869079122725 3270763883262537952335511)
            ·
              refine ⟨4906145824893806928503267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270763883262537952335511 4906145824893806928503267)
              ·
                refine ⟨7359218737340710392754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906145824893806928503267 7359218737340710392754901)
                ·
                  refine ⟨172481689156422899830193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7359218737340710392754901 172481689156422899830193)
                  ·
                    rfl

theorem cell23_3023162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_3023162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023162 prefixEnd_3023162 := by exact prefixLift 3023162
  have htrace : WordTrace (prefixWord ++ tailWord_3023162) baseStart_3023162 baseEnd_3023162 := by
    simpa [prefixWord, tailWord_3023162, baseEnd_3023162] using wordTrace_append hprefix tailTrace_3023162
  have hstable : (prefixWord ++ tailWord_3023162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023162).length < 2 ^ (prefixWord ++ tailWord_3023162).sum := by decide
  have hdescent : baseEnd_3023162 < baseStart_3023162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023175 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 4, 5]
def baseStart_3023175 : Nat := 118140960795 + 3023175 * 2 ^ 59
def prefixEnd_3023175 : Nat := 4983230072969 + 3 ^ 40 * 3023175 * 2
def baseEnd_3023175 : Nat := 517447292552104849203059

theorem tailTrace_3023175 : CollatzResearch.WordTrace tailWord_3023175 prefixEnd_3023175 517447292552104849203059 := by
  unfold tailWord_3023175
  simp only [CollatzResearch.WordTrace]
  refine ⟨110264250822560767028998979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73509500548373844685999319 110264250822560767028998979)
  ·
    refine ⟨165396376233841150543498469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110264250822560767028998979 165396376233841150543498469)
    ·
      refine ⟨31011820543845215726905963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165396376233841150543498469 31011820543845215726905963)
      ·
        refine ⟨46517730815767823590358945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31011820543845215726905963 46517730815767823590358945)
        ·
          refine ⟨34888298111825867692769209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46517730815767823590358945 34888298111825867692769209)
          ·
            refine ⟨26166223583869400769576907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34888298111825867692769209 26166223583869400769576907)
            ·
              refine ⟨39249335375804101154365361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26166223583869400769576907 39249335375804101154365361)
              ·
                refine ⟨29437001531853075865774021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39249335375804101154365361 29437001531853075865774021)
                ·
                  refine ⟨5519437787222451724832629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29437001531853075865774021 5519437787222451724832629)
                  ·
                    refine ⟨517447292552104849203059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5519437787222451724832629 517447292552104849203059)
                    ·
                      rfl

theorem cell23_3023175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_3023175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023175 prefixEnd_3023175 := by exact prefixLift 3023175
  have htrace : WordTrace (prefixWord ++ tailWord_3023175) baseStart_3023175 baseEnd_3023175 := by
    simpa [prefixWord, tailWord_3023175, baseEnd_3023175] using wordTrace_append hprefix tailTrace_3023175
  have hstable : (prefixWord ++ tailWord_3023175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023175).length < 2 ^ (prefixWord ++ tailWord_3023175).sum := by decide
  have hdescent : baseEnd_3023175 < baseStart_3023175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023182 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_3023182 : Nat := 118140960795 + 3023182 * 2 ^ 59
def prefixEnd_3023182 : Nat := 4983230072969 + 3 ^ 40 * 3023182 * 2
def baseEnd_3023182 : Nat := 1552345472020896020221645

theorem tailTrace_3023182 : CollatzResearch.WordTrace tailWord_3023182 prefixEnd_3023182 1552345472020896020221645 := by
  unfold tailWord_3023182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13783063266691925903062975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73509670755690271483002533 13783063266691925903062975)
  ·
    refine ⟨20674594900037888854594463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13783063266691925903062975 20674594900037888854594463)
    ·
      refine ⟨31011892350056833281891695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20674594900037888854594463 31011892350056833281891695)
      ·
        refine ⟨46517838525085249922837543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31011892350056833281891695 46517838525085249922837543)
        ·
          refine ⟨69776757787627874884256315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46517838525085249922837543 69776757787627874884256315)
          ·
            refine ⟨104665136681441812326384473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69776757787627874884256315 104665136681441812326384473)
            ·
              refine ⟨78498852511081359244788355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104665136681441812326384473 78498852511081359244788355)
              ·
                refine ⟨117748278766622038867182533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78498852511081359244788355 117748278766622038867182533)
                ·
                  refine ⟨22077802268741632287596725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117748278766622038867182533 22077802268741632287596725)
                  ·
                    refine ⟨2069793962694528026962193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22077802268741632287596725 2069793962694528026962193)
                    ·
                      refine ⟨1552345472020896020221645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069793962694528026962193 1552345472020896020221645)
                      ·
                        rfl

theorem cell23_3023182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_3023182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023182 prefixEnd_3023182 := by exact prefixLift 3023182
  have htrace : WordTrace (prefixWord ++ tailWord_3023182) baseStart_3023182 baseEnd_3023182 := by
    simpa [prefixWord, tailWord_3023182, baseEnd_3023182] using wordTrace_append hprefix tailTrace_3023182
  have hstable : (prefixWord ++ tailWord_3023182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023182).length < 2 ^ (prefixWord ++ tailWord_3023182).sum := by decide
  have hdescent : baseEnd_3023182 < baseStart_3023182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023202 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3023202 : Nat := 118140960795 + 3023202 * 2 ^ 59
def prefixEnd_3023202 : Nat := 4983230072969 + 3 ^ 40 * 3023202 * 2
def baseEnd_3023202 : Nat := 1552355741633985941971553

theorem tailTrace_3023202 : CollatzResearch.WordTrace tailWord_3023202 prefixEnd_3023202 1552355741633985941971553 := by
  unfold tailWord_3023202
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566308898365737660057965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73510157062308633760154573 27566308898365737660057965)
  ·
    refine ⟨10337365836887151622521737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27566308898365737660057965 10337365836887151622521737)
    ·
      refine ⟨7753024377665363716891303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10337365836887151622521737 7753024377665363716891303)
      ·
        refine ⟨11629536566498045575336955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753024377665363716891303 11629536566498045575336955)
        ·
          refine ⟨17444304849747068363005433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11629536566498045575336955 17444304849747068363005433)
          ·
            refine ⟨13083228637310301272254075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17444304849747068363005433 13083228637310301272254075)
            ·
              refine ⟨19624842955965451908381113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083228637310301272254075 19624842955965451908381113)
              ·
                refine ⟨14718632216974088931285835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19624842955965451908381113 14718632216974088931285835)
                ·
                  refine ⟨22077948325461133396928753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14718632216974088931285835 22077948325461133396928753)
                  ·
                    refine ⟨16558461244095850047696565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22077948325461133396928753 16558461244095850047696565)
                    ·
                      refine ⟨1552355741633985941971553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16558461244095850047696565 1552355741633985941971553)
                      ·
                        rfl

theorem cell23_3023202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3023202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023202 prefixEnd_3023202 := by exact prefixLift 3023202
  have htrace : WordTrace (prefixWord ++ tailWord_3023202) baseStart_3023202 baseEnd_3023202 := by
    simpa [prefixWord, tailWord_3023202, baseEnd_3023202] using wordTrace_append hprefix tailTrace_3023202
  have hstable : (prefixWord ++ tailWord_3023202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023202).length < 2 ^ (prefixWord ++ tailWord_3023202).sum := by decide
  have hdescent : baseEnd_3023202 < baseStart_3023202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023225 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3023225 : Nat := 118140960795 + 3023225 * 2 ^ 59
def prefixEnd_3023225 : Nat := 4983230072969 + 3 ^ 40 * 3023225 * 2
def baseEnd_3023225 : Nat := 1552367551689039351983947

theorem tailTrace_3023225 : CollatzResearch.WordTrace tailWord_3023225 prefixEnd_3023225 1552367551689039351983947 := by
  unfold tailWord_3023225
  simp only [CollatzResearch.WordTrace]
  refine ⟨110266074472379625568319129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73510716314919750378879419 110266074472379625568319129)
  ·
    refine ⟨82699555854284719176239347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110266074472379625568319129 82699555854284719176239347)
    ·
      refine ⟨124049333781427078764359021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82699555854284719176239347 124049333781427078764359021)
      ·
        refine ⟨46518500168035154536634633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124049333781427078764359021 46518500168035154536634633)
        ·
          refine ⟨34888875126026365902475975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46518500168035154536634633 34888875126026365902475975)
          ·
            refine ⟨52333312689039548853713963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34888875126026365902475975 52333312689039548853713963)
            ·
              refine ⟨78499969033559323280570945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52333312689039548853713963 78499969033559323280570945)
              ·
                refine ⟨58874976775169492460428209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78499969033559323280570945 58874976775169492460428209)
                ·
                  refine ⟨44156232581377119345321157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58874976775169492460428209 44156232581377119345321157)
                  ·
                    refine ⟨8279293609008209877247717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44156232581377119345321157 8279293609008209877247717)
                    ·
                      refine ⟨1552367551689039351983947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8279293609008209877247717 1552367551689039351983947)
                      ·
                        rfl

theorem cell23_3023225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3023225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023225 prefixEnd_3023225 := by exact prefixLift 3023225
  have htrace : WordTrace (prefixWord ++ tailWord_3023225) baseStart_3023225 baseEnd_3023225 := by
    simpa [prefixWord, tailWord_3023225, baseEnd_3023225] using wordTrace_append hprefix tailTrace_3023225
  have hstable : (prefixWord ++ tailWord_3023225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023225).length < 2 ^ (prefixWord ++ tailWord_3023225).sum := by decide
  have hdescent : baseEnd_3023225 < baseStart_3023225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023229 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_3023229 : Nat := 118140960795 + 3023229 * 2 ^ 59
def prefixEnd_3023229 : Nat := 4983230072969 + 3 ^ 40 * 3023229 * 2
def baseEnd_3023229 : Nat := 1552369605611657336333929

theorem tailTrace_3023229 : CollatzResearch.WordTrace tailWord_3023229 prefixEnd_3023229 1552369605611657336333929 := by
  unfold tailWord_3023229
  simp only [CollatzResearch.WordTrace]
  refine ⟨110266220364365134251464741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73510813576243422834309827 110266220364365134251464741)
  ·
    refine ⟨20674916318318462672149639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110266220364365134251464741 20674916318318462672149639)
    ·
      refine ⟨31012374477477694008224459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20674916318318462672149639 31012374477477694008224459)
      ·
        refine ⟨46518561716216541012336689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31012374477477694008224459 46518561716216541012336689)
        ·
          refine ⟨34888921287162405759252517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46518561716216541012336689 34888921287162405759252517)
          ·
            refine ⟨6541672741342951079859847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34888921287162405759252517 6541672741342951079859847)
            ·
              refine ⟨9812509112014426619789771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541672741342951079859847 9812509112014426619789771)
              ·
                refine ⟨14718763668021639929684657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9812509112014426619789771 14718763668021639929684657)
                ·
                  refine ⟨11039072751016229947263493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14718763668021639929684657 11039072751016229947263493)
                  ·
                    refine ⟨2069826140815543115111905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11039072751016229947263493 2069826140815543115111905)
                    ·
                      refine ⟨1552369605611657336333929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069826140815543115111905 1552369605611657336333929)
                      ·
                        rfl

theorem cell23_3023229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_3023229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023229 prefixEnd_3023229 := by exact prefixLift 3023229
  have htrace : WordTrace (prefixWord ++ tailWord_3023229) baseStart_3023229 baseEnd_3023229 := by
    simpa [prefixWord, tailWord_3023229, baseEnd_3023229] using wordTrace_append hprefix tailTrace_3023229
  have hstable : (prefixWord ++ tailWord_3023229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023229).length < 2 ^ (prefixWord ++ tailWord_3023229).sum := by decide
  have hdescent : baseEnd_3023229 < baseStart_3023229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023246 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3023246 : Nat := 118140960795 + 3023246 * 2 ^ 59
def prefixEnd_3023246 : Nat := 4983230072969 + 3 ^ 40 * 3023246 * 2
def baseEnd_3023246 : Nat := 1552378334782783769821351

theorem tailTrace_3023246 : CollatzResearch.WordTrace tailWord_3023246 prefixEnd_3023246 1552378334782783769821351 := by
  unfold tailWord_3023246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13783355050662943269354199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73511226936869030769889061 13783355050662943269354199)
  ·
    refine ⟨20675032575994414904031299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13783355050662943269354199 20675032575994414904031299)
    ·
      refine ⟨31012548863991622356046949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20675032575994414904031299 31012548863991622356046949)
      ·
        refine ⟨5814852911998429191758803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31012548863991622356046949 5814852911998429191758803)
        ·
          refine ⟨8722279367997643787638205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814852911998429191758803 8722279367997643787638205)
          ·
            refine ⟨3270854762999116420364327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8722279367997643787638205 3270854762999116420364327)
            ·
              refine ⟨4906282144498674630546491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270854762999116420364327 4906282144498674630546491)
              ·
                refine ⟨7359423216748011945819737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906282144498674630546491 7359423216748011945819737)
                ·
                  refine ⟨5519567412561008959364803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7359423216748011945819737 5519567412561008959364803)
                  ·
                    refine ⟨8279351118841513439047205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5519567412561008959364803 8279351118841513439047205)
                    ·
                      refine ⟨1552378334782783769821351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8279351118841513439047205 1552378334782783769821351)
                      ·
                        rfl

theorem cell23_3023246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3023246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023246 prefixEnd_3023246 := by exact prefixLift 3023246
  have htrace : WordTrace (prefixWord ++ tailWord_3023246) baseStart_3023246 baseEnd_3023246 := by
    simpa [prefixWord, tailWord_3023246, baseEnd_3023246] using wordTrace_append hprefix tailTrace_3023246
  have hstable : (prefixWord ++ tailWord_3023246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023246).length < 2 ^ (prefixWord ++ tailWord_3023246).sum := by decide
  have hdescent : baseEnd_3023246 < baseStart_3023246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023256 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 1, 4]
def baseStart_3023256 : Nat := 118140960795 + 3023256 * 2 ^ 59
def prefixEnd_3023256 : Nat := 4983230072969 + 3 ^ 40 * 3023256 * 2
def baseEnd_3023256 : Nat := 517461156529776243565435

theorem tailTrace_3023256 : CollatzResearch.WordTrace tailWord_3023256 prefixEnd_3023256 517461156529776243565435 := by
  unfold tailWord_3023256
  simp only [CollatzResearch.WordTrace]
  refine ⟨55133602567633658931348811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73511470090178211908465081 55133602567633658931348811)
  ·
    refine ⟨82700403851450488397023217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55133602567633658931348811 82700403851450488397023217)
    ·
      refine ⟨62025302888587866297767413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82700403851450488397023217 62025302888587866297767413)
      ·
        refine ⟨5814872145805112465415695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62025302888587866297767413 5814872145805112465415695)
        ·
          refine ⟨8722308218707668698123543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814872145805112465415695 8722308218707668698123543)
          ·
            refine ⟨13083462328061503047185315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722308218707668698123543 13083462328061503047185315)
            ·
              refine ⟨19625193492092254570777973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083462328061503047185315 19625193492092254570777973)
              ·
                refine ⟨1839861889883648866010435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19625193492092254570777973 1839861889883648866010435)
                ·
                  refine ⟨2759792834825473299015653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839861889883648866010435 2759792834825473299015653)
                  ·
                    refine ⟨517461156529776243565435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2759792834825473299015653 517461156529776243565435)
                    ·
                      rfl

theorem cell23_3023256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_3023256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023256 prefixEnd_3023256 := by exact prefixLift 3023256
  have htrace : WordTrace (prefixWord ++ tailWord_3023256) baseStart_3023256 baseEnd_3023256 := by
    simpa [prefixWord, tailWord_3023256, baseEnd_3023256] using wordTrace_append hprefix tailTrace_3023256
  have hstable : (prefixWord ++ tailWord_3023256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023256).length < 2 ^ (prefixWord ++ tailWord_3023256).sum := by decide
  have hdescent : baseEnd_3023256 < baseStart_3023256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023289 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 1, 5, 2]
def baseStart_3023289 : Nat := 118140960795 + 3023289 * 2 ^ 59
def prefixEnd_3023289 : Nat := 4983230072969 + 3 ^ 40 * 3023289 * 2
def baseEnd_3023289 : Nat := 1552400414450927101583653

theorem tailTrace_3023289 : CollatzResearch.WordTrace tailWord_3023289 prefixEnd_3023289 1552400414450927101583653 := by
  unfold tailWord_3023289
  simp only [CollatzResearch.WordTrace]
  refine ⟨110268408744147764498648921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73512272496098509665765947 110268408744147764498648921)
  ·
    refine ⟨82701306558110823373986691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110268408744147764498648921 82701306558110823373986691)
    ·
      refine ⟨124051959837166235060980037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82701306558110823373986691 124051959837166235060980037)
      ·
        refine ⟨23259742469468669073933757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124051959837166235060980037 23259742469468669073933757)
        ·
          refine ⟨8722403426050750902725159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23259742469468669073933757 8722403426050750902725159)
          ·
            refine ⟨13083605139076126354087739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722403426050750902725159 13083605139076126354087739)
            ·
              refine ⟨19625407708614189531131609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083605139076126354087739 19625407708614189531131609)
              ·
                refine ⟨14719055781460642148348707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19625407708614189531131609 14719055781460642148348707)
                ·
                  refine ⟨22078583672190963222523061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14719055781460642148348707 22078583672190963222523061)
                  ·
                    refine ⟨2069867219267902802111537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22078583672190963222523061 2069867219267902802111537)
                    ·
                      refine ⟨1552400414450927101583653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069867219267902802111537 1552400414450927101583653)
                      ·
                        rfl

theorem cell23_3023289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_3023289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023289 prefixEnd_3023289 := by exact prefixLift 3023289
  have htrace : WordTrace (prefixWord ++ tailWord_3023289) baseStart_3023289 baseEnd_3023289 := by
    simpa [prefixWord, tailWord_3023289, baseEnd_3023289] using wordTrace_append hprefix tailTrace_3023289
  have hstable : (prefixWord ++ tailWord_3023289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023289).length < 2 ^ (prefixWord ++ tailWord_3023289).sum := by decide
  have hdescent : baseEnd_3023289 < baseStart_3023289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023329 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 2, 4]
def baseStart_3023329 : Nat := 118140960795 + 3023329 * 2 ^ 59
def prefixEnd_3023329 : Nat := 4983230072969 + 3 ^ 40 * 3023329 * 2
def baseEnd_3023329 : Nat := 517473651225702315027823

theorem tailTrace_3023329 : CollatzResearch.WordTrace tailWord_3023329 prefixEnd_3023329 517473651225702315027823 := by
  unfold tailWord_3023329
  simp only [CollatzResearch.WordTrace]
  refine ⟨110269867664002851330105041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73513245109335234220070027 110269867664002851330105041)
  ·
    refine ⟨82702400748002138497578781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110269867664002851330105041 82702400748002138497578781)
    ·
      refine ⟨31013400280500801936592043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82702400748002138497578781 31013400280500801936592043)
      ·
        refine ⟨46520100420751202904888065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31013400280500801936592043 46520100420751202904888065)
        ·
          refine ⟨34890075315563402178666049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46520100420751202904888065 34890075315563402178666049)
          ·
            refine ⟨26167556486672551633999537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34890075315563402178666049 26167556486672551633999537)
            ·
              refine ⟨19625667365004413725499653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26167556486672551633999537 19625667365004413725499653)
              ·
                refine ⟨3679812630938327573531185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19625667365004413725499653 3679812630938327573531185)
                ·
                  refine ⟨2759859473203745680148389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679812630938327573531185 2759859473203745680148389)
                  ·
                    refine ⟨517473651225702315027823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2759859473203745680148389 517473651225702315027823)
                    ·
                      rfl

theorem cell23_3023329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_3023329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023329 prefixEnd_3023329 := by exact prefixLift 3023329
  have htrace : WordTrace (prefixWord ++ tailWord_3023329) baseStart_3023329 baseEnd_3023329 := by
    simpa [prefixWord, tailWord_3023329, baseEnd_3023329] using wordTrace_append hprefix tailTrace_3023329
  have hstable : (prefixWord ++ tailWord_3023329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023329).length < 2 ^ (prefixWord ++ tailWord_3023329).sum := by decide
  have hdescent : baseEnd_3023329 < baseStart_3023329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023342 : List Nat := [4, 1, 2, 1, 2, 2, 1, 10]
def baseStart_3023342 : Nat := 118140960795 + 3023342 * 2 ^ 59
def prefixEnd_3023342 : Nat := 4983230072969 + 3 ^ 40 * 3023342 * 2
def baseEnd_3023342 : Nat := 57497319589837607193367

theorem tailTrace_3023342 : CollatzResearch.WordTrace tailWord_3023342 prefixEnd_3023342 57497319589837607193367 := by
  unfold tailWord_3023342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13783792726619469318791035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73513561208637169700218853 13783792726619469318791035)
  ·
    refine ⟨20675689089929203978186553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13783792726619469318791035 20675689089929203978186553)
    ·
      refine ⟨15506766817446902983639915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20675689089929203978186553 15506766817446902983639915)
      ·
        refine ⟨23260150226170354475459873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15506766817446902983639915 23260150226170354475459873)
        ·
          refine ⟨17445112669627765856594905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23260150226170354475459873 17445112669627765856594905)
          ·
            refine ⟨13083834502220824392446179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17445112669627765856594905 13083834502220824392446179)
            ·
              refine ⟨19625751753331236588669269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083834502220824392446179 19625751753331236588669269)
              ·
                refine ⟨57497319589837607193367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19625751753331236588669269 57497319589837607193367)
                ·
                  rfl

theorem cell23_3023342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_3023342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023342 prefixEnd_3023342 := by exact prefixLift 3023342
  have htrace : WordTrace (prefixWord ++ tailWord_3023342) baseStart_3023342 baseEnd_3023342 := by
    simpa [prefixWord, tailWord_3023342, baseEnd_3023342] using wordTrace_append hprefix tailTrace_3023342
  have hstable : (prefixWord ++ tailWord_3023342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023342).length < 2 ^ (prefixWord ++ tailWord_3023342).sum := by decide
  have hdescent : baseEnd_3023342 < baseStart_3023342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023369 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 3]
def baseStart_3023369 : Nat := 118140960795 + 3023369 * 2 ^ 59
def prefixEnd_3023369 : Nat := 4983230072969 + 3 ^ 40 * 3023369 * 2
def baseEnd_3023369 : Nat := 1552441492903286788583285

theorem tailTrace_3023369 : CollatzResearch.WordTrace tailWord_3023369 prefixEnd_3023369 1552441492903286788583285 := by
  unfold tailWord_3023369
  simp only [CollatzResearch.WordTrace]
  refine ⟨110271326583857938161561161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73514217722571958774374107 110271326583857938161561161)
  ·
    refine ⟨82703494937893453621170871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110271326583857938161561161 82703494937893453621170871)
    ·
      refine ⟨124055242406840180431756307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82703494937893453621170871 124055242406840180431756307)
      ·
        refine ⟨186082863610260270647634461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124055242406840180431756307 186082863610260270647634461)
        ·
          refine ⟨69781073853847601492862923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186082863610260270647634461 69781073853847601492862923)
          ·
            refine ⟨104671610780771402239294385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69781073853847601492862923 104671610780771402239294385)
            ·
              refine ⟨78503708085578551679470789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104671610780771402239294385 78503708085578551679470789)
              ·
                refine ⟨14719445266045978439900773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78503708085578551679470789 14719445266045978439900773)
                ·
                  refine ⟨2759895987383620957481395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14719445266045978439900773 2759895987383620957481395)
                  ·
                    refine ⟨4139843981075431436222093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759895987383620957481395 4139843981075431436222093)
                    ·
                      refine ⟨1552441492903286788583285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139843981075431436222093 1552441492903286788583285)
                      ·
                        rfl

theorem cell23_3023369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_3023369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023369 prefixEnd_3023369 := by exact prefixLift 3023369
  have htrace : WordTrace (prefixWord ++ tailWord_3023369) baseStart_3023369 baseEnd_3023369 := by
    simpa [prefixWord, tailWord_3023369, baseEnd_3023369] using wordTrace_append hprefix tailTrace_3023369
  have hstable : (prefixWord ++ tailWord_3023369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023369).length < 2 ^ (prefixWord ++ tailWord_3023369).sum := by decide
  have hdescent : baseEnd_3023369 < baseStart_3023369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023373 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3023373 : Nat := 118140960795 + 3023373 * 2 ^ 59
def prefixEnd_3023373 : Nat := 4983230072969 + 3 ^ 40 * 3023373 * 2
def baseEnd_3023373 : Nat := 1552443546825904772933267

theorem tailTrace_3023373 : CollatzResearch.WordTrace tailWord_3023373 prefixEnd_3023373 1552443546825904772933267 := by
  unfold tailWord_3023373
  simp only [CollatzResearch.WordTrace]
  refine ⟨110271472475843446844706773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73514314983895631229804515 110271472475843446844706773)
  ·
    refine ⟨2584487636152580785422815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110271472475843446844706773 2584487636152580785422815)
    ·
      refine ⟨3876731454228871178134223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584487636152580785422815 3876731454228871178134223)
      ·
        refine ⟨5815097181343306767201335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876731454228871178134223 5815097181343306767201335)
        ·
          refine ⟨8722645772014960150802003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815097181343306767201335 8722645772014960150802003)
          ·
            refine ⟨13083968658022440226203005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722645772014960150802003 13083968658022440226203005)
            ·
              refine ⟨4906488246758415084826127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13083968658022440226203005 4906488246758415084826127)
              ·
                refine ⟨7359732370137622627239191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906488246758415084826127 7359732370137622627239191)
                ·
                  refine ⟨11039598555206433940858787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359732370137622627239191 11039598555206433940858787)
                  ·
                    refine ⟨16559397832809650911288181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11039598555206433940858787 16559397832809650911288181)
                    ·
                      refine ⟨1552443546825904772933267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16559397832809650911288181 1552443546825904772933267)
                      ·
                        rfl

theorem cell23_3023373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3023373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023373 prefixEnd_3023373 := by exact prefixLift 3023373
  have htrace : WordTrace (prefixWord ++ tailWord_3023373) baseStart_3023373 baseEnd_3023373 := by
    simpa [prefixWord, tailWord_3023373, baseEnd_3023373] using wordTrace_append hprefix tailTrace_3023373
  have hstable : (prefixWord ++ tailWord_3023373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023373).length < 2 ^ (prefixWord ++ tailWord_3023373).sum := by decide
  have hdescent : baseEnd_3023373 < baseStart_3023373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023386 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_3023386 : Nat := 118140960795 + 3023386 * 2 ^ 59
def prefixEnd_3023386 : Nat := 4983230072969 + 3 ^ 40 * 3023386 * 2
def baseEnd_3023386 : Nat := 1552450222074413222070707

theorem tailTrace_3023386 : CollatzResearch.WordTrace tailWord_3023386 prefixEnd_3023386 1552450222074413222070707 := by
  unfold tailWord_3023386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27567986656199087516232503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73514631083197566709953341 27567986656199087516232503)
  ·
    refine ⟨41351979984298631274348755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27567986656199087516232503 41351979984298631274348755)
    ·
      refine ⟨62027969976447946911523133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41351979984298631274348755 62027969976447946911523133)
      ·
        refine ⟨23260488741167980091821175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62027969976447946911523133 23260488741167980091821175)
        ·
          refine ⟨34890733111751970137731763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23260488741167980091821175 34890733111751970137731763)
          ·
            refine ⟨52336099667627955206597645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34890733111751970137731763 52336099667627955206597645)
            ·
              refine ⟨19626037375360483202474117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52336099667627955206597645 19626037375360483202474117)
              ·
                refine ⟨3679882007880090600463897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19626037375360483202474117 3679882007880090600463897)
                ·
                  refine ⟨2759911505910067950347923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679882007880090600463897 2759911505910067950347923)
                  ·
                    refine ⟨4139867258865101925521885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759911505910067950347923 4139867258865101925521885)
                    ·
                      refine ⟨1552450222074413222070707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139867258865101925521885 1552450222074413222070707)
                      ·
                        rfl

theorem cell23_3023386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_3023386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023386 prefixEnd_3023386 := by exact prefixLift 3023386
  have htrace : WordTrace (prefixWord ++ tailWord_3023386) baseStart_3023386 baseEnd_3023386 := by
    simpa [prefixWord, tailWord_3023386, baseEnd_3023386] using wordTrace_append hprefix tailTrace_3023386
  have hstable : (prefixWord ++ tailWord_3023386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023386).length < 2 ^ (prefixWord ++ tailWord_3023386).sum := by decide
  have hdescent : baseEnd_3023386 < baseStart_3023386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023454 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3023454 : Nat := 118140960795 + 3023454 * 2 ^ 59
def prefixEnd_3023454 : Nat := 4983230072969 + 3 ^ 40 * 3023454 * 2
def baseEnd_3023454 : Nat := 1552485138758918956020395

theorem tailTrace_3023454 : CollatzResearch.WordTrace tailWord_3023454 prefixEnd_3023454 1552485138758918956020395 := by
  unfold tailWord_3023454
  simp only [CollatzResearch.WordTrace]
  refine ⟨13784303348568749709800677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73516284525699998452270277 13784303348568749709800677)
  ·
    refine ⟨2584556877856640570587627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13784303348568749709800677 2584556877856640570587627)
    ·
      refine ⟨3876835316784960855881441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584556877856640570587627 3876835316784960855881441)
      ·
        refine ⟨2907626487588720641911081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3876835316784960855881441 2907626487588720641911081)
        ·
          refine ⟨2180719865691540481433311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907626487588720641911081 2180719865691540481433311)
          ·
            refine ⟨3271079798537310722149967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180719865691540481433311 3271079798537310722149967)
            ·
              refine ⟨4906619697805966083224951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271079798537310722149967 4906619697805966083224951)
              ·
                refine ⟨7359929546708949124837427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906619697805966083224951 7359929546708949124837427)
                ·
                  refine ⟨11039894320063423687256141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359929546708949124837427 11039894320063423687256141)
                  ·
                    refine ⟨4139960370023783882721053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11039894320063423687256141 4139960370023783882721053)
                    ·
                      refine ⟨1552485138758918956020395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139960370023783882721053 1552485138758918956020395)
                      ·
                        rfl

theorem cell23_3023454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3023454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023454 prefixEnd_3023454 := by exact prefixLift 3023454
  have htrace : WordTrace (prefixWord ++ tailWord_3023454) baseStart_3023454 baseEnd_3023454 := by
    simpa [prefixWord, tailWord_3023454, baseEnd_3023454] using wordTrace_append hprefix tailTrace_3023454
  have hstable : (prefixWord ++ tailWord_3023454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023454).length < 2 ^ (prefixWord ++ tailWord_3023454).sum := by decide
  have hdescent : baseEnd_3023454 < baseStart_3023454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023459 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 3]
def baseStart_3023459 : Nat := 118140960795 + 3023459 * 2 ^ 59
def prefixEnd_3023459 : Nat := 4983230072969 + 3 ^ 40 * 3023459 * 2
def baseEnd_3023459 : Nat := 1552487706162191436457871

theorem tailTrace_3023459 : CollatzResearch.WordTrace tailWord_3023459 prefixEnd_3023459 1552487706162191436457871 := by
  unfold tailWord_3023459
  simp only [CollatzResearch.WordTrace]
  refine ⟨110274609153531883532337431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73516406102354589021558287 110274609153531883532337431)
  ·
    refine ⟨165411913730297825298506147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110274609153531883532337431 165411913730297825298506147)
    ·
      refine ⟨248117870595446737947759221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165411913730297825298506147 248117870595446737947759221)
      ·
        refine ⟨23261050368323131682602427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248117870595446737947759221 23261050368323131682602427)
        ·
          refine ⟨34891575552484697523903641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23261050368323131682602427 34891575552484697523903641)
          ·
            refine ⟨26168681664363523142927731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34891575552484697523903641 26168681664363523142927731)
            ·
              refine ⟨39253022496545284714391597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26168681664363523142927731 39253022496545284714391597)
              ·
                refine ⟨14719883436204481767896849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39253022496545284714391597 14719883436204481767896849)
                ·
                  refine ⟨11039912577153361325922637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14719883436204481767896849 11039912577153361325922637)
                  ·
                    refine ⟨4139967216432510497220989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11039912577153361325922637 4139967216432510497220989)
                    ·
                      refine ⟨1552487706162191436457871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4139967216432510497220989 1552487706162191436457871)
                      ·
                        rfl

theorem cell23_3023459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_3023459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023459 prefixEnd_3023459 := by exact prefixLift 3023459
  have htrace : WordTrace (prefixWord ++ tailWord_3023459) baseStart_3023459 baseEnd_3023459 := by
    simpa [prefixWord, tailWord_3023459, baseEnd_3023459] using wordTrace_append hprefix tailTrace_3023459
  have hstable : (prefixWord ++ tailWord_3023459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023459).length < 2 ^ (prefixWord ++ tailWord_3023459).sum := by decide
  have hdescent : baseEnd_3023459 < baseStart_3023459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023460 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_3023460 : Nat := 118140960795 + 3023460 * 2 ^ 59
def prefixEnd_3023460 : Nat := 4983230072969 + 3 ^ 40 * 3023460 * 2
def baseEnd_3023460 : Nat := 1552488219642845932545367

theorem tailTrace_3023460 : CollatzResearch.WordTrace tailWord_3023460 prefixEnd_3023460 1552488219642845932545367 := by
  unfold tailWord_3023460
  simp only [CollatzResearch.WordTrace]
  refine ⟨55137322813264130351561917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73516430417685507135415889 55137322813264130351561917)
  ·
    refine ⟨20676496054974048881835719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55137322813264130351561917 20676496054974048881835719)
    ·
      refine ⟨31014744082461073322753579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20676496054974048881835719 31014744082461073322753579)
      ·
        refine ⟨46522116123691609984130369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31014744082461073322753579 46522116123691609984130369)
        ·
          refine ⟨34891587092768707488097777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46522116123691609984130369 34891587092768707488097777)
          ·
            refine ⟨26168690319576530616073333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34891587092768707488097777 26168690319576530616073333)
            ·
              refine ⟨2453314717460299745256875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26168690319576530616073333 2453314717460299745256875)
              ·
                refine ⟨3679972076190449617885313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453314717460299745256875 3679972076190449617885313)
                ·
                  refine ⟨2759979057142837213413985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679972076190449617885313 2759979057142837213413985)
                  ·
                    refine ⟨2069984292857127910060489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759979057142837213413985 2069984292857127910060489)
                    ·
                      refine ⟨1552488219642845932545367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069984292857127910060489 1552488219642845932545367)
                      ·
                        rfl

theorem cell23_3023460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_3023460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023460 prefixEnd_3023460 := by exact prefixLift 3023460
  have htrace : WordTrace (prefixWord ++ tailWord_3023460) baseStart_3023460 baseEnd_3023460 := by
    simpa [prefixWord, tailWord_3023460, baseEnd_3023460] using wordTrace_append hprefix tailTrace_3023460
  have hstable : (prefixWord ++ tailWord_3023460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023460).length < 2 ^ (prefixWord ++ tailWord_3023460).sum := by decide
  have hdescent : baseEnd_3023460 < baseStart_3023460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_3023482 : Nat := 118140960795 + 3023482 * 2 ^ 59
def prefixEnd_3023482 : Nat := 4983230072969 + 3 ^ 40 * 3023482 * 2
def baseEnd_3023482 : Nat := 1552499516217244846470265

theorem tailTrace_3023482 : CollatzResearch.WordTrace tailWord_3023482 prefixEnd_3023482 1552499516217244846470265 := by
  unfold tailWord_3023482
  simp only [CollatzResearch.WordTrace]
  refine ⟨27568862008112139615106175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73516965354965705640283133 27568862008112139615106175)
  ·
    refine ⟨41353293012168209422659263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27568862008112139615106175 41353293012168209422659263)
    ·
      refine ⟨62029939518252314133988895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41353293012168209422659263 62029939518252314133988895)
      ·
        refine ⟨93044909277378471200983343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62029939518252314133988895 93044909277378471200983343)
        ·
          refine ⟨139567363916067706801475015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93044909277378471200983343 139567363916067706801475015)
          ·
            refine ⟨209351045874101560202212523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139567363916067706801475015 209351045874101560202212523)
            ·
              refine ⟨314026568811152340303318785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209351045874101560202212523 314026568811152340303318785)
              ·
                refine ⟨235519926608364255227489089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314026568811152340303318785 235519926608364255227489089)
                ·
                  refine ⟨176639944956273191420616817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235519926608364255227489089 176639944956273191420616817)
                  ·
                    refine ⟨132479958717204893565462613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176639944956273191420616817 132479958717204893565462613)
                    ·
                      refine ⟨1552499516217244846470265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 132479958717204893565462613 1552499516217244846470265)
                      ·
                        rfl

theorem cell23_3023482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_3023482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023482 prefixEnd_3023482 := by exact prefixLift 3023482
  have htrace : WordTrace (prefixWord ++ tailWord_3023482) baseStart_3023482 baseEnd_3023482 := by
    simpa [prefixWord, tailWord_3023482, baseEnd_3023482] using wordTrace_append hprefix tailTrace_3023482
  have hstable : (prefixWord ++ tailWord_3023482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023482).length < 2 ^ (prefixWord ++ tailWord_3023482).sum := by decide
  have hdescent : baseEnd_3023482 < baseStart_3023482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023489 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3023489 : Nat := 118140960795 + 3023489 * 2 ^ 59
def prefixEnd_3023489 : Nat := 4983230072969 + 3 ^ 40 * 3023489 * 2
def baseEnd_3023489 : Nat := 1552503110581826319082733

theorem tailTrace_3023489 : CollatzResearch.WordTrace tailWord_3023489 prefixEnd_3023489 1552503110581826319082733 := by
  unfold tailWord_3023489
  simp only [CollatzResearch.WordTrace]
  refine ⟨110275703343423198655929521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73517135562282132437286347 110275703343423198655929521)
  ·
    refine ⟨82706777507567398991947141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110275703343423198655929521 82706777507567398991947141)
    ·
      refine ⟨15507520782668887310990089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82706777507567398991947141 15507520782668887310990089)
      ·
        refine ⟨11630640587001665483242567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15507520782668887310990089 11630640587001665483242567)
        ·
          refine ⟨17445960880502498224863851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630640587001665483242567 17445960880502498224863851)
          ·
            refine ⟨26168941320753747337295777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17445960880502498224863851 26168941320753747337295777)
            ·
              refine ⟨19626705990565310502971833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26168941320753747337295777 19626705990565310502971833)
              ·
                refine ⟨14720029492923982877228875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19626705990565310502971833 14720029492923982877228875)
                ·
                  refine ⟨22080044239385974315843313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14720029492923982877228875 22080044239385974315843313)
                  ·
                    refine ⟨16560033179539480736882485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22080044239385974315843313 16560033179539480736882485)
                    ·
                      refine ⟨1552503110581826319082733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16560033179539480736882485 1552503110581826319082733)
                      ·
                        rfl

theorem cell23_3023489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3023489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023489 prefixEnd_3023489 := by exact prefixLift 3023489
  have htrace : WordTrace (prefixWord ++ tailWord_3023489) baseStart_3023489 baseEnd_3023489 := by
    simpa [prefixWord, tailWord_3023489, baseEnd_3023489] using wordTrace_append hprefix tailTrace_3023489
  have hstable : (prefixWord ++ tailWord_3023489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023489).length < 2 ^ (prefixWord ++ tailWord_3023489).sum := by decide
  have hdescent : baseEnd_3023489 < baseStart_3023489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023506 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3023506 : Nat := 118140960795 + 3023506 * 2 ^ 59
def prefixEnd_3023506 : Nat := 4983230072969 + 3 ^ 40 * 3023506 * 2
def baseEnd_3023506 : Nat := 1552511839752952752570155

theorem tailTrace_3023506 : CollatzResearch.WordTrace tailWord_3023506 prefixEnd_3023506 1552511839752952752570155 := by
  unfold tailWord_3023506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27569080846090402639824593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73517548922907740372865581 27569080846090402639824593)
  ·
    refine ⟨20676810634567801979868445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27569080846090402639824593 20676810634567801979868445)
    ·
      refine ⟨7753803987962925742450667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20676810634567801979868445 7753803987962925742450667)
      ·
        refine ⟨11630705981944388613676001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753803987962925742450667 11630705981944388613676001)
        ·
          refine ⟨8723029486458291460257001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11630705981944388613676001 8723029486458291460257001)
          ·
            refine ⟨6542272114843718595192751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8723029486458291460257001 6542272114843718595192751)
            ·
              refine ⟨9813408172265577892789127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542272114843718595192751 9813408172265577892789127)
              ·
                refine ⟨14720112258398366839183691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9813408172265577892789127 14720112258398366839183691)
                ·
                  refine ⟨22080168387597550258775537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14720112258398366839183691 22080168387597550258775537)
                  ·
                    refine ⟨16560126290698162694081653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22080168387597550258775537 16560126290698162694081653)
                    ·
                      refine ⟨1552511839752952752570155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16560126290698162694081653 1552511839752952752570155)
                      ·
                        rfl

theorem cell23_3023506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3023506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023506 prefixEnd_3023506 := by exact prefixLift 3023506
  have htrace : WordTrace (prefixWord ++ tailWord_3023506) baseStart_3023506 baseEnd_3023506 := by
    simpa [prefixWord, tailWord_3023506, baseEnd_3023506] using wordTrace_append hprefix tailTrace_3023506
  have hstable : (prefixWord ++ tailWord_3023506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023506).length < 2 ^ (prefixWord ++ tailWord_3023506).sum := by decide
  have hdescent : baseEnd_3023506 < baseStart_3023506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023530 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3023530 : Nat := 118140960795 + 3023530 * 2 ^ 59
def prefixEnd_3023530 : Nat := 4983230072969 + 3 ^ 40 * 3023530 * 2
def baseEnd_3023530 : Nat := 517508054429553552890015

theorem tailTrace_3023530 : CollatzResearch.WordTrace tailWord_3023530 prefixEnd_3023530 517508054429553552890015 := by
  unfold tailWord_3023530
  simp only [CollatzResearch.WordTrace]
  refine ⟨27569299684068665664543011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73518132490849775105448029 27569299684068665664543011)
  ·
    refine ⟨41353949526102998496814517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27569299684068665664543011 41353949526102998496814517)
    ·
      refine ⟨3876932768072156109076361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41353949526102998496814517 3876932768072156109076361)
      ·
        refine ⟨2907699576054117081807271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3876932768072156109076361 2907699576054117081807271)
        ·
          refine ⟨4361549364081175622710907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907699576054117081807271 4361549364081175622710907)
          ·
            refine ⟨6542324046121763434066361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361549364081175622710907 6542324046121763434066361)
            ·
              refine ⟨4906743034591322575549771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6542324046121763434066361 4906743034591322575549771)
              ·
                refine ⟨7360114551886983863324657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906743034591322575549771 7360114551886983863324657)
                ·
                  refine ⟨5520085913915237897493493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7360114551886983863324657 5520085913915237897493493)
                  ·
                    refine ⟨517508054429553552890015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5520085913915237897493493 517508054429553552890015)
                    ·
                      rfl

theorem cell23_3023530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3023530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023530 prefixEnd_3023530 := by exact prefixLift 3023530
  have htrace : WordTrace (prefixWord ++ tailWord_3023530) baseStart_3023530 baseEnd_3023530 := by
    simpa [prefixWord, tailWord_3023530, baseEnd_3023530] using wordTrace_append hprefix tailTrace_3023530
  have hstable : (prefixWord ++ tailWord_3023530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023530).length < 2 ^ (prefixWord ++ tailWord_3023530).sum := by decide
  have hdescent : baseEnd_3023530 < baseStart_3023530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023533 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3023533 : Nat := 118140960795 + 3023533 * 2 ^ 59
def prefixEnd_3023533 : Nat := 4983230072969 + 3 ^ 40 * 3023533 * 2
def baseEnd_3023533 : Nat := 1552525703730624146932531

theorem tailTrace_3023533 : CollatzResearch.WordTrace tailWord_3023533 prefixEnd_3023533 1552525703730624146932531 := by
  unfold tailWord_3023533
  simp only [CollatzResearch.WordTrace]
  refine ⟨110277308155263794170531253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73518205436842529447020835 110277308155263794170531253)
  ·
    refine ⟨10338497639555980703487305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110277308155263794170531253 10338497639555980703487305)
    ·
      refine ⟨7753873229666985527615479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10338497639555980703487305 7753873229666985527615479)
      ·
        refine ⟨11630809844500478291423219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753873229666985527615479 11630809844500478291423219)
        ·
          refine ⟨17446214766750717437134829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630809844500478291423219 17446214766750717437134829)
          ·
            refine ⟨6542330537531519038925561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17446214766750717437134829 6542330537531519038925561)
            ·
              refine ⟨4906747903148639279194171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6542330537531519038925561 4906747903148639279194171)
              ·
                refine ⟨7360121854722958918791257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906747903148639279194171 7360121854722958918791257)
                ·
                  refine ⟨5520091391042219189093443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7360121854722958918791257 5520091391042219189093443)
                  ·
                    refine ⟨8280137086563328783640165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520091391042219189093443 8280137086563328783640165)
                    ·
                      refine ⟨1552525703730624146932531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8280137086563328783640165 1552525703730624146932531)
                      ·
                        rfl

theorem cell23_3023533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3023533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023533 prefixEnd_3023533 := by exact prefixLift 3023533
  have htrace : WordTrace (prefixWord ++ tailWord_3023533) baseStart_3023533 baseEnd_3023533 := by
    simpa [prefixWord, tailWord_3023533, baseEnd_3023533] using wordTrace_append hprefix tailTrace_3023533
  have hstable : (prefixWord ++ tailWord_3023533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023533).length < 2 ^ (prefixWord ++ tailWord_3023533).sum := by decide
  have hdescent : baseEnd_3023533 < baseStart_3023533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023556 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 6]
def baseStart_3023556 : Nat := 118140960795 + 3023556 * 2 ^ 59
def prefixEnd_3023556 : Nat := 4983230072969 + 3 ^ 40 * 3023556 * 2
def baseEnd_3023556 : Nat := 172504168198408617438325

theorem tailTrace_3023556 : CollatzResearch.WordTrace tailWord_3023556 prefixEnd_3023556 172504168198408617438325 := by
  unfold tailWord_3023556
  simp only [CollatzResearch.WordTrace]
  refine ⟨55139073517090234549309261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73518764689453646065745681 55139073517090234549309261)
  ·
    refine ⟨20677152568908837955990973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55139073517090234549309261 20677152568908837955990973)
    ·
      refine ⟨7753932213340814233496615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20677152568908837955990973 7753932213340814233496615)
      ·
        refine ⟨11630898320011221350244923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753932213340814233496615 11630898320011221350244923)
        ·
          refine ⟨17446347480016832025367385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630898320011221350244923 17446347480016832025367385)
          ·
            refine ⟨13084760610012624019025539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17446347480016832025367385 13084760610012624019025539)
            ·
              refine ⟨19627140915018936028538309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13084760610012624019025539 19627140915018936028538309)
              ·
                refine ⟨3680088921566050505350933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19627140915018936028538309 3680088921566050505350933)
                ·
                  refine ⟨172504168198408617438325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3680088921566050505350933 172504168198408617438325)
                  ·
                    rfl

theorem cell23_3023556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_3023556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023556 prefixEnd_3023556 := by exact prefixLift 3023556
  have htrace : WordTrace (prefixWord ++ tailWord_3023556) baseStart_3023556 baseEnd_3023556 := by
    simpa [prefixWord, tailWord_3023556, baseEnd_3023556] using wordTrace_append hprefix tailTrace_3023556
  have hstable : (prefixWord ++ tailWord_3023556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023556).length < 2 ^ (prefixWord ++ tailWord_3023556).sum := by decide
  have hdescent : baseEnd_3023556 < baseStart_3023556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023560 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 1, 4]
def baseStart_3023560 : Nat := 118140960795 + 3023560 * 2 ^ 59
def prefixEnd_3023560 : Nat := 4983230072969 + 3 ^ 40 * 3023560 * 2
def baseEnd_3023560 : Nat := 517513189236098513764969

theorem tailTrace_3023560 : CollatzResearch.WordTrace tailWord_3023560 prefixEnd_3023560 517513189236098513764969 := by
  unfold tailWord_3023560
  simp only [CollatzResearch.WordTrace]
  refine ⟨55139146463082988890882067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73518861950777318521176089 55139146463082988890882067)
  ·
    refine ⟨82708719694624483336323101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55139146463082988890882067 82708719694624483336323101)
    ·
      refine ⟨31015769885484181251121163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82708719694624483336323101 31015769885484181251121163)
      ·
        refine ⟨46523654828226271876681745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31015769885484181251121163 46523654828226271876681745)
        ·
          refine ⟨34892741121169703907511309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46523654828226271876681745 34892741121169703907511309)
          ·
            refine ⟨13084777920438638965316741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34892741121169703907511309 13084777920438638965316741)
            ·
              refine ⟨2453395860082244805996889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13084777920438638965316741 2453395860082244805996889)
              ·
                refine ⟨1840046895061683604497667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453395860082244805996889 1840046895061683604497667)
                ·
                  refine ⟨2760070342592525406746501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840046895061683604497667 2760070342592525406746501)
                  ·
                    refine ⟨517513189236098513764969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760070342592525406746501 517513189236098513764969)
                    ·
                      rfl

theorem cell23_3023560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_3023560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023560 prefixEnd_3023560 := by exact prefixLift 3023560
  have htrace : WordTrace (prefixWord ++ tailWord_3023560) baseStart_3023560 baseEnd_3023560 := by
    simpa [prefixWord, tailWord_3023560, baseEnd_3023560] using wordTrace_append hprefix tailTrace_3023560
  have hstable : (prefixWord ++ tailWord_3023560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023560).length < 2 ^ (prefixWord ++ tailWord_3023560).sum := by decide
  have hdescent : baseEnd_3023560 < baseStart_3023560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023569 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_3023569 : Nat := 118140960795 + 3023569 * 2 ^ 59
def prefixEnd_3023569 : Nat := 4983230072969 + 3 ^ 40 * 3023569 * 2
def baseEnd_3023569 : Nat := 517514729678062002027455

theorem tailTrace_3023569 : CollatzResearch.WordTrace tailWord_3023569 prefixEnd_3023569 517514729678062002027455 := by
  unfold tailWord_3023569
  simp only [CollatzResearch.WordTrace]
  refine ⟨110278621183133372318841761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73519080788755581545894507 110278621183133372318841761)
  ·
    refine ⟨82708965887350029239131321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110278621183133372318841761 82708965887350029239131321)
    ·
      refine ⟨62031724415512521929348491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82708965887350029239131321 62031724415512521929348491)
      ·
        refine ⟨93047586623268782894022737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62031724415512521929348491 93047586623268782894022737)
        ·
          refine ⟨69785689967451587170517053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93047586623268782894022737 69785689967451587170517053)
          ·
            refine ⟨26169633737794345188943895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69785689967451587170517053 26169633737794345188943895)
            ·
              refine ⟨39254450606691517783415843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26169633737794345188943895 39254450606691517783415843)
              ·
                refine ⟨58881675910037276675123765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39254450606691517783415843 58881675910037276675123765)
                ·
                  refine ⟨5520157116565994688292853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58881675910037276675123765 5520157116565994688292853)
                  ·
                    refine ⟨517514729678062002027455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5520157116565994688292853 517514729678062002027455)
                    ·
                      rfl

theorem cell23_3023569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_3023569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023569 prefixEnd_3023569 := by exact prefixLift 3023569
  have htrace : WordTrace (prefixWord ++ tailWord_3023569) baseStart_3023569 baseEnd_3023569 := by
    simpa [prefixWord, tailWord_3023569, baseEnd_3023569] using wordTrace_append hprefix tailTrace_3023569
  have hstable : (prefixWord ++ tailWord_3023569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023569).length < 2 ^ (prefixWord ++ tailWord_3023569).sum := by decide
  have hdescent : baseEnd_3023569 < baseStart_3023569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023583 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 3]
def baseStart_3023583 : Nat := 118140960795 + 3023583 * 2 ^ 59
def prefixEnd_3023583 : Nat := 4983230072969 + 3 ^ 40 * 3023583 * 2
def baseEnd_3023583 : Nat := 1552551377763348951307301

theorem tailTrace_3023583 : CollatzResearch.WordTrace tailWord_3023583 prefixEnd_3023583 1552551377763348951307301 := by
  unfold tailWord_3023583
  simp only [CollatzResearch.WordTrace]
  refine ⟨110279131805082652709851403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73519421203388435139900935 110279131805082652709851403)
  ·
    refine ⟨165418697707623979064777105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110279131805082652709851403 165418697707623979064777105)
    ·
      refine ⟨124064023280717984298582829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165418697707623979064777105 124064023280717984298582829)
      ·
        refine ⟨46524008730269244111968561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124064023280717984298582829 46524008730269244111968561)
        ·
          refine ⟨34893006547701933083976421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46524008730269244111968561 34893006547701933083976421)
          ·
            refine ⟨6542438727694112453245579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34893006547701933083976421 6542438727694112453245579)
            ·
              refine ⟨9813658091541168679868369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542438727694112453245579 9813658091541168679868369)
              ·
                refine ⟨7360243568655876509901277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9813658091541168679868369 7360243568655876509901277)
                ·
                  refine ⟨2760091338245953691212979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7360243568655876509901277 2760091338245953691212979)
                  ·
                    refine ⟨4140137007368930536819469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2760091338245953691212979 4140137007368930536819469)
                    ·
                      refine ⟨1552551377763348951307301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4140137007368930536819469 1552551377763348951307301)
                      ·
                        rfl

theorem cell23_3023583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_3023583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023583 prefixEnd_3023583 := by exact prefixLift 3023583
  have htrace : WordTrace (prefixWord ++ tailWord_3023583) baseStart_3023583 baseEnd_3023583 := by
    simpa [prefixWord, tailWord_3023583, baseEnd_3023583] using wordTrace_append hprefix tailTrace_3023583
  have hstable : (prefixWord ++ tailWord_3023583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023583).length < 2 ^ (prefixWord ++ tailWord_3023583).sum := by decide
  have hdescent : baseEnd_3023583 < baseStart_3023583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023593 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 2, 3, 2]
def baseStart_3023593 : Nat := 118140960795 + 3023593 * 2 ^ 59
def prefixEnd_3023593 : Nat := 4983230072969 + 3 ^ 40 * 3023593 * 2
def baseEnd_3023593 : Nat := 1552556512569893912182255

theorem tailTrace_3023593 : CollatzResearch.WordTrace tailWord_3023593 prefixEnd_3023593 1552556512569893912182255 := by
  unfold tailWord_3023593
  simp only [CollatzResearch.WordTrace]
  refine ⟨110279496535046424417715433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73519664356697616278476955 110279496535046424417715433)
  ·
    refine ⟨82709622401284818313286575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110279496535046424417715433 82709622401284818313286575)
    ·
      refine ⟨124064433601927227469929863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82709622401284818313286575 124064433601927227469929863)
      ·
        refine ⟨186096650402890841204894795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124064433601927227469929863 186096650402890841204894795)
        ·
          refine ⟨279144975604336261807342193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186096650402890841204894795 279144975604336261807342193)
          ·
            refine ⟨209358731703252196355506645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279144975604336261807342193 209358731703252196355506645)
            ·
              refine ⟨4906845274294973352082187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 209358731703252196355506645 4906845274294973352082187)
              ·
                refine ⟨7360267911442460028123281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906845274294973352082187 7360267911442460028123281)
                ·
                  refine ⟨5520200933581845021092461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7360267911442460028123281 5520200933581845021092461)
                  ·
                    refine ⟨2070075350093191882909673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5520200933581845021092461 2070075350093191882909673)
                    ·
                      refine ⟨1552556512569893912182255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070075350093191882909673 1552556512569893912182255)
                      ·
                        rfl

theorem cell23_3023593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 3, 2].length) (baseStart_3023593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023593 prefixEnd_3023593 := by exact prefixLift 3023593
  have htrace : WordTrace (prefixWord ++ tailWord_3023593) baseStart_3023593 baseEnd_3023593 := by
    simpa [prefixWord, tailWord_3023593, baseEnd_3023593] using wordTrace_append hprefix tailTrace_3023593
  have hstable : (prefixWord ++ tailWord_3023593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023593).length < 2 ^ (prefixWord ++ tailWord_3023593).sum := by decide
  have hdescent : baseEnd_3023593 < baseStart_3023593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023600 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 1, 1, 3]
def baseStart_3023600 : Nat := 118140960795 + 3023600 * 2 ^ 59
def prefixEnd_3023600 : Nat := 4983230072969 + 3 ^ 40 * 3023600 * 2
def baseEnd_3023600 : Nat := 1552560106934475384794723

theorem tailTrace_3023600 : CollatzResearch.WordTrace tailWord_3023600 prefixEnd_3023600 1552560106934475384794723 := by
  unfold tailWord_3023600
  simp only [CollatzResearch.WordTrace]
  refine ⟨55139875923010532306610127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73519834564014043075480169 55139875923010532306610127)
  ·
    refine ⟨82709813884515798459915191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55139875923010532306610127 82709813884515798459915191)
    ·
      refine ⟨124064720826773697689872787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82709813884515798459915191 124064720826773697689872787)
      ·
        refine ⟨186097081240160546534809181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124064720826773697689872787 186097081240160546534809181)
        ·
          refine ⟨69786405465060204950553443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186097081240160546534809181 69786405465060204950553443)
          ·
            refine ⟨104679608197590307425830165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69786405465060204950553443 104679608197590307425830165)
            ·
              refine ⟨4906856634262045660585789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104679608197590307425830165 4906856634262045660585789)
              ·
                refine ⟨1840071237848267122719671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4906856634262045660585789 1840071237848267122719671)
                ·
                  refine ⟨2760106856772400684079507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840071237848267122719671 2760106856772400684079507)
                  ·
                    refine ⟨4140160285158601026119261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2760106856772400684079507 4140160285158601026119261)
                    ·
                      refine ⟨1552560106934475384794723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4140160285158601026119261 1552560106934475384794723)
                      ·
                        rfl

theorem cell23_3023600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 1, 3].length) (baseStart_3023600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023600 prefixEnd_3023600 := by exact prefixLift 3023600
  have htrace : WordTrace (prefixWord ++ tailWord_3023600) baseStart_3023600 baseEnd_3023600 := by
    simpa [prefixWord, tailWord_3023600, baseEnd_3023600] using wordTrace_append hprefix tailTrace_3023600
  have hstable : (prefixWord ++ tailWord_3023600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023600).length < 2 ^ (prefixWord ++ tailWord_3023600).sum := by decide
  have hdescent : baseEnd_3023600 < baseStart_3023600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023609 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3023609 : Nat := 118140960795 + 3023609 * 2 ^ 59
def prefixEnd_3023609 : Nat := 4983230072969 + 3 ^ 40 * 3023609 * 2
def baseEnd_3023609 : Nat := 1552564728260365849582181

theorem tailTrace_3023609 : CollatzResearch.WordTrace tailWord_3023609 prefixEnd_3023609 1552564728260365849582181 := by
  unfold tailWord_3023609
  simp only [CollatzResearch.WordTrace]
  refine ⟨110280080102988459150297881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73520053401992306100198587 110280080102988459150297881)
  ·
    refine ⟨82710060077241344362723411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110280080102988459150297881 82710060077241344362723411)
    ·
      refine ⟨124065090115862016544085117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82710060077241344362723411 124065090115862016544085117)
      ·
        refine ⟨46524408793448256204031919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124065090115862016544085117 46524408793448256204031919)
        ·
          refine ⟨69786613190172384306047879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46524408793448256204031919 69786613190172384306047879)
          ·
            refine ⟨104679919785258576459071819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69786613190172384306047879 104679919785258576459071819)
            ·
              refine ⟨157019879677887864688607729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104679919785258576459071819 157019879677887864688607729)
              ·
                refine ⟨117764909758415898516455797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157019879677887864688607729 117764909758415898516455797)
                ·
                  refine ⟨11040460289851490485917731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117764909758415898516455797 11040460289851490485917731)
                  ·
                    refine ⟨16560690434777235728876597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11040460289851490485917731 16560690434777235728876597)
                    ·
                      refine ⟨1552564728260365849582181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16560690434777235728876597 1552564728260365849582181)
                      ·
                        rfl

theorem cell23_3023609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3023609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023609 prefixEnd_3023609 := by exact prefixLift 3023609
  have htrace : WordTrace (prefixWord ++ tailWord_3023609) baseStart_3023609 baseEnd_3023609 := by
    simpa [prefixWord, tailWord_3023609, baseEnd_3023609] using wordTrace_append hprefix tailTrace_3023609
  have hstable : (prefixWord ++ tailWord_3023609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023609).length < 2 ^ (prefixWord ++ tailWord_3023609).sum := by decide
  have hdescent : baseEnd_3023609 < baseStart_3023609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023619 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6]
def baseStart_3023619 : Nat := 118140960795 + 3023619 * 2 ^ 59
def prefixEnd_3023619 : Nat := 4983230072969 + 3 ^ 40 * 3023619 * 2
def baseEnd_3023619 : Nat := 1552569863066910810457135

theorem tailTrace_3023619 : CollatzResearch.WordTrace tailWord_3023619 prefixEnd_3023619 1552569863066910810457135 := by
  unfold tailWord_3023619
  simp only [CollatzResearch.WordTrace]
  refine ⟨110280444832952230858161911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73520296555301487238774607 110280444832952230858161911)
  ·
    refine ⟨165420667249428346287242867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110280444832952230858161911 165420667249428346287242867)
    ·
      refine ⟨248131000874142519430864301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165420667249428346287242867 248131000874142519430864301)
      ·
        refine ⟨93049125327803444786574113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248131000874142519430864301 93049125327803444786574113)
        ·
          refine ⟨69786843995852583589930585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93049125327803444786574113 69786843995852583589930585)
          ·
            refine ⟨52340132996889437692447939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69786843995852583589930585 52340132996889437692447939)
            ·
              refine ⟨78510199495334156538671909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52340132996889437692447939 78510199495334156538671909)
              ·
                refine ⟨14720662405375154351000983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78510199495334156538671909 14720662405375154351000983)
                ·
                  refine ⟨22080993608062731526501475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14720662405375154351000983 22080993608062731526501475)
                  ·
                    refine ⟨33121490412094097289752213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22080993608062731526501475 33121490412094097289752213)
                    ·
                      refine ⟨1552569863066910810457135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33121490412094097289752213 1552569863066910810457135)
                      ·
                        rfl

theorem cell23_3023619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_3023619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023619 prefixEnd_3023619 := by exact prefixLift 3023619
  have htrace : WordTrace (prefixWord ++ tailWord_3023619) baseStart_3023619 baseEnd_3023619 := by
    simpa [prefixWord, tailWord_3023619, baseEnd_3023619] using wordTrace_append hprefix tailTrace_3023619
  have hstable : (prefixWord ++ tailWord_3023619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023619).length < 2 ^ (prefixWord ++ tailWord_3023619).sum := by decide
  have hdescent : baseEnd_3023619 < baseStart_3023619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023626 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3023626 : Nat := 118140960795 + 3023626 * 2 ^ 59
def prefixEnd_3023626 : Nat := 4983230072969 + 3 ^ 40 * 3023626 * 2
def baseEnd_3023626 : Nat := 1552573457431492283069603

theorem tailTrace_3023626 : CollatzResearch.WordTrace tailWord_3023626 prefixEnd_3023626 1552573457431492283069603 := by
  unfold tailWord_3023626
  simp only [CollatzResearch.WordTrace]
  refine ⟨27570175035981717763416683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73520466762617914035777821 27570175035981717763416683)
  ·
    refine ⟨41355262553972576645125025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27570175035981717763416683 41355262553972576645125025)
    ·
      refine ⟨31016446915479432483843769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41355262553972576645125025 31016446915479432483843769)
      ·
        refine ⟨23262335186609574362882827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31016446915479432483843769 23262335186609574362882827)
        ·
          refine ⟨34893502779914361544324241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23262335186609574362882827 34893502779914361544324241)
          ·
            refine ⟨26170127084935771158243181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34893502779914361544324241 26170127084935771158243181)
            ·
              refine ⟨9813797656850914184341193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26170127084935771158243181 9813797656850914184341193)
              ·
                refine ⟨7360348242638185638255895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9813797656850914184341193 7360348242638185638255895)
                ·
                  refine ⟨11040522363957278457383843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360348242638185638255895 11040522363957278457383843)
                  ·
                    refine ⟨16560783545935917686075765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11040522363957278457383843 16560783545935917686075765)
                    ·
                      refine ⟨1552573457431492283069603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16560783545935917686075765 1552573457431492283069603)
                      ·
                        rfl

theorem cell23_3023626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3023626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023626 prefixEnd_3023626 := by exact prefixLift 3023626
  have htrace : WordTrace (prefixWord ++ tailWord_3023626) baseStart_3023626 baseEnd_3023626 := by
    simpa [prefixWord, tailWord_3023626, baseEnd_3023626] using wordTrace_append hprefix tailTrace_3023626
  have hstable : (prefixWord ++ tailWord_3023626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023626).length < 2 ^ (prefixWord ++ tailWord_3023626).sum := by decide
  have hdescent : baseEnd_3023626 < baseStart_3023626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023674 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2]
def baseStart_3023674 : Nat := 118140960795 + 3023674 * 2 ^ 59
def prefixEnd_3023674 : Nat := 4983230072969 + 3 ^ 40 * 3023674 * 2
def baseEnd_3023674 : Nat := 1552598104502908095269383

theorem tailTrace_3023674 : CollatzResearch.WordTrace tailWord_3023674 prefixEnd_3023674 1552598104502908095269383 := by
  unfold tailWord_3023674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27570612711938243812853519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73521633898501983500942717 27570612711938243812853519)
  ·
    refine ⟨41355919067907365719280279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27570612711938243812853519 41355919067907365719280279)
    ·
      refine ⟨62033878601861048578920419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41355919067907365719280279 62033878601861048578920419)
      ·
        refine ⟨93050817902791572868380629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62033878601861048578920419 93050817902791572868380629)
        ·
          refine ⟨2180878544596677489102671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93050817902791572868380629 2180878544596677489102671)
          ·
            refine ⟨3271317816895016233654007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180878544596677489102671 3271317816895016233654007)
            ·
              refine ⟨4906976725342524350481011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271317816895016233654007 4906976725342524350481011)
              ·
                refine ⟨7360465088013786525721517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906976725342524350481011 7360465088013786525721517)
                ·
                  refine ⟨2760174408005169947145569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7360465088013786525721517 2760174408005169947145569)
                  ·
                    refine ⟨2070130806003877460359177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2760174408005169947145569 2070130806003877460359177)
                    ·
                      refine ⟨1552598104502908095269383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070130806003877460359177 1552598104502908095269383)
                      ·
                        rfl

theorem cell23_3023674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_3023674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023674 prefixEnd_3023674 := by exact prefixLift 3023674
  have htrace : WordTrace (prefixWord ++ tailWord_3023674) baseStart_3023674 baseEnd_3023674 := by
    simpa [prefixWord, tailWord_3023674, baseEnd_3023674] using wordTrace_append hprefix tailTrace_3023674
  have hstable : (prefixWord ++ tailWord_3023674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023674).length < 2 ^ (prefixWord ++ tailWord_3023674).sum := by decide
  have hdescent : baseEnd_3023674 < baseStart_3023674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023683 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 3, 3, 2]
def baseStart_3023683 : Nat := 118140960795 + 3023683 * 2 ^ 59
def prefixEnd_3023683 : Nat := 4983230072969 + 3 ^ 40 * 3023683 * 2
def baseEnd_3023683 : Nat := 1552602725828798560056841

theorem tailTrace_3023683 : CollatzResearch.WordTrace tailWord_3023683 prefixEnd_3023683 1552602725828798560056841 := by
  unfold tailWord_3023683
  simp only [CollatzResearch.WordTrace]
  refine ⟨110282779104720369788491703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73521852736480246525661135 110282779104720369788491703)
  ·
    refine ⟨165424168657080554682737555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110282779104720369788491703 165424168657080554682737555)
    ·
      refine ⟨248136252985620832024106333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165424168657080554682737555 248136252985620832024106333)
      ·
        refine ⟨93051094869607812009039875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248136252985620832024106333 93051094869607812009039875)
        ·
          refine ⟨139576642304411718013559813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93051094869607812009039875 139576642304411718013559813)
          ·
            refine ⟨26170620432077197127542465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139576642304411718013559813 26170620432077197127542465)
            ·
              refine ⟨19627965324057897845656849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26170620432077197127542465 19627965324057897845656849)
              ·
                refine ⟨14720973993043423384242637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19627965324057897845656849 14720973993043423384242637)
                ·
                  refine ⟨5520365247391283769090989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14720973993043423384242637 5520365247391283769090989)
                  ·
                    refine ⟨2070136967771731413409121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5520365247391283769090989 2070136967771731413409121)
                    ·
                      refine ⟨1552602725828798560056841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070136967771731413409121 1552602725828798560056841)
                      ·
                        rfl

theorem cell23_3023683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_3023683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023683 prefixEnd_3023683 := by exact prefixLift 3023683
  have htrace : WordTrace (prefixWord ++ tailWord_3023683) baseStart_3023683 baseEnd_3023683 := by
    simpa [prefixWord, tailWord_3023683, baseEnd_3023683] using wordTrace_append hprefix tailTrace_3023683
  have hstable : (prefixWord ++ tailWord_3023683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023683).length < 2 ^ (prefixWord ++ tailWord_3023683).sum := by decide
  have hdescent : baseEnd_3023683 < baseStart_3023683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023730 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3023730 : Nat := 118140960795 + 3023730 * 2 ^ 59
def prefixEnd_3023730 : Nat := 4983230072969 + 3 ^ 40 * 3023730 * 2
def baseEnd_3023730 : Nat := 1552626859419559876169125

theorem tailTrace_3023730 : CollatzResearch.WordTrace tailWord_3023730 prefixEnd_3023730 1552626859419559876169125 := by
  unfold tailWord_3023730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27571123333887524203863161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73522995557033397876968429 27571123333887524203863161)
  ·
    refine ⟨20678342500415643152897371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27571123333887524203863161 20678342500415643152897371)
    ·
      refine ⟨31017513750623464729346057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20678342500415643152897371 31017513750623464729346057)
      ·
        refine ⟨23263135312967598547009543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31017513750623464729346057 23263135312967598547009543)
        ·
          refine ⟨34894702969451397820514315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23263135312967598547009543 34894702969451397820514315)
          ·
            refine ⟨52342054454177096730771473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34894702969451397820514315 52342054454177096730771473)
            ·
              refine ⟨39256540840632822548078605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52342054454177096730771473 39256540840632822548078605)
              ·
                refine ⟨14721202815237308455529477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39256540840632822548078605 14721202815237308455529477)
                ·
                  refine ⟨2760225527856995335411777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14721202815237308455529477 2760225527856995335411777)
                  ·
                    refine ⟨2070169145892746501558833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2760225527856995335411777 2070169145892746501558833)
                    ·
                      refine ⟨1552626859419559876169125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070169145892746501558833 1552626859419559876169125)
                      ·
                        rfl

theorem cell23_3023730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3023730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023730 prefixEnd_3023730 := by exact prefixLift 3023730
  have htrace : WordTrace (prefixWord ++ tailWord_3023730) baseStart_3023730 baseEnd_3023730 := by
    simpa [prefixWord, tailWord_3023730, baseEnd_3023730] using wordTrace_append hprefix tailTrace_3023730
  have hstable : (prefixWord ++ tailWord_3023730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023730).length < 2 ^ (prefixWord ++ tailWord_3023730).sum := by decide
  have hdescent : baseEnd_3023730 < baseStart_3023730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023733 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3023733 : Nat := 118140960795 + 3023733 * 2 ^ 59
def prefixEnd_3023733 : Nat := 4983230072969 + 3 ^ 40 * 3023733 * 2
def baseEnd_3023733 : Nat := 1552628399861523364431611

theorem tailTrace_3023733 : CollatzResearch.WordTrace tailWord_3023733 prefixEnd_3023733 1552628399861523364431611 := by
  unfold tailWord_3023733
  simp only [CollatzResearch.WordTrace]
  refine ⟨110284602754539228327811853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73523068503026152218541235 110284602754539228327811853)
  ·
    refine ⟨41356726032952210622929445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110284602754539228327811853 41356726032952210622929445)
    ·
      refine ⟨7754386131178539491799271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41356726032952210622929445 7754386131178539491799271)
      ·
        refine ⟨11631579196767809237698907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7754386131178539491799271 11631579196767809237698907)
        ·
          refine ⟨17447368795151713856548361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11631579196767809237698907 17447368795151713856548361)
          ·
            refine ⟨13085526596363785392411271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17447368795151713856548361 13085526596363785392411271)
            ·
              refine ⟨19628289894545678088616907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085526596363785392411271 19628289894545678088616907)
              ·
                refine ⟨29442434841818517132925361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19628289894545678088616907 29442434841818517132925361)
                ·
                  refine ⟨22081826131363887849694021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29442434841818517132925361 22081826131363887849694021)
                  ·
                    refine ⟨4140342399630728971817629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22081826131363887849694021 4140342399630728971817629)
                    ·
                      refine ⟨1552628399861523364431611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4140342399630728971817629 1552628399861523364431611)
                      ·
                        rfl

theorem cell23_3023733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3023733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023733 prefixEnd_3023733 := by exact prefixLift 3023733
  have htrace : WordTrace (prefixWord ++ tailWord_3023733) baseStart_3023733 baseEnd_3023733 := by
    simpa [prefixWord, tailWord_3023733, baseEnd_3023733] using wordTrace_append hprefix tailTrace_3023733
  have hstable : (prefixWord ++ tailWord_3023733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023733).length < 2 ^ (prefixWord ++ tailWord_3023733).sum := by decide
  have hdescent : baseEnd_3023733 < baseStart_3023733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023776 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3023776 : Nat := 118140960795 + 3023776 * 2 ^ 59
def prefixEnd_3023776 : Nat := 4983230072969 + 3 ^ 40 * 3023776 * 2
def baseEnd_3023776 : Nat := 1552650479529666696193913

theorem tailTrace_3023776 : CollatzResearch.WordTrace tailWord_3023776 prefixEnd_3023776 1552650479529666696193913 := by
  unfold tailWord_3023776
  simp only [CollatzResearch.WordTrace]
  refine ⟨55143085546691723335813591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73524114062255631114418121 55143085546691723335813591)
  ·
    refine ⟨82714628320037585003720387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55143085546691723335813591 82714628320037585003720387)
    ·
      refine ⟨124071942480056377505580581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82714628320037585003720387 124071942480056377505580581)
      ·
        refine ⟨23263489215010570782296359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124071942480056377505580581 23263489215010570782296359)
        ·
          refine ⟨34895233822515856173444539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23263489215010570782296359 34895233822515856173444539)
          ·
            refine ⟨52342850733773784260166809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34895233822515856173444539 52342850733773784260166809)
            ·
              refine ⟨39257138050330338195125107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52342850733773784260166809 39257138050330338195125107)
              ·
                refine ⟨58885707075495507292687661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39257138050330338195125107 58885707075495507292687661)
                ·
                  refine ⟨22082140153310815234757873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58885707075495507292687661 22082140153310815234757873)
                  ·
                    refine ⟨16561605114983111426068405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22082140153310815234757873 16561605114983111426068405)
                    ·
                      refine ⟨1552650479529666696193913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16561605114983111426068405 1552650479529666696193913)
                      ·
                        rfl

theorem cell23_3023776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3023776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023776 prefixEnd_3023776 := by exact prefixLift 3023776
  have htrace : WordTrace (prefixWord ++ tailWord_3023776) baseStart_3023776 baseEnd_3023776 := by
    simpa [prefixWord, tailWord_3023776, baseEnd_3023776] using wordTrace_append hprefix tailTrace_3023776
  have hstable : (prefixWord ++ tailWord_3023776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023776).length < 2 ^ (prefixWord ++ tailWord_3023776).sum := by decide
  have hdescent : baseEnd_3023776 < baseStart_3023776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023798 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3023798 : Nat := 118140960795 + 3023798 * 2 ^ 59
def prefixEnd_3023798 : Nat := 4983230072969 + 3 ^ 40 * 3023798 * 2
def baseEnd_3023798 : Nat := 1552661776104065610118813

theorem tailTrace_3023798 : CollatzResearch.WordTrace tailWord_3023798 prefixEnd_3023798 1552661776104065610118813 := by
  unfold tailWord_3023798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892935843706484026808003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73524648999535829619285365 6892935843706484026808003)
  ·
    refine ⟨10339403765559726040212005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892935843706484026808003 10339403765559726040212005)
    ·
      refine ⟨1938638206042448632539751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10339403765559726040212005 1938638206042448632539751)
      ·
        refine ⟨2907957309063672948809627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938638206042448632539751 2907957309063672948809627)
        ·
          refine ⟨4361935963595509423214441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907957309063672948809627 4361935963595509423214441)
          ·
            refine ⟨3271451972696632067410831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4361935963595509423214441 3271451972696632067410831)
            ·
              refine ⟨4907177959044948101116247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271451972696632067410831 4907177959044948101116247)
              ·
                refine ⟨7360766938567422151674371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907177959044948101116247 7360766938567422151674371)
                ·
                  refine ⟨11041150407851133227511557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360766938567422151674371 11041150407851133227511557)
                  ·
                    refine ⟨2070215701472087480158417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11041150407851133227511557 2070215701472087480158417)
                    ·
                      refine ⟨1552661776104065610118813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070215701472087480158417 1552661776104065610118813)
                      ·
                        rfl

theorem cell23_3023798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3023798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023798 prefixEnd_3023798 := by exact prefixLift 3023798
  have htrace : WordTrace (prefixWord ++ tailWord_3023798) baseStart_3023798 baseEnd_3023798 := by
    simpa [prefixWord, tailWord_3023798, baseEnd_3023798] using wordTrace_append hprefix tailTrace_3023798
  have hstable : (prefixWord ++ tailWord_3023798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023798).length < 2 ^ (prefixWord ++ tailWord_3023798).sum := by decide
  have hdescent : baseEnd_3023798 < baseStart_3023798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023803 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 6, 4, 2]
def baseStart_3023803 : Nat := 118140960795 + 3023803 * 2 ^ 59
def prefixEnd_3023803 : Nat := 4983230072969 + 3 ^ 40 * 3023803 * 2
def baseEnd_3023803 : Nat := 1552664343507338090556289

theorem tailTrace_3023803 : CollatzResearch.WordTrace tailWord_3023803 prefixEnd_3023803 1552664343507338090556289 := by
  unfold tailWord_3023803
  simp only [CollatzResearch.WordTrace]
  refine ⟨110287155864285630282860063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73524770576190420188573375 110287155864285630282860063)
  ·
    refine ⟨165430733796428445424290095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110287155864285630282860063 165430733796428445424290095)
    ·
      refine ⟨248146100694642668136435143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165430733796428445424290095 248146100694642668136435143)
      ·
        refine ⟨372219151041964002204652715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248146100694642668136435143 372219151041964002204652715)
        ·
          refine ⟨558328726562946003306979073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372219151041964002204652715 558328726562946003306979073)
          ·
            refine ⟨418746544922209502480234305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558328726562946003306979073 418746544922209502480234305)
            ·
              refine ⟨314059908691657126860175729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418746544922209502480234305 314059908691657126860175729)
              ·
                refine ⟨235544931518742845145131797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314059908691657126860175729 235544931518742845145131797)
                ·
                  refine ⟨11041168664941070866178053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 235544931518742845145131797 11041168664941070866178053)
                  ·
                    refine ⟨2070219124676450787408385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11041168664941070866178053 2070219124676450787408385)
                    ·
                      refine ⟨1552664343507338090556289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070219124676450787408385 1552664343507338090556289)
                      ·
                        rfl

theorem cell23_3023803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4, 2].length) (baseStart_3023803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023803 prefixEnd_3023803 := by exact prefixLift 3023803
  have htrace : WordTrace (prefixWord ++ tailWord_3023803) baseStart_3023803 baseEnd_3023803 := by
    simpa [prefixWord, tailWord_3023803, baseEnd_3023803] using wordTrace_append hprefix tailTrace_3023803
  have hstable : (prefixWord ++ tailWord_3023803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023803).length < 2 ^ (prefixWord ++ tailWord_3023803).sum := by decide
  have hdescent : baseEnd_3023803 < baseStart_3023803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023823 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_3023823 : Nat := 118140960795 + 3023823 * 2 ^ 59
def prefixEnd_3023823 : Nat := 4983230072969 + 3 ^ 40 * 3023823 * 2
def baseEnd_3023823 : Nat := 1552674613120428012306197

theorem tailTrace_3023823 : CollatzResearch.WordTrace tailWord_3023823 prefixEnd_3023823 1552674613120428012306197 := by
  unfold tailWord_3023823
  simp only [CollatzResearch.WordTrace]
  refine ⟨110287885324213173698588123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73525256882808782465725415 110287885324213173698588123)
  ·
    refine ⟨165431827986319760547882185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110287885324213173698588123 165431827986319760547882185)
    ·
      refine ⟨124073870989739820410911639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165431827986319760547882185 124073870989739820410911639)
      ·
        refine ⟨186110806484609730616367459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124073870989739820410911639 186110806484609730616367459)
        ·
          refine ⟨279166209726914595924551189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186110806484609730616367459 279166209726914595924551189)
          ·
            refine ⟨13085916080949121683963337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279166209726914595924551189 13085916080949121683963337)
            ·
              refine ⟨9814437060711841262972503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13085916080949121683963337 9814437060711841262972503)
              ·
                refine ⟨14721655591067761894458755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9814437060711841262972503 14721655591067761894458755)
                ·
                  refine ⟨22082483386601642841688133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14721655591067761894458755 22082483386601642841688133)
                  ·
                    refine ⟨4140465634987808032816525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22082483386601642841688133 4140465634987808032816525)
                    ·
                      refine ⟨1552674613120428012306197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4140465634987808032816525 1552674613120428012306197)
                      ·
                        rfl

theorem cell23_3023823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_3023823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023823 prefixEnd_3023823 := by exact prefixLift 3023823
  have htrace : WordTrace (prefixWord ++ tailWord_3023823) baseStart_3023823 baseEnd_3023823 := by
    simpa [prefixWord, tailWord_3023823, baseEnd_3023823] using wordTrace_append hprefix tailTrace_3023823
  have hstable : (prefixWord ++ tailWord_3023823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023823).length < 2 ^ (prefixWord ++ tailWord_3023823).sum := by decide
  have hdescent : baseEnd_3023823 < baseStart_3023823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023843 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 6]
def baseStart_3023843 : Nat := 118140960795 + 3023843 * 2 ^ 59
def prefixEnd_3023843 : Nat := 4983230072969 + 3 ^ 40 * 3023843 * 2
def baseEnd_3023843 : Nat := 172520542525946437117345

theorem tailTrace_3023843 : CollatzResearch.WordTrace tailWord_3023843 prefixEnd_3023843 172520542525946437117345 := by
  unfold tailWord_3023843
  simp only [CollatzResearch.WordTrace]
  refine ⟨110288614784140717114316183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73525743189427144742877455 110288614784140717114316183)
  ·
    refine ⟨165432922176211075671474275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110288614784140717114316183 165432922176211075671474275)
    ·
      refine ⟨248149383264316613507211413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165432922176211075671474275 248149383264316613507211413)
      ·
        refine ⟨11632002340514841258150535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 248149383264316613507211413 11632002340514841258150535)
        ·
          refine ⟨17448003510772261887225803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11632002340514841258150535 17448003510772261887225803)
          ·
            refine ⟨26172005266158392830838705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17448003510772261887225803 26172005266158392830838705)
            ·
              refine ⟨19629003949618794623129029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26172005266158392830838705 19629003949618794623129029)
              ·
                refine ⟨3680438240553523991836693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19629003949618794623129029 3680438240553523991836693)
                ·
                  refine ⟨172520542525946437117345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3680438240553523991836693 172520542525946437117345)
                  ·
                    rfl

theorem cell23_3023843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 6].length) (baseStart_3023843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023843 prefixEnd_3023843 := by exact prefixLift 3023843
  have htrace : WordTrace (prefixWord ++ tailWord_3023843) baseStart_3023843 baseEnd_3023843 := by
    simpa [prefixWord, tailWord_3023843, baseEnd_3023843] using wordTrace_append hprefix tailTrace_3023843
  have hstable : (prefixWord ++ tailWord_3023843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023843).length < 2 ^ (prefixWord ++ tailWord_3023843).sum := by decide
  have hdescent : baseEnd_3023843 < baseStart_3023843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023847 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3023847 : Nat := 118140960795 + 3023847 * 2 ^ 59
def prefixEnd_3023847 : Nat := 4983230072969 + 3 ^ 40 * 3023847 * 2
def baseEnd_3023847 : Nat := 517562312218711972802029

theorem tailTrace_3023847 : CollatzResearch.WordTrace tailWord_3023847 prefixEnd_3023847 517562312218711972802029 := by
  unfold tailWord_3023847
  simp only [CollatzResearch.WordTrace]
  refine ⟨110288760676126225797461795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73525840450750817198307863 110288760676126225797461795)
  ·
    refine ⟨165433141014189338696192693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110288760676126225797461795 165433141014189338696192693)
    ·
      refine ⟨15509356970080250502768065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165433141014189338696192693 15509356970080250502768065)
      ·
        refine ⟨11632017727560187877076049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15509356970080250502768065 11632017727560187877076049)
        ·
          refine ⟨8724013295670140907807037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11632017727560187877076049 8724013295670140907807037)
          ·
            refine ⟨3271504985876302840427639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8724013295670140907807037 3271504985876302840427639)
            ·
              refine ⟨4907257478814454260641459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271504985876302840427639 4907257478814454260641459)
              ·
                refine ⟨7360886218221681390962189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907257478814454260641459 7360886218221681390962189)
                ·
                  refine ⟨2760332331833130521610821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7360886218221681390962189 2760332331833130521610821)
                  ·
                    refine ⟨517562312218711972802029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760332331833130521610821 517562312218711972802029)
                    ·
                      rfl

theorem cell23_3023847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3023847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023847 prefixEnd_3023847 := by exact prefixLift 3023847
  have htrace : WordTrace (prefixWord ++ tailWord_3023847) baseStart_3023847 baseEnd_3023847 := by
    simpa [prefixWord, tailWord_3023847, baseEnd_3023847] using wordTrace_append hprefix tailTrace_3023847
  have hstable : (prefixWord ++ tailWord_3023847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023847).length < 2 ^ (prefixWord ++ tailWord_3023847).sum := by decide
  have hdescent : baseEnd_3023847 < baseStart_3023847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023856 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_3023856 : Nat := 118140960795 + 3023856 * 2 ^ 59
def prefixEnd_3023856 : Nat := 4983230072969 + 3 ^ 40 * 3023856 * 2
def baseEnd_3023856 : Nat := 517563852660675461064515

theorem tailTrace_3023856 : CollatzResearch.WordTrace tailWord_3023856 prefixEnd_3023856 517563852660675461064515 := by
  unfold tailWord_3023856
  simp only [CollatzResearch.WordTrace]
  refine ⟨55144544466546810167269711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73526059288729080223026281 55144544466546810167269711)
  ·
    refine ⟨82716816699820215250904567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55144544466546810167269711 82716816699820215250904567)
    ·
      refine ⟨124075225049730322876356851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82716816699820215250904567 124075225049730322876356851)
      ·
        refine ⟨186112837574595484314535277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124075225049730322876356851 186112837574595484314535277)
        ·
          refine ⟨69792314090473306617950729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186112837574595484314535277 69792314090473306617950729)
          ·
            refine ⟨52344235567854979963463047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69792314090473306617950729 52344235567854979963463047)
            ·
              refine ⟨78516353351782469945194571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52344235567854979963463047 78516353351782469945194571)
              ·
                refine ⟨117774530027673704917791857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78516353351782469945194571 117774530027673704917791857)
                ·
                  refine ⟨88330897520755278688343893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117774530027673704917791857 88330897520755278688343893)
                  ·
                    refine ⟨517563852660675461064515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 88330897520755278688343893 517563852660675461064515)
                    ·
                      rfl

theorem cell23_3023856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_3023856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023856 prefixEnd_3023856 := by exact prefixLift 3023856
  have htrace : WordTrace (prefixWord ++ tailWord_3023856) baseStart_3023856 baseEnd_3023856 := by
    simpa [prefixWord, tailWord_3023856, baseEnd_3023856] using wordTrace_append hprefix tailTrace_3023856
  have hstable : (prefixWord ++ tailWord_3023856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023856).length < 2 ^ (prefixWord ++ tailWord_3023856).sum := by decide
  have hdescent : baseEnd_3023856 < baseStart_3023856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023920 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 2, 4]
def baseStart_3023920 : Nat := 118140960795 + 3023920 * 2 ^ 59
def prefixEnd_3023920 : Nat := 4983230072969 + 3 ^ 40 * 3023920 * 2
def baseEnd_3023920 : Nat := 517574806914638044264417

theorem tailTrace_3023920 : CollatzResearch.WordTrace tailWord_3023920 prefixEnd_3023920 517574806914638044264417 := by
  unfold tailWord_3023920
  simp only [CollatzResearch.WordTrace]
  refine ⟨55145711602430879632434607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73527615469907839509912809 55145711602430879632434607)
  ·
    refine ⟨82718567403646319448651911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55145711602430879632434607 82718567403646319448651911)
    ·
      refine ⟨124077851105469479172977867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82718567403646319448651911 124077851105469479172977867)
      ·
        refine ⟨186116776658204218759466801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124077851105469479172977867 186116776658204218759466801)
        ·
          refine ⟨139587582493653164069600101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186116776658204218759466801 139587582493653164069600101)
          ·
            refine ⟨26172671717559968263050019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139587582493653164069600101 26172671717559968263050019)
            ·
              refine ⟨39259007576339952394575029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26172671717559968263050019 39259007576339952394575029)
              ·
                refine ⟨3680531960281870536991409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39259007576339952394575029 3680531960281870536991409)
                ·
                  refine ⟨2760398970211402902743557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680531960281870536991409 2760398970211402902743557)
                  ·
                    refine ⟨517574806914638044264417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760398970211402902743557 517574806914638044264417)
                    ·
                      rfl

theorem cell23_3023920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_3023920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023920 prefixEnd_3023920 := by exact prefixLift 3023920
  have htrace : WordTrace (prefixWord ++ tailWord_3023920) baseStart_3023920 baseEnd_3023920 := by
    simpa [prefixWord, tailWord_3023920, baseEnd_3023920] using wordTrace_append hprefix tailTrace_3023920
  have hstable : (prefixWord ++ tailWord_3023920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023920).length < 2 ^ (prefixWord ++ tailWord_3023920).sum := by decide
  have hdescent : baseEnd_3023920 < baseStart_3023920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023930 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_3023930 : Nat := 118140960795 + 3023930 * 2 ^ 59
def prefixEnd_3023930 : Nat := 4983230072969 + 3 ^ 40 * 3023930 * 2
def baseEnd_3023930 : Nat := 1552729555550459093668205

theorem tailTrace_3023930 : CollatzResearch.WordTrace tailWord_3023930 prefixEnd_3023930 1552729555550459093668205 := by
  unfold tailWord_3023930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27572946983706382743183311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73527858623217020648488829 27572946983706382743183311)
  ·
    refine ⟨41359420475559574114774967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27572946983706382743183311 41359420475559574114774967)
    ·
      refine ⟨62039130713339361172162451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41359420475559574114774967 62039130713339361172162451)
      ·
        refine ⟨93058696070009041758243677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62039130713339361172162451 93058696070009041758243677)
        ·
          refine ⟨34897011026253390659341379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93058696070009041758243677 34897011026253390659341379)
          ·
            refine ⟨52345516539380085989012069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34897011026253390659341379 52345516539380085989012069)
            ·
              refine ⟨9814784351133766122939763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52345516539380085989012069 9814784351133766122939763)
              ·
                refine ⟨14722176526700649184409645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9814784351133766122939763 14722176526700649184409645)
                ·
                  refine ⟨5520816197512743444153617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14722176526700649184409645 5520816197512743444153617)
                  ·
                    refine ⟨4140612148134557583115213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5520816197512743444153617 4140612148134557583115213)
                    ·
                      refine ⟨1552729555550459093668205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4140612148134557583115213 1552729555550459093668205)
                      ·
                        rfl

theorem cell23_3023930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_3023930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023930 prefixEnd_3023930 := by exact prefixLift 3023930
  have htrace : WordTrace (prefixWord ++ tailWord_3023930) baseStart_3023930 baseEnd_3023930 := by
    simpa [prefixWord, tailWord_3023930, baseEnd_3023930] using wordTrace_append hprefix tailTrace_3023930
  have hstable : (prefixWord ++ tailWord_3023930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023930).length < 2 ^ (prefixWord ++ tailWord_3023930).sum := by decide
  have hdescent : baseEnd_3023930 < baseStart_3023930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023954 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3023954 : Nat := 118140960795 + 3023954 * 2 ^ 59
def prefixEnd_3023954 : Nat := 4983230072969 + 3 ^ 40 * 3023954 * 2
def baseEnd_3023954 : Nat := 517580626362055666589365

theorem tailTrace_3023954 : CollatzResearch.WordTrace tailWord_3023954 prefixEnd_3023954 517580626362055666589365 := by
  unfold tailWord_3023954
  simp only [CollatzResearch.WordTrace]
  refine ⟨27573165821684645767901729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73528442191159055381071277 27573165821684645767901729)
  ·
    refine ⟨20679874366263484325926297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27573165821684645767901729 20679874366263484325926297)
    ·
      refine ⟨15509905774697613244444723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20679874366263484325926297 15509905774697613244444723)
      ·
        refine ⟨23264858662046419866667085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15509905774697613244444723 23264858662046419866667085)
        ·
          refine ⟨8724321998267407450000157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23264858662046419866667085 8724321998267407450000157)
          ·
            refine ⟨3271620749350277793750059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8724321998267407450000157 3271620749350277793750059)
            ·
              refine ⟨4907431124025416690625089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271620749350277793750059 4907431124025416690625089)
              ·
                refine ⟨3680573343019062517968817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4907431124025416690625089 3680573343019062517968817)
                ·
                  refine ⟨2760430007264296888476613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680573343019062517968817 2760430007264296888476613)
                  ·
                    refine ⟨517580626362055666589365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760430007264296888476613 517580626362055666589365)
                    ·
                      rfl

theorem cell23_3023954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3023954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023954 prefixEnd_3023954 := by exact prefixLift 3023954
  have htrace : WordTrace (prefixWord ++ tailWord_3023954) baseStart_3023954 baseEnd_3023954 := by
    simpa [prefixWord, tailWord_3023954, baseEnd_3023954] using wordTrace_append hprefix tailTrace_3023954
  have hstable : (prefixWord ++ tailWord_3023954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023954).length < 2 ^ (prefixWord ++ tailWord_3023954).sum := by decide
  have hdescent : baseEnd_3023954 < baseStart_3023954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023977 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 3]
def baseStart_3023977 : Nat := 118140960795 + 3023977 * 2 ^ 59
def prefixEnd_3023977 : Nat := 4983230072969 + 3 ^ 40 * 3023977 * 2
def baseEnd_3023977 : Nat := 1552753689141220409780489

theorem tailTrace_3023977 : CollatzResearch.WordTrace tailWord_3023977 prefixEnd_3023977 1552753689141220409780489 := by
  unfold tailWord_3023977
  simp only [CollatzResearch.WordTrace]
  refine ⟨110293502165655257999694185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73529001443770171999796123 110293502165655257999694185)
  ·
    refine ⟨82720126624241443499770639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110293502165655257999694185 82720126624241443499770639)
    ·
      refine ⟨124080189936362165249655959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82720126624241443499770639 124080189936362165249655959)
      ·
        refine ⟨186120284904543247874483939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124080189936362165249655959 186120284904543247874483939)
        ·
          refine ⟨279180427356814871811725909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186120284904543247874483939 279180427356814871811725909)
          ·
            refine ⟨3271645633087674279043663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 279180427356814871811725909 3271645633087674279043663)
            ·
              refine ⟨4907468449631511418565495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271645633087674279043663 4907468449631511418565495)
              ·
                refine ⟨7361202674447267127848243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907468449631511418565495 7361202674447267127848243)
                ·
                  refine ⟨11041804011670900691772365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7361202674447267127848243 11041804011670900691772365)
                  ·
                    refine ⟨4140676504376587759414637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11041804011670900691772365 4140676504376587759414637)
                    ·
                      refine ⟨1552753689141220409780489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4140676504376587759414637 1552753689141220409780489)
                      ·
                        rfl

theorem cell23_3023977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_3023977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023977 prefixEnd_3023977 := by exact prefixLift 3023977
  have htrace : WordTrace (prefixWord ++ tailWord_3023977) baseStart_3023977 baseEnd_3023977 := by
    simpa [prefixWord, tailWord_3023977, baseEnd_3023977] using wordTrace_append hprefix tailTrace_3023977
  have hstable : (prefixWord ++ tailWord_3023977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023977).length < 2 ^ (prefixWord ++ tailWord_3023977).sum := by decide
  have hdescent : baseEnd_3023977 < baseStart_3023977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3023990 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3023990 : Nat := 118140960795 + 3023990 * 2 ^ 59
def prefixEnd_3023990 : Nat := 4983230072969 + 3 ^ 40 * 3023990 * 2
def baseEnd_3023990 : Nat := 1552760364389728858917929

theorem tailTrace_3023990 : CollatzResearch.WordTrace tailWord_3023990 prefixEnd_3023990 1552760364389728858917929 := by
  unfold tailWord_3023990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893373519663010076244839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73529317543072107479944949 6893373519663010076244839)
  ·
    refine ⟨10340060279494515114367259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6893373519663010076244839 10340060279494515114367259)
    ·
      refine ⟨15510090419241772671550889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10340060279494515114367259 15510090419241772671550889)
      ·
        refine ⟨11632567814431329503663167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15510090419241772671550889 11632567814431329503663167)
        ·
          refine ⟨17448851721646994255494751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11632567814431329503663167 17448851721646994255494751)
          ·
            refine ⟨26173277582470491383242127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17448851721646994255494751 26173277582470491383242127)
            ·
              refine ⟨39259916373705737074863191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26173277582470491383242127 39259916373705737074863191)
              ·
                refine ⟨58889874560558605612294787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39259916373705737074863191 58889874560558605612294787)
                ·
                  refine ⟨88334811840837908418442181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58889874560558605612294787 88334811840837908418442181)
                  ·
                    refine ⟨16562777220157107828457909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88334811840837908418442181 16562777220157107828457909)
                    ·
                      refine ⟨1552760364389728858917929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16562777220157107828457909 1552760364389728858917929)
                      ·
                        rfl

theorem cell23_3023990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3023990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3023990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3023990 prefixEnd_3023990 := by exact prefixLift 3023990
  have htrace : WordTrace (prefixWord ++ tailWord_3023990) baseStart_3023990 baseEnd_3023990 := by
    simpa [prefixWord, tailWord_3023990, baseEnd_3023990] using wordTrace_append hprefix tailTrace_3023990
  have hstable : (prefixWord ++ tailWord_3023990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3023990).length < 2 ^ (prefixWord ++ tailWord_3023990).sum := by decide
  have hdescent : baseEnd_3023990 < baseStart_3023990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3023990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024004 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_3024004 : Nat := 118140960795 + 3024004 * 2 ^ 59
def prefixEnd_3024004 : Nat := 4983230072969 + 3 ^ 40 * 3024004 * 2
def baseEnd_3024004 : Nat := 1552767553118891804142865

theorem tailTrace_3024004 : CollatzResearch.WordTrace tailWord_3024004 prefixEnd_3024004 1552767553118891804142865 := by
  unfold tailWord_3024004
  simp only [CollatzResearch.WordTrace]
  refine ⟨55147243468278720805463533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73529657957704961073951377 55147243468278720805463533)
  ·
    refine ⟨20680216300604520302048825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55147243468278720805463533 20680216300604520302048825)
    ·
      refine ⟨15510162225453390226536619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20680216300604520302048825 15510162225453390226536619)
      ·
        refine ⟨23265243338180085339804929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15510162225453390226536619 23265243338180085339804929)
        ·
          refine ⟨17448932503635064004853697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23265243338180085339804929 17448932503635064004853697)
          ·
            refine ⟨13086699377726298003640273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17448932503635064004853697 13086699377726298003640273)
            ·
              refine ⟨9815024533294723502730205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13086699377726298003640273 9815024533294723502730205)
              ·
                refine ⟨3680634199985521313523827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9815024533294723502730205 3680634199985521313523827)
                ·
                  refine ⟨5520951299978281970285741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680634199985521313523827 5520951299978281970285741)
                  ·
                    refine ⟨2070356737491855738857153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5520951299978281970285741 2070356737491855738857153)
                    ·
                      refine ⟨1552767553118891804142865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070356737491855738857153 1552767553118891804142865)
                      ·
                        rfl

theorem cell23_3024004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_3024004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024004 prefixEnd_3024004 := by exact prefixLift 3024004
  have htrace : WordTrace (prefixWord ++ tailWord_3024004) baseStart_3024004 baseEnd_3024004 := by
    simpa [prefixWord, tailWord_3024004, baseEnd_3024004] using wordTrace_append hprefix tailTrace_3024004
  have hstable : (prefixWord ++ tailWord_3024004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024004).length < 2 ^ (prefixWord ++ tailWord_3024004).sum := by decide
  have hdescent : baseEnd_3024004 < baseStart_3024004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024068 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3024068 : Nat := 118140960795 + 3024068 * 2 ^ 59
def prefixEnd_3024068 : Nat := 4983230072969 + 3 ^ 40 * 3024068 * 2
def baseEnd_3024068 : Nat := 1552800415880779553742571

theorem tailTrace_3024068 : CollatzResearch.WordTrace tailWord_3024068 prefixEnd_3024068 1552800415880779553742571 := by
  unfold tailWord_3024068
  simp only [CollatzResearch.WordTrace]
  refine ⟨55148410604162790270628429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73531214138883720360837905 55148410604162790270628429)
  ·
    refine ⟨20680653976561046351485661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55148410604162790270628429 20680653976561046351485661)
    ·
      refine ⟨7755245241210392381807123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20680653976561046351485661 7755245241210392381807123)
      ·
        refine ⟨11632867861815588572710685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755245241210392381807123 11632867861815588572710685)
        ·
          refine ⟨4362325448180845714766507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11632867861815588572710685 4362325448180845714766507)
          ·
            refine ⟨6543488172271268572149761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362325448180845714766507 6543488172271268572149761)
            ·
              refine ⟨4907616129203451429112321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6543488172271268572149761 4907616129203451429112321)
              ·
                refine ⟨3680712096902588571834241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4907616129203451429112321 3680712096902588571834241)
                ·
                  refine ⟨2760534072676941428875681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680712096902588571834241 2760534072676941428875681)
                  ·
                    refine ⟨2070400554507706071656761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2760534072676941428875681 2070400554507706071656761)
                    ·
                      refine ⟨1552800415880779553742571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070400554507706071656761 1552800415880779553742571)
                      ·
                        rfl

theorem cell23_3024068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3024068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024068 prefixEnd_3024068 := by exact prefixLift 3024068
  have htrace : WordTrace (prefixWord ++ tailWord_3024068) baseStart_3024068 baseEnd_3024068 := by
    simpa [prefixWord, tailWord_3024068, baseEnd_3024068] using wordTrace_append hprefix tailTrace_3024068
  have hstable : (prefixWord ++ tailWord_3024068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024068).length < 2 ^ (prefixWord ++ tailWord_3024068).sum := by decide
  have hdescent : baseEnd_3024068 < baseStart_3024068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024074 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_3024074 : Nat := 118140960795 + 3024074 * 2 ^ 59
def prefixEnd_3024074 : Nat := 4983230072969 + 3 ^ 40 * 3024074 * 2
def baseEnd_3024074 : Nat := 172533721862745170029727

theorem tailTrace_3024074 : CollatzResearch.WordTrace tailWord_3024074 prefixEnd_3024074 172533721862745170029727 := by
  unfold tailWord_3024074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27574260011575960891493819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73531360030869229043983517 27574260011575960891493819)
  ·
    refine ⟨41361390017363941337240729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27574260011575960891493819 41361390017363941337240729)
    ·
      refine ⟨31021042513022956002930547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41361390017363941337240729 31021042513022956002930547)
      ·
        refine ⟨46531563769534434004395821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31021042513022956002930547 46531563769534434004395821)
        ·
          refine ⟨17449336413575412751648433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46531563769534434004395821 17449336413575412751648433)
          ·
            refine ⟨13087002310181559563736325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17449336413575412751648433 13087002310181559563736325)
            ·
              refine ⟨2453812933159042418200561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13087002310181559563736325 2453812933159042418200561)
              ·
                refine ⟨1840359699869281813650421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453812933159042418200561 1840359699869281813650421)
                ·
                  refine ⟨172533721862745170029727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1840359699869281813650421 172533721862745170029727)
                  ·
                    rfl

theorem cell23_3024074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_3024074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024074 prefixEnd_3024074 := by exact prefixLift 3024074
  have htrace : WordTrace (prefixWord ++ tailWord_3024074) baseStart_3024074 baseEnd_3024074 := by
    simpa [prefixWord, tailWord_3024074, baseEnd_3024074] using wordTrace_append hprefix tailTrace_3024074
  have hstable : (prefixWord ++ tailWord_3024074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024074).length < 2 ^ (prefixWord ++ tailWord_3024074).sum := by decide
  have hdescent : baseEnd_3024074 < baseStart_3024074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024090 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_3024090 : Nat := 118140960795 + 3024090 * 2 ^ 59
def prefixEnd_3024090 : Nat := 4983230072969 + 3 ^ 40 * 3024090 * 2
def baseEnd_3024090 : Nat := 1552811712455178467667469

theorem tailTrace_3024090 : CollatzResearch.WordTrace tailWord_3024090 prefixEnd_3024090 1552811712455178467667469 := by
  unfold tailWord_3024090
  simp only [CollatzResearch.WordTrace]
  refine ⟨27574405903561469574639431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73531749076163918865705149 27574405903561469574639431)
  ·
    refine ⟨41361608855342204361959147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27574405903561469574639431 41361608855342204361959147)
    ·
      refine ⟨62042413283013306542938721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41361608855342204361959147 62042413283013306542938721)
      ·
        refine ⟨46531809962259979907204041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62042413283013306542938721 46531809962259979907204041)
        ·
          refine ⟨34898857471694984930403031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46531809962259979907204041 34898857471694984930403031)
          ·
            refine ⟨52348286207542477395604547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34898857471694984930403031 52348286207542477395604547)
            ·
              refine ⟨78522429311313716093406821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52348286207542477395604547 78522429311313716093406821)
              ·
                refine ⟨14722955495871321767513779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78522429311313716093406821 14722955495871321767513779)
                ·
                  refine ⟨22084433243806982651270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14722955495871321767513779 22084433243806982651270669)
                  ·
                    refine ⟨8281662466427618494226501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22084433243806982651270669 8281662466427618494226501)
                    ·
                      refine ⟨1552811712455178467667469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8281662466427618494226501 1552811712455178467667469)
                      ·
                        rfl

theorem cell23_3024090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3024090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024090 prefixEnd_3024090 := by exact prefixLift 3024090
  have htrace : WordTrace (prefixWord ++ tailWord_3024090) baseStart_3024090 baseEnd_3024090 := by
    simpa [prefixWord, tailWord_3024090, baseEnd_3024090] using wordTrace_append hprefix tailTrace_3024090
  have hstable : (prefixWord ++ tailWord_3024090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024090).length < 2 ^ (prefixWord ++ tailWord_3024090).sum := by decide
  have hdescent : baseEnd_3024090 < baseStart_3024090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024107 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 4]
def baseStart_3024107 : Nat := 118140960795 + 3024107 * 2 ^ 59
def prefixEnd_3024107 : Nat := 4983230072969 + 3 ^ 40 * 3024107 * 2
def baseEnd_3024107 : Nat := 1552820441626304901154891

theorem tailTrace_3024107 : CollatzResearch.WordTrace tailWord_3024107 prefixEnd_3024107 1552820441626304901154891 := by
  unfold tailWord_3024107
  simp only [CollatzResearch.WordTrace]
  refine ⟨110298243655184290201926575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73532162436789526801284383 110298243655184290201926575)
  ·
    refine ⟨165447365482776435302889863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110298243655184290201926575 165447365482776435302889863)
    ·
      refine ⟨248171048224164652954334795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165447365482776435302889863 248171048224164652954334795)
      ·
        refine ⟨372256572336246979431502193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248171048224164652954334795 372256572336246979431502193)
        ·
          refine ⟨279192429252185234573626645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372256572336246979431502193 279192429252185234573626645)
          ·
            refine ⟨13087145121196182870638749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279192429252185234573626645 13087145121196182870638749)
            ·
              refine ⟨4907679420448568576489531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13087145121196182870638749 4907679420448568576489531)
              ·
                refine ⟨7361519130672852864734297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907679420448568576489531 7361519130672852864734297)
                ·
                  refine ⟨5521139348004639648550723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7361519130672852864734297 5521139348004639648550723)
                  ·
                    refine ⟨8281709022006959472826085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521139348004639648550723 8281709022006959472826085)
                    ·
                      refine ⟨1552820441626304901154891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8281709022006959472826085 1552820441626304901154891)
                      ·
                        rfl

theorem cell23_3024107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 4].length) (baseStart_3024107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024107 prefixEnd_3024107 := by exact prefixLift 3024107
  have htrace : WordTrace (prefixWord ++ tailWord_3024107) baseStart_3024107 baseEnd_3024107 := by
    simpa [prefixWord, tailWord_3024107, baseEnd_3024107] using wordTrace_append hprefix tailTrace_3024107
  have hstable : (prefixWord ++ tailWord_3024107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024107).length < 2 ^ (prefixWord ++ tailWord_3024107).sum := by decide
  have hdescent : baseEnd_3024107 < baseStart_3024107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024168 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3024168 : Nat := 118140960795 + 3024168 * 2 ^ 59
def prefixEnd_3024168 : Nat := 4983230072969 + 3 ^ 40 * 3024168 * 2
def baseEnd_3024168 : Nat := 517617254648743054164037

theorem tailTrace_3024168 : CollatzResearch.WordTrace tailWord_3024168 prefixEnd_3024168 517617254648743054164037 := by
  unfold tailWord_3024168
  simp only [CollatzResearch.WordTrace]
  refine ⟨55150234253981648809948579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73533645671975531746598105 55150234253981648809948579)
  ·
    refine ⟨82725351380972473214922869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55150234253981648809948579 82725351380972473214922869)
    ·
      refine ⟨7755501691966169363899019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82725351380972473214922869 7755501691966169363899019)
      ·
        refine ⟨11633252537949254045848529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755501691966169363899019 11633252537949254045848529)
        ·
          refine ⟨8724939403461940534386397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11633252537949254045848529 8724939403461940534386397)
          ·
            refine ⟨3271852276298227700394899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8724939403461940534386397 3271852276298227700394899)
            ·
              refine ⟨4907778414447341550592349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271852276298227700394899 4907778414447341550592349)
              ·
                refine ⟨1840416905417753081472131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4907778414447341550592349 1840416905417753081472131)
                ·
                  refine ⟨2760625358126629622208197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840416905417753081472131 2760625358126629622208197)
                  ·
                    refine ⟨517617254648743054164037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760625358126629622208197 517617254648743054164037)
                    ·
                      rfl

theorem cell23_3024168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3024168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024168 prefixEnd_3024168 := by exact prefixLift 3024168
  have htrace : WordTrace (prefixWord ++ tailWord_3024168) baseStart_3024168 baseEnd_3024168 := by
    simpa [prefixWord, tailWord_3024168, baseEnd_3024168] using wordTrace_append hprefix tailTrace_3024168
  have hstable : (prefixWord ++ tailWord_3024168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024168).length < 2 ^ (prefixWord ++ tailWord_3024168).sum := by decide
  have hdescent : baseEnd_3024168 < baseStart_3024168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024191 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 3]
def baseStart_3024191 : Nat := 118140960795 + 3024191 * 2 ^ 59
def prefixEnd_3024191 : Nat := 4983230072969 + 3 ^ 40 * 3024191 * 2
def baseEnd_3024191 : Nat := 1552863574001282572504505

theorem tailTrace_3024191 : CollatzResearch.WordTrace tailWord_3024191 prefixEnd_3024191 1552863574001282572504505 := by
  unfold tailWord_3024191
  simp only [CollatzResearch.WordTrace]
  refine ⟨110301307386879972547984427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73534204924586648365322951 110301307386879972547984427)
  ·
    refine ⟨165451961080319958821976641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110301307386879972547984427 165451961080319958821976641)
    ·
      refine ⟨124088970810239969116482481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165451961080319958821976641 124088970810239969116482481)
      ·
        refine ⟨93066728107679976837361861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124088970810239969116482481 93066728107679976837361861)
        ·
          refine ⟨17450011520189995657005349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93066728107679976837361861 17450011520189995657005349)
          ·
            refine ⟨3271877160035624185688503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17450011520189995657005349 3271877160035624185688503)
            ·
              refine ⟨4907815740053436278532755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271877160035624185688503 4907815740053436278532755)
              ·
                refine ⟨7361723610080154417799133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907815740053436278532755 7361723610080154417799133)
                ·
                  refine ⟨2760646353780057906674675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7361723610080154417799133 2760646353780057906674675)
                  ·
                    refine ⟨4140969530670086860012013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2760646353780057906674675 4140969530670086860012013)
                    ·
                      refine ⟨1552863574001282572504505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4140969530670086860012013 1552863574001282572504505)
                      ·
                        rfl

theorem cell23_3024191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_3024191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024191 prefixEnd_3024191 := by exact prefixLift 3024191
  have htrace : WordTrace (prefixWord ++ tailWord_3024191) baseStart_3024191 baseEnd_3024191 := by
    simpa [prefixWord, tailWord_3024191, baseEnd_3024191] using wordTrace_append hprefix tailTrace_3024191
  have hstable : (prefixWord ++ tailWord_3024191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024191).length < 2 ^ (prefixWord ++ tailWord_3024191).sum := by decide
  have hdescent : baseEnd_3024191 < baseStart_3024191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024198 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3024198 : Nat := 118140960795 + 3024198 * 2 ^ 59
def prefixEnd_3024198 : Nat := 4983230072969 + 3 ^ 40 * 3024198 * 2
def baseEnd_3024198 : Nat := 172540796485096005012997

theorem tailTrace_3024198 : CollatzResearch.WordTrace tailWord_3024198 prefixEnd_3024198 172540796485096005012997 := by
  unfold tailWord_3024198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446923834307956648234039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73534375131903075162326165 3446923834307956648234039)
  ·
    refine ⟨5170385751461934972351059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3446923834307956648234039 5170385751461934972351059)
    ·
      refine ⟨7755578627192902458526589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5170385751461934972351059 7755578627192902458526589)
      ·
        refine ⟨2908341985197338421947471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7755578627192902458526589 2908341985197338421947471)
        ·
          refine ⟨4362512977796007632921207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908341985197338421947471 4362512977796007632921207)
          ·
            refine ⟨6543769466694011449381811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362512977796007632921207 6543769466694011449381811)
            ·
              refine ⟨9815654200041017174072717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6543769466694011449381811 9815654200041017174072717)
              ·
                refine ⟨3680870325015381440277269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9815654200041017174072717 3680870325015381440277269)
                ·
                  refine ⟨172540796485096005012997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3680870325015381440277269 172540796485096005012997)
                  ·
                    rfl

theorem cell23_3024198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3024198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024198 prefixEnd_3024198 := by exact prefixLift 3024198
  have htrace : WordTrace (prefixWord ++ tailWord_3024198) baseStart_3024198 baseEnd_3024198 := by
    simpa [prefixWord, tailWord_3024198, baseEnd_3024198] using wordTrace_append hprefix tailTrace_3024198
  have hstable : (prefixWord ++ tailWord_3024198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024198).length < 2 ^ (prefixWord ++ tailWord_3024198).sum := by decide
  have hdescent : baseEnd_3024198 < baseStart_3024198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024227 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3024227 : Nat := 118140960795 + 3024227 * 2 ^ 59
def prefixEnd_3024227 : Nat := 4983230072969 + 3 ^ 40 * 3024227 * 2
def baseEnd_3024227 : Nat := 1552882059304844431654339

theorem tailTrace_3024227 : CollatzResearch.WordTrace tailWord_3024227 prefixEnd_3024227 1552882059304844431654339 := by
  unfold tailWord_3024227
  simp only [CollatzResearch.WordTrace]
  refine ⟨110302620414749550696294935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73535080276499700464196623 110302620414749550696294935)
  ·
    refine ⟨165453930622124326044442403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110302620414749550696294935 165453930622124326044442403)
    ·
      refine ⟨248180895933186489066663605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165453930622124326044442403 248180895933186489066663605)
      ·
        refine ⟨23266958993736233349999713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248180895933186489066663605 23266958993736233349999713)
        ·
          refine ⟨17450219245302175012499785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23266958993736233349999713 17450219245302175012499785)
          ·
            refine ⟨13087664433976631259374839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17450219245302175012499785 13087664433976631259374839)
            ·
              refine ⟨19631496650964946889062259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13087664433976631259374839 19631496650964946889062259)
              ·
                refine ⟨29447244976447420333593389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19631496650964946889062259 29447244976447420333593389)
                ·
                  refine ⟨11042716866167782625097521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29447244976447420333593389 11042716866167782625097521)
                  ·
                    refine ⟨8282037649625836968823141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11042716866167782625097521 8282037649625836968823141)
                    ·
                      refine ⟨1552882059304844431654339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8282037649625836968823141 1552882059304844431654339)
                      ·
                        rfl

theorem cell23_3024227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3024227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024227 prefixEnd_3024227 := by exact prefixLift 3024227
  have htrace : WordTrace (prefixWord ++ tailWord_3024227) baseStart_3024227 baseEnd_3024227 := by
    simpa [prefixWord, tailWord_3024227, baseEnd_3024227] using wordTrace_append hprefix tailTrace_3024227
  have hstable : (prefixWord ++ tailWord_3024227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024227).length < 2 ^ (prefixWord ++ tailWord_3024227).sum := by decide
  have hdescent : baseEnd_3024227 < baseStart_3024227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024247 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_3024247 : Nat := 118140960795 + 3024247 * 2 ^ 59
def prefixEnd_3024247 : Nat := 4983230072969 + 3 ^ 40 * 3024247 * 2
def baseEnd_3024247 : Nat := 1552892328917934353404247

theorem tailTrace_3024247 : CollatzResearch.WordTrace tailWord_3024247 prefixEnd_3024247 1552892328917934353404247 := by
  unfold tailWord_3024247
  simp only [CollatzResearch.WordTrace]
  refine ⟨110303349874677094112022995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73535566583118062741348663 110303349874677094112022995)
  ·
    refine ⟨165455024812015641168034493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110303349874677094112022995 165455024812015641168034493)
    ·
      refine ⟨62045634304505865438012935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165455024812015641168034493 62045634304505865438012935)
      ·
        refine ⟨93068451456758798157019403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62045634304505865438012935 93068451456758798157019403)
        ·
          refine ⟨139602677185138197235529105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93068451456758798157019403 139602677185138197235529105)
          ·
            refine ⟨104702007888853647926646829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139602677185138197235529105 104702007888853647926646829)
            ·
              refine ⟨39263252958320117972492561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104702007888853647926646829 39263252958320117972492561)
              ·
                refine ⟨29447439718740088479369421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39263252958320117972492561 29447439718740088479369421)
                ·
                  refine ⟨11042789894527533179763533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29447439718740088479369421 11042789894527533179763533)
                  ·
                    refine ⟨4141046210447824942411325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11042789894527533179763533 4141046210447824942411325)
                    ·
                      refine ⟨1552892328917934353404247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141046210447824942411325 1552892328917934353404247)
                      ·
                        rfl

theorem cell23_3024247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_3024247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024247 prefixEnd_3024247 := by exact prefixLift 3024247
  have htrace : WordTrace (prefixWord ++ tailWord_3024247) baseStart_3024247 baseEnd_3024247 := by
    simpa [prefixWord, tailWord_3024247, baseEnd_3024247] using wordTrace_append hprefix tailTrace_3024247
  have hstable : (prefixWord ++ tailWord_3024247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024247).length < 2 ^ (prefixWord ++ tailWord_3024247).sum := by decide
  have hdescent : baseEnd_3024247 < baseStart_3024247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024258 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3024258 : Nat := 118140960795 + 3024258 * 2 ^ 59
def prefixEnd_3024258 : Nat := 4983230072969 + 3 ^ 40 * 3024258 * 2
def baseEnd_3024258 : Nat := 517632659068377936788899

theorem tailTrace_3024258 : CollatzResearch.WordTrace tailWord_3024258 prefixEnd_3024258 517632659068377936788899 := by
  unfold tailWord_3024258
  simp only [CollatzResearch.WordTrace]
  refine ⟨27575937769409310747668357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73535834051758161993782285 27575937769409310747668357)
  ·
    refine ⟨5170488331764245765187817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27575937769409310747668357 5170488331764245765187817)
    ·
      refine ⟨3877866248823184323890863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170488331764245765187817 3877866248823184323890863)
      ·
        refine ⟨5816799373234776485836295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877866248823184323890863 5816799373234776485836295)
        ·
          refine ⟨8725199059852164728754443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816799373234776485836295 8725199059852164728754443)
          ·
            refine ⟨13087798589778247093131665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725199059852164728754443 13087798589778247093131665)
            ·
              refine ⟨9815848942333685319848749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13087798589778247093131665 9815848942333685319848749)
              ·
                refine ⟨3680943353375131994943281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9815848942333685319848749 3680943353375131994943281)
                ·
                  refine ⟨2760707515031348996207461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680943353375131994943281 2760707515031348996207461)
                  ·
                    refine ⟨517632659068377936788899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760707515031348996207461 517632659068377936788899)
                    ·
                      rfl

theorem cell23_3024258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3024258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024258 prefixEnd_3024258 := by exact prefixLift 3024258
  have htrace : WordTrace (prefixWord ++ tailWord_3024258) baseStart_3024258 baseEnd_3024258 := by
    simpa [prefixWord, tailWord_3024258, baseEnd_3024258] using wordTrace_append hprefix tailTrace_3024258
  have hstable : (prefixWord ++ tailWord_3024258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024258).length < 2 ^ (prefixWord ++ tailWord_3024258).sum := by decide
  have hdescent : baseEnd_3024258 < baseStart_3024258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024264 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3024264 : Nat := 118140960795 + 3024264 * 2 ^ 59
def prefixEnd_3024264 : Nat := 4983230072969 + 3 ^ 40 * 3024264 * 2
def baseEnd_3024264 : Nat := 1552901058089060786891669

theorem tailTrace_3024264 : CollatzResearch.WordTrace tailWord_3024264 prefixEnd_3024264 1552901058089060786891669 := by
  unfold tailWord_3024264
  simp only [CollatzResearch.WordTrace]
  refine ⟨55151984957807753007695923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73535979943743670676927897 55151984957807753007695923)
  ·
    refine ⟨82727977436711629511543885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55151984957807753007695923 82727977436711629511543885)
    ·
      refine ⟨31022991538766861066828957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82727977436711629511543885 31022991538766861066828957)
      ·
        refine ⟨11633621827037572900060859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31022991538766861066828957 11633621827037572900060859)
        ·
          refine ⟨17450432740556359350091289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633621827037572900060859 17450432740556359350091289)
          ·
            refine ⟨13087824555417269512568467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17450432740556359350091289 13087824555417269512568467)
            ·
              refine ⟨19631736833125904268852701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13087824555417269512568467 19631736833125904268852701)
              ·
                refine ⟨7361901312422214100819763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19631736833125904268852701 7361901312422214100819763)
                ·
                  refine ⟨11042851968633321151229645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7361901312422214100819763 11042851968633321151229645)
                  ·
                    refine ⟨4141069488237495431711117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11042851968633321151229645 4141069488237495431711117)
                    ·
                      refine ⟨1552901058089060786891669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141069488237495431711117 1552901058089060786891669)
                      ·
                        rfl

theorem cell23_3024264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3024264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024264 prefixEnd_3024264 := by exact prefixLift 3024264
  have htrace : WordTrace (prefixWord ++ tailWord_3024264) baseStart_3024264 baseEnd_3024264 := by
    simpa [prefixWord, tailWord_3024264, baseEnd_3024264] using wordTrace_append hprefix tailTrace_3024264
  have hstable : (prefixWord ++ tailWord_3024264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024264).length < 2 ^ (prefixWord ++ tailWord_3024264).sum := by decide
  have hdescent : baseEnd_3024264 < baseStart_3024264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024291 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 1, 3, 2]
def baseStart_3024291 : Nat := 118140960795 + 3024291 * 2 ^ 59
def prefixEnd_3024291 : Nat := 4983230072969 + 3 ^ 40 * 3024291 * 2
def baseEnd_3024291 : Nat := 1552914922066732181254045

theorem tailTrace_3024291 : CollatzResearch.WordTrace tailWord_3024291 prefixEnd_3024291 1552914922066732181254045 := by
  unfold tailWord_3024291
  simp only [CollatzResearch.WordTrace]
  refine ⟨110304954686517689626624727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73536636457678459751083151 110304954686517689626624727)
  ·
    refine ⟨165457432029776534439937091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110304954686517689626624727 165457432029776534439937091)
    ·
      refine ⟨248186148044664801659905637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165457432029776534439937091 248186148044664801659905637)
      ·
        refine ⟨46534902758374650311232307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248186148044664801659905637 46534902758374650311232307)
        ·
          refine ⟨69802354137561975466848461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46534902758374650311232307 69802354137561975466848461)
          ·
            refine ⟨26175882801585740800068173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69802354137561975466848461 26175882801585740800068173)
            ·
              refine ⟨9815956050594652800025565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26175882801585740800068173 9815956050594652800025565)
              ·
                refine ⟨3680983518972994800009587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9815956050594652800025565 3680983518972994800009587)
                ·
                  refine ⟨5521475278459492200014381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680983518972994800009587 5521475278459492200014381)
                  ·
                    refine ⟨2070553229422309575005393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5521475278459492200014381 2070553229422309575005393)
                    ·
                      refine ⟨1552914922066732181254045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070553229422309575005393 1552914922066732181254045)
                      ·
                        rfl

theorem cell23_3024291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_3024291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024291 prefixEnd_3024291 := by exact prefixLift 3024291
  have htrace : WordTrace (prefixWord ++ tailWord_3024291) baseStart_3024291 baseEnd_3024291 := by
    simpa [prefixWord, tailWord_3024291, baseEnd_3024291] using wordTrace_append hprefix tailTrace_3024291
  have hstable : (prefixWord ++ tailWord_3024291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024291).length < 2 ^ (prefixWord ++ tailWord_3024291).sum := by decide
  have hdescent : baseEnd_3024291 < baseStart_3024291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024307 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 3]
def baseStart_3024307 : Nat := 118140960795 + 3024307 * 2 ^ 59
def prefixEnd_3024307 : Nat := 4983230072969 + 3 ^ 40 * 3024307 * 2
def baseEnd_3024307 : Nat := 1552923137757204118653971

theorem tailTrace_3024307 : CollatzResearch.WordTrace tailWord_3024307 prefixEnd_3024307 1552923137757204118653971 := by
  unfold tailWord_3024307
  simp only [CollatzResearch.WordTrace]
  refine ⟨110305538254459724359207175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73537025502973149572804783 110305538254459724359207175)
  ·
    refine ⟨165458307381689586538810763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110305538254459724359207175 165458307381689586538810763)
    ·
      refine ⟨248187461072534379808216145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165458307381689586538810763 248187461072534379808216145)
      ·
        refine ⟨186140595804400784856162109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248187461072534379808216145 186140595804400784856162109)
        ·
          refine ⟨69802723426650294321060791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186140595804400784856162109 69802723426650294321060791)
          ·
            refine ⟨104704085139975441481591187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69802723426650294321060791 104704085139975441481591187)
            ·
              refine ⟨157056127709963162222386781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104704085139975441481591187 157056127709963162222386781)
              ·
                refine ⟨58896047891236185833395043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157056127709963162222386781 58896047891236185833395043)
                ·
                  refine ⟨88344071836854278750092565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58896047891236185833395043 88344071836854278750092565)
                  ·
                    refine ⟨4141128367352544316410589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88344071836854278750092565 4141128367352544316410589)
                    ·
                      refine ⟨1552923137757204118653971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141128367352544316410589 1552923137757204118653971)
                      ·
                        rfl

theorem cell23_3024307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_3024307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024307 prefixEnd_3024307 := by exact prefixLift 3024307
  have htrace : WordTrace (prefixWord ++ tailWord_3024307) baseStart_3024307 baseEnd_3024307 := by
    simpa [prefixWord, tailWord_3024307, baseEnd_3024307] using wordTrace_append hprefix tailTrace_3024307
  have hstable : (prefixWord ++ tailWord_3024307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024307).length < 2 ^ (prefixWord ++ tailWord_3024307).sum := by decide
  have hdescent : baseEnd_3024307 < baseStart_3024307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024322 : List Nat := [3, 5, 2, 1, 1, 2, 2, 7]
def baseStart_3024322 : Nat := 118140960795 + 3024322 * 2 ^ 59
def prefixEnd_3024322 : Nat := 4983230072969 + 3 ^ 40 * 3024322 * 2
def baseEnd_3024322 : Nat := 57515957035815613332089

theorem tailTrace_3024322 : CollatzResearch.WordTrace tailWord_3024322 prefixEnd_3024322 57515957035815613332089 := by
  unfold tailWord_3024322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27576521337351345480250805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73537390232936921280668813 27576521337351345480250805)
  ·
    refine ⟨2585298875376688638773513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27576521337351345480250805 2585298875376688638773513)
    ·
      refine ⟨1938974156532516479080135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2585298875376688638773513 1938974156532516479080135)
      ·
        refine ⟨2908461234798774718620203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938974156532516479080135 2908461234798774718620203)
        ·
          refine ⟨4362691852198162077930305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908461234798774718620203 4362691852198162077930305)
          ·
            refine ⟨3272018889148621558447729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4362691852198162077930305 3272018889148621558447729)
            ·
              refine ⟨2454014166861466168835797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272018889148621558447729 2454014166861466168835797)
              ·
                refine ⟨57515957035815613332089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2454014166861466168835797 57515957035815613332089)
                ·
                  rfl

theorem cell23_3024322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_3024322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024322 prefixEnd_3024322 := by exact prefixLift 3024322
  have htrace : WordTrace (prefixWord ++ tailWord_3024322) baseStart_3024322 baseEnd_3024322 := by
    simpa [prefixWord, tailWord_3024322, baseEnd_3024322] using wordTrace_append hprefix tailTrace_3024322
  have hstable : (prefixWord ++ tailWord_3024322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024322).length < 2 ^ (prefixWord ++ tailWord_3024322).sum := by decide
  have hdescent : baseEnd_3024322 < baseStart_3024322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024327 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 7]
def baseStart_3024327 : Nat := 118140960795 + 3024327 * 2 ^ 59
def prefixEnd_3024327 : Nat := 4983230072969 + 3 ^ 40 * 3024327 * 2
def baseEnd_3024327 : Nat := 172548156374477115600431

theorem tailTrace_3024327 : CollatzResearch.WordTrace tailWord_3024327 prefixEnd_3024327 172548156374477115600431 := by
  unfold tailWord_3024327
  simp only [CollatzResearch.WordTrace]
  refine ⟨110306267714387267774935235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73537511809591511849956823 110306267714387267774935235)
  ·
    refine ⟨165459401571580901662402853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110306267714387267774935235 165459401571580901662402853)
    ·
      refine ⟨31023637794671419061700535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165459401571580901662402853 31023637794671419061700535)
      ·
        refine ⟨46535456692007128592550803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31023637794671419061700535 46535456692007128592550803)
        ·
          refine ⟨69803185038010692888826205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46535456692007128592550803 69803185038010692888826205)
          ·
            refine ⟨26176194389254009833309827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69803185038010692888826205 26176194389254009833309827)
            ·
              refine ⟨39264291583881014749964741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26176194389254009833309827 39264291583881014749964741)
              ·
                refine ⟨7362054671977690265618389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39264291583881014749964741 7362054671977690265618389)
                ·
                  refine ⟨172548156374477115600431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7362054671977690265618389 172548156374477115600431)
                  ·
                    rfl

theorem cell23_3024327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 7].length) (baseStart_3024327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024327 prefixEnd_3024327 := by exact prefixLift 3024327
  have htrace : WordTrace (prefixWord ++ tailWord_3024327) baseStart_3024327 baseEnd_3024327 := by
    simpa [prefixWord, tailWord_3024327, baseEnd_3024327] using wordTrace_append hprefix tailTrace_3024327
  have hstable : (prefixWord ++ tailWord_3024327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024327).length < 2 ^ (prefixWord ++ tailWord_3024327).sum := by decide
  have hdescent : baseEnd_3024327 < baseStart_3024327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024367 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_3024367 : Nat := 118140960795 + 3024367 * 2 ^ 59
def prefixEnd_3024367 : Nat := 4983230072969 + 3 ^ 40 * 3024367 * 2
def baseEnd_3024367 : Nat := 1552953946596473883903695

theorem tailTrace_3024367 : CollatzResearch.WordTrace tailWord_3024367 prefixEnd_3024367 1552953946596473883903695 := by
  unfold tailWord_3024367
  simp only [CollatzResearch.WordTrace]
  refine ⟨110307726634242354606391355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73538484422828236404260903 110307726634242354606391355)
  ·
    refine ⟨165461589951363531909587033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110307726634242354606391355 165461589951363531909587033)
    ·
      refine ⟨124096192463522648932190275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165461589951363531909587033 124096192463522648932190275)
      ·
        refine ⟨186144288695283973398285413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124096192463522648932190275 186144288695283973398285413)
        ·
          refine ⟨34902054130365745012178515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186144288695283973398285413 34902054130365745012178515)
          ·
            refine ⟨52353081195548617518267773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34902054130365745012178515 52353081195548617518267773)
            ·
              refine ⟨19632405448330731569350415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52353081195548617518267773 19632405448330731569350415)
              ·
                refine ⟨29448608172496097354025623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19632405448330731569350415 29448608172496097354025623)
                ·
                  refine ⟨44172912258744146031038435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29448608172496097354025623 44172912258744146031038435)
                  ·
                    refine ⟨66259368388116219046557653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44172912258744146031038435 66259368388116219046557653)
                    ·
                      refine ⟨1552953946596473883903695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66259368388116219046557653 1552953946596473883903695)
                      ·
                        rfl

theorem cell23_3024367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_3024367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024367 prefixEnd_3024367 := by exact prefixLift 3024367
  have htrace : WordTrace (prefixWord ++ tailWord_3024367) baseStart_3024367 baseEnd_3024367 := by
    simpa [prefixWord, tailWord_3024367, baseEnd_3024367] using wordTrace_append hprefix tailTrace_3024367
  have hstable : (prefixWord ++ tailWord_3024367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024367).length < 2 ^ (prefixWord ++ tailWord_3024367).sum := by decide
  have hdescent : baseEnd_3024367 < baseStart_3024367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024391 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3024391 : Nat := 118140960795 + 3024391 * 2 ^ 59
def prefixEnd_3024391 : Nat := 4983230072969 + 3 ^ 40 * 3024391 * 2
def baseEnd_3024391 : Nat := 517655423377393930001195

theorem tailTrace_3024391 : CollatzResearch.WordTrace tailWord_3024391 prefixEnd_3024391 517655423377393930001195 := by
  unfold tailWord_3024391
  simp only [CollatzResearch.WordTrace]
  refine ⟨110308601986155406705265027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73539067990770271136843351 110308601986155406705265027)
  ·
    refine ⟨165462902979233110057897541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110308601986155406705265027 165462902979233110057897541)
    ·
      refine ⟨31024294308606208135855789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165462902979233110057897541 31024294308606208135855789)
      ·
        refine ⟨11634110365727328050945921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31024294308606208135855789 11634110365727328050945921)
        ·
          refine ⟨8725582774295496038209441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11634110365727328050945921 8725582774295496038209441)
          ·
            refine ⟨6544187080721622028657081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8725582774295496038209441 6544187080721622028657081)
            ·
              refine ⟨4908140310541216521492811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544187080721622028657081 4908140310541216521492811)
              ·
                refine ⟨7362210465811824782239217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908140310541216521492811 7362210465811824782239217)
                ·
                  refine ⟨5521657849358868586679413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7362210465811824782239217 5521657849358868586679413)
                  ·
                    refine ⟨517655423377393930001195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5521657849358868586679413 517655423377393930001195)
                    ·
                      rfl

theorem cell23_3024391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3024391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024391 prefixEnd_3024391 := by exact prefixLift 3024391
  have htrace : WordTrace (prefixWord ++ tailWord_3024391) baseStart_3024391 baseEnd_3024391 := by
    simpa [prefixWord, tailWord_3024391, baseEnd_3024391] using wordTrace_append hprefix tailTrace_3024391
  have hstable : (prefixWord ++ tailWord_3024391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024391).length < 2 ^ (prefixWord ++ tailWord_3024391).sum := by decide
  have hdescent : baseEnd_3024391 < baseStart_3024391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024445 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_3024445 : Nat := 118140960795 + 3024445 * 2 ^ 59
def prefixEnd_3024445 : Nat := 4983230072969 + 3 ^ 40 * 3024445 * 2
def baseEnd_3024445 : Nat := 1552993998087524578728337

theorem tailTrace_3024445 : CollatzResearch.WordTrace tailWord_3024445 prefixEnd_3024445 1552993998087524578728337 := by
  unfold tailWord_3024445
  simp only [CollatzResearch.WordTrace]
  refine ⟨110310571527959773927730789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73540381018639849285153859 110310571527959773927730789)
  ·
    refine ⟨20683232161492457611449523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110310571527959773927730789 20683232161492457611449523)
    ·
      refine ⟨31024848242238686417174285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20683232161492457611449523 31024848242238686417174285)
      ·
        refine ⟨11634318090839507406440357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31024848242238686417174285 11634318090839507406440357)
        ·
          refine ⟨2181434642032407638707567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11634318090839507406440357 2181434642032407638707567)
          ·
            refine ⟨3272151963048611458061351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181434642032407638707567 3272151963048611458061351)
            ·
              refine ⟨4908227944572917187092027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272151963048611458061351 4908227944572917187092027)
              ·
                refine ⟨7362341916859375780638041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908227944572917187092027 7362341916859375780638041)
                ·
                  refine ⟨5521756437644531835478531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7362341916859375780638041 5521756437644531835478531)
                  ·
                    refine ⟨8282634656466797753217797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521756437644531835478531 8282634656466797753217797)
                    ·
                      refine ⟨1552993998087524578728337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8282634656466797753217797 1552993998087524578728337)
                      ·
                        rfl

theorem cell23_3024445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_3024445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024445 prefixEnd_3024445 := by exact prefixLift 3024445
  have htrace : WordTrace (prefixWord ++ tailWord_3024445) baseStart_3024445 baseEnd_3024445 := by
    simpa [prefixWord, tailWord_3024445, baseEnd_3024445] using wordTrace_append hprefix tailTrace_3024445
  have hstable : (prefixWord ++ tailWord_3024445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024445).length < 2 ^ (prefixWord ++ tailWord_3024445).sum := by decide
  have hdescent : baseEnd_3024445 < baseStart_3024445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024455 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 1, 4]
def baseStart_3024455 : Nat := 118140960795 + 3024455 * 2 ^ 59
def prefixEnd_3024455 : Nat := 4983230072969 + 3 ^ 40 * 3024455 * 2
def baseEnd_3024455 : Nat := 517666377631356513201097

theorem tailTrace_3024455 : CollatzResearch.WordTrace tailWord_3024455 prefixEnd_3024455 517666377631356513201097 := by
  unfold tailWord_3024455
  simp only [CollatzResearch.WordTrace]
  refine ⟨110310936257923545635594819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73540624171949030423729879 110310936257923545635594819)
  ·
    refine ⟨165466404386885318453392229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110310936257923545635594819 165466404386885318453392229)
    ·
      refine ⟨31024950822540997210011043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165466404386885318453392229 31024950822540997210011043)
      ·
        refine ⟨46537426233811495815016565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31024950822540997210011043 46537426233811495815016565)
        ·
          refine ⟨4362883709419827732657803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46537426233811495815016565 4362883709419827732657803)
          ·
            refine ⟨6544325564129741598986705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362883709419827732657803 6544325564129741598986705)
            ·
              refine ⟨4908244173097306199240029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544325564129741598986705 4908244173097306199240029)
              ·
                refine ⟨1840591564911489824715011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4908244173097306199240029 1840591564911489824715011)
                ·
                  refine ⟨2760887347367234737072517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840591564911489824715011 2760887347367234737072517)
                  ·
                    refine ⟨517666377631356513201097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760887347367234737072517 517666377631356513201097)
                    ·
                      rfl

theorem cell23_3024455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_3024455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024455 prefixEnd_3024455 := by exact prefixLift 3024455
  have htrace : WordTrace (prefixWord ++ tailWord_3024455) baseStart_3024455 baseEnd_3024455 := by
    simpa [prefixWord, tailWord_3024455, baseEnd_3024455] using wordTrace_append hprefix tailTrace_3024455
  have hstable : (prefixWord ++ tailWord_3024455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024455).length < 2 ^ (prefixWord ++ tailWord_3024455).sum := by decide
  have hdescent : baseEnd_3024455 < baseStart_3024455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024488 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3024488 : Nat := 118140960795 + 3024488 * 2 ^ 59
def prefixEnd_3024488 : Nat := 4983230072969 + 3 ^ 40 * 3024488 * 2
def baseEnd_3024488 : Nat := 1553016077755667910490639

theorem tailTrace_3024488 : CollatzResearch.WordTrace tailWord_3024488 prefixEnd_3024488 1553016077755667910490639 := by
  unfold tailWord_3024488
  simp only [CollatzResearch.WordTrace]
  refine ⟨55156069933401996135773059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73541426577869328181030745 55156069933401996135773059)
  ·
    refine ⟨82734104900102994203659589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55156069933401996135773059 82734104900102994203659589)
    ·
      refine ⟨15512644668769311413186173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82734104900102994203659589 15512644668769311413186173)
      ·
        refine ⟨5817241750788491779944815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15512644668769311413186173 5817241750788491779944815)
        ·
          refine ⟨8725862626182737669917223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817241750788491779944815 8725862626182737669917223)
          ·
            refine ⟨13088793939274106504875835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725862626182737669917223 13088793939274106504875835)
            ·
              refine ⟨19633190908911159757313753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13088793939274106504875835 19633190908911159757313753)
              ·
                refine ⟨14724893181683369817985315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19633190908911159757313753 14724893181683369817985315)
                ·
                  refine ⟨22087339772525054726977973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14724893181683369817985315 22087339772525054726977973)
                  ·
                    refine ⟨2070688103674223880654185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22087339772525054726977973 2070688103674223880654185)
                    ·
                      refine ⟨1553016077755667910490639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070688103674223880654185 1553016077755667910490639)
                      ·
                        rfl

theorem cell23_3024488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3024488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024488 prefixEnd_3024488 := by exact prefixLift 3024488
  have htrace : WordTrace (prefixWord ++ tailWord_3024488) baseStart_3024488 baseEnd_3024488 := by
    simpa [prefixWord, tailWord_3024488, baseEnd_3024488] using wordTrace_append hprefix tailTrace_3024488
  have hstable : (prefixWord ++ tailWord_3024488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024488).length < 2 ^ (prefixWord ++ tailWord_3024488).sum := by decide
  have hdescent : baseEnd_3024488 < baseStart_3024488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024498 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3024498 : Nat := 118140960795 + 3024498 * 2 ^ 59
def prefixEnd_3024498 : Nat := 4983230072969 + 3 ^ 40 * 3024498 * 2
def baseEnd_3024498 : Nat := 517673737520737623788531

theorem tailTrace_3024498 : CollatzResearch.WordTrace tailWord_3024498 prefixEnd_3024498 517673737520737623788531 := by
  unfold tailWord_3024498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27578126149191940994852537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73541669731178509319606765 27578126149191940994852537)
  ·
    refine ⟨20683594611893955746139403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27578126149191940994852537 20683594611893955746139403)
    ·
      refine ⟨31025391917840933619209105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20683594611893955746139403 31025391917840933619209105)
      ·
        refine ⟨23269043938380700214406829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31025391917840933619209105 23269043938380700214406829)
        ·
          refine ⟨8725891476892762580402561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23269043938380700214406829 8725891476892762580402561)
          ·
            refine ⟨6544418607669571935301921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8725891476892762580402561 6544418607669571935301921)
            ·
              refine ⟨4908313955752178951476441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544418607669571935301921 4908313955752178951476441)
              ·
                refine ⟨3681235466814134213607331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4908313955752178951476441 3681235466814134213607331)
                ·
                  refine ⟨5521853200221201320410997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681235466814134213607331 5521853200221201320410997)
                  ·
                    refine ⟨517673737520737623788531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5521853200221201320410997 517673737520737623788531)
                    ·
                      rfl

theorem cell23_3024498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3024498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024498 prefixEnd_3024498 := by exact prefixLift 3024498
  have htrace : WordTrace (prefixWord ++ tailWord_3024498) baseStart_3024498 baseEnd_3024498 := by
    simpa [prefixWord, tailWord_3024498, baseEnd_3024498] using wordTrace_append hprefix tailTrace_3024498
  have hstable : (prefixWord ++ tailWord_3024498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024498).length < 2 ^ (prefixWord ++ tailWord_3024498).sum := by decide
  have hdescent : baseEnd_3024498 < baseStart_3024498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024535 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 3, 2, 2]
def baseStart_3024535 : Nat := 118140960795 + 3024535 * 2 ^ 59
def prefixEnd_3024535 : Nat := 4983230072969 + 3 ^ 40 * 3024535 * 2
def baseEnd_3024535 : Nat := 1553040211346429226602923

theorem tailTrace_3024535 : CollatzResearch.WordTrace tailWord_3024535 prefixEnd_3024535 1553040211346429226602923 := by
  unfold tailWord_3024535
  simp only [CollatzResearch.WordTrace]
  refine ⟨110313854097633719298507059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73542569398422479532338039 110313854097633719298507059)
  ·
    refine ⟨165470781146450578947760589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110313854097633719298507059 165470781146450578947760589)
    ·
      refine ⟨62051542929918967105410221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165470781146450578947760589 62051542929918967105410221)
      ·
        refine ⟨23269328598719612664528833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62051542929918967105410221 23269328598719612664528833)
        ·
          refine ⟨17451996449039709498396625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23269328598719612664528833 17451996449039709498396625)
          ·
            refine ⟨13088997336779782123797469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17451996449039709498396625 13088997336779782123797469)
            ·
              refine ⟨4908374001292418296424051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13088997336779782123797469 4908374001292418296424051)
              ·
                refine ⟨7362561001938627444636077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908374001292418296424051 7362561001938627444636077)
                ·
                  refine ⟨2760960375726985291738529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7362561001938627444636077 2760960375726985291738529)
                  ·
                    refine ⟨2070720281795238968803897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2760960375726985291738529 2070720281795238968803897)
                    ·
                      refine ⟨1553040211346429226602923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070720281795238968803897 1553040211346429226602923)
                      ·
                        rfl

theorem cell23_3024535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_3024535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024535 prefixEnd_3024535 := by exact prefixLift 3024535
  have htrace : WordTrace (prefixWord ++ tailWord_3024535) baseStart_3024535 baseEnd_3024535 := by
    simpa [prefixWord, tailWord_3024535, baseEnd_3024535] using wordTrace_append hprefix tailTrace_3024535
  have hstable : (prefixWord ++ tailWord_3024535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024535).length < 2 ^ (prefixWord ++ tailWord_3024535).sum := by decide
  have hdescent : baseEnd_3024535 < baseStart_3024535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024545 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 2, 4]
def baseStart_3024545 : Nat := 118140960795 + 3024545 * 2 ^ 59
def prefixEnd_3024545 : Nat := 4983230072969 + 3 ^ 40 * 3024545 * 2
def baseEnd_3024545 : Nat := 517681782050991395825959

theorem tailTrace_3024545 : CollatzResearch.WordTrace tailWord_3024545 prefixEnd_3024545 517681782050991395825959 := by
  unfold tailWord_3024545
  simp only [CollatzResearch.WordTrace]
  refine ⟨110314218827597491006371089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73542812551731660670914059 110314218827597491006371089)
  ·
    refine ⟨82735664120698118254778317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110314218827597491006371089 82735664120698118254778317)
    ·
      refine ⟨31025874045261794345541869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82735664120698118254778317 31025874045261794345541869)
      ·
        refine ⟨11634702766973172879578201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31025874045261794345541869 11634702766973172879578201)
        ·
          refine ⟨8726027075229879659683651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11634702766973172879578201 8726027075229879659683651)
          ·
            refine ⟨13089040612844819489525477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726027075229879659683651 13089040612844819489525477)
            ·
              refine ⟨2454195114908403654286027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13089040612844819489525477 2454195114908403654286027)
              ·
                refine ⟨3681292672362605481429041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454195114908403654286027 3681292672362605481429041)
                ·
                  refine ⟨2760969504271954111071781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681292672362605481429041 2760969504271954111071781)
                  ·
                    refine ⟨517681782050991395825959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760969504271954111071781 517681782050991395825959)
                    ·
                      rfl

theorem cell23_3024545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_3024545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024545 prefixEnd_3024545 := by exact prefixLift 3024545
  have htrace : WordTrace (prefixWord ++ tailWord_3024545) baseStart_3024545 baseEnd_3024545 := by
    simpa [prefixWord, tailWord_3024545, baseEnd_3024545] using wordTrace_append hprefix tailTrace_3024545
  have hstable : (prefixWord ++ tailWord_3024545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024545).length < 2 ^ (prefixWord ++ tailWord_3024545).sum := by decide
  have hdescent : baseEnd_3024545 < baseStart_3024545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024552 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3024552 : Nat := 118140960795 + 3024552 * 2 ^ 59
def prefixEnd_3024552 : Nat := 4983230072969 + 3 ^ 40 * 3024552 * 2
def baseEnd_3024552 : Nat := 1553048940517555660090345

theorem tailTrace_3024552 : CollatzResearch.WordTrace tailWord_3024552 prefixEnd_3024552 1553048940517555660090345 := by
  unfold tailWord_3024552
  simp only [CollatzResearch.WordTrace]
  refine ⟨55157237069286065600937955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73542982759048087467917273 55157237069286065600937955)
  ·
    refine ⟨82735855603929098401406933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55157237069286065600937955 82735855603929098401406933)
    ·
      refine ⟨1939121615717088243782975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 82735855603929098401406933 1939121615717088243782975)
      ·
        refine ⟨2908682423575632365674463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939121615717088243782975 2908682423575632365674463)
        ·
          refine ⟨4363023635363448548511695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908682423575632365674463 4363023635363448548511695)
          ·
            refine ⟨6544535453045172822767543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363023635363448548511695 6544535453045172822767543)
            ·
              refine ⟨9816803179567759234151315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544535453045172822767543 9816803179567759234151315)
              ·
                refine ⟨14725204769351638851226973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816803179567759234151315 14725204769351638851226973)
                ·
                  refine ⟨5521951788506864569210115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14725204769351638851226973 5521951788506864569210115)
                  ·
                    refine ⟨8282927682760296853815173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521951788506864569210115 8282927682760296853815173)
                    ·
                      refine ⟨1553048940517555660090345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8282927682760296853815173 1553048940517555660090345)
                      ·
                        rfl

theorem cell23_3024552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3024552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024552 prefixEnd_3024552 := by exact prefixLift 3024552
  have htrace : WordTrace (prefixWord ++ tailWord_3024552) baseStart_3024552 baseEnd_3024552 := by
    simpa [prefixWord, tailWord_3024552, baseEnd_3024552] using wordTrace_append hprefix tailTrace_3024552
  have hstable : (prefixWord ++ tailWord_3024552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024552).length < 2 ^ (prefixWord ++ tailWord_3024552).sum := by decide
  have hdescent : baseEnd_3024552 < baseStart_3024552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024586 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_3024586 : Nat := 118140960795 + 3024586 * 2 ^ 59
def prefixEnd_3024586 : Nat := 4983230072969 + 3 ^ 40 * 3024586 * 2
def baseEnd_3024586 : Nat := 1553066398859808527065189

theorem tailTrace_3024586 : CollatzResearch.WordTrace tailWord_3024586 prefixEnd_3024586 1553066398859808527065189 := by
  unfold tailWord_3024586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27578928555112238752153403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73543809480299303339075741 27578928555112238752153403)
  ·
    refine ⟨41368392832668358128230105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27578928555112238752153403 41368392832668358128230105)
    ·
      refine ⟨31026294624501268596172579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41368392832668358128230105 31026294624501268596172579)
      ·
        refine ⟨46539441936751902894258869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31026294624501268596172579 46539441936751902894258869)
        ·
          refine ⟨4363072681570490896336769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46539441936751902894258869 4363072681570490896336769)
          ·
            refine ⟨3272304511177868172252577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363072681570490896336769 3272304511177868172252577)
            ·
              refine ⟨2454228383383401129189433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272304511177868172252577 2454228383383401129189433)
              ·
                refine ⟨1840671287537550846892075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2454228383383401129189433 1840671287537550846892075)
                ·
                  refine ⟨2761006931306326270338113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840671287537550846892075 2761006931306326270338113)
                  ·
                    refine ⟨2070755198479744702753585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2761006931306326270338113 2070755198479744702753585)
                    ·
                      refine ⟨1553066398859808527065189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070755198479744702753585 1553066398859808527065189)
                      ·
                        rfl

theorem cell23_3024586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_3024586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024586 prefixEnd_3024586 := by exact prefixLift 3024586
  have htrace : WordTrace (prefixWord ++ tailWord_3024586) baseStart_3024586 baseEnd_3024586 := by
    simpa [prefixWord, tailWord_3024586, baseEnd_3024586] using wordTrace_append hprefix tailTrace_3024586
  have hstable : (prefixWord ++ tailWord_3024586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024586).length < 2 ^ (prefixWord ++ tailWord_3024586).sum := by decide
  have hdescent : baseEnd_3024586 < baseStart_3024586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024601 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_3024601 : Nat := 118140960795 + 3024601 * 2 ^ 59
def prefixEnd_3024601 : Nat := 4983230072969 + 3 ^ 40 * 3024601 * 2
def baseEnd_3024601 : Nat := 517691367023208656125873

theorem tailTrace_3024601 : CollatzResearch.WordTrace tailWord_3024601 prefixEnd_3024601 517691367023208656125873 := by
  unfold tailWord_3024601
  simp only [CollatzResearch.WordTrace]
  refine ⟨110316261315394612570409657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73544174210263075046939771 110316261315394612570409657)
  ·
    refine ⟨82737195986545959427807243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110316261315394612570409657 82737195986545959427807243)
    ·
      refine ⟨124105793979818939141710865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82737195986545959427807243 124105793979818939141710865)
      ·
        refine ⟨93079345484864204356283149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124105793979818939141710865 93079345484864204356283149)
        ·
          refine ⟨34904754556824076633606181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93079345484864204356283149 34904754556824076633606181)
          ·
            refine ⟨6544641479404514368801159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34904754556824076633606181 6544641479404514368801159)
            ·
              refine ⟨9816962219106771553201739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544641479404514368801159 9816962219106771553201739)
              ·
                refine ⟨14725443328660157329802609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816962219106771553201739 14725443328660157329802609)
                ·
                  refine ⟨11044082496495117997351957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14725443328660157329802609 11044082496495117997351957)
                  ·
                    refine ⟨517691367023208656125873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11044082496495117997351957 517691367023208656125873)
                    ·
                      rfl

theorem cell23_3024601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_3024601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024601 prefixEnd_3024601 := by exact prefixLift 3024601
  have htrace : WordTrace (prefixWord ++ tailWord_3024601) baseStart_3024601 baseEnd_3024601 := by
    simpa [prefixWord, tailWord_3024601, baseEnd_3024601] using wordTrace_append hprefix tailTrace_3024601
  have hstable : (prefixWord ++ tailWord_3024601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024601).length < 2 ^ (prefixWord ++ tailWord_3024601).sum := by decide
  have hdescent : baseEnd_3024601 < baseStart_3024601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024608 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 1, 4, 2]
def baseStart_3024608 : Nat := 118140960795 + 3024608 * 2 ^ 59
def prefixEnd_3024608 : Nat := 4983230072969 + 3 ^ 40 * 3024608 * 2
def baseEnd_3024608 : Nat := 1553077695434207440990087

theorem tailTrace_3024608 : CollatzResearch.WordTrace tailWord_3024608 prefixEnd_3024608 1553077695434207440990087 := by
  unfold tailWord_3024608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55158258313184626382957239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73544344417579501843942985 55158258313184626382957239)
  ·
    refine ⟨82737387469776939574435859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55158258313184626382957239 82737387469776939574435859)
    ·
      refine ⟨124106081204665409361653789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82737387469776939574435859 124106081204665409361653789)
      ·
        refine ⟨46539780451749528510620171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124106081204665409361653789 46539780451749528510620171)
        ·
          refine ⟨69809670677624292765930257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46539780451749528510620171 69809670677624292765930257)
          ·
            refine ⟨52357253008218219574447693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69809670677624292765930257 52357253008218219574447693)
            ·
              refine ⟨19633969878081832340417885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52357253008218219574447693 19633969878081832340417885)
              ·
                refine ⟨7362738704280687127656707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19633969878081832340417885 7362738704280687127656707)
                ·
                  refine ⟨11044108056421030691485061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362738704280687127656707 11044108056421030691485061)
                  ·
                    refine ⟨2070770260578943254653449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11044108056421030691485061 2070770260578943254653449)
                    ·
                      refine ⟨1553077695434207440990087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070770260578943254653449 1553077695434207440990087)
                      ·
                        rfl

theorem cell23_3024608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_3024608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024608 prefixEnd_3024608 := by exact prefixLift 3024608
  have htrace : WordTrace (prefixWord ++ tailWord_3024608) baseStart_3024608 baseEnd_3024608 := by
    simpa [prefixWord, tailWord_3024608, baseEnd_3024608] using wordTrace_append hprefix tailTrace_3024608
  have hstable : (prefixWord ++ tailWord_3024608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024608).length < 2 ^ (prefixWord ++ tailWord_3024608).sum := by decide
  have hdescent : baseEnd_3024608 < baseStart_3024608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024642 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3024642 : Nat := 118140960795 + 3024642 * 2 ^ 59
def prefixEnd_3024642 : Nat := 4983230072969 + 3 ^ 40 * 3024642 * 2
def baseEnd_3024642 : Nat := 1553095153776460307964931

theorem tailTrace_3024642 : CollatzResearch.WordTrace tailWord_3024642 prefixEnd_3024642 1553095153776460307964931 := by
  unfold tailWord_3024642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27579439177061519143163045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73545171138830717715101453 27579439177061519143163045)
  ·
    refine ⟨5171144845699034839343071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27579439177061519143163045 5171144845699034839343071)
    ·
      refine ⟨7756717268548552259014607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171144845699034839343071 7756717268548552259014607)
      ·
        refine ⟨11635075902822828388521911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756717268548552259014607 11635075902822828388521911)
        ·
          refine ⟨17452613854234242582782867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11635075902822828388521911 17452613854234242582782867)
          ·
            refine ⟨26178920781351363874174301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17452613854234242582782867 26178920781351363874174301)
            ·
              refine ⟨9817095293006761452815363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26178920781351363874174301 9817095293006761452815363)
              ·
                refine ⟨14725642939510142179223045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9817095293006761452815363 14725642939510142179223045)
                ·
                  refine ⟨2761058051158151658604321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14725642939510142179223045 2761058051158151658604321)
                  ·
                    refine ⟨2070793538368613743953241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2761058051158151658604321 2070793538368613743953241)
                    ·
                      refine ⟨1553095153776460307964931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070793538368613743953241 1553095153776460307964931)
                      ·
                        rfl

theorem cell23_3024642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3024642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024642 prefixEnd_3024642 := by exact prefixLift 3024642
  have htrace : WordTrace (prefixWord ++ tailWord_3024642) baseStart_3024642 baseEnd_3024642 := by
    simpa [prefixWord, tailWord_3024642, baseEnd_3024642] using wordTrace_append hprefix tailTrace_3024642
  have hstable : (prefixWord ++ tailWord_3024642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024642).length < 2 ^ (prefixWord ++ tailWord_3024642).sum := by decide
  have hdescent : baseEnd_3024642 < baseStart_3024642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024648 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 5]
def baseStart_3024648 : Nat := 118140960795 + 3024648 * 2 ^ 59
def prefixEnd_3024648 : Nat := 4983230072969 + 3 ^ 40 * 3024648 * 2
def baseEnd_3024648 : Nat := 172566470517820809387767

theorem tailTrace_3024648 : CollatzResearch.WordTrace tailWord_3024648 prefixEnd_3024648 172566470517820809387767 := by
  unfold tailWord_3024648
  simp only [CollatzResearch.WordTrace]
  refine ⟨55158987773112169798685299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73545317030816226398247065 55158987773112169798685299)
  ·
    refine ⟨82738481659668254698027949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55158987773112169798685299 82738481659668254698027949)
    ·
      refine ⟨31026930622375595511760481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82738481659668254698027949 31026930622375595511760481)
      ·
        refine ⟨23270197966781696633820361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31026930622375595511760481 23270197966781696633820361)
        ·
          refine ⟨17452648475086272475365271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23270197966781696633820361 17452648475086272475365271)
          ·
            refine ⟨26178972712629408713047907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17452648475086272475365271 26178972712629408713047907)
            ·
              refine ⟨39268459068944113069571861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26178972712629408713047907 39268459068944113069571861)
              ·
                refine ⟨1840709018856755300136181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39268459068944113069571861 1840709018856755300136181)
                ·
                  refine ⟨172566470517820809387767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1840709018856755300136181 172566470517820809387767)
                  ·
                    rfl

theorem cell23_3024648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 5].length) (baseStart_3024648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024648 prefixEnd_3024648 := by exact prefixLift 3024648
  have htrace : WordTrace (prefixWord ++ tailWord_3024648) baseStart_3024648 baseEnd_3024648 := by
    simpa [prefixWord, tailWord_3024648, baseEnd_3024648] using wordTrace_append hprefix tailTrace_3024648
  have hstable : (prefixWord ++ tailWord_3024648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024648).length < 2 ^ (prefixWord ++ tailWord_3024648).sum := by decide
  have hdescent : baseEnd_3024648 < baseStart_3024648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024653 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3024653 : Nat := 118140960795 + 3024653 * 2 ^ 59
def prefixEnd_3024653 : Nat := 4983230072969 + 3 ^ 40 * 3024653 * 2
def baseEnd_3024653 : Nat := 1553100802063659764927381

theorem tailTrace_3024653 : CollatzResearch.WordTrace tailWord_3024653 prefixEnd_3024653 1553100802063659764927381 := by
  unfold tailWord_3024653
  simp only [CollatzResearch.WordTrace]
  refine ⟨110318157911206225451302613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73545438607470816967535075 110318157911206225451302613)
  ·
    refine ⟨2585581826043895909014905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110318157911206225451302613 2585581826043895909014905)
    ·
      refine ⟨1939186369532921931761179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2585581826043895909014905 1939186369532921931761179)
      ·
        refine ⟨2908779554299382897641769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939186369532921931761179 2908779554299382897641769)
        ·
          refine ⟨2181584665724537173231327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2908779554299382897641769 2181584665724537173231327)
          ·
            refine ⟨3272376998586805759846991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181584665724537173231327 3272376998586805759846991)
            ·
              refine ⟨4908565497880208639770487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272376998586805759846991 4908565497880208639770487)
              ·
                refine ⟨7362848246820312959655731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908565497880208639770487 7362848246820312959655731)
                ·
                  refine ⟨11044272370230469439483597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362848246820312959655731 11044272370230469439483597)
                  ·
                    refine ⟨4141602138836426039806349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11044272370230469439483597 4141602138836426039806349)
                    ·
                      refine ⟨1553100802063659764927381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141602138836426039806349 1553100802063659764927381)
                      ·
                        rfl

theorem cell23_3024653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3024653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024653 prefixEnd_3024653 := by exact prefixLift 3024653
  have htrace : WordTrace (prefixWord ++ tailWord_3024653) baseStart_3024653 baseEnd_3024653 := by
    simpa [prefixWord, tailWord_3024653, baseEnd_3024653] using wordTrace_append hprefix tailTrace_3024653
  have hstable : (prefixWord ++ tailWord_3024653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024653).length < 2 ^ (prefixWord ++ tailWord_3024653).sum := by decide
  have hdescent : baseEnd_3024653 < baseStart_3024653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024661 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_3024661 : Nat := 118140960795 + 3024661 * 2 ^ 59
def prefixEnd_3024661 : Nat := 4983230072969 + 3 ^ 40 * 3024661 * 2
def baseEnd_3024661 : Nat := 517701636636298577875781

theorem tailTrace_3024661 : CollatzResearch.WordTrace tailWord_3024661 prefixEnd_3024661 517701636636298577875781 := by
  unfold tailWord_3024661
  simp only [CollatzResearch.WordTrace]
  refine ⟨110318449695177242817593837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73545633130118161878395891 110318449695177242817593837)
  ·
    refine ⟨41369418635691466056597689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110318449695177242817593837 41369418635691466056597689)
    ·
      refine ⟨31027063976768599542448267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41369418635691466056597689 31027063976768599542448267)
      ·
        refine ⟨46540595965152899313672401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31027063976768599542448267 46540595965152899313672401)
        ·
          refine ⟨34905446973864674485254301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46540595965152899313672401 34905446973864674485254301)
          ·
            refine ⟨13089542615199252931970363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34905446973864674485254301 13089542615199252931970363)
            ·
              refine ⟨19634313922798879397955545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13089542615199252931970363 19634313922798879397955545)
              ·
                refine ⟨14725735442099159548466659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19634313922798879397955545 14725735442099159548466659)
                ·
                  refine ⟨22088603163148739322699989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14725735442099159548466659 22088603163148739322699989)
                  ·
                    refine ⟨517701636636298577875781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22088603163148739322699989 517701636636298577875781)
                    ·
                      rfl

theorem cell23_3024661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_3024661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024661 prefixEnd_3024661 := by exact prefixLift 3024661
  have htrace : WordTrace (prefixWord ++ tailWord_3024661) baseStart_3024661 baseEnd_3024661 := by
    simpa [prefixWord, tailWord_3024661, baseEnd_3024661] using wordTrace_append hprefix tailTrace_3024661
  have hstable : (prefixWord ++ tailWord_3024661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024661).length < 2 ^ (prefixWord ++ tailWord_3024661).sum := by decide
  have hdescent : baseEnd_3024661 < baseStart_3024661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024698 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_3024698 : Nat := 118140960795 + 3024698 * 2 ^ 59
def prefixEnd_3024698 : Nat := 4983230072969 + 3 ^ 40 * 3024698 * 2
def baseEnd_3024698 : Nat := 1553123908693112088864673

theorem tailTrace_3024698 : CollatzResearch.WordTrace tailWord_3024698 prefixEnd_3024698 1553123908693112088864673 := by
  unfold tailWord_3024698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27579949799010799534172687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73546532797362132091127165 27579949799010799534172687)
  ·
    refine ⟨41369924698516199301259031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27579949799010799534172687 41369924698516199301259031)
    ·
      refine ⟨62054887047774298951888547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41369924698516199301259031 62054887047774298951888547)
      ·
        refine ⟨93082330571661448427832821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62054887047774298951888547 93082330571661448427832821)
        ·
          refine ⟨8726468491093260790109327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93082330571661448427832821 8726468491093260790109327)
          ·
            refine ⟨13089702736639891185163991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726468491093260790109327 13089702736639891185163991)
            ·
              refine ⟨19634554104959836777745987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13089702736639891185163991 19634554104959836777745987)
              ·
                refine ⟨29451831157439755166618981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19634554104959836777745987 29451831157439755166618981)
                ·
                  refine ⟨5522218342019954093741059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29451831157439755166618981 5522218342019954093741059)
                  ·
                    refine ⟨8283327513029931140611589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5522218342019954093741059 8283327513029931140611589)
                    ·
                      refine ⟨1553123908693112088864673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8283327513029931140611589 1553123908693112088864673)
                      ·
                        rfl

theorem cell23_3024698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_3024698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024698 prefixEnd_3024698 := by exact prefixLift 3024698
  have htrace : WordTrace (prefixWord ++ tailWord_3024698) baseStart_3024698 baseEnd_3024698 := by
    simpa [prefixWord, tailWord_3024698, baseEnd_3024698] using wordTrace_append hprefix tailTrace_3024698
  have hstable : (prefixWord ++ tailWord_3024698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024698).length < 2 ^ (prefixWord ++ tailWord_3024698).sum := by decide
  have hdescent : baseEnd_3024698 < baseStart_3024698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024711 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_3024711 : Nat := 118140960795 + 3024711 * 2 ^ 59
def prefixEnd_3024711 : Nat := 4983230072969 + 3 ^ 40 * 3024711 * 2
def baseEnd_3024711 : Nat := 1553130583941620538002113

theorem tailTrace_3024711 : CollatzResearch.WordTrace tailWord_3024711 prefixEnd_3024711 1553130583941620538002113 := by
  unfold tailWord_3024711
  simp only [CollatzResearch.WordTrace]
  refine ⟨110320273344996101356913987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73546848896664067571275991 110320273344996101356913987)
  ·
    refine ⟨165480410017494152035370981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110320273344996101356913987 165480410017494152035370981)
    ·
      refine ⟨31027576878280153506632059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165480410017494152035370981 31027576878280153506632059)
      ·
        refine ⟨46541365317420230259948089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31027576878280153506632059 46541365317420230259948089)
        ·
          refine ⟨34906023988065172694961067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46541365317420230259948089 34906023988065172694961067)
          ·
            refine ⟨52359035982097759042441601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34906023988065172694961067 52359035982097759042441601)
            ·
              refine ⟨39269276986573319281831201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52359035982097759042441601 39269276986573319281831201)
              ·
                refine ⟨29451957739929989461373401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39269276986573319281831201 29451957739929989461373401)
                ·
                  refine ⟨22088968304947492096030051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29451957739929989461373401 22088968304947492096030051)
                  ·
                    refine ⟨33133452457421238144045077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22088968304947492096030051 33133452457421238144045077)
                    ·
                      refine ⟨1553130583941620538002113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33133452457421238144045077 1553130583941620538002113)
                      ·
                        rfl

theorem cell23_3024711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_3024711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024711 prefixEnd_3024711 := by exact prefixLift 3024711
  have htrace : WordTrace (prefixWord ++ tailWord_3024711) baseStart_3024711 baseEnd_3024711 := by
    simpa [prefixWord, tailWord_3024711, baseEnd_3024711] using wordTrace_append hprefix tailTrace_3024711
  have hstable : (prefixWord ++ tailWord_3024711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024711).length < 2 ^ (prefixWord ++ tailWord_3024711).sum := by decide
  have hdescent : baseEnd_3024711 < baseStart_3024711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024732 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3024732 : Nat := 118140960795 + 3024732 * 2 ^ 59
def prefixEnd_3024732 : Nat := 4983230072969 + 3 ^ 40 * 3024732 * 2
def baseEnd_3024732 : Nat := 1553141367035364955839517

theorem tailTrace_3024732 : CollatzResearch.WordTrace tailWord_3024732 prefixEnd_3024732 1553141367035364955839517 := by
  unfold tailWord_3024732
  simp only [CollatzResearch.WordTrace]
  refine ⟨55160519638960010971714225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73547359518613347962285633 55160519638960010971714225)
  ·
    refine ⟨41370389729220008228785669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55160519638960010971714225 41370389729220008228785669)
    ·
      refine ⟨7756948074228751542897313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41370389729220008228785669 7756948074228751542897313)
      ·
        refine ⟨5817711055671563657172985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756948074228751542897313 5817711055671563657172985)
        ·
          refine ⟨4363283291753672742879739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817711055671563657172985 4363283291753672742879739)
          ·
            refine ⟨6544924937630509114319609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363283291753672742879739 6544924937630509114319609)
            ·
              refine ⟨4908693703222881835739707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544924937630509114319609 4908693703222881835739707)
              ·
                refine ⟨7363040554834322753609561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908693703222881835739707 7363040554834322753609561)
                ·
                  refine ⟨5522280416125742065207171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7363040554834322753609561 5522280416125742065207171)
                  ·
                    refine ⟨8283420624188613097810757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5522280416125742065207171 8283420624188613097810757)
                    ·
                      refine ⟨1553141367035364955839517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8283420624188613097810757 1553141367035364955839517)
                      ·
                        rfl

theorem cell23_3024732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3024732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024732 prefixEnd_3024732 := by exact prefixLift 3024732
  have htrace : WordTrace (prefixWord ++ tailWord_3024732) baseStart_3024732 baseEnd_3024732 := by
    simpa [prefixWord, tailWord_3024732, baseEnd_3024732] using wordTrace_append hprefix tailTrace_3024732
  have hstable : (prefixWord ++ tailWord_3024732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024732).length < 2 ^ (prefixWord ++ tailWord_3024732).sum := by decide
  have hdescent : baseEnd_3024732 < baseStart_3024732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024735 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_3024735 : Nat := 118140960795 + 3024735 * 2 ^ 59
def prefixEnd_3024735 : Nat := 4983230072969 + 3 ^ 40 * 3024735 * 2
def baseEnd_3024735 : Nat := 1553142907477328444102003

theorem tailTrace_3024735 : CollatzResearch.WordTrace tailWord_3024735 prefixEnd_3024735 1553142907477328444102003 := by
  unfold tailWord_3024735
  simp only [CollatzResearch.WordTrace]
  refine ⟨110321148696909153455787659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73547432464606102303858439 110321148696909153455787659)
  ·
    refine ⟨165481723045363730183681489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110321148696909153455787659 165481723045363730183681489)
    ·
      refine ⟨124111292284022797637761117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165481723045363730183681489 124111292284022797637761117)
      ·
        refine ⟨46541734606508549114160419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124111292284022797637761117 46541734606508549114160419)
        ·
          refine ⟨69812601909762823671240629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46541734606508549114160419 69812601909762823671240629)
          ·
            refine ⟨6544931429040264719178809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69812601909762823671240629 6544931429040264719178809)
            ·
              refine ⟨4908698571780198539384107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544931429040264719178809 4908698571780198539384107)
              ·
                refine ⟨7363047857670297809076161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908698571780198539384107 7363047857670297809076161)
                ·
                  refine ⟨5522285893252723356807121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7363047857670297809076161 5522285893252723356807121)
                  ·
                    refine ⟨4141714419939542517605341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5522285893252723356807121 4141714419939542517605341)
                    ·
                      refine ⟨1553142907477328444102003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141714419939542517605341 1553142907477328444102003)
                      ·
                        rfl

theorem cell23_3024735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_3024735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024735 prefixEnd_3024735 := by exact prefixLift 3024735
  have htrace : WordTrace (prefixWord ++ tailWord_3024735) baseStart_3024735 baseEnd_3024735 := by
    simpa [prefixWord, tailWord_3024735, baseEnd_3024735] using wordTrace_append hprefix tailTrace_3024735
  have hstable : (prefixWord ++ tailWord_3024735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024735).length < 2 ^ (prefixWord ++ tailWord_3024735).sum := by decide
  have hdescent : baseEnd_3024735 < baseStart_3024735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024741 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3024741 : Nat := 118140960795 + 3024741 * 2 ^ 59
def prefixEnd_3024741 : Nat := 4983230072969 + 3 ^ 40 * 3024741 * 2
def baseEnd_3024741 : Nat := 1553145988361255420626975

theorem tailTrace_3024741 : CollatzResearch.WordTrace tailWord_3024741 prefixEnd_3024741 1553145988361255420626975 := by
  unfold tailWord_3024741
  simp only [CollatzResearch.WordTrace]
  refine ⟨110321367534887416480506077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73547578356591610987004051 110321367534887416480506077)
  ·
    refine ⟨41370512825582781180189779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110321367534887416480506077 41370512825582781180189779)
    ·
      refine ⟨62055769238374171770284669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41370512825582781180189779 62055769238374171770284669)
      ·
        refine ⟨23270913464390314413856751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62055769238374171770284669 23270913464390314413856751)
        ·
          refine ⟨34906370196585471620785127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23270913464390314413856751 34906370196585471620785127)
          ·
            refine ⟨52359555294878207431177691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34906370196585471620785127 52359555294878207431177691)
            ·
              refine ⟨78539332942317311146766537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52359555294878207431177691 78539332942317311146766537)
              ·
                refine ⟨58904499706737983360074903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78539332942317311146766537 58904499706737983360074903)
                ·
                  refine ⟨88356749560106975040112355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58904499706737983360074903 88356749560106975040112355)
                  ·
                    refine ⟨132535124340160462560168533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88356749560106975040112355 132535124340160462560168533)
                    ·
                      refine ⟨1553145988361255420626975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 132535124340160462560168533 1553145988361255420626975)
                      ·
                        rfl

theorem cell23_3024741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3024741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024741 prefixEnd_3024741 := by exact prefixLift 3024741
  have htrace : WordTrace (prefixWord ++ tailWord_3024741) baseStart_3024741 baseEnd_3024741 := by
    simpa [prefixWord, tailWord_3024741, baseEnd_3024741] using wordTrace_append hprefix tailTrace_3024741
  have hstable : (prefixWord ++ tailWord_3024741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024741).length < 2 ^ (prefixWord ++ tailWord_3024741).sum := by decide
  have hdescent : baseEnd_3024741 < baseStart_3024741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024765 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_3024765 : Nat := 118140960795 + 3024765 * 2 ^ 59
def prefixEnd_3024765 : Nat := 4983230072969 + 3 ^ 40 * 3024765 * 2
def baseEnd_3024765 : Nat := 1553158311896963326726865

theorem tailTrace_3024765 : CollatzResearch.WordTrace tailWord_3024765 prefixEnd_3024765 1553158311896963326726865 := by
  unfold tailWord_3024765
  simp only [CollatzResearch.WordTrace]
  refine ⟨110322242886800468579379749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73548161924533645719586499 110322242886800468579379749)
  ·
    refine ⟨20685420541275087858633703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110322242886800468579379749 20685420541275087858633703)
    ·
      refine ⟨31028130811912631787950555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20685420541275087858633703 31028130811912631787950555)
      ·
        refine ⟨46542196217868947681925833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31028130811912631787950555 46542196217868947681925833)
        ·
          refine ⟨34906647163401710761444375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46542196217868947681925833 34906647163401710761444375)
          ·
            refine ⟨52359970745102566142166563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34906647163401710761444375 52359970745102566142166563)
            ·
              refine ⟨78539956117653849213249845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52359970745102566142166563 78539956117653849213249845)
              ·
                refine ⟨7363120886030048363742173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78539956117653849213249845 7363120886030048363742173)
                ·
                  refine ⟨2761170332261268136403315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7363120886030048363742173 2761170332261268136403315)
                  ·
                    refine ⟨4141755498391902204604973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761170332261268136403315 4141755498391902204604973)
                    ·
                      refine ⟨1553158311896963326726865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141755498391902204604973 1553158311896963326726865)
                      ·
                        rfl

theorem cell23_3024765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_3024765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024765 prefixEnd_3024765 := by exact prefixLift 3024765
  have htrace : WordTrace (prefixWord ++ tailWord_3024765) baseStart_3024765 baseEnd_3024765 := by
    simpa [prefixWord, tailWord_3024765, baseEnd_3024765] using wordTrace_append hprefix tailTrace_3024765
  have hstable : (prefixWord ++ tailWord_3024765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024765).length < 2 ^ (prefixWord ++ tailWord_3024765).sum := by decide
  have hdescent : baseEnd_3024765 < baseStart_3024765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024802 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3024802 : Nat := 118140960795 + 3024802 * 2 ^ 59
def prefixEnd_3024802 : Nat := 4983230072969 + 3 ^ 40 * 3024802 * 2
def baseEnd_3024802 : Nat := 517725770227059893988065

theorem tailTrace_3024802 : CollatzResearch.WordTrace tailWord_3024802 prefixEnd_3024802 517725770227059893988065 := by
  unfold tailWord_3024802
  simp only [CollatzResearch.WordTrace]
  refine ⟨27580898096916605974619165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73549061591777615932317773 27580898096916605974619165)
  ·
    refine ⟨10342836786343727240482187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27580898096916605974619165 10342836786343727240482187)
    ·
      refine ⟨15514255179515590860723281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10342836786343727240482187 15514255179515590860723281)
      ·
        refine ⟨11635691384636693145542461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15514255179515590860723281 11635691384636693145542461)
        ·
          refine ⟨4363384269238759929578423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11635691384636693145542461 4363384269238759929578423)
          ·
            refine ⟨6545076403858139894367635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363384269238759929578423 6545076403858139894367635)
            ·
              refine ⟨9817614605787209841551453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545076403858139894367635 9817614605787209841551453)
              ·
                refine ⟨3681605477170203690581795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9817614605787209841551453 3681605477170203690581795)
                ·
                  refine ⟨5522408215755305535872693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681605477170203690581795 5522408215755305535872693)
                  ·
                    refine ⟨517725770227059893988065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5522408215755305535872693 517725770227059893988065)
                    ·
                      rfl

theorem cell23_3024802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3024802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024802 prefixEnd_3024802 := by exact prefixLift 3024802
  have htrace : WordTrace (prefixWord ++ tailWord_3024802) baseStart_3024802 baseEnd_3024802 := by
    simpa [prefixWord, tailWord_3024802, baseEnd_3024802] using wordTrace_append hprefix tailTrace_3024802
  have hstable : (prefixWord ++ tailWord_3024802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024802).length < 2 ^ (prefixWord ++ tailWord_3024802).sum := by decide
  have hdescent : baseEnd_3024802 < baseStart_3024802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024818 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3024818 : Nat := 118140960795 + 3024818 * 2 ^ 59
def prefixEnd_3024818 : Nat := 4983230072969 + 3 ^ 40 * 3024818 * 2
def baseEnd_3024818 : Nat := 1553185526371651619364121

theorem tailTrace_3024818 : CollatzResearch.WordTrace tailWord_3024818 prefixEnd_3024818 1553185526371651619364121 := by
  unfold tailWord_3024818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27581043988902114657764777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73549450637072305754039405 27581043988902114657764777)
  ·
    refine ⟨20685782991676585993323583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27581043988902114657764777 20685782991676585993323583)
    ·
      refine ⟨31028674487514878989985375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20685782991676585993323583 31028674487514878989985375)
      ·
        refine ⟨46543011731272318484978063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31028674487514878989985375 46543011731272318484978063)
        ·
          refine ⟨69814517596908477727467095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46543011731272318484978063 69814517596908477727467095)
          ·
            refine ⟨104721776395362716591200643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69814517596908477727467095 104721776395362716591200643)
            ·
              refine ⟨157082664593044074886800965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104721776395362716591200643 157082664593044074886800965)
              ·
                refine ⟨29452999611195764041275181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157082664593044074886800965 29452999611195764041275181)
                ·
                  refine ⟨11044874854198411515478193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29452999611195764041275181 11044874854198411515478193)
                  ·
                    refine ⟨8283656140648808636608645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11044874854198411515478193 8283656140648808636608645)
                    ·
                      refine ⟨1553185526371651619364121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8283656140648808636608645 1553185526371651619364121)
                      ·
                        rfl

theorem cell23_3024818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3024818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024818 prefixEnd_3024818 := by exact prefixLift 3024818
  have htrace : WordTrace (prefixWord ++ tailWord_3024818) baseStart_3024818 baseEnd_3024818 := by
    simpa [prefixWord, tailWord_3024818, baseEnd_3024818] using wordTrace_append hprefix tailTrace_3024818
  have hstable : (prefixWord ++ tailWord_3024818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024818).length < 2 ^ (prefixWord ++ tailWord_3024818).sum := by decide
  have hdescent : baseEnd_3024818 < baseStart_3024818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024832 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 2, 4]
def baseStart_3024832 : Nat := 118140960795 + 3024832 * 2 ^ 59
def prefixEnd_3024832 : Nat := 4983230072969 + 3 ^ 40 * 3024832 * 2
def baseEnd_3024832 : Nat := 517730905033604854863019

theorem tailTrace_3024832 : CollatzResearch.WordTrace tailWord_3024832 prefixEnd_3024832 517730905033604854863019 := by
  unfold tailWord_3024832
  simp only [CollatzResearch.WordTrace]
  refine ⟨55162343288778869511034375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73549791051705159348045833 55162343288778869511034375)
  ·
    refine ⟨82743514933168304266551563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55162343288778869511034375 82743514933168304266551563)
    ·
      refine ⟨124115272399752456399827345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82743514933168304266551563 124115272399752456399827345)
      ·
        refine ⟨93086454299814342299870509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124115272399752456399827345 93086454299814342299870509)
        ·
          refine ⟨34907420362430378362451441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93086454299814342299870509 34907420362430378362451441)
          ·
            refine ⟨26180565271822783771838581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34907420362430378362451441 26180565271822783771838581)
            ·
              refine ⟨2454427994233385978609867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26180565271822783771838581 2454427994233385978609867)
              ·
                refine ⟨3681641991350078967914801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454427994233385978609867 3681641991350078967914801)
                ·
                  refine ⟨2761231493512559225936101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681641991350078967914801 2761231493512559225936101)
                  ·
                    refine ⟨517730905033604854863019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761231493512559225936101 517730905033604854863019)
                    ·
                      rfl

theorem cell23_3024832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 4].length) (baseStart_3024832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024832 prefixEnd_3024832 := by exact prefixLift 3024832
  have htrace : WordTrace (prefixWord ++ tailWord_3024832) baseStart_3024832 baseEnd_3024832 := by
    simpa [prefixWord, tailWord_3024832, baseEnd_3024832] using wordTrace_append hprefix tailTrace_3024832
  have hstable : (prefixWord ++ tailWord_3024832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024832).length < 2 ^ (prefixWord ++ tailWord_3024832).sum := by decide
  have hdescent : baseEnd_3024832 < baseStart_3024832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024855 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3024855 : Nat := 118140960795 + 3024855 * 2 ^ 59
def prefixEnd_3024855 : Nat := 4983230072969 + 3 ^ 40 * 3024855 * 2
def baseEnd_3024855 : Nat := 1553204525155867974601451

theorem tailTrace_3024855 : CollatzResearch.WordTrace tailWord_3024855 prefixEnd_3024855 1553204525155867974601451 := by
  unfold tailWord_3024855
  simp only [CollatzResearch.WordTrace]
  refine ⟨110325525456474413950156019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73550350304316275966770679 110325525456474413950156019)
  ·
    refine ⟨165488288184711620925234029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110325525456474413950156019 165488288184711620925234029)
    ·
      refine ⟨62058108069266857846962761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165488288184711620925234029 62058108069266857846962761)
      ·
        refine ⟨46543581051950143385222071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62058108069266857846962761 46543581051950143385222071)
        ·
          refine ⟨69815371577925215077833107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46543581051950143385222071 69815371577925215077833107)
          ·
            refine ⟨104723057366887822616749661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69815371577925215077833107 104723057366887822616749661)
            ·
              refine ⟨39271146512582933481281123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104723057366887822616749661 39271146512582933481281123)
              ·
                refine ⟨58906719768874400221921685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39271146512582933481281123 58906719768874400221921685)
                ·
                  refine ⟨2761252489165987510402579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58906719768874400221921685 2761252489165987510402579)
                  ·
                    refine ⟨4141878733748981265603869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761252489165987510402579 4141878733748981265603869)
                    ·
                      refine ⟨1553204525155867974601451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141878733748981265603869 1553204525155867974601451)
                      ·
                        rfl

theorem cell23_3024855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3024855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024855 prefixEnd_3024855 := by exact prefixLift 3024855
  have htrace : WordTrace (prefixWord ++ tailWord_3024855) baseStart_3024855 baseEnd_3024855 := by
    simpa [prefixWord, tailWord_3024855, baseEnd_3024855] using wordTrace_append hprefix tailTrace_3024855
  have hstable : (prefixWord ++ tailWord_3024855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024855).length < 2 ^ (prefixWord ++ tailWord_3024855).sum := by decide
  have hdescent : baseEnd_3024855 < baseStart_3024855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024868 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_3024868 : Nat := 118140960795 + 3024868 * 2 ^ 59
def prefixEnd_3024868 : Nat := 4983230072969 + 3 ^ 40 * 3024868 * 2
def baseEnd_3024868 : Nat := 1553211200404376423738891

theorem tailTrace_3024868 : CollatzResearch.WordTrace tailWord_3024868 prefixEnd_3024868 1553211200404376423738891 := by
  unfold tailWord_3024868
  simp only [CollatzResearch.WordTrace]
  refine ⟨55162999802713658585189629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73550666403618211446919505 55162999802713658585189629)
  ·
    refine ⟨20686124926017621969446111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55162999802713658585189629 20686124926017621969446111)
    ·
      refine ⟨31029187389026432954169167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20686124926017621969446111 31029187389026432954169167)
      ·
        refine ⟨46543781083539649431253751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31029187389026432954169167 46543781083539649431253751)
        ·
          refine ⟨69815671625309474146880627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46543781083539649431253751 69815671625309474146880627)
          ·
            refine ⟨104723507437964211220320941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69815671625309474146880627 104723507437964211220320941)
            ·
              refine ⟨39271315289236579207620353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104723507437964211220320941 39271315289236579207620353)
              ·
                refine ⟨29453486466927434405715265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39271315289236579207620353 29453486466927434405715265)
                ·
                  refine ⟨22090114850195575804286449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29453486466927434405715265 22090114850195575804286449)
                  ·
                    refine ⟨16567586137646681853214837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22090114850195575804286449 16567586137646681853214837)
                    ·
                      refine ⟨1553211200404376423738891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16567586137646681853214837 1553211200404376423738891)
                      ·
                        rfl

theorem cell23_3024868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_3024868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024868 prefixEnd_3024868 := by exact prefixLift 3024868
  have htrace : WordTrace (prefixWord ++ tailWord_3024868) baseStart_3024868 baseEnd_3024868 := by
    simpa [prefixWord, tailWord_3024868, baseEnd_3024868] using wordTrace_append hprefix tailTrace_3024868
  have hstable : (prefixWord ++ tailWord_3024868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024868).length < 2 ^ (prefixWord ++ tailWord_3024868).sum := by decide
  have hdescent : baseEnd_3024868 < baseStart_3024868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024872 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3024872 : Nat := 118140960795 + 3024872 * 2 ^ 59
def prefixEnd_3024872 : Nat := 4983230072969 + 3 ^ 40 * 3024872 * 2
def baseEnd_3024872 : Nat := 1553213254326994408088873

theorem tailTrace_3024872 : CollatzResearch.WordTrace tailWord_3024872 prefixEnd_3024872 1553213254326994408088873 := by
  unfold tailWord_3024872
  simp only [CollatzResearch.WordTrace]
  refine ⟨55163072748706412926762435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73550763664941883902349913 55163072748706412926762435)
  ·
    refine ⟨82744609123059619390143653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55163072748706412926762435 82744609123059619390143653)
    ·
      refine ⟨15514614210573678635651935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82744609123059619390143653 15514614210573678635651935)
      ·
        refine ⟨23271921315860517953477903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514614210573678635651935 23271921315860517953477903)
        ·
          refine ⟨34907881973790776930216855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23271921315860517953477903 34907881973790776930216855)
          ·
            refine ⟨52361822960686165395325283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34907881973790776930216855 52361822960686165395325283)
            ·
              refine ⟨78542734441029248092987925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52361822960686165395325283 78542734441029248092987925)
              ·
                refine ⟨3681690676923246004358809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78542734441029248092987925 3681690676923246004358809)
                ·
                  refine ⟨2761268007692434503269107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681690676923246004358809 2761268007692434503269107)
                  ·
                    refine ⟨4141902011538651754903661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761268007692434503269107 4141902011538651754903661)
                    ·
                      refine ⟨1553213254326994408088873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141902011538651754903661 1553213254326994408088873)
                      ·
                        rfl

theorem cell23_3024872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3024872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024872 prefixEnd_3024872 := by exact prefixLift 3024872
  have htrace : WordTrace (prefixWord ++ tailWord_3024872) baseStart_3024872 baseEnd_3024872 := by
    simpa [prefixWord, tailWord_3024872, baseEnd_3024872] using wordTrace_append hprefix tailTrace_3024872
  have hstable : (prefixWord ++ tailWord_3024872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024872).length < 2 ^ (prefixWord ++ tailWord_3024872).sum := by decide
  have hdescent : baseEnd_3024872 < baseStart_3024872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024888 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_3024888 : Nat := 118140960795 + 3024888 * 2 ^ 59
def prefixEnd_3024888 : Nat := 4983230072969 + 3 ^ 40 * 3024888 * 2
def baseEnd_3024888 : Nat := 517740490005822115162933

theorem tailTrace_3024888 : CollatzResearch.WordTrace tailWord_3024888 prefixEnd_3024888 517740490005822115162933 := by
  unfold tailWord_3024888
  simp only [CollatzResearch.WordTrace]
  refine ⟨55163364532677430293053659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73551152710236573724071545 55163364532677430293053659)
  ·
    refine ⟨82745046799016145439580489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55163364532677430293053659 82745046799016145439580489)
    ·
      refine ⟨62058785099262109079685367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82745046799016145439580489 62058785099262109079685367)
      ·
        refine ⟨93088177648893163619528051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62058785099262109079685367 93088177648893163619528051)
        ·
          refine ⟨139632266473339745429292077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93088177648893163619528051 139632266473339745429292077)
          ·
            refine ⟨52362099927502404535984529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139632266473339745429292077 52362099927502404535984529)
            ·
              refine ⟨39271574945626803401988397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52362099927502404535984529 39271574945626803401988397)
              ·
                refine ⟨14726840604610051275745649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39271574945626803401988397 14726840604610051275745649)
                ·
                  refine ⟨11045130453457538456809237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14726840604610051275745649 11045130453457538456809237)
                  ·
                    refine ⟨517740490005822115162933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11045130453457538456809237 517740490005822115162933)
                    ·
                      rfl

theorem cell23_3024888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_3024888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024888 prefixEnd_3024888 := by exact prefixLift 3024888
  have htrace : WordTrace (prefixWord ++ tailWord_3024888) baseStart_3024888 baseEnd_3024888 := by
    simpa [prefixWord, tailWord_3024888, baseEnd_3024888] using wordTrace_append hprefix tailTrace_3024888
  have hstable : (prefixWord ++ tailWord_3024888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024888).length < 2 ^ (prefixWord ++ tailWord_3024888).sum := by decide
  have hdescent : baseEnd_3024888 < baseStart_3024888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024889 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 2, 1, 3]
def baseStart_3024889 : Nat := 118140960795 + 3024889 * 2 ^ 59
def prefixEnd_3024889 : Nat := 4983230072969 + 3 ^ 40 * 3024889 * 2
def baseEnd_3024889 : Nat := 1553221983498120841576295

theorem tailTrace_3024889 : CollatzResearch.WordTrace tailWord_3024889 prefixEnd_3024889 1553221983498120841576295 := by
  unfold tailWord_3024889
  simp only [CollatzResearch.WordTrace]
  refine ⟨110326765538351237756893721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73551177025567491837929147 110326765538351237756893721)
  ·
    refine ⟨82745074153763428317670291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110326765538351237756893721 82745074153763428317670291)
    ·
      refine ⟨124117611230645142476505437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82745074153763428317670291 124117611230645142476505437)
      ·
        refine ⟨46544104211491928428689539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124117611230645142476505437 46544104211491928428689539)
        ·
          refine ⟨69816156317237892643034309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46544104211491928428689539 69816156317237892643034309)
          ·
            refine ⟨13090529309482104870568933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69816156317237892643034309 13090529309482104870568933)
            ·
              refine ⟨2454474245527894663231675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13090529309482104870568933 2454474245527894663231675)
              ·
                refine ⟨3681711368291841994847513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454474245527894663231675 3681711368291841994847513)
                ·
                  refine ⟨2761283526218881496135635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681711368291841994847513 2761283526218881496135635)
                  ·
                    refine ⟨4141925289328322244203453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761283526218881496135635 4141925289328322244203453)
                    ·
                      refine ⟨1553221983498120841576295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4141925289328322244203453 1553221983498120841576295)
                      ·
                        rfl

theorem cell23_3024889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_3024889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024889 prefixEnd_3024889 := by exact prefixLift 3024889
  have htrace : WordTrace (prefixWord ++ tailWord_3024889) baseStart_3024889 baseEnd_3024889 := by
    simpa [prefixWord, tailWord_3024889, baseEnd_3024889] using wordTrace_append hprefix tailTrace_3024889
  have hstable : (prefixWord ++ tailWord_3024889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024889).length < 2 ^ (prefixWord ++ tailWord_3024889).sum := by decide
  have hdescent : baseEnd_3024889 < baseStart_3024889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024895 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 5, 4, 2]
def baseStart_3024895 : Nat := 118140960795 + 3024895 * 2 ^ 59
def prefixEnd_3024895 : Nat := 4983230072969 + 3 ^ 40 * 3024895 * 2
def baseEnd_3024895 : Nat := 1553225064382047818101267

theorem tailTrace_3024895 : CollatzResearch.WordTrace tailWord_3024895 prefixEnd_3024895 1553225064382047818101267 := by
  unfold tailWord_3024895
  simp only [CollatzResearch.WordTrace]
  refine ⟨110326984376329500781612139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73551322917553000521074759 110326984376329500781612139)
  ·
    refine ⟨165490476564494251172418209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110326984376329500781612139 165490476564494251172418209)
    ·
      refine ⟨124117857423370688379313657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165490476564494251172418209 124117857423370688379313657)
      ·
        refine ⟨93088393067528016284485243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124117857423370688379313657 93088393067528016284485243)
        ·
          refine ⟨139632589601292024426727865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93088393067528016284485243 139632589601292024426727865)
          ·
            refine ⟨104724442200969018320045899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139632589601292024426727865 104724442200969018320045899)
            ·
              refine ⟨157086663301453527480068849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104724442200969018320045899 157086663301453527480068849)
              ·
                refine ⟨117814997476090145610051637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157086663301453527480068849 117814997476090145610051637)
                ·
                  refine ⟨11045156013383451150942341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117814997476090145610051637 11045156013383451150942341)
                  ·
                    refine ⟨2070966752509397090801689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11045156013383451150942341 2070966752509397090801689)
                    ·
                      refine ⟨1553225064382047818101267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2070966752509397090801689 1553225064382047818101267)
                      ·
                        rfl

theorem cell23_3024895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_3024895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024895 prefixEnd_3024895 := by exact prefixLift 3024895
  have htrace : WordTrace (prefixWord ++ tailWord_3024895) baseStart_3024895 baseEnd_3024895 := by
    simpa [prefixWord, tailWord_3024895, baseEnd_3024895] using wordTrace_append hprefix tailTrace_3024895
  have hstable : (prefixWord ++ tailWord_3024895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024895).length < 2 ^ (prefixWord ++ tailWord_3024895).sum := by decide
  have hdescent : baseEnd_3024895 < baseStart_3024895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024942 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3024942 : Nat := 118140960795 + 3024942 * 2 ^ 59
def prefixEnd_3024942 : Nat := 4983230072969 + 3 ^ 40 * 3024942 * 2
def baseEnd_3024942 : Nat := 1553249197972809134213551

theorem tailTrace_3024942 : CollatzResearch.WordTrace tailWord_3024942 prefixEnd_3024942 1553249197972809134213551 := by
  unfold tailWord_3024942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13791087325894903476071635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73552465738106151872382053 13791087325894903476071635)
  ·
    refine ⟨20686630988842355214107453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13791087325894903476071635 20686630988842355214107453)
    ·
      refine ⟨7757486620815883205290295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20686630988842355214107453 7757486620815883205290295)
      ·
        refine ⟨11636229931223824807935443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7757486620815883205290295 11636229931223824807935443)
        ·
          refine ⟨17454344896835737211903165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11636229931223824807935443 17454344896835737211903165)
          ·
            refine ⟨6545379336313401454463687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17454344896835737211903165 6545379336313401454463687)
            ·
              refine ⟨9818069004470102181695531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545379336313401454463687 9818069004470102181695531)
              ·
                refine ⟨14727103506705153272543297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9818069004470102181695531 14727103506705153272543297)
                ·
                  refine ⟨11045327630028864954407473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14727103506705153272543297 11045327630028864954407473)
                  ·
                    refine ⟨8283995722521648715805605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11045327630028864954407473 8283995722521648715805605)
                    ·
                      refine ⟨1553249197972809134213551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8283995722521648715805605 1553249197972809134213551)
                      ·
                        rfl

theorem cell23_3024942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3024942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024942 prefixEnd_3024942 := by exact prefixLift 3024942
  have htrace : WordTrace (prefixWord ++ tailWord_3024942) baseStart_3024942 baseEnd_3024942 := by
    simpa [prefixWord, tailWord_3024942, baseEnd_3024942] using wordTrace_append hprefix tailTrace_3024942
  have hstable : (prefixWord ++ tailWord_3024942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024942).length < 2 ^ (prefixWord ++ tailWord_3024942).sum := by decide
  have hdescent : baseEnd_3024942 < baseStart_3024942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024945 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_3024945 : Nat := 118140960795 + 3024945 * 2 ^ 59
def prefixEnd_3024945 : Nat := 4983230072969 + 3 ^ 40 * 3024945 * 2
def baseEnd_3024945 : Nat := 1553250738414772622476037

theorem tailTrace_3024945 : CollatzResearch.WordTrace tailWord_3024945 prefixEnd_3024945 1553250738414772622476037 := by
  unfold tailWord_3024945
  simp only [CollatzResearch.WordTrace]
  refine ⟨110328808026148359320932289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73552538684098906213954859 110328808026148359320932289)
  ·
    refine ⟨82746606019611269490699217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110328808026148359320932289 82746606019611269490699217)
    ·
      refine ⟨62059954514708452118024413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82746606019611269490699217 62059954514708452118024413)
      ·
        refine ⟨23272482943015669544259155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62059954514708452118024413 23272482943015669544259155)
        ·
          refine ⟨34908724414523504316388733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23272482943015669544259155 34908724414523504316388733)
          ·
            refine ⟨13090771655446314118645775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34908724414523504316388733 13090771655446314118645775)
            ·
              refine ⟨19636157483169471177968663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13090771655446314118645775 19636157483169471177968663)
              ·
                refine ⟨29454236224754206766952995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19636157483169471177968663 29454236224754206766952995)
                ·
                  refine ⟨44181354337131310150429493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29454236224754206766952995 44181354337131310150429493)
                  ·
                    refine ⟨4142001969106060326602765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44181354337131310150429493 4142001969106060326602765)
                    ·
                      refine ⟨1553250738414772622476037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4142001969106060326602765 1553250738414772622476037)
                      ·
                        rfl

theorem cell23_3024945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_3024945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024945 prefixEnd_3024945 := by exact prefixLift 3024945
  have htrace : WordTrace (prefixWord ++ tailWord_3024945) baseStart_3024945 baseEnd_3024945 := by
    simpa [prefixWord, tailWord_3024945, baseEnd_3024945] using wordTrace_append hprefix tailTrace_3024945
  have hstable : (prefixWord ++ tailWord_3024945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024945).length < 2 ^ (prefixWord ++ tailWord_3024945).sum := by decide
  have hdescent : baseEnd_3024945 < baseStart_3024945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3024985 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_3024985 : Nat := 118140960795 + 3024985 * 2 ^ 59
def prefixEnd_3024985 : Nat := 4983230072969 + 3 ^ 40 * 3024985 * 2
def baseEnd_3024985 : Nat := 1553271277640952465975853

theorem tailTrace_3024985 : CollatzResearch.WordTrace tailWord_3024985 prefixEnd_3024985 1553271277640952465975853 := by
  unfold tailWord_3024985
  simp only [CollatzResearch.WordTrace]
  refine ⟨110330266946003446152388409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73553511297335630768258939 110330266946003446152388409)
  ·
    refine ⟨82747700209502584614291307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110330266946003446152388409 82747700209502584614291307)
    ·
      refine ⟨124121550314253876921436961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82747700209502584614291307 124121550314253876921436961)
      ·
        refine ⟨93091162735690407691077721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124121550314253876921436961 93091162735690407691077721)
        ·
          refine ⟨69818372051767805768308291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93091162735690407691077721 69818372051767805768308291)
          ·
            refine ⟨104727558077651708652462437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69818372051767805768308291 104727558077651708652462437)
            ·
              refine ⟨19636417139559695372336707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104727558077651708652462437 19636417139559695372336707)
              ·
                refine ⟨29454625709339543058505061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19636417139559695372336707 29454625709339543058505061)
                ·
                  refine ⟨5522742320501164323469699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29454625709339543058505061 5522742320501164323469699)
                  ·
                    refine ⟨8284113480751746485204549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5522742320501164323469699 8284113480751746485204549)
                    ·
                      refine ⟨1553271277640952465975853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8284113480751746485204549 1553271277640952465975853)
                      ·
                        rfl

theorem cell23_3024985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_3024985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3024985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3024985 prefixEnd_3024985 := by exact prefixLift 3024985
  have htrace : WordTrace (prefixWord ++ tailWord_3024985) baseStart_3024985 baseEnd_3024985 := by
    simpa [prefixWord, tailWord_3024985, baseEnd_3024985] using wordTrace_append hprefix tailTrace_3024985
  have hstable : (prefixWord ++ tailWord_3024985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3024985).length < 2 ^ (prefixWord ++ tailWord_3024985).sum := by decide
  have hdescent : baseEnd_3024985 < baseStart_3024985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3024985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025042 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3025042 : Nat := 118140960795 + 3025042 * 2 ^ 59
def prefixEnd_3025042 : Nat := 4983230072969 + 3 ^ 40 * 3025042 * 2
def baseEnd_3025042 : Nat := 172588949559806526995899

theorem tailTrace_3025042 : CollatzResearch.WordTrace tailWord_3025042 prefixEnd_3025042 172588949559806526995899 := by
  unfold tailWord_3025042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583086476699236221803345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73554897271197963258142253 27583086476699236221803345)
  ·
    refine ⟨20687314857524427166352509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27583086476699236221803345 20687314857524427166352509)
    ·
      refine ⟨7757743071571660187382191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20687314857524427166352509 7757743071571660187382191)
      ·
        refine ⟨11636614607357490281073287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7757743071571660187382191 11636614607357490281073287)
        ·
          refine ⟨17454921911036235421609931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11636614607357490281073287 17454921911036235421609931)
          ·
            refine ⟨26182382866554353132414897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17454921911036235421609931 26182382866554353132414897)
            ·
              refine ⟨19636787149915764849311173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26182382866554353132414897 19636787149915764849311173)
              ·
                refine ⟨3681897590609205909245845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19636787149915764849311173 3681897590609205909245845)
                ·
                  refine ⟨172588949559806526995899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3681897590609205909245845 172588949559806526995899)
                  ·
                    rfl

theorem cell23_3025042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3025042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025042 prefixEnd_3025042 := by exact prefixLift 3025042
  have htrace : WordTrace (prefixWord ++ tailWord_3025042) baseStart_3025042 baseEnd_3025042 := by
    simpa [prefixWord, tailWord_3025042, baseEnd_3025042] using wordTrace_append hprefix tailTrace_3025042
  have hstable : (prefixWord ++ tailWord_3025042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025042).length < 2 ^ (prefixWord ++ tailWord_3025042).sum := by decide
  have hdescent : baseEnd_3025042 < baseStart_3025042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025079 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 2, 3, 2]
def baseStart_3025079 : Nat := 118140960795 + 3025079 * 2 ^ 59
def prefixEnd_3025079 : Nat := 4983230072969 + 3 ^ 40 * 3025079 * 2
def baseEnd_3025079 : Nat := 1553319544822475098200421

theorem tailTrace_3025079 : CollatzResearch.WordTrace tailWord_3025079 prefixEnd_3025079 1553319544822475098200421 := by
  unfold tailWord_3025079
  simp only [CollatzResearch.WordTrace]
  refine ⟨110333695407662900206310291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73555796938441933470873527 110333695407662900206310291)
  ·
    refine ⟨165500543111494350309465437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110333695407662900206310291 165500543111494350309465437)
    ·
      refine ⟨62062703666810381366049539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165500543111494350309465437 62062703666810381366049539)
      ·
        refine ⟨93094055500215572049074309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62062703666810381366049539 93094055500215572049074309)
        ·
          refine ⟨17455135406290419759201433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93094055500215572049074309 17455135406290419759201433)
          ·
            refine ⟨13091351554717814819401075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17455135406290419759201433 13091351554717814819401075)
            ·
              refine ⟨19637027332076722229101613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13091351554717814819401075 19637027332076722229101613)
              ·
                refine ⟨7363885249528770835913105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19637027332076722229101613 7363885249528770835913105)
                ·
                  refine ⟨5522913937146578126934829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7363885249528770835913105 5522913937146578126934829)
                  ·
                    refine ⟨2071092726429966797600561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5522913937146578126934829 2071092726429966797600561)
                    ·
                      refine ⟨1553319544822475098200421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071092726429966797600561 1553319544822475098200421)
                      ·
                        rfl

theorem cell23_3025079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_3025079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025079 prefixEnd_3025079 := by exact prefixLift 3025079
  have htrace : WordTrace (prefixWord ++ tailWord_3025079) baseStart_3025079 baseEnd_3025079 := by
    simpa [prefixWord, tailWord_3025079, baseEnd_3025079] using wordTrace_append hprefix tailTrace_3025079
  have hstable : (prefixWord ++ tailWord_3025079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025079).length < 2 ^ (prefixWord ++ tailWord_3025079).sum := by decide
  have hdescent : baseEnd_3025079 < baseStart_3025079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025105 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_3025105 : Nat := 118140960795 + 3025105 * 2 ^ 59
def prefixEnd_3025105 : Nat := 4983230072969 + 3 ^ 40 * 3025105 * 2
def baseEnd_3025105 : Nat := 1553332895319491996475301

theorem tailTrace_3025105 : CollatzResearch.WordTrace tailWord_3025105 prefixEnd_3025105 1553332895319491996475301 := by
  unfold tailWord_3025105
  simp only [CollatzResearch.WordTrace]
  refine ⟨110334643705568706646756769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73556429137045804431171179 110334643705568706646756769)
  ·
    refine ⟨82750982779176529985067577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110334643705568706646756769 82750982779176529985067577)
    ·
      refine ⟨62063237084382397488800683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82750982779176529985067577 62063237084382397488800683)
      ·
        refine ⟨93094855626573596233201025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62063237084382397488800683 93094855626573596233201025)
        ·
          refine ⟨69821141719930197174900769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93094855626573596233201025 69821141719930197174900769)
          ·
            refine ⟨52365856289947647881175577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69821141719930197174900769 52365856289947647881175577)
            ·
              refine ⟨39274392217460735910881683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52365856289947647881175577 39274392217460735910881683)
              ·
                refine ⟨58911588326191103866322525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39274392217460735910881683 58911588326191103866322525)
                ·
                  refine ⟨22091845622321663949870947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58911588326191103866322525 22091845622321663949870947)
                  ·
                    refine ⟨33137768433482495924806421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22091845622321663949870947 33137768433482495924806421)
                    ·
                      refine ⟨1553332895319491996475301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33137768433482495924806421 1553332895319491996475301)
                      ·
                        rfl

theorem cell23_3025105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_3025105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025105 prefixEnd_3025105 := by exact prefixLift 3025105
  have htrace : WordTrace (prefixWord ++ tailWord_3025105) baseStart_3025105 baseEnd_3025105 := by
    simpa [prefixWord, tailWord_3025105, baseEnd_3025105] using wordTrace_append hprefix tailTrace_3025105
  have hstable : (prefixWord ++ tailWord_3025105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025105).length < 2 ^ (prefixWord ++ tailWord_3025105).sum := by decide
  have hdescent : baseEnd_3025105 < baseStart_3025105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025132 : List Nat := [2, 2, 1, 1, 2, 3, 5, 7]
def baseStart_3025132 : Nat := 118140960795 + 3025132 * 2 ^ 59
def prefixEnd_3025132 : Nat := 4983230072969 + 3 ^ 40 * 3025132 * 2
def baseEnd_3025132 : Nat := 57531361455450495956951

theorem tailTrace_3025132 : CollatzResearch.WordTrace tailWord_3025132 prefixEnd_3025132 57531361455450495956951 := by
  unfold tailWord_3025132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55167814238235445128994825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73557085650980593505326433 55167814238235445128994825)
  ·
    refine ⟨41375860678676583846746119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55167814238235445128994825 41375860678676583846746119)
    ·
      refine ⟨62063791018014875770119179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41375860678676583846746119 62063791018014875770119179)
      ·
        refine ⟨93095686527022313655178769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62063791018014875770119179 93095686527022313655178769)
        ·
          refine ⟨69821764895266735241384077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93095686527022313655178769 69821764895266735241384077)
          ·
            refine ⟨26183161835725025715519029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69821764895266735241384077 26183161835725025715519029)
            ·
              refine ⟨2454671422099221160829909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26183161835725025715519029 2454671422099221160829909)
              ·
                refine ⟨57531361455450495956951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2454671422099221160829909 57531361455450495956951)
                ·
                  rfl

theorem cell23_3025132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 7].length) (baseStart_3025132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025132 prefixEnd_3025132 := by exact prefixLift 3025132
  have htrace : WordTrace (prefixWord ++ tailWord_3025132) baseStart_3025132 baseEnd_3025132 := by
    simpa [prefixWord, tailWord_3025132, baseEnd_3025132] using wordTrace_append hprefix tailTrace_3025132
  have hstable : (prefixWord ++ tailWord_3025132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025132).length < 2 ^ (prefixWord ++ tailWord_3025132).sum := by decide
  have hdescent : baseEnd_3025132 < baseStart_3025132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025145 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_3025145 : Nat := 118140960795 + 3025145 * 2 ^ 59
def prefixEnd_3025145 : Nat := 4983230072969 + 3 ^ 40 * 3025145 * 2
def baseEnd_3025145 : Nat := 517784478181890613325039

theorem tailTrace_3025145 : CollatzResearch.WordTrace tailWord_3025145 prefixEnd_3025145 517784478181890613325039 := by
  unfold tailWord_3025145
  simp only [CollatzResearch.WordTrace]
  refine ⟨110336102625423793478212889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73557401750282528985475259 110336102625423793478212889)
  ·
    refine ⟨82752076969067845108659667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110336102625423793478212889 82752076969067845108659667)
    ·
      refine ⟨124128115453601767662989501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82752076969067845108659667 124128115453601767662989501)
      ·
        refine ⟨46548043295100662873621063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124128115453601767662989501 46548043295100662873621063)
        ·
          refine ⟨69822064942650994310431595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46548043295100662873621063 69822064942650994310431595)
          ·
            refine ⟨104733097413976491465647393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69822064942650994310431595 104733097413976491465647393)
            ·
              refine ⟨78549823060482368599235545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104733097413976491465647393 78549823060482368599235545)
              ·
                refine ⟨58912367295361776449426659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78549823060482368599235545 58912367295361776449426659)
                ·
                  refine ⟨88368550943042664674139989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58912367295361776449426659 88368550943042664674139989)
                  ·
                    refine ⟨517784478181890613325039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 88368550943042664674139989 517784478181890613325039)
                    ·
                      rfl

theorem cell23_3025145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_3025145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025145 prefixEnd_3025145 := by exact prefixLift 3025145
  have htrace : WordTrace (prefixWord ++ tailWord_3025145) baseStart_3025145 baseEnd_3025145 := by
    simpa [prefixWord, tailWord_3025145, baseEnd_3025145] using wordTrace_append hprefix tailTrace_3025145
  have hstable : (prefixWord ++ tailWord_3025145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025145).length < 2 ^ (prefixWord ++ tailWord_3025145).sum := by decide
  have hdescent : baseEnd_3025145 < baseStart_3025145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025146 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3]
def baseStart_3025146 : Nat := 118140960795 + 3025146 * 2 ^ 59
def prefixEnd_3025146 : Nat := 4983230072969 + 3 ^ 40 * 3025146 * 2
def baseEnd_3025146 : Nat := 1553353948026326336062613

theorem tailTrace_3025146 : CollatzResearch.WordTrace tailWord_3025146 prefixEnd_3025146 1553353948026326336062613 := by
  unfold tailWord_3025146
  simp only [CollatzResearch.WordTrace]
  refine ⟨27584034774605042662249823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73557426065613447099332861 27584034774605042662249823)
  ·
    refine ⟨41376052161907563993374735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27584034774605042662249823 41376052161907563993374735)
    ·
      refine ⟨62064078242861345990062103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41376052161907563993374735 62064078242861345990062103)
      ·
        refine ⟨93096117364292018985093155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62064078242861345990062103 93096117364292018985093155)
        ·
          refine ⟨139644176046438028477639733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93096117364292018985093155 139644176046438028477639733)
          ·
            refine ⟨13091641504353565169778725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139644176046438028477639733 13091641504353565169778725)
            ·
              refine ⟨2454682782066293469333511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13091641504353565169778725 2454682782066293469333511)
              ·
                refine ⟨3682024173099440204000267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454682782066293469333511 3682024173099440204000267)
                ·
                  refine ⟨5523036259649160306000401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682024173099440204000267 5523036259649160306000401)
                  ·
                    refine ⟨4142277194736870229500301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5523036259649160306000401 4142277194736870229500301)
                    ·
                      refine ⟨1553353948026326336062613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4142277194736870229500301 1553353948026326336062613)
                      ·
                        rfl

theorem cell23_3025146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_3025146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025146 prefixEnd_3025146 := by exact prefixLift 3025146
  have htrace : WordTrace (prefixWord ++ tailWord_3025146) baseStart_3025146 baseEnd_3025146 := by
    simpa [prefixWord, tailWord_3025146, baseEnd_3025146] using wordTrace_append hprefix tailTrace_3025146
  have hstable : (prefixWord ++ tailWord_3025146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025146).length < 2 ^ (prefixWord ++ tailWord_3025146).sum := by decide
  have hdescent : baseEnd_3025146 < baseStart_3025146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025194 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3025194 : Nat := 118140960795 + 3025194 * 2 ^ 59
def prefixEnd_3025194 : Nat := 4983230072969 + 3 ^ 40 * 3025194 * 2
def baseEnd_3025194 : Nat := 1553378595097742148262393

theorem tailTrace_3025194 : CollatzResearch.WordTrace tailWord_3025194 prefixEnd_3025194 1553378595097742148262393 := by
  unfold tailWord_3025194
  simp only [CollatzResearch.WordTrace]
  refine ⟨27584472450561568711686659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73558593201497516564497757 27584472450561568711686659)
  ·
    refine ⟨41376708675842353067529989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27584472450561568711686659 41376708675842353067529989)
    ·
      refine ⟨7758132876720441200161873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41376708675842353067529989 7758132876720441200161873)
      ·
        refine ⟨5818599657540330900121405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7758132876720441200161873 5818599657540330900121405)
        ·
          refine ⟨2181974871577624087545527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5818599657540330900121405 2181974871577624087545527)
          ·
            refine ⟨3272962307366436131318291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181974871577624087545527 3272962307366436131318291)
            ·
              refine ⟨4909443461049654196977437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272962307366436131318291 4909443461049654196977437)
              ·
                refine ⟨1841041297893620323866539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4909443461049654196977437 1841041297893620323866539)
                ·
                  refine ⟨2761561946840430485799809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841041297893620323866539 2761561946840430485799809)
                  ·
                    refine ⟨2071171460130322864349857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2761561946840430485799809 2071171460130322864349857)
                    ·
                      refine ⟨1553378595097742148262393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071171460130322864349857 1553378595097742148262393)
                      ·
                        rfl

theorem cell23_3025194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3025194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025194 prefixEnd_3025194 := by exact prefixLift 3025194
  have htrace : WordTrace (prefixWord ++ tailWord_3025194) baseStart_3025194 baseEnd_3025194 := by
    simpa [prefixWord, tailWord_3025194, baseEnd_3025194] using wordTrace_append hprefix tailTrace_3025194
  have hstable : (prefixWord ++ tailWord_3025194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025194).length < 2 ^ (prefixWord ++ tailWord_3025194).sum := by decide
  have hdescent : baseEnd_3025194 < baseStart_3025194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025199 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 1, 4, 2]
def baseStart_3025199 : Nat := 118140960795 + 3025199 * 2 ^ 59
def prefixEnd_3025199 : Nat := 4983230072969 + 3 ^ 40 * 3025199 * 2
def baseEnd_3025199 : Nat := 1553381162501014628699869

theorem tailTrace_3025199 : CollatzResearch.WordTrace tailWord_3025199 prefixEnd_3025199 1553381162501014628699869 := by
  unfold tailWord_3025199
  simp only [CollatzResearch.WordTrace]
  refine ⟨110338072167228160700678651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73558714778152107133785767 110338072167228160700678651)
  ·
    refine ⟨165507108250842241051017977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110338072167228160700678651 165507108250842241051017977)
    ·
      refine ⟨124130331188131680788263483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165507108250842241051017977 124130331188131680788263483)
      ·
        refine ⟨186195496782197521182395225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124130331188131680788263483 186195496782197521182395225)
        ·
          refine ⟨139646622586648140886796419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186195496782197521182395225 139646622586648140886796419)
          ·
            refine ⟨209469933879972211330194629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139646622586648140886796419 209469933879972211330194629)
            ·
              refine ⟨39275612602494789624411493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209469933879972211330194629 39275612602494789624411493)
              ·
                refine ⟨7364177362967773054577155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39275612602494789624411493 7364177362967773054577155)
                ·
                  refine ⟨11046266044451659581865733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7364177362967773054577155 11046266044451659581865733)
                  ·
                    refine ⟨2071174883334686171599825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11046266044451659581865733 2071174883334686171599825)
                    ·
                      refine ⟨1553381162501014628699869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071174883334686171599825 1553381162501014628699869)
                      ·
                        rfl

theorem cell23_3025199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4, 2].length) (baseStart_3025199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025199 prefixEnd_3025199 := by exact prefixLift 3025199
  have htrace : WordTrace (prefixWord ++ tailWord_3025199) baseStart_3025199 baseEnd_3025199 := by
    simpa [prefixWord, tailWord_3025199, baseEnd_3025199] using wordTrace_append hprefix tailTrace_3025199
  have hstable : (prefixWord ++ tailWord_3025199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025199).length < 2 ^ (prefixWord ++ tailWord_3025199).sum := by decide
  have hdescent : baseEnd_3025199 < baseStart_3025199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025233 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 2, 2, 2]
def baseStart_3025233 : Nat := 118140960795 + 3025233 * 2 ^ 59
def prefixEnd_3025233 : Nat := 4983230072969 + 3 ^ 40 * 3025233 * 2
def baseEnd_3025233 : Nat := 1553398620843267495674713

theorem tailTrace_3025233 : CollatzResearch.WordTrace tailWord_3025233 prefixEnd_3025233 1553398620843267495674713 := by
  unfold tailWord_3025233
  simp only [CollatzResearch.WordTrace]
  refine ⟨110339312249104984507416353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73559541499403323004944235 110339312249104984507416353)
  ·
    refine ⟨82754484186828738380562265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110339312249104984507416353 82754484186828738380562265)
    ·
      refine ⟨62065863140121553785421699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82754484186828738380562265 62065863140121553785421699)
      ·
        refine ⟨93098794710182330678132549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62065863140121553785421699 93098794710182330678132549)
        ·
          refine ⟨17456024008159187002149853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93098794710182330678132549 17456024008159187002149853)
          ·
            refine ⟨6546009003059695125806195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17456024008159187002149853 6546009003059695125806195)
            ·
              refine ⟨9819013504589542688709293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546009003059695125806195 9819013504589542688709293)
              ·
                refine ⟨3682130064221078508265985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9819013504589542688709293 3682130064221078508265985)
                ·
                  refine ⟨2761597548165808881199489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682130064221078508265985 2761597548165808881199489)
                  ·
                    refine ⟨2071198161124356660899617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2761597548165808881199489 2071198161124356660899617)
                    ·
                      refine ⟨1553398620843267495674713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071198161124356660899617 1553398620843267495674713)
                      ·
                        rfl

theorem cell23_3025233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_3025233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025233 prefixEnd_3025233 := by exact prefixLift 3025233
  have htrace : WordTrace (prefixWord ++ tailWord_3025233) baseStart_3025233 baseEnd_3025233 := by
    simpa [prefixWord, tailWord_3025233, baseEnd_3025233] using wordTrace_append hprefix tailTrace_3025233
  have hstable : (prefixWord ++ tailWord_3025233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025233).length < 2 ^ (prefixWord ++ tailWord_3025233).sum := by decide
  have hdescent : baseEnd_3025233 < baseStart_3025233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025306 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3025306 : Nat := 118140960795 + 3025306 * 2 ^ 59
def prefixEnd_3025306 : Nat := 4983230072969 + 3 ^ 40 * 3025306 * 2
def baseEnd_3025306 : Nat := 1553436104931045710061877

theorem tailTrace_3025306 : CollatzResearch.WordTrace tailWord_3025306 prefixEnd_3025306 1553436104931045710061877 := by
  unfold tailWord_3025306
  simp only [CollatzResearch.WordTrace]
  refine ⟨27585493694460129493705943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73561316518560345316549181 27585493694460129493705943)
  ·
    refine ⟨41378240541690194240558915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27585493694460129493705943 41378240541690194240558915)
    ·
      refine ⟨62067360812535291360838373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41378240541690194240558915 62067360812535291360838373)
      ·
        refine ⟨11637630152350367130157195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62067360812535291360838373 11637630152350367130157195)
        ·
          refine ⟨17456445228525550695235793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11637630152350367130157195 17456445228525550695235793)
          ·
            refine ⟨13092333921394163021426845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17456445228525550695235793 13092333921394163021426845)
            ·
              refine ⟨4909625220522811133035067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13092333921394163021426845 4909625220522811133035067)
              ·
                refine ⟨7364437830784216699552601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909625220522811133035067 7364437830784216699552601)
                ·
                  refine ⟨5523328373088162524664451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7364437830784216699552601 5523328373088162524664451)
                  ·
                    refine ⟨8284992559632243786996677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5523328373088162524664451 8284992559632243786996677)
                    ·
                      refine ⟨1553436104931045710061877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8284992559632243786996677 1553436104931045710061877)
                      ·
                        rfl

theorem cell23_3025306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3025306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025306 prefixEnd_3025306 := by exact prefixLift 3025306
  have htrace : WordTrace (prefixWord ++ tailWord_3025306) baseStart_3025306 baseEnd_3025306 := by
    simpa [prefixWord, tailWord_3025306, baseEnd_3025306] using wordTrace_append hprefix tailTrace_3025306
  have hstable : (prefixWord ++ tailWord_3025306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025306).length < 2 ^ (prefixWord ++ tailWord_3025306).sum := by decide
  have hdescent : baseEnd_3025306 < baseStart_3025306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025319 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3025319 : Nat := 118140960795 + 3025319 * 2 ^ 59
def prefixEnd_3025319 : Nat := 4983230072969 + 3 ^ 40 * 3025319 * 2
def baseEnd_3025319 : Nat := 1553442780179554159199317

theorem tailTrace_3025319 : CollatzResearch.WordTrace tailWord_3025319 prefixEnd_3025319 1553442780179554159199317 := by
  unfold tailWord_3025319
  simp only [CollatzResearch.WordTrace]
  refine ⟨110342448926793421195047011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73561632617862280796698007 110342448926793421195047011)
  ·
    refine ⟨165513673390190131792570517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110342448926793421195047011 165513673390190131792570517)
    ·
      refine ⟨7758453440165162427776743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165513673390190131792570517 7758453440165162427776743)
      ·
        refine ⟨11637680160247743641665115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7758453440165162427776743 11637680160247743641665115)
        ·
          refine ⟨17456520240371615462497673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11637680160247743641665115 17456520240371615462497673)
          ·
            refine ⟨13092390180278711596873255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17456520240371615462497673 13092390180278711596873255)
            ·
              refine ⟨19638585270418067395309883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13092390180278711596873255 19638585270418067395309883)
              ·
                refine ⟨29457877905627101092964825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19638585270418067395309883 29457877905627101092964825)
                ·
                  refine ⟨22093408429220325819723619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29457877905627101092964825 22093408429220325819723619)
                  ·
                    refine ⟨33140112643830488729585429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22093408429220325819723619 33140112643830488729585429)
                    ·
                      refine ⟨1553442780179554159199317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33140112643830488729585429 1553442780179554159199317)
                      ·
                        rfl

theorem cell23_3025319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3025319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025319 prefixEnd_3025319 := by exact prefixLift 3025319
  have htrace : WordTrace (prefixWord ++ tailWord_3025319) baseStart_3025319 baseEnd_3025319 := by
    simpa [prefixWord, tailWord_3025319, baseEnd_3025319] using wordTrace_append hprefix tailTrace_3025319
  have hstable : (prefixWord ++ tailWord_3025319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025319).length < 2 ^ (prefixWord ++ tailWord_3025319).sum := by decide
  have hdescent : baseEnd_3025319 < baseStart_3025319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025329 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 8]
def baseStart_3025329 : Nat := 118140960795 + 3025329 * 2 ^ 59
def prefixEnd_3025329 : Nat := 4983230072969 + 3 ^ 40 * 3025329 * 2
def baseEnd_3025329 : Nat := 172605323887344346674919

theorem tailTrace_3025329 : CollatzResearch.WordTrace tailWord_3025329 prefixEnd_3025329 172605323887344346674919 := by
  unfold tailWord_3025329
  simp only [CollatzResearch.WordTrace]
  refine ⟨110342813656757192902911041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73561875771171461935274027 110342813656757192902911041)
  ·
    refine ⟨82757110242567894677183281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110342813656757192902911041 82757110242567894677183281)
    ·
      refine ⟨62067832681925921007887461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82757110242567894677183281 62067832681925921007887461)
      ·
        refine ⟨11637718627861110188978899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62067832681925921007887461 11637718627861110188978899)
        ·
          refine ⟨17456577941791665283468349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11637718627861110188978899 17456577941791665283468349)
          ·
            refine ⟨6546216728171874481300631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17456577941791665283468349 6546216728171874481300631)
            ·
              refine ⟨9819325092257811721950947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546216728171874481300631 9819325092257811721950947)
              ·
                refine ⟨14728987638386717582926421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9819325092257811721950947 14728987638386717582926421)
                ·
                  refine ⟨172605323887344346674919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14728987638386717582926421 172605323887344346674919)
                  ·
                    rfl

theorem cell23_3025329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_3025329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025329 prefixEnd_3025329 := by exact prefixLift 3025329
  have htrace : WordTrace (prefixWord ++ tailWord_3025329) baseStart_3025329 baseEnd_3025329 := by
    simpa [prefixWord, tailWord_3025329, baseEnd_3025329] using wordTrace_append hprefix tailTrace_3025329
  have hstable : (prefixWord ++ tailWord_3025329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025329).length < 2 ^ (prefixWord ++ tailWord_3025329).sum := by decide
  have hdescent : baseEnd_3025329 < baseStart_3025329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025333 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_3025333 : Nat := 118140960795 + 3025333 * 2 ^ 59
def prefixEnd_3025333 : Nat := 4983230072969 + 3 ^ 40 * 3025333 * 2
def baseEnd_3025333 : Nat := 517816656302905701474751

theorem tailTrace_3025333 : CollatzResearch.WordTrace tailWord_3025333 prefixEnd_3025333 517816656302905701474751 := by
  unfold tailWord_3025333
  simp only [CollatzResearch.WordTrace]
  refine ⟨110342959548742701586056653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73561973032495134390704435 110342959548742701586056653)
  ·
    refine ⟨41378609830778513094771245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110342959548742701586056653 41378609830778513094771245)
    ·
      refine ⟨15516978686541942410539217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41378609830778513094771245 15516978686541942410539217)
      ·
        refine ⟨11637734014906456807904413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15516978686541942410539217 11637734014906456807904413)
        ·
          refine ⟨4364150255589921302964155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11637734014906456807904413 4364150255589921302964155)
          ·
            refine ⟨6546225383384881954446233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364150255589921302964155 6546225383384881954446233)
            ·
              refine ⟨4909669037538661465834675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546225383384881954446233 4909669037538661465834675)
              ·
                refine ⟨7364503556307992198752013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909669037538661465834675 7364503556307992198752013)
                ·
                  refine ⟨2761688833615497074532005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7364503556307992198752013 2761688833615497074532005)
                  ·
                    refine ⟨517816656302905701474751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761688833615497074532005 517816656302905701474751)
                    ·
                      rfl

theorem cell23_3025333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_3025333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025333 prefixEnd_3025333 := by exact prefixLift 3025333
  have htrace : WordTrace (prefixWord ++ tailWord_3025333) baseStart_3025333 baseEnd_3025333 := by
    simpa [prefixWord, tailWord_3025333, baseEnd_3025333] using wordTrace_append hprefix tailTrace_3025333
  have hstable : (prefixWord ++ tailWord_3025333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025333).length < 2 ^ (prefixWord ++ tailWord_3025333).sum := by decide
  have hdescent : baseEnd_3025333 < baseStart_3025333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025383 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_3025383 : Nat := 118140960795 + 3025383 * 2 ^ 59
def prefixEnd_3025383 : Nat := 4983230072969 + 3 ^ 40 * 3025383 * 2
def baseEnd_3025383 : Nat := 1553475642941441908799023

theorem tailTrace_3025383 : CollatzResearch.WordTrace tailWord_3025383 prefixEnd_3025383 1553475642941441908799023 := by
  unfold tailWord_3025383
  simp only [CollatzResearch.WordTrace]
  refine ⟨110344783198561560125376803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73563188799041040083584535 110344783198561560125376803)
  ·
    refine ⟨165517174797842340188065205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110344783198561560125376803 165517174797842340188065205)
    ·
      refine ⟨15517235137297719392631113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165517174797842340188065205 15517235137297719392631113)
      ·
        refine ⟨11637926352973289544473335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15517235137297719392631113 11637926352973289544473335)
        ·
          refine ⟨17456889529459934316710003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11637926352973289544473335 17456889529459934316710003)
          ·
            refine ⟨26185334294189901475065005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17456889529459934316710003 26185334294189901475065005)
            ·
              refine ⟨9819500360321213053149377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26185334294189901475065005 9819500360321213053149377)
              ·
                refine ⟨7364625270240909789862033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819500360321213053149377 7364625270240909789862033)
                ·
                  refine ⟨5523468952680682342396525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7364625270240909789862033 5523468952680682342396525)
                  ·
                    refine ⟨2071300857255255878398697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5523468952680682342396525 2071300857255255878398697)
                    ·
                      refine ⟨1553475642941441908799023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071300857255255878398697 1553475642941441908799023)
                      ·
                        rfl

theorem cell23_3025383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_3025383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025383 prefixEnd_3025383 := by exact prefixLift 3025383
  have htrace : WordTrace (prefixWord ++ tailWord_3025383) baseStart_3025383 baseEnd_3025383 := by
    simpa [prefixWord, tailWord_3025383, baseEnd_3025383] using wordTrace_append hprefix tailTrace_3025383
  have hstable : (prefixWord ++ tailWord_3025383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025383).length < 2 ^ (prefixWord ++ tailWord_3025383).sum := by decide
  have hdescent : baseEnd_3025383 < baseStart_3025383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025390 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3025390 : Nat := 118140960795 + 3025390 * 2 ^ 59
def prefixEnd_3025390 : Nat := 4983230072969 + 3 ^ 40 * 3025390 * 2
def baseEnd_3025390 : Nat := 1553479237306023381411491

theorem tailTrace_3025390 : CollatzResearch.WordTrace tailWord_3025390 prefixEnd_3025390 1553479237306023381411491 := by
  unfold tailWord_3025390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13793129813692025040110203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73563359006357466880587749 13793129813692025040110203)
  ·
    refine ⟨20689694720538037560165305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13793129813692025040110203 20689694720538037560165305)
    ·
      refine ⟨15517271040403528170123979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20689694720538037560165305 15517271040403528170123979)
      ·
        refine ⟨23275906560605292255185969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15517271040403528170123979 23275906560605292255185969)
        ·
          refine ⟨17456929920453969191389477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23275906560605292255185969 17456929920453969191389477)
          ·
            refine ⟨3273174360085119223385527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17456929920453969191389477 3273174360085119223385527)
            ·
              refine ⟨4909761540127678835078291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273174360085119223385527 4909761540127678835078291)
              ·
                refine ⟨7364642310191518252617437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909761540127678835078291 7364642310191518252617437)
                ·
                  refine ⟨2761740866321819344731539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7364642310191518252617437 2761740866321819344731539)
                  ·
                    refine ⟨4142611299482729017097309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761740866321819344731539 4142611299482729017097309)
                    ·
                      refine ⟨1553479237306023381411491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4142611299482729017097309 1553479237306023381411491)
                      ·
                        rfl

theorem cell23_3025390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3025390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025390 prefixEnd_3025390 := by exact prefixLift 3025390
  have htrace : WordTrace (prefixWord ++ tailWord_3025390) baseStart_3025390 baseEnd_3025390 := by
    simpa [prefixWord, tailWord_3025390, baseEnd_3025390] using wordTrace_append hprefix tailTrace_3025390
  have hstable : (prefixWord ++ tailWord_3025390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025390).length < 2 ^ (prefixWord ++ tailWord_3025390).sum := by decide
  have hdescent : baseEnd_3025390 < baseStart_3025390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025397 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 6]
def baseStart_3025397 : Nat := 118140960795 + 3025397 * 2 ^ 59
def prefixEnd_3025397 : Nat := 4983230072969 + 3 ^ 40 * 3025397 * 2
def baseEnd_3025397 : Nat := 172609203518956094891551

theorem tailTrace_3025397 : CollatzResearch.WordTrace tailWord_3025397 prefixEnd_3025397 172609203518956094891551 := by
  unfold tailWord_3025397
  simp only [CollatzResearch.WordTrace]
  refine ⟨110345293820510840516386445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73563529213673893677590963 110345293820510840516386445)
  ·
    refine ⟨41379485182691565193644917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110345293820510840516386445 41379485182691565193644917)
    ·
      refine ⟨3879326735877334236904211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41379485182691565193644917 3879326735877334236904211)
      ·
        refine ⟨5818990103816001355356317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3879326735877334236904211 5818990103816001355356317)
        ·
          refine ⟨2182121288931000508258619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5818990103816001355356317 2182121288931000508258619)
          ·
            refine ⟨3273181933396500762387929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182121288931000508258619 3273181933396500762387929)
            ·
              refine ⟨2454886450047375571790947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3273181933396500762387929 2454886450047375571790947)
              ·
                refine ⟨3682329675071063357686421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454886450047375571790947 3682329675071063357686421)
                ·
                  refine ⟨172609203518956094891551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3682329675071063357686421 172609203518956094891551)
                  ·
                    rfl

theorem cell23_3025397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_3025397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025397 prefixEnd_3025397 := by exact prefixLift 3025397
  have htrace : WordTrace (prefixWord ++ tailWord_3025397) baseStart_3025397 baseEnd_3025397 := by
    simpa [prefixWord, tailWord_3025397, baseEnd_3025397] using wordTrace_append hprefix tailTrace_3025397
  have hstable : (prefixWord ++ tailWord_3025397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025397).length < 2 ^ (prefixWord ++ tailWord_3025397).sum := by decide
  have hdescent : baseEnd_3025397 < baseStart_3025397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025413 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 3, 2, 2]
def baseStart_3025413 : Nat := 118140960795 + 3025413 * 2 ^ 59
def prefixEnd_3025413 : Nat := 4983230072969 + 3 ^ 40 * 3025413 * 2
def baseEnd_3025413 : Nat := 1553491047361076791423885

theorem tailTrace_3025413 : CollatzResearch.WordTrace tailWord_3025413 prefixEnd_3025413 1553491047361076791423885 := by
  unfold tailWord_3025413
  simp only [CollatzResearch.WordTrace]
  refine ⟨110345877388452875248968893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73563918258968583499312595 110345877388452875248968893)
  ·
    refine ⟨41379704020669828218363335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110345877388452875248968893 41379704020669828218363335)
    ·
      refine ⟨62069556031004742327545003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41379704020669828218363335 62069556031004742327545003)
      ·
        refine ⟨93104334046507113491317505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62069556031004742327545003 93104334046507113491317505)
        ·
          refine ⟨69828250534880335118488129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93104334046507113491317505 69828250534880335118488129)
          ·
            refine ⟨52371187901160251338866097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69828250534880335118488129 52371187901160251338866097)
            ·
              refine ⟨39278390925870188504149573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52371187901160251338866097 39278390925870188504149573)
              ·
                refine ⟨7364698298600660344528045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39278390925870188504149573 7364698298600660344528045)
                ·
                  refine ⟨2761761861975247629198017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7364698298600660344528045 2761761861975247629198017)
                  ·
                    refine ⟨2071321396481435721898513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2761761861975247629198017 2071321396481435721898513)
                    ·
                      refine ⟨1553491047361076791423885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071321396481435721898513 1553491047361076791423885)
                      ·
                        rfl

theorem cell23_3025413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_3025413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025413 prefixEnd_3025413 := by exact prefixLift 3025413
  have htrace : WordTrace (prefixWord ++ tailWord_3025413) baseStart_3025413 baseEnd_3025413 := by
    simpa [prefixWord, tailWord_3025413, baseEnd_3025413] using wordTrace_append hprefix tailTrace_3025413
  have hstable : (prefixWord ++ tailWord_3025413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025413).length < 2 ^ (prefixWord ++ tailWord_3025413).sum := by decide
  have hdescent : baseEnd_3025413 < baseStart_3025413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025419 : List Nat := [1, 1, 1, 1, 7, 1, 2, 9]
def baseStart_3025419 : Nat := 118140960795 + 3025419 * 2 ^ 59
def prefixEnd_3025419 : Nat := 4983230072969 + 3 ^ 40 * 3025419 * 2
def baseEnd_3025419 : Nat := 57536819564629769183291

theorem tailTrace_3025419 : CollatzResearch.WordTrace tailWord_3025419 prefixEnd_3025419 57536819564629769183291 := by
  unfold tailWord_3025419
  simp only [CollatzResearch.WordTrace]
  refine ⟨110346096226431138273687311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73564064150954092182458207 110346096226431138273687311)
  ·
    refine ⟨165519144339646707410530967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110346096226431138273687311 165519144339646707410530967)
    ·
      refine ⟨248278716509470061115796451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165519144339646707410530967 248278716509470061115796451)
      ·
        refine ⟨372418074764205091673694677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248278716509470061115796451 372418074764205091673694677)
        ·
          refine ⟨8728548627286056836102219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 372418074764205091673694677 8728548627286056836102219)
          ·
            refine ⟨13092822940929085254153329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8728548627286056836102219 13092822940929085254153329)
            ·
              refine ⟨9819617205696813940614997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13092822940929085254153329 9819617205696813940614997)
              ·
                refine ⟨57536819564629769183291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9819617205696813940614997 57536819564629769183291)
                ·
                  rfl

theorem cell23_3025419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 9].length) (baseStart_3025419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025419 prefixEnd_3025419 := by exact prefixLift 3025419
  have htrace : WordTrace (prefixWord ++ tailWord_3025419) baseStart_3025419 baseEnd_3025419 := by
    simpa [prefixWord, tailWord_3025419, baseEnd_3025419] using wordTrace_append hprefix tailTrace_3025419
  have hstable : (prefixWord ++ tailWord_3025419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025419).length < 2 ^ (prefixWord ++ tailWord_3025419).sum := by decide
  have hdescent : baseEnd_3025419 < baseStart_3025419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025440 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 2, 4]
def baseStart_3025440 : Nat := 118140960795 + 3025440 * 2 ^ 59
def prefixEnd_3025440 : Nat := 4983230072969 + 3 ^ 40 * 3025440 * 2
def baseEnd_3025440 : Nat := 517834970446249395262087

theorem tailTrace_3025440 : CollatzResearch.WordTrace tailWord_3025440 prefixEnd_3025440 517834970446249395262087 := by
  unfold tailWord_3025440
  simp only [CollatzResearch.WordTrace]
  refine ⟨55173431079677529430100887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73564574772903372573467849 55173431079677529430100887)
  ·
    refine ⟨82760146619516294145151331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55173431079677529430100887 82760146619516294145151331)
    ·
      refine ⟨124140219929274441217726997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82760146619516294145151331 124140219929274441217726997)
      ·
        refine ⟨5819072809184739432080953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124140219929274441217726997 5819072809184739432080953)
        ·
          refine ⟨4364304606888554574060715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5819072809184739432080953 4364304606888554574060715)
          ·
            refine ⟨6546456910332831861091073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364304606888554574060715 6546456910332831861091073)
            ·
              refine ⟨4909842682749623895818305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546456910332831861091073 4909842682749623895818305)
              ·
                refine ⟨3682382012062217921863729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4909842682749623895818305 3682382012062217921863729)
                ·
                  refine ⟨2761786509046663441397797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682382012062217921863729 2761786509046663441397797)
                  ·
                    refine ⟨517834970446249395262087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761786509046663441397797 517834970446249395262087)
                    ·
                      rfl

theorem cell23_3025440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_3025440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025440 prefixEnd_3025440 := by exact prefixLift 3025440
  have htrace : WordTrace (prefixWord ++ tailWord_3025440) baseStart_3025440 baseEnd_3025440 := by
    simpa [prefixWord, tailWord_3025440, baseEnd_3025440] using wordTrace_append hprefix tailTrace_3025440
  have hstable : (prefixWord ++ tailWord_3025440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025440).length < 2 ^ (prefixWord ++ tailWord_3025440).sum := by decide
  have hdescent : baseEnd_3025440 < baseStart_3025440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025463 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_3025463 : Nat := 118140960795 + 3025463 * 2 ^ 59
def prefixEnd_3025463 : Nat := 4983230072969 + 3 ^ 40 * 3025463 * 2
def baseEnd_3025463 : Nat := 1553516721393801595798655

theorem tailTrace_3025463 : CollatzResearch.WordTrace tailWord_3025463 prefixEnd_3025463 1553516721393801595798655 := by
  unfold tailWord_3025463
  simp only [CollatzResearch.WordTrace]
  refine ⟨110347701038271733788289043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73565134025514489192192695 110347701038271733788289043)
  ·
    refine ⟨165521551557407600682433565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110347701038271733788289043 165521551557407600682433565)
    ·
      refine ⟨62070581834027850255912587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165521551557407600682433565 62070581834027850255912587)
      ·
        refine ⟨93105872751041775383868881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62070581834027850255912587 93105872751041775383868881)
        ·
          refine ⟨69829404563281331537901661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93105872751041775383868881 69829404563281331537901661)
          ·
            refine ⟨26186026711230499326713123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69829404563281331537901661 26186026711230499326713123)
            ·
              refine ⟨39279040066845748990069685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26186026711230499326713123 39279040066845748990069685)
              ·
                refine ⟨3682410006266788967819033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39279040066845748990069685 3682410006266788967819033)
                ·
                  refine ⟨2761807504700091725864275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682410006266788967819033 2761807504700091725864275)
                  ·
                    refine ⟨4142711257050137588796413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761807504700091725864275 4142711257050137588796413)
                    ·
                      refine ⟨1553516721393801595798655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4142711257050137588796413 1553516721393801595798655)
                      ·
                        rfl

theorem cell23_3025463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_3025463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025463 prefixEnd_3025463 := by exact prefixLift 3025463
  have htrace : WordTrace (prefixWord ++ tailWord_3025463) baseStart_3025463 baseEnd_3025463 := by
    simpa [prefixWord, tailWord_3025463, baseEnd_3025463] using wordTrace_append hprefix tailTrace_3025463
  have hstable : (prefixWord ++ tailWord_3025463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025463).length < 2 ^ (prefixWord ++ tailWord_3025463).sum := by decide
  have hdescent : baseEnd_3025463 < baseStart_3025463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025470 : List Nat := [4, 2, 1, 4, 1, 1, 3, 7]
def baseStart_3025470 : Nat := 118140960795 + 3025470 * 2 ^ 59
def prefixEnd_3025470 : Nat := 4983230072969 + 3 ^ 40 * 3025470 * 2
def baseEnd_3025470 : Nat := 57537789472532706237449

theorem tailTrace_3025470 : CollatzResearch.WordTrace tailWord_3025470 prefixEnd_3025470 57537789472532706237449 := by
  unfold tailWord_3025470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13793494543655796747974233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73565304232830915989195909 13793494543655796747974233)
  ·
    refine ⟨10345120907741847560980675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13793494543655796747974233 10345120907741847560980675)
    ·
      refine ⟨15517681361612771341471013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10345120907741847560980675 15517681361612771341471013)
      ·
        refine ⟨2909565255302394626525815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15517681361612771341471013 2909565255302394626525815)
        ·
          refine ⟨4364347882953591939788723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909565255302394626525815 4364347882953591939788723)
          ·
            refine ⟨6546521824430387909683085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364347882953591939788723 6546521824430387909683085)
            ·
              refine ⟨2454945684161395466131157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6546521824430387909683085 2454945684161395466131157)
              ·
                refine ⟨57537789472532706237449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2454945684161395466131157 57537789472532706237449)
                ·
                  rfl

theorem cell23_3025470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_3025470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025470 prefixEnd_3025470 := by exact prefixLift 3025470
  have htrace : WordTrace (prefixWord ++ tailWord_3025470) baseStart_3025470 baseEnd_3025470 := by
    simpa [prefixWord, tailWord_3025470, baseEnd_3025470] using wordTrace_append hprefix tailTrace_3025470
  have hstable : (prefixWord ++ tailWord_3025470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025470).length < 2 ^ (prefixWord ++ tailWord_3025470).sum := by decide
  have hdescent : baseEnd_3025470 < baseStart_3025470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025490 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_3025490 : Nat := 118140960795 + 3025490 * 2 ^ 59
def prefixEnd_3025490 : Nat := 4983230072969 + 3 ^ 40 * 3025490 * 2
def baseEnd_3025490 : Nat := 1553530585371472990161031

theorem tailTrace_3025490 : CollatzResearch.WordTrace tailWord_3025490 prefixEnd_3025490 1553530585371472990161031 := by
  unfold tailWord_3025490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27587171452293479349880481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73565790539449278266347949 27587171452293479349880481)
  ·
    refine ⟨20690378589220109512410361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27587171452293479349880481 20690378589220109512410361)
    ·
      refine ⟨15517783941915082134307771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20690378589220109512410361 15517783941915082134307771)
      ·
        refine ⟨23276675912872623201461657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15517783941915082134307771 23276675912872623201461657)
        ·
          refine ⟨17457506934654467401096243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23276675912872623201461657 17457506934654467401096243)
          ·
            refine ⟨26186260401981701101644365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17457506934654467401096243 26186260401981701101644365)
            ·
              refine ⟨9819847650743137913116637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26186260401981701101644365 9819847650743137913116637)
              ·
                refine ⟨3682442869028676717418739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9819847650743137913116637 3682442869028676717418739)
                ·
                  refine ⟨5523664303543015076128109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682442869028676717418739 5523664303543015076128109)
                  ·
                    refine ⟨2071374113828630653548041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5523664303543015076128109 2071374113828630653548041)
                    ·
                      refine ⟨1553530585371472990161031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071374113828630653548041 1553530585371472990161031)
                      ·
                        rfl

theorem cell23_3025490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_3025490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025490 prefixEnd_3025490 := by exact prefixLift 3025490
  have htrace : WordTrace (prefixWord ++ tailWord_3025490) baseStart_3025490 baseEnd_3025490 := by
    simpa [prefixWord, tailWord_3025490, baseEnd_3025490] using wordTrace_append hprefix tailTrace_3025490
  have hstable : (prefixWord ++ tailWord_3025490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025490).length < 2 ^ (prefixWord ++ tailWord_3025490).sum := by decide
  have hdescent : baseEnd_3025490 < baseStart_3025490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4]
def baseStart_3025499 : Nat := 118140960795 + 3025499 * 2 ^ 59
def prefixEnd_3025499 : Nat := 4983230072969 + 3 ^ 40 * 3025499 * 2
def baseEnd_3025499 : Nat := 1553535206697363454948489

theorem tailTrace_3025499 : CollatzResearch.WordTrace tailWord_3025499 prefixEnd_3025499 1553535206697363454948489 := by
  unfold tailWord_3025499
  simp only [CollatzResearch.WordTrace]
  refine ⟨110349014066141311936599551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73566009377427541291066367 110349014066141311936599551)
  ·
    refine ⟨165523521099211967904899327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110349014066141311936599551 165523521099211967904899327)
    ·
      refine ⟨248285281648817951857348991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165523521099211967904899327 248285281648817951857348991)
      ·
        refine ⟨372427922473226927786023487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248285281648817951857348991 372427922473226927786023487)
        ·
          refine ⟨558641883709840391679035231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372427922473226927786023487 558641883709840391679035231)
          ·
            refine ⟨837962825564760587518552847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558641883709840391679035231 837962825564760587518552847)
            ·
              refine ⟨1256944238347140881277829271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837962825564760587518552847 1256944238347140881277829271)
              ·
                refine ⟨1885416357520711321916743907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256944238347140881277829271 1885416357520711321916743907)
                ·
                  refine ⟨2828124536281066982875115861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885416357520711321916743907 2828124536281066982875115861)
                  ·
                    refine ⟨8285521102385938426391941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 2828124536281066982875115861 8285521102385938426391941)
                    ·
                      refine ⟨1553535206697363454948489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8285521102385938426391941 1553535206697363454948489)
                      ·
                        rfl

theorem cell23_3025499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_3025499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025499 prefixEnd_3025499 := by exact prefixLift 3025499
  have htrace : WordTrace (prefixWord ++ tailWord_3025499) baseStart_3025499 baseEnd_3025499 := by
    simpa [prefixWord, tailWord_3025499, baseEnd_3025499] using wordTrace_append hprefix tailTrace_3025499
  have hstable : (prefixWord ++ tailWord_3025499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025499).length < 2 ^ (prefixWord ++ tailWord_3025499).sum := by decide
  have hdescent : baseEnd_3025499 < baseStart_3025499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025516 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3025516 : Nat := 118140960795 + 3025516 * 2 ^ 59
def prefixEnd_3025516 : Nat := 4983230072969 + 3 ^ 40 * 3025516 * 2
def baseEnd_3025516 : Nat := 1553543935868489888435911

theorem tailTrace_3025516 : CollatzResearch.WordTrace tailWord_3025516 prefixEnd_3025516 1553543935868489888435911 := by
  unfold tailWord_3025516
  simp only [CollatzResearch.WordTrace]
  refine ⟨55174817053539861919984201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73566422738053149226645601 55174817053539861919984201)
  ·
    refine ⟨41381112790154896439988151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55174817053539861919984201 41381112790154896439988151)
    ·
      refine ⟨62071669185232344659982227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41381112790154896439988151 62071669185232344659982227)
      ·
        refine ⟨93107503777848516989973341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62071669185232344659982227 93107503777848516989973341)
        ·
          refine ⟨34915313916693193871240003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93107503777848516989973341 34915313916693193871240003)
          ·
            refine ⟨52372970875039790806860005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34915313916693193871240003 52372970875039790806860005)
            ·
              refine ⟨9819932039069960776286251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52372970875039790806860005 9819932039069960776286251)
              ·
                refine ⟨14729898058604941164429377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9819932039069960776286251 14729898058604941164429377)
                ·
                  refine ⟨11047423543953705873322033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14729898058604941164429377 11047423543953705873322033)
                  ·
                    refine ⟨8285567657965279404991525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11047423543953705873322033 8285567657965279404991525)
                    ·
                      refine ⟨1553543935868489888435911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8285567657965279404991525 1553543935868489888435911)
                      ·
                        rfl

theorem cell23_3025516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3025516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025516 prefixEnd_3025516 := by exact prefixLift 3025516
  have htrace : WordTrace (prefixWord ++ tailWord_3025516) baseStart_3025516 baseEnd_3025516 := by
    simpa [prefixWord, tailWord_3025516, baseEnd_3025516] using wordTrace_append hprefix tailTrace_3025516
  have hstable : (prefixWord ++ tailWord_3025516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025516).length < 2 ^ (prefixWord ++ tailWord_3025516).sum := by decide
  have hdescent : baseEnd_3025516 < baseStart_3025516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025560 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 5]
def baseStart_3025560 : Nat := 118140960795 + 3025560 * 2 ^ 59
def prefixEnd_3025560 : Nat := 4983230072969 + 3 ^ 40 * 3025560 * 2
def baseEnd_3025560 : Nat := 172618503224143079587301

theorem tailTrace_3025560 : CollatzResearch.WordTrace tailWord_3025560 prefixEnd_3025560 172618503224143079587301 := by
  unfold tailWord_3025560
  simp only [CollatzResearch.WordTrace]
  refine ⟨55175619459460159677285067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73567492612613546236380089 55175619459460159677285067)
  ·
    refine ⟨82763429189190239515927601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55175619459460159677285067 82763429189190239515927601)
    ·
      refine ⟨62072571891892679636945701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82763429189190239515927601 62072571891892679636945701)
      ·
        refine ⟨11638607229729877431927319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62072571891892679636945701 11638607229729877431927319)
        ·
          refine ⟨17457910844594816147890979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11638607229729877431927319 17457910844594816147890979)
          ·
            refine ⟨26186866266892224221836469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17457910844594816147890979 26186866266892224221836469)
            ·
              refine ⟨2455018712521146020797169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26186866266892224221836469 2455018712521146020797169)
              ·
                refine ⟨1841264034390859515597877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455018712521146020797169 1841264034390859515597877)
                ·
                  refine ⟨172618503224143079587301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1841264034390859515597877 172618503224143079587301)
                  ·
                    rfl

theorem cell23_3025560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 5].length) (baseStart_3025560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025560 prefixEnd_3025560 := by exact prefixLift 3025560
  have htrace : WordTrace (prefixWord ++ tailWord_3025560) baseStart_3025560 baseEnd_3025560 := by
    simpa [prefixWord, tailWord_3025560, baseEnd_3025560] using wordTrace_append hprefix tailTrace_3025560
  have hstable : (prefixWord ++ tailWord_3025560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025560).length < 2 ^ (prefixWord ++ tailWord_3025560).sum := by decide
  have hdescent : baseEnd_3025560 < baseStart_3025560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025593 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 4, 4, 2]
def baseStart_3025593 : Nat := 118140960795 + 3025593 * 2 ^ 59
def prefixEnd_3025593 : Nat := 4983230072969 + 3 ^ 40 * 3025593 * 2
def baseEnd_3025593 : Nat := 1553583473878886087173057

theorem tailTrace_3025593 : CollatzResearch.WordTrace tailWord_3025593 prefixEnd_3025593 1553583473878886087173057 := by
  unfold tailWord_3025593
  simp only [CollatzResearch.WordTrace]
  refine ⟨110352442527800765990521433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73568295018533843993680955 110352442527800765990521433)
  ·
    refine ⟨82764331895850574492891075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110352442527800765990521433 82764331895850574492891075)
    ·
      refine ⟨124146497843775861739336613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82764331895850574492891075 124146497843775861739336613)
      ·
        refine ⟨23277468345707974076125615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124146497843775861739336613 23277468345707974076125615)
        ·
          refine ⟨34916202518561961114188423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23277468345707974076125615 34916202518561961114188423)
          ·
            refine ⟨52374303777842941671282635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34916202518561961114188423 52374303777842941671282635)
            ·
              refine ⟨78561455666764412506923953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52374303777842941671282635 78561455666764412506923953)
              ·
                refine ⟨58921091750073309380192965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78561455666764412506923953 58921091750073309380192965)
                ·
                  refine ⟨11047704703138745508786181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58921091750073309380192965 11047704703138745508786181)
                  ·
                    refine ⟨2071444631838514782897409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11047704703138745508786181 2071444631838514782897409)
                    ·
                      refine ⟨1553583473878886087173057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071444631838514782897409 1553583473878886087173057)
                      ·
                        rfl

theorem cell23_3025593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_3025593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025593 prefixEnd_3025593 := by exact prefixLift 3025593
  have htrace : WordTrace (prefixWord ++ tailWord_3025593) baseStart_3025593 baseEnd_3025593 := by
    simpa [prefixWord, tailWord_3025593, baseEnd_3025593] using wordTrace_append hprefix tailTrace_3025593
  have hstable : (prefixWord ++ tailWord_3025593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025593).length < 2 ^ (prefixWord ++ tailWord_3025593).sum := by decide
  have hdescent : baseEnd_3025593 < baseStart_3025593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025633 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 6]
def baseStart_3025633 : Nat := 118140960795 + 3025633 * 2 ^ 59
def prefixEnd_3025633 : Nat := 4983230072969 + 3 ^ 40 * 3025633 * 2
def baseEnd_3025633 : Nat := 172622668122785103408097

theorem tailTrace_3025633 : CollatzResearch.WordTrace tailWord_3025633 prefixEnd_3025633 172622668122785103408097 := by
  unfold tailWord_3025633
  simp only [CollatzResearch.WordTrace]
  refine ⟨110353901447655852821977553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73569267631770568547985035 110353901447655852821977553)
  ·
    refine ⟨82765426085741889616483165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110353901447655852821977553 82765426085741889616483165)
    ·
      refine ⟨31037034782153208606181187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82765426085741889616483165 31037034782153208606181187)
      ·
        refine ⟨46555552173229812909271781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31037034782153208606181187 46555552173229812909271781)
        ·
          refine ⟨8729166032480589920488459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46555552173229812909271781 8729166032480589920488459)
          ·
            refine ⟨13093749048720884880732689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8729166032480589920488459 13093749048720884880732689)
            ·
              refine ⟨9820311786540663660549517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13093749048720884880732689 9820311786540663660549517)
              ·
                refine ⟨3682616919952748872706069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9820311786540663660549517 3682616919952748872706069)
                ·
                  refine ⟨172622668122785103408097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3682616919952748872706069 172622668122785103408097)
                  ·
                    rfl

theorem cell23_3025633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 6].length) (baseStart_3025633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025633 prefixEnd_3025633 := by exact prefixLift 3025633
  have htrace : WordTrace (prefixWord ++ tailWord_3025633) baseStart_3025633 baseEnd_3025633 := by
    simpa [prefixWord, tailWord_3025633, baseEnd_3025633] using wordTrace_append hprefix tailTrace_3025633
  have hstable : (prefixWord ++ tailWord_3025633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025633).length < 2 ^ (prefixWord ++ tailWord_3025633).sum := by decide
  have hdescent : baseEnd_3025633 < baseStart_3025633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025713 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3025713 : Nat := 118140960795 + 3025713 * 2 ^ 59
def prefixEnd_3025713 : Nat := 4983230072969 + 3 ^ 40 * 3025713 * 2
def baseEnd_3025713 : Nat := 1553645091557425617672505

theorem tailTrace_3025713 : CollatzResearch.WordTrace tailWord_3025713 prefixEnd_3025713 1553645091557425617672505 := by
  unfold tailWord_3025713
  simp only [CollatzResearch.WordTrace]
  refine ⟨110356819287366026484889793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73571212858244017656593195 110356819287366026484889793)
  ·
    refine ⟨82767614465524519863667345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110356819287366026484889793 82767614465524519863667345)
    ·
      refine ⟨62075710849143389897750509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82767614465524519863667345 62075710849143389897750509)
      ·
        refine ⟨23278391568428771211656441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62075710849143389897750509 23278391568428771211656441)
        ·
          refine ⟨17458793676321578408742331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23278391568428771211656441 17458793676321578408742331)
          ·
            refine ⟨26188190514482367613113497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17458793676321578408742331 26188190514482367613113497)
            ·
              refine ⟨19641142885861775709835123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26188190514482367613113497 19641142885861775709835123)
              ·
                refine ⟨29461714328792663564752685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19641142885861775709835123 29461714328792663564752685)
                ·
                  refine ⟨11048142873297248836782257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29461714328792663564752685 11048142873297248836782257)
                  ·
                    refine ⟨8286107154972936627586693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11048142873297248836782257 8286107154972936627586693)
                    ·
                      refine ⟨1553645091557425617672505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8286107154972936627586693 1553645091557425617672505)
                      ·
                        rfl

theorem cell23_3025713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3025713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025713 prefixEnd_3025713 := by exact prefixLift 3025713
  have htrace : WordTrace (prefixWord ++ tailWord_3025713) baseStart_3025713 baseEnd_3025713 := by
    simpa [prefixWord, tailWord_3025713, baseEnd_3025713] using wordTrace_append hprefix tailTrace_3025713
  have hstable : (prefixWord ++ tailWord_3025713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025713).length < 2 ^ (prefixWord ++ tailWord_3025713).sum := by decide
  have hdescent : baseEnd_3025713 < baseStart_3025713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025720 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_3025720 : Nat := 118140960795 + 3025720 * 2 ^ 59
def prefixEnd_3025720 : Nat := 4983230072969 + 3 ^ 40 * 3025720 * 2
def baseEnd_3025720 : Nat := 1553648685922007090284973

theorem tailTrace_3025720 : CollatzResearch.WordTrace tailWord_3025720 prefixEnd_3025720 1553648685922007090284973 := by
  unfold tailWord_3025720
  simp only [CollatzResearch.WordTrace]
  refine ⟨55178537299170333340197307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73571383065560444453596409 55178537299170333340197307)
  ·
    refine ⟨82767805948755500010295961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55178537299170333340197307 82767805948755500010295961)
    ·
      refine ⟨62075854461566625007721971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82767805948755500010295961 62075854461566625007721971)
      ·
        refine ⟨93113781692349937511582957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62075854461566625007721971 93113781692349937511582957)
        ·
          refine ⟨34917668134631226566843609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93113781692349937511582957 34917668134631226566843609)
          ·
            refine ⟨26188251100973419925132707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34917668134631226566843609 26188251100973419925132707)
            ·
              refine ⟨39282376651460129887699061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26188251100973419925132707 39282376651460129887699061)
              ·
                refine ⟨3682722811074387176971787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39282376651460129887699061 3682722811074387176971787)
                ·
                  refine ⟨5524084216611580765457681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682722811074387176971787 5524084216611580765457681)
                  ·
                    refine ⟨4143063162458685574093261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5524084216611580765457681 4143063162458685574093261)
                    ·
                      refine ⟨1553648685922007090284973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143063162458685574093261 1553648685922007090284973)
                      ·
                        rfl

theorem cell23_3025720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_3025720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025720 prefixEnd_3025720 := by exact prefixLift 3025720
  have htrace : WordTrace (prefixWord ++ tailWord_3025720) baseStart_3025720 baseEnd_3025720 := by
    simpa [prefixWord, tailWord_3025720, baseEnd_3025720] using wordTrace_append hprefix tailTrace_3025720
  have hstable : (prefixWord ++ tailWord_3025720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025720).length < 2 ^ (prefixWord ++ tailWord_3025720).sum := by decide
  have hdescent : baseEnd_3025720 < baseStart_3025720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025733 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_3025733 : Nat := 118140960795 + 3025733 * 2 ^ 59
def prefixEnd_3025733 : Nat := 4983230072969 + 3 ^ 40 * 3025733 * 2
def baseEnd_3025733 : Nat := 1553655361170515539422413

theorem tailTrace_3025733 : CollatzResearch.WordTrace tailWord_3025733 prefixEnd_3025733 1553655361170515539422413 := by
  unfold tailWord_3025733
  simp only [CollatzResearch.WordTrace]
  refine ⟨110357548747293569900617853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73571699164862379933745235 110357548747293569900617853)
  ·
    refine ⟨41384080780235088712731695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110357548747293569900617853 41384080780235088712731695)
    ·
      refine ⟨62076121170352633069097543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41384080780235088712731695 62076121170352633069097543)
      ·
        refine ⟨93114181755528949603646315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62076121170352633069097543 93114181755528949603646315)
        ·
          refine ⟨139671272633293424405469473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93114181755528949603646315 139671272633293424405469473)
          ·
            refine ⟨104753454474970068304102105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139671272633293424405469473 104753454474970068304102105)
            ·
              refine ⟨78565090856227551228076579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104753454474970068304102105 78565090856227551228076579)
              ·
                refine ⟨117847636284341326842114869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78565090856227551228076579 117847636284341326842114869)
                ·
                  refine ⟨11048215901656999391448269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117847636284341326842114869 11048215901656999391448269)
                  ·
                    refine ⟨4143080963121374771793101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11048215901656999391448269 4143080963121374771793101)
                    ·
                      refine ⟨1553655361170515539422413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143080963121374771793101 1553655361170515539422413)
                      ·
                        rfl

theorem cell23_3025733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_3025733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025733 prefixEnd_3025733 := by exact prefixLift 3025733
  have htrace : WordTrace (prefixWord ++ tailWord_3025733) baseStart_3025733 baseEnd_3025733 := by
    simpa [prefixWord, tailWord_3025733, baseEnd_3025733] using wordTrace_append hprefix tailTrace_3025733
  have hstable : (prefixWord ++ tailWord_3025733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025733).length < 2 ^ (prefixWord ++ tailWord_3025733).sum := by decide
  have hdescent : baseEnd_3025733 < baseStart_3025733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025800 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3025800 : Nat := 118140960795 + 3025800 * 2 ^ 59
def prefixEnd_3025800 : Nat := 4983230072969 + 3 ^ 40 * 3025800 * 2
def baseEnd_3025800 : Nat := 517896588124788925761535

theorem tailTrace_3025800 : CollatzResearch.WordTrace tailWord_3025800 prefixEnd_3025800 517896588124788925761535 := by
  unfold tailWord_3025800
  simp only [CollatzResearch.WordTrace]
  refine ⟨55179996219025420171653427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73573328292033893562204569 55179996219025420171653427)
  ·
    refine ⟨82769994328538130257480141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55179996219025420171653427 82769994328538130257480141)
    ·
      refine ⟨31038747873201798846555053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82769994328538130257480141 31038747873201798846555053)
      ·
        refine ⟨11639530452450674567458145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31038747873201798846555053 11639530452450674567458145)
        ·
          refine ⟨8729647839338005925593609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11639530452450674567458145 8729647839338005925593609)
          ·
            refine ⟨6547235879503504444195207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8729647839338005925593609 6547235879503504444195207)
            ·
              refine ⟨9820853819255256666292811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547235879503504444195207 9820853819255256666292811)
              ·
                refine ⟨14731280728882884999439217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9820853819255256666292811 14731280728882884999439217)
                ·
                  refine ⟨11048460546662163749579413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14731280728882884999439217 11048460546662163749579413)
                  ·
                    refine ⟨517896588124788925761535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11048460546662163749579413 517896588124788925761535)
                    ·
                      rfl

theorem cell23_3025800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3025800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025800 prefixEnd_3025800 := by exact prefixLift 3025800
  have htrace : WordTrace (prefixWord ++ tailWord_3025800) baseStart_3025800 baseEnd_3025800 := by
    simpa [prefixWord, tailWord_3025800, baseEnd_3025800] using wordTrace_append hprefix tailTrace_3025800
  have hstable : (prefixWord ++ tailWord_3025800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025800).length < 2 ^ (prefixWord ++ tailWord_3025800).sum := by decide
  have hdescent : baseEnd_3025800 < baseStart_3025800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025803 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4]
def baseStart_3025803 : Nat := 118140960795 + 3025803 * 2 ^ 59
def prefixEnd_3025803 : Nat := 4983230072969 + 3 ^ 40 * 3025803 * 2
def baseEnd_3025803 : Nat := 1553691304816330265547091

theorem tailTrace_3025803 : CollatzResearch.WordTrace tailWord_3025803 prefixEnd_3025803 1553691304816330265547091 := by
  unfold tailWord_3025803
  simp only [CollatzResearch.WordTrace]
  refine ⟨110360101857039971855666063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73573401238026647903777375 110360101857039971855666063)
  ·
    refine ⟨165540152785559957783499095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110360101857039971855666063 165540152785559957783499095)
    ·
      refine ⟨248310229178339936675248643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165540152785559957783499095 248310229178339936675248643)
      ·
        refine ⟨372465343767509905012872965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248310229178339936675248643 372465343767509905012872965)
        ·
          refine ⟨69837251956408107189913681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372465343767509905012872965 69837251956408107189913681)
          ·
            refine ⟨52377938967306080392435261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69837251956408107189913681 52377938967306080392435261)
            ·
              refine ⟨19641727112739780147163223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52377938967306080392435261 19641727112739780147163223)
              ·
                refine ⟨29462590669109670220744835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19641727112739780147163223 29462590669109670220744835)
                ·
                  refine ⟨44193886003664505331117253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29462590669109670220744835 44193886003664505331117253)
                  ·
                    refine ⟨8286353625687094749584485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44193886003664505331117253 8286353625687094749584485)
                    ·
                      refine ⟨1553691304816330265547091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8286353625687094749584485 1553691304816330265547091)
                      ·
                        rfl

theorem cell23_3025803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_3025803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025803 prefixEnd_3025803 := by exact prefixLift 3025803
  have htrace : WordTrace (prefixWord ++ tailWord_3025803) baseStart_3025803 baseEnd_3025803 := by
    simpa [prefixWord, tailWord_3025803, baseEnd_3025803] using wordTrace_append hprefix tailTrace_3025803
  have hstable : (prefixWord ++ tailWord_3025803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025803).length < 2 ^ (prefixWord ++ tailWord_3025803).sum := by decide
  have hdescent : baseEnd_3025803 < baseStart_3025803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025813 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 9]
def baseStart_3025813 : Nat := 118140960795 + 3025813 * 2 ^ 59
def prefixEnd_3025813 : Nat := 4983230072969 + 3 ^ 40 * 3025813 * 2
def baseEnd_3025813 : Nat := 172632937735875025158005

theorem tailTrace_3025813 : CollatzResearch.WordTrace tailWord_3025813 prefixEnd_3025813 172632937735875025158005 := by
  unfold tailWord_3025813
  simp only [CollatzResearch.WordTrace]
  refine ⟨110360466587003743563530093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73573644391335829042353395 110360466587003743563530093)
  ·
    refine ⟨41385174970126403836323785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110360466587003743563530093 41385174970126403836323785)
    ·
      refine ⟨31038881227594802877242839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41385174970126403836323785 31038881227594802877242839)
      ·
        refine ⟨46558321841392204315864259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31038881227594802877242839 46558321841392204315864259)
        ·
          refine ⟨69837482762088306473796389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46558321841392204315864259 69837482762088306473796389)
          ·
            refine ⟨13094528017891557463836823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69837482762088306473796389 13094528017891557463836823)
            ·
              refine ⟨19641792026837336195755235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13094528017891557463836823 19641792026837336195755235)
              ·
                refine ⟨29462688040256004293632853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19641792026837336195755235 29462688040256004293632853)
                ·
                  refine ⟨172632937735875025158005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29462688040256004293632853 172632937735875025158005)
                  ·
                    rfl

theorem cell23_3025813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_3025813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025813 prefixEnd_3025813 := by exact prefixLift 3025813
  have htrace : WordTrace (prefixWord ++ tailWord_3025813) baseStart_3025813 baseEnd_3025813 := by
    simpa [prefixWord, tailWord_3025813, baseEnd_3025813] using wordTrace_append hprefix tailTrace_3025813
  have hstable : (prefixWord ++ tailWord_3025813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025813).length < 2 ^ (prefixWord ++ tailWord_3025813).sum := by decide
  have hdescent : baseEnd_3025813 < baseStart_3025813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025862 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3025862 : Nat := 118140960795 + 3025862 * 2 ^ 59
def prefixEnd_3025862 : Nat := 4983230072969 + 3 ^ 40 * 3025862 * 2
def baseEnd_3025862 : Nat := 1553721600174945534709321

theorem tailTrace_3025862 : CollatzResearch.WordTrace tailWord_3025862 prefixEnd_3025862 1553721600174945534709321 := by
  unfold tailWord_3025862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448820430119569529126995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73574835842550816621375893 3448820430119569529126995)
  ·
    refine ⟨5173230645179354293690493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3448820430119569529126995 5173230645179354293690493)
    ·
      refine ⟨1939961491942257860133935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5173230645179354293690493 1939961491942257860133935)
      ·
        refine ⟨2909942237913386790200903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939961491942257860133935 2909942237913386790200903)
        ·
          refine ⟨4364913356870080185301355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909942237913386790200903 4364913356870080185301355)
          ·
            refine ⟨6547370035305120277952033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364913356870080185301355 6547370035305120277952033)
            ·
              refine ⟨4910527526478840208464025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6547370035305120277952033 4910527526478840208464025)
              ·
                refine ⟨3682895644859130156348019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910527526478840208464025 3682895644859130156348019)
                ·
                  refine ⟨5524343467288695234522029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682895644859130156348019 5524343467288695234522029)
                  ·
                    refine ⟨2071628800233260712945761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5524343467288695234522029 2071628800233260712945761)
                    ·
                      refine ⟨1553721600174945534709321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071628800233260712945761 1553721600174945534709321)
                      ·
                        rfl

theorem cell23_3025862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3025862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025862 prefixEnd_3025862 := by exact prefixLift 3025862
  have htrace : WordTrace (prefixWord ++ tailWord_3025862) baseStart_3025862 baseEnd_3025862 := by
    simpa [prefixWord, tailWord_3025862, baseEnd_3025862] using wordTrace_append hprefix tailTrace_3025862
  have hstable : (prefixWord ++ tailWord_3025862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025862).length < 2 ^ (prefixWord ++ tailWord_3025862).sum := by decide
  have hdescent : baseEnd_3025862 < baseStart_3025862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025873 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_3025873 : Nat := 118140960795 + 3025873 * 2 ^ 59
def prefixEnd_3025873 : Nat := 4983230072969 + 3 ^ 40 * 3025873 * 2
def baseEnd_3025873 : Nat := 517909082820714997223923

theorem tailTrace_3025873 : CollatzResearch.WordTrace tailWord_3025873 prefixEnd_3025873 517909082820714997223923 := by
  unfold tailWord_3025873
  simp only [CollatzResearch.WordTrace]
  refine ⟨110362654966786373810714273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73575103311190915873809515 110362654966786373810714273)
  ·
    refine ⟨82771991225089780358035705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110362654966786373810714273 82771991225089780358035705)
    ·
      refine ⟨62078993418817335268526779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82771991225089780358035705 62078993418817335268526779)
      ·
        refine ⟨93118490128226002902790169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62078993418817335268526779 93118490128226002902790169)
        ·
          refine ⟨69838867596169502177092627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93118490128226002902790169 69838867596169502177092627)
          ·
            refine ⟨104758301394254253265638941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69838867596169502177092627 104758301394254253265638941)
            ·
              refine ⟨39284363022845344974614603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104758301394254253265638941 39284363022845344974614603)
              ·
                refine ⟨58926544534268017461921905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39284363022845344974614603 58926544534268017461921905)
                ·
                  refine ⟨44194908400701013096441429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58926544534268017461921905 44194908400701013096441429)
                  ·
                    refine ⟨517909082820714997223923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44194908400701013096441429 517909082820714997223923)
                    ·
                      rfl

theorem cell23_3025873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_3025873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025873 prefixEnd_3025873 := by exact prefixLift 3025873
  have htrace : WordTrace (prefixWord ++ tailWord_3025873) baseStart_3025873 baseEnd_3025873 := by
    simpa [prefixWord, tailWord_3025873, baseEnd_3025873] using wordTrace_append hprefix tailTrace_3025873
  have hstable : (prefixWord ++ tailWord_3025873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025873).length < 2 ^ (prefixWord ++ tailWord_3025873).sum := by decide
  have hdescent : baseEnd_3025873 < baseStart_3025873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025880 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3025880 : Nat := 118140960795 + 3025880 * 2 ^ 59
def prefixEnd_3025880 : Nat := 4983230072969 + 3 ^ 40 * 3025880 * 2
def baseEnd_3025880 : Nat := 1553730842826726464284237

theorem tailTrace_3025880 : CollatzResearch.WordTrace tailWord_3025880 prefixEnd_3025880 1553730842826726464284237 := by
  unfold tailWord_3025880
  simp only [CollatzResearch.WordTrace]
  refine ⟨55181455138880507003109547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73575273518507342670812729 55181455138880507003109547)
  ·
    refine ⟨82772182708320760504664321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55181455138880507003109547 82772182708320760504664321)
    ·
      refine ⟨62079137031240570378498241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82772182708320760504664321 62079137031240570378498241)
      ·
        refine ⟨46559352773430427783873681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62079137031240570378498241 46559352773430427783873681)
        ·
          refine ⟨34919514580072820837905261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46559352773430427783873681 34919514580072820837905261)
          ·
            refine ⟨13094817967527307814214473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34919514580072820837905261 13094817967527307814214473)
            ·
              refine ⟨9821113475645480860660855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13094817967527307814214473 9821113475645480860660855)
              ·
                refine ⟨14731670213468221290991283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9821113475645480860660855 14731670213468221290991283)
                ·
                  refine ⟨22097505320202331936486925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14731670213468221290991283 22097505320202331936486925)
                  ·
                    refine ⟨8286564495075874476182597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22097505320202331936486925 8286564495075874476182597)
                    ·
                      refine ⟨1553730842826726464284237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8286564495075874476182597 1553730842826726464284237)
                      ·
                        rfl

theorem cell23_3025880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3025880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025880 prefixEnd_3025880 := by exact prefixLift 3025880
  have htrace : WordTrace (prefixWord ++ tailWord_3025880) baseStart_3025880 baseEnd_3025880 := by
    simpa [prefixWord, tailWord_3025880, baseEnd_3025880] using wordTrace_append hprefix tailTrace_3025880
  have hstable : (prefixWord ++ tailWord_3025880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025880).length < 2 ^ (prefixWord ++ tailWord_3025880).sum := by decide
  have hdescent : baseEnd_3025880 < baseStart_3025880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025934 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3025934 : Nat := 118140960795 + 3025934 * 2 ^ 59
def prefixEnd_3025934 : Nat := 4983230072969 + 3 ^ 40 * 3025934 * 2
def baseEnd_3025934 : Nat := 1553758570782069253008989

theorem tailTrace_3025934 : CollatzResearch.WordTrace tailWord_3025934 prefixEnd_3025934 1553758570782069253008989 := by
  unfold tailWord_3025934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795609977445672653585607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73576586546376920819123237 13795609977445672653585607)
  ·
    refine ⟨20693414966168508980378411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13795609977445672653585607 20693414966168508980378411)
    ·
      refine ⟨31040122449252763470567617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20693414966168508980378411 31040122449252763470567617)
      ·
        refine ⟨23280091836939572602925713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31040122449252763470567617 23280091836939572602925713)
        ·
          refine ⟨17460068877704679452194285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23280091836939572602925713 17460068877704679452194285)
          ·
            refine ⟨6547525829139254794572857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17460068877704679452194285 6547525829139254794572857)
            ·
              refine ⟨4910644371854441095929643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6547525829139254794572857 4910644371854441095929643)
              ·
                refine ⟨7365966557781661643894465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910644371854441095929643 7365966557781661643894465)
                ·
                  refine ⟨5524474918336246232920849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7365966557781661643894465 5524474918336246232920849)
                  ·
                    refine ⟨4143356188752184674690637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5524474918336246232920849 4143356188752184674690637)
                    ·
                      refine ⟨1553758570782069253008989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143356188752184674690637 1553758570782069253008989)
                      ·
                        rfl

theorem cell23_3025934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3025934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025934 prefixEnd_3025934 := by exact prefixLift 3025934
  have htrace : WordTrace (prefixWord ++ tailWord_3025934) baseStart_3025934 baseEnd_3025934 := by
    simpa [prefixWord, tailWord_3025934, baseEnd_3025934] using wordTrace_append hprefix tailTrace_3025934
  have hstable : (prefixWord ++ tailWord_3025934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025934).length < 2 ^ (prefixWord ++ tailWord_3025934).sum := by decide
  have hdescent : baseEnd_3025934 < baseStart_3025934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025987 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 4]
def baseStart_3025987 : Nat := 118140960795 + 3025987 * 2 ^ 59
def prefixEnd_3025987 : Nat := 4983230072969 + 3 ^ 40 * 3025987 * 2
def baseEnd_3025987 : Nat := 1553785785256757545646245

theorem tailTrace_3025987 : CollatzResearch.WordTrace tailWord_3025987 prefixEnd_3025987 1553785785256757545646245 := by
  unfold tailWord_3025987
  simp only [CollatzResearch.WordTrace]
  refine ⟨110366812888373371280364215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73577875258915580853576143 110366812888373371280364215)
  ·
    refine ⟨165550219332560056920546323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110366812888373371280364215 165550219332560056920546323)
    ·
      refine ⟨248325328998840085380819485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165550219332560056920546323 248325328998840085380819485)
      ·
        refine ⟨93121998374565032017807307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248325328998840085380819485 93121998374565032017807307)
        ·
          refine ⟨139682997561847548026710961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93121998374565032017807307 139682997561847548026710961)
          ·
            refine ⟨104762248171385661020033221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139682997561847548026710961 104762248171385661020033221)
            ·
              refine ⟨19642921532134811441256229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104762248171385661020033221 19642921532134811441256229)
              ·
                refine ⟨3683047787275277145235543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19642921532134811441256229 3683047787275277145235543)
                ·
                  refine ⟨5524571680912915717853315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683047787275277145235543 5524571680912915717853315)
                  ·
                    refine ⟨8286857521369373576779973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5524571680912915717853315 8286857521369373576779973)
                    ·
                      refine ⟨1553785785256757545646245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8286857521369373576779973 1553785785256757545646245)
                      ·
                        rfl

theorem cell23_3025987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_3025987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025987 prefixEnd_3025987 := by exact prefixLift 3025987
  have htrace : WordTrace (prefixWord ++ tailWord_3025987) baseStart_3025987 baseEnd_3025987 := by
    simpa [prefixWord, tailWord_3025987, baseEnd_3025987] using wordTrace_append hprefix tailTrace_3025987
  have hstable : (prefixWord ++ tailWord_3025987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025987).length < 2 ^ (prefixWord ++ tailWord_3025987).sum := by decide
  have hdescent : baseEnd_3025987 < baseStart_3025987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3025991 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_3025991 : Nat := 118140960795 + 3025991 * 2 ^ 59
def prefixEnd_3025991 : Nat := 4983230072969 + 3 ^ 40 * 3025991 * 2
def baseEnd_3025991 : Nat := 1553787839179375529996227

theorem tailTrace_3025991 : CollatzResearch.WordTrace tailWord_3025991 prefixEnd_3025991 1553787839179375529996227 := by
  unfold tailWord_3025991
  simp only [CollatzResearch.WordTrace]
  refine ⟨110366958780358879963509827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73577972520239253309006551 110366958780358879963509827)
  ·
    refine ⟨165550438170538319945264741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110366958780358879963509827 165550438170538319945264741)
    ·
      refine ⟨31040707156975934989737139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165550438170538319945264741 31040707156975934989737139)
      ·
        refine ⟨46561060735463902484605709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31040707156975934989737139 46561060735463902484605709)
        ·
          refine ⟨17460397775798963431727141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46561060735463902484605709 17460397775798963431727141)
          ·
            refine ⟨3273824582962305643448839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17460397775798963431727141 3273824582962305643448839)
            ·
              refine ⟨4910736874443458465173259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273824582962305643448839 4910736874443458465173259)
              ·
                refine ⟨7366105311665187697759889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910736874443458465173259 7366105311665187697759889)
                ·
                  refine ⟨5524578983748890773319917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7366105311665187697759889 5524578983748890773319917)
                  ·
                    refine ⟨2071717118905834039994969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5524578983748890773319917 2071717118905834039994969)
                    ·
                      refine ⟨1553787839179375529996227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071717118905834039994969 1553787839179375529996227)
                      ·
                        rfl

theorem cell23_3025991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_3025991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3025991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3025991 prefixEnd_3025991 := by exact prefixLift 3025991
  have htrace : WordTrace (prefixWord ++ tailWord_3025991) baseStart_3025991 baseEnd_3025991 := by
    simpa [prefixWord, tailWord_3025991, baseEnd_3025991] using wordTrace_append hprefix tailTrace_3025991
  have hstable : (prefixWord ++ tailWord_3025991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3025991).length < 2 ^ (prefixWord ++ tailWord_3025991).sum := by decide
  have hdescent : baseEnd_3025991 < baseStart_3025991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3025991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026020 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_3026020 : Nat := 118140960795 + 3026020 * 2 ^ 59
def prefixEnd_3026020 : Nat := 4983230072969 + 3 ^ 40 * 3026020 * 2
def baseEnd_3026020 : Nat := 1553802730118355916533593

theorem tailTrace_3026020 : CollatzResearch.WordTrace tailWord_3026020 prefixEnd_3026020 1553802730118355916533593 := by
  unfold tailWord_3026020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55184008248626908958157757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73578677664835878610877009 55184008248626908958157757)
  ·
    refine ⟨20694003093235090859309159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55184008248626908958157757 20694003093235090859309159)
    ·
      refine ⟨31041004639852636288963739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20694003093235090859309159 31041004639852636288963739)
      ·
        refine ⟨46561506959778954433445609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31041004639852636288963739 46561506959778954433445609)
        ·
          refine ⟨34921130219834215825084207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46561506959778954433445609 34921130219834215825084207)
          ·
            refine ⟨52381695329751323737626311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34921130219834215825084207 52381695329751323737626311)
            ·
              refine ⟨78572542994626985606439467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52381695329751323737626311 78572542994626985606439467)
              ·
                refine ⟨117858814491940478409659201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78572542994626985606439467 117858814491940478409659201)
                ·
                  refine ⟨88394110868955358807244401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117858814491940478409659201 88394110868955358807244401)
                  ·
                    refine ⟨66295583151716519105433301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88394110868955358807244401 66295583151716519105433301)
                    ·
                      refine ⟨1553802730118355916533593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66295583151716519105433301 1553802730118355916533593)
                      ·
                        rfl

theorem cell23_3026020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_3026020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026020 prefixEnd_3026020 := by exact prefixLift 3026020
  have htrace : WordTrace (prefixWord ++ tailWord_3026020) baseStart_3026020 baseEnd_3026020 := by
    simpa [prefixWord, tailWord_3026020, baseEnd_3026020] using wordTrace_append hprefix tailTrace_3026020
  have hstable : (prefixWord ++ tailWord_3026020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026020).length < 2 ^ (prefixWord ++ tailWord_3026020).sum := by decide
  have hdescent : baseEnd_3026020 < baseStart_3026020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026021 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 3, 2, 2]
def baseStart_3026021 : Nat := 118140960795 + 3026021 * 2 ^ 59
def prefixEnd_3026021 : Nat := 4983230072969 + 3 ^ 40 * 3026021 * 2
def baseEnd_3026021 : Nat := 1553803243599010412621089

theorem tailTrace_3026021 : CollatzResearch.WordTrace tailWord_3026021 prefixEnd_3026021 1553803243599010412621089 := by
  unfold tailWord_3026021
  simp only [CollatzResearch.WordTrace]
  refine ⟨110368052970250195087101917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73578701980166796724734611 110368052970250195087101917)
  ·
    refine ⟨41388019863843823157663219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110368052970250195087101917 41388019863843823157663219)
    ·
      refine ⟨62082029795765734736494829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41388019863843823157663219 62082029795765734736494829)
      ·
        refine ⟨23280761173412150526185561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62082029795765734736494829 23280761173412150526185561)
        ·
          refine ⟨17460570880059112894639171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23280761173412150526185561 17460570880059112894639171)
          ·
            refine ⟨26190856320088669341958757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17460570880059112894639171 26190856320088669341958757)
            ·
              refine ⟨4910785560016625501617267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26190856320088669341958757 4910785560016625501617267)
              ·
                refine ⟨7366178340024938252425901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910785560016625501617267 7366178340024938252425901)
                ·
                  refine ⟨2762316877509351844659713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7366178340024938252425901 2762316877509351844659713)
                  ·
                    refine ⟨2071737658132013883494785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2762316877509351844659713 2071737658132013883494785)
                    ·
                      refine ⟨1553803243599010412621089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071737658132013883494785 1553803243599010412621089)
                      ·
                        rfl

theorem cell23_3026021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_3026021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026021 prefixEnd_3026021 := by exact prefixLift 3026021
  have htrace : WordTrace (prefixWord ++ tailWord_3026021) baseStart_3026021 baseEnd_3026021 := by
    simpa [prefixWord, tailWord_3026021, baseEnd_3026021] using wordTrace_append hprefix tailTrace_3026021
  have hstable : (prefixWord ++ tailWord_3026021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026021).length < 2 ^ (prefixWord ++ tailWord_3026021).sum := by decide
  have hdescent : baseEnd_3026021 < baseStart_3026021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026040 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_3026040 : Nat := 118140960795 + 3026040 * 2 ^ 59
def prefixEnd_3026040 : Nat := 4983230072969 + 3 ^ 40 * 3026040 * 2
def baseEnd_3026040 : Nat := 517937666577148612761167

theorem tailTrace_3026040 : CollatzResearch.WordTrace tailWord_3026040 prefixEnd_3026040 517937666577148612761167 := by
  unfold tailWord_3026040
  simp only [CollatzResearch.WordTrace]
  refine ⟨55184372978590680666021787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73579163971454240888029049 55184372978590680666021787)
  ·
    refine ⟨82776559467886020999032681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55184372978590680666021787 82776559467886020999032681)
    ·
      refine ⟨62082419600914515749274511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82776559467886020999032681 62082419600914515749274511)
      ·
        refine ⟨93123629401371773623911767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62082419600914515749274511 93123629401371773623911767)
        ·
          refine ⟨139685444102057660435867651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93123629401371773623911767 139685444102057660435867651)
          ·
            refine ⟨209528166153086490653801477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139685444102057660435867651 209528166153086490653801477)
            ·
              refine ⟨39286531153703716997587777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209528166153086490653801477 39286531153703716997587777)
              ·
                refine ⟨29464898365277787748190833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39286531153703716997587777 29464898365277787748190833)
                ·
                  refine ⟨22098673773958340811143125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29464898365277787748190833 22098673773958340811143125)
                  ·
                    refine ⟨517937666577148612761167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22098673773958340811143125 517937666577148612761167)
                    ·
                      rfl

theorem cell23_3026040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_3026040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026040 prefixEnd_3026040 := by exact prefixLift 3026040
  have htrace : WordTrace (prefixWord ++ tailWord_3026040) baseStart_3026040 baseEnd_3026040 := by
    simpa [prefixWord, tailWord_3026040, baseEnd_3026040] using wordTrace_append hprefix tailTrace_3026040
  have hstable : (prefixWord ++ tailWord_3026040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026040).length < 2 ^ (prefixWord ++ tailWord_3026040).sum := by decide
  have hdescent : baseEnd_3026040 < baseStart_3026040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026041 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 3]
def baseStart_3026041 : Nat := 118140960795 + 3026041 * 2 ^ 59
def prefixEnd_3026041 : Nat := 4983230072969 + 3 ^ 40 * 3026041 * 2
def baseEnd_3026041 : Nat := 1553813513212100334370997

theorem tailTrace_3026041 : CollatzResearch.WordTrace tailWord_3026041 prefixEnd_3026041 1553813513212100334370997 := by
  unfold tailWord_3026041
  simp only [CollatzResearch.WordTrace]
  refine ⟨110368782430177738502829977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73579188286785159001886651 110368782430177738502829977)
  ·
    refine ⟨82776586822633303877122483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110368782430177738502829977 82776586822633303877122483)
    ·
      refine ⟨124164880233949955815683725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82776586822633303877122483 124164880233949955815683725)
      ·
        refine ⟨46561830087731233430881397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124164880233949955815683725 46561830087731233430881397)
        ·
          refine ⟨4365171570724803134145131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46561830087731233430881397 4365171570724803134145131)
          ·
            refine ⟨6547757356087204701217697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4365171570724803134145131 6547757356087204701217697)
            ·
              refine ⟨4910818017065403525913273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6547757356087204701217697 4910818017065403525913273)
              ·
                refine ⟨3683113512799052644434955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910818017065403525913273 3683113512799052644434955)
                ·
                  refine ⟨5524670269198578966652433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683113512799052644434955 5524670269198578966652433)
                  ·
                    refine ⟨4143502701898934224989325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5524670269198578966652433 4143502701898934224989325)
                    ·
                      refine ⟨1553813513212100334370997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143502701898934224989325 1553813513212100334370997)
                      ·
                        rfl

theorem cell23_3026041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_3026041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026041 prefixEnd_3026041 := by exact prefixLift 3026041
  have htrace : WordTrace (prefixWord ++ tailWord_3026041) baseStart_3026041 baseEnd_3026041 := by
    simpa [prefixWord, tailWord_3026041, baseEnd_3026041] using wordTrace_append hprefix tailTrace_3026041
  have hstable : (prefixWord ++ tailWord_3026041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026041).length < 2 ^ (prefixWord ++ tailWord_3026041).sum := by decide
  have hdescent : baseEnd_3026041 < baseStart_3026041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 7, 2]
def baseStart_3026047 : Nat := 118140960795 + 3026047 * 2 ^ 59
def prefixEnd_3026047 : Nat := 4983230072969 + 3 ^ 40 * 3026047 * 2
def baseEnd_3026047 : Nat := 1553816594096027310895969

theorem tailTrace_3026047 : CollatzResearch.WordTrace tailWord_3026047 prefixEnd_3026047 1553816594096027310895969 := by
  unfold tailWord_3026047
  simp only [CollatzResearch.WordTrace]
  refine ⟨110369001268156001527548395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73579334178770667685032263 110369001268156001527548395)
  ·
    refine ⟨165553501902234002291322593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110369001268156001527548395 165553501902234002291322593)
    ·
      refine ⟨124165126426675501718491945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165553501902234002291322593 124165126426675501718491945)
      ·
        refine ⟨93123844820006626288868959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124165126426675501718491945 93123844820006626288868959)
        ·
          refine ⟨139685767230009939433303439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93123844820006626288868959 139685767230009939433303439)
          ·
            refine ⟨209528650845014909149955159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139685767230009939433303439 209528650845014909149955159)
            ·
              refine ⟨314292976267522363724932739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209528650845014909149955159 314292976267522363724932739)
              ·
                refine ⟨471439464401283545587399109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314292976267522363724932739 471439464401283545587399109)
                ·
                  refine ⟨88394899575240664797637333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471439464401283545587399109 88394899575240664797637333)
                  ·
                    refine ⟨2071755458794703081194625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 88394899575240664797637333 2071755458794703081194625)
                    ·
                      refine ⟨1553816594096027310895969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071755458794703081194625 1553816594096027310895969)
                      ·
                        rfl

theorem cell23_3026047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_3026047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026047 prefixEnd_3026047 := by exact prefixLift 3026047
  have htrace : WordTrace (prefixWord ++ tailWord_3026047) baseStart_3026047 baseEnd_3026047 := by
    simpa [prefixWord, tailWord_3026047, baseEnd_3026047] using wordTrace_append hprefix tailTrace_3026047
  have hstable : (prefixWord ++ tailWord_3026047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026047).length < 2 ^ (prefixWord ++ tailWord_3026047).sum := by decide
  have hdescent : baseEnd_3026047 < baseStart_3026047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026060 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3026060 : Nat := 118140960795 + 3026060 * 2 ^ 59
def prefixEnd_3026060 : Nat := 4983230072969 + 3 ^ 40 * 3026060 * 2
def baseEnd_3026060 : Nat := 1553823269344535760033409

theorem tailTrace_3026060 : CollatzResearch.WordTrace tailWord_3026060 prefixEnd_3026060 1553823269344535760033409 := by
  unfold tailWord_3026060
  simp only [CollatzResearch.WordTrace]
  refine ⟨55184737708554452373885817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73579650278072603165181089 55184737708554452373885817)
  ·
    refine ⟨41388553281415839280414363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55184737708554452373885817 41388553281415839280414363)
    ·
      refine ⟨62082829922123758920621545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41388553281415839280414363 62082829922123758920621545)
      ·
        refine ⟨46562122441592819190466159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62082829922123758920621545 46562122441592819190466159)
        ·
          refine ⟨69843183662389228785699239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46562122441592819190466159 69843183662389228785699239)
          ·
            refine ⟨104764775493583843178548859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69843183662389228785699239 104764775493583843178548859)
            ·
              refine ⟨157147163240375764767823289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104764775493583843178548859 157147163240375764767823289)
              ·
                refine ⟨117860372430281823575867467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157147163240375764767823289 117860372430281823575867467)
                ·
                  refine ⟨176790558645422735363801201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117860372430281823575867467 176790558645422735363801201)
                  ·
                    refine ⟨132592918984067051522850901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176790558645422735363801201 132592918984067051522850901)
                    ·
                      refine ⟨1553823269344535760033409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 132592918984067051522850901 1553823269344535760033409)
                      ·
                        rfl

theorem cell23_3026060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3026060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026060 prefixEnd_3026060 := by exact prefixLift 3026060
  have htrace : WordTrace (prefixWord ++ tailWord_3026060) baseStart_3026060 baseEnd_3026060 := by
    simpa [prefixWord, tailWord_3026060, baseEnd_3026060] using wordTrace_append hprefix tailTrace_3026060
  have hstable : (prefixWord ++ tailWord_3026060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026060).length < 2 ^ (prefixWord ++ tailWord_3026060).sum := by decide
  have hdescent : baseEnd_3026060 < baseStart_3026060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026077 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3026077 : Nat := 118140960795 + 3026077 * 2 ^ 59
def prefixEnd_3026077 : Nat := 4983230072969 + 3 ^ 40 * 3026077 * 2
def baseEnd_3026077 : Nat := 1553831998515662193520831

theorem tailTrace_3026077 : CollatzResearch.WordTrace tailWord_3026077 prefixEnd_3026077 1553831998515662193520831 := by
  unfold tailWord_3026077
  simp only [CollatzResearch.WordTrace]
  refine ⟨110370095458047316651140485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73580063638698211100760323 110370095458047316651140485)
  ·
    refine ⟨20694392898383871872088841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110370095458047316651140485 20694392898383871872088841)
    ·
      refine ⟨15520794673787903904066631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20694392898383871872088841 15520794673787903904066631)
      ·
        refine ⟨23281192010681855856099947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15520794673787903904066631 23281192010681855856099947)
        ·
          refine ⟨34921788016022783784149921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23281192010681855856099947 34921788016022783784149921)
          ·
            refine ⟨26191341012017087838112441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34921788016022783784149921 26191341012017087838112441)
            ·
              refine ⟨19643505759012815878584331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26191341012017087838112441 19643505759012815878584331)
              ·
                refine ⟨29465258638519223817876497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19643505759012815878584331 29465258638519223817876497)
                ·
                  refine ⟨22098943978889417863407373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29465258638519223817876497 22098943978889417863407373)
                  ·
                    refine ⟨8287103992083531698777765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22098943978889417863407373 8287103992083531698777765)
                    ·
                      refine ⟨1553831998515662193520831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8287103992083531698777765 1553831998515662193520831)
                      ·
                        rfl

theorem cell23_3026077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3026077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026077 prefixEnd_3026077 := by exact prefixLift 3026077
  have htrace : WordTrace (prefixWord ++ tailWord_3026077) baseStart_3026077 baseEnd_3026077 := by
    simpa [prefixWord, tailWord_3026077, baseEnd_3026077] using wordTrace_append hprefix tailTrace_3026077
  have hstable : (prefixWord ++ tailWord_3026077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026077).length < 2 ^ (prefixWord ++ tailWord_3026077).sum := by decide
  have hdescent : baseEnd_3026077 < baseStart_3026077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026098 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_3026098 : Nat := 118140960795 + 3026098 * 2 ^ 59
def prefixEnd_3026098 : Nat := 4983230072969 + 3 ^ 40 * 3026098 * 2
def baseEnd_3026098 : Nat := 1553842781609406611358235

theorem tailTrace_3026098 : CollatzResearch.WordTrace tailWord_3026098 prefixEnd_3026098 1553842781609406611358235 := by
  unfold tailWord_3026098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27592715347742809309413737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73580574260647491491769965 27592715347742809309413737)
  ·
    refine ⟨20694536510807106982060303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27592715347742809309413737 20694536510807106982060303)
    ·
      refine ⟨31041804766210660473090455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20694536510807106982060303 31041804766210660473090455)
      ·
        refine ⟨46562707149315990709635683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31041804766210660473090455 46562707149315990709635683)
        ·
          refine ⟨69844060723973986064453525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46562707149315990709635683 69844060723973986064453525)
          ·
            refine ⟨3273940346436280596771259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69844060723973986064453525 3273940346436280596771259)
            ·
              refine ⟨4910910519654420895156889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273940346436280596771259 4910910519654420895156889)
              ·
                refine ⟨3683182889740815671367667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910910519654420895156889 3683182889740815671367667)
                ·
                  refine ⟨5524774334611223507051501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683182889740815671367667 5524774334611223507051501)
                  ·
                    refine ⟨2071790375479208815144313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5524774334611223507051501 2071790375479208815144313)
                    ·
                      refine ⟨1553842781609406611358235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2071790375479208815144313 1553842781609406611358235)
                      ·
                        rfl

theorem cell23_3026098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_3026098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026098 prefixEnd_3026098 := by exact prefixLift 3026098
  have htrace : WordTrace (prefixWord ++ tailWord_3026098) baseStart_3026098 baseEnd_3026098 := by
    simpa [prefixWord, tailWord_3026098, baseEnd_3026098] using wordTrace_append hprefix tailTrace_3026098
  have hstable : (prefixWord ++ tailWord_3026098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026098).length < 2 ^ (prefixWord ++ tailWord_3026098).sum := by decide
  have hdescent : baseEnd_3026098 < baseStart_3026098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026141 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3026141 : Nat := 118140960795 + 3026141 * 2 ^ 59
def prefixEnd_3026141 : Nat := 4983230072969 + 3 ^ 40 * 3026141 * 2
def baseEnd_3026141 : Nat := 1553864861277549943120537

theorem tailTrace_3026141 : CollatzResearch.WordTrace tailWord_3026141 prefixEnd_3026141 1553864861277549943120537 := by
  unfold tailWord_3026141
  simp only [CollatzResearch.WordTrace]
  refine ⟨110372429729815455581470277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73581619819876970387646851 110372429729815455581470277)
  ·
    refine ⟨20694830574340397921525677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110372429729815455581470277 20694830574340397921525677)
    ·
      refine ⟨7760561465377649220572129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20694830574340397921525677 7760561465377649220572129)
      ·
        refine ⟨5820421099033236915429097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7760561465377649220572129 5820421099033236915429097)
        ·
          refine ⟨4365315824274927686571823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5820421099033236915429097 4365315824274927686571823)
          ·
            refine ⟨6547973736412391529857735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4365315824274927686571823 6547973736412391529857735)
            ·
              refine ⟨9821960604618587294786603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547973736412391529857735 9821960604618587294786603)
              ·
                refine ⟨14732940906927880942179905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9821960604618587294786603 14732940906927880942179905)
                ·
                  refine ⟨11049705680195910706634929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14732940906927880942179905 11049705680195910706634929)
                  ·
                    refine ⟨8287279260146933029976197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11049705680195910706634929 8287279260146933029976197)
                    ·
                      refine ⟨1553864861277549943120537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8287279260146933029976197 1553864861277549943120537)
                      ·
                        rfl

theorem cell23_3026141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3026141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026141 prefixEnd_3026141 := by exact prefixLift 3026141
  have htrace : WordTrace (prefixWord ++ tailWord_3026141) baseStart_3026141 baseEnd_3026141 := by
    simpa [prefixWord, tailWord_3026141, baseEnd_3026141] using wordTrace_append hprefix tailTrace_3026141
  have hstable : (prefixWord ++ tailWord_3026141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026141).length < 2 ^ (prefixWord ++ tailWord_3026141).sum := by decide
  have hdescent : baseEnd_3026141 < baseStart_3026141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026144 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_3026144 : Nat := 118140960795 + 3026144 * 2 ^ 59
def prefixEnd_3026144 : Nat := 4983230072969 + 3 ^ 40 * 3026144 * 2
def baseEnd_3026144 : Nat := 1553866401719513431383023

theorem tailTrace_3026144 : CollatzResearch.WordTrace tailWord_3026144 prefixEnd_3026144 1553866401719513431383023 := by
  unfold tailWord_3026144
  simp only [CollatzResearch.WordTrace]
  refine ⟨55186269574402293546914743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73581692765869724729219657 55186269574402293546914743)
  ·
    refine ⟨82779404361603440320372115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55186269574402293546914743 82779404361603440320372115)
    ·
      refine ⟨124169106542405160480558173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82779404361603440320372115 124169106542405160480558173)
      ·
        refine ⟨46563414953401935180209315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124169106542405160480558173 46563414953401935180209315)
        ·
          refine ⟨69845122430102902770313973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46563414953401935180209315 69845122430102902770313973)
          ·
            refine ⟨6547980227822147134716935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69845122430102902770313973 6547980227822147134716935)
            ·
              refine ⟨9821970341733220702075403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547980227822147134716935 9821970341733220702075403)
              ·
                refine ⟨14732955512599831053113105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9821970341733220702075403 14732955512599831053113105)
                ·
                  refine ⟨11049716634449873289834829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14732955512599831053113105 11049716634449873289834829)
                  ·
                    refine ⟨4143643737918702483688061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11049716634449873289834829 4143643737918702483688061)
                    ·
                      refine ⟨1553866401719513431383023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143643737918702483688061 1553866401719513431383023)
                      ·
                        rfl

theorem cell23_3026144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_3026144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026144 prefixEnd_3026144 := by exact prefixLift 3026144
  have htrace : WordTrace (prefixWord ++ tailWord_3026144) baseStart_3026144 baseEnd_3026144 := by
    simpa [prefixWord, tailWord_3026144, baseEnd_3026144] using wordTrace_append hprefix tailTrace_3026144
  have hstable : (prefixWord ++ tailWord_3026144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026144).length < 2 ^ (prefixWord ++ tailWord_3026144).sum := by decide
  have hdescent : baseEnd_3026144 < baseStart_3026144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026167 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_3026167 : Nat := 118140960795 + 3026167 * 2 ^ 59
def prefixEnd_3026167 : Nat := 4983230072969 + 3 ^ 40 * 3026167 * 2
def baseEnd_3026167 : Nat := 1553878211774566841395417

theorem tailTrace_3026167 : CollatzResearch.WordTrace tailWord_3026167 prefixEnd_3026167 1553878211774566841395417 := by
  unfold tailWord_3026167
  simp only [CollatzResearch.WordTrace]
  refine ⟨110373378027721262021916755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73582252018480841347944503 110373378027721262021916755)
  ·
    refine ⟨165560067041581893032875133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110373378027721262021916755 165560067041581893032875133)
    ·
      refine ⟨62085025140593209887328175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165560067041581893032875133 62085025140593209887328175)
      ·
        refine ⟨93127537710889814830992263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62085025140593209887328175 93127537710889814830992263)
        ·
          refine ⟨139691306566334722246488395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93127537710889814830992263 139691306566334722246488395)
          ·
            refine ⟨209536959849502083369732593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139691306566334722246488395 209536959849502083369732593)
            ·
              refine ⟨157152719887126562527299445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209536959849502083369732593 157152719887126562527299445)
              ·
                refine ⟨14733067489418115236934323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157152719887126562527299445 14733067489418115236934323)
                ·
                  refine ⟨22099601234127172855401485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14733067489418115236934323 22099601234127172855401485)
                  ·
                    refine ⟨8287350462797689820775557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22099601234127172855401485 8287350462797689820775557)
                    ·
                      refine ⟨1553878211774566841395417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8287350462797689820775557 1553878211774566841395417)
                      ·
                        rfl

theorem cell23_3026167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_3026167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026167 prefixEnd_3026167 := by exact prefixLift 3026167
  have htrace : WordTrace (prefixWord ++ tailWord_3026167) baseStart_3026167 baseEnd_3026167 := by
    simpa [prefixWord, tailWord_3026167, baseEnd_3026167] using wordTrace_append hprefix tailTrace_3026167
  have hstable : (prefixWord ++ tailWord_3026167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026167).length < 2 ^ (prefixWord ++ tailWord_3026167).sum := by decide
  have hdescent : baseEnd_3026167 < baseStart_3026167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026197 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3026197 : Nat := 118140960795 + 3026197 * 2 ^ 59
def prefixEnd_3026197 : Nat := 4983230072969 + 3 ^ 40 * 3026197 * 2
def baseEnd_3026197 : Nat := 1553893616194201724020279

theorem tailTrace_3026197 : CollatzResearch.WordTrace tailWord_3026197 prefixEnd_3026197 1553893616194201724020279 := by
  unfold tailWord_3026197
  simp only [CollatzResearch.WordTrace]
  refine ⟨110374472217612577145508845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73582981478408384763672563 110374472217612577145508845)
  ·
    refine ⟨41390427081604716429565817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110374472217612577145508845 41390427081604716429565817)
    ·
      refine ⟨31042820311203537322174363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41390427081604716429565817 31042820311203537322174363)
      ·
        refine ⟨46564230466805305983261545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31042820311203537322174363 46564230466805305983261545)
        ·
          refine ⟨34923172850103979487446159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46564230466805305983261545 34923172850103979487446159)
          ·
            refine ⟨52384759275155969231169239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34923172850103979487446159 52384759275155969231169239)
            ·
              refine ⟨78577138912733953846753859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52384759275155969231169239 78577138912733953846753859)
              ·
                refine ⟨117865708369100930770130789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78577138912733953846753859 117865708369100930770130789)
                ·
                  refine ⟨22099820319206424519399523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117865708369100930770130789 22099820319206424519399523)
                  ·
                    refine ⟨33149730478809636779099285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22099820319206424519399523 33149730478809636779099285)
                    ·
                      refine ⟨1553893616194201724020279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33149730478809636779099285 1553893616194201724020279)
                      ·
                        rfl

theorem cell23_3026197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3026197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026197 prefixEnd_3026197 := by exact prefixLift 3026197
  have htrace : WordTrace (prefixWord ++ tailWord_3026197) baseStart_3026197 baseEnd_3026197 := by
    simpa [prefixWord, tailWord_3026197, baseEnd_3026197] using wordTrace_append hprefix tailTrace_3026197
  have hstable : (prefixWord ++ tailWord_3026197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026197).length < 2 ^ (prefixWord ++ tailWord_3026197).sum := by decide
  have hdescent : baseEnd_3026197 < baseStart_3026197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026204 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_3026204 : Nat := 118140960795 + 3026204 * 2 ^ 59
def prefixEnd_3026204 : Nat := 4983230072969 + 3 ^ 40 * 3026204 * 2
def baseEnd_3026204 : Nat := 1553897210558783196632747

theorem tailTrace_3026204 : CollatzResearch.WordTrace tailWord_3026204 prefixEnd_3026204 1553897210558783196632747 := by
  unfold tailWord_3026204
  simp only [CollatzResearch.WordTrace]
  refine ⟨55187363764293608670506833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73583151685724811560675777 55187363764293608670506833)
  ·
    refine ⟨41390522823220206502880125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55187363764293608670506833 41390522823220206502880125)
    ·
      refine ⟨15521446058707577438580047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41390522823220206502880125 15521446058707577438580047)
      ·
        refine ⟨23282169088061366157870071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15521446058707577438580047 23282169088061366157870071)
        ·
          refine ⟨34923253632092049236805107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23282169088061366157870071 34923253632092049236805107)
          ·
            refine ⟨52384880448138073855207661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34923253632092049236805107 52384880448138073855207661)
            ·
              refine ⟨19644330168051777695702873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52384880448138073855207661 19644330168051777695702873)
              ·
                refine ⟨14733247626038833271777155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19644330168051777695702873 14733247626038833271777155)
                ·
                  refine ⟨22099871439058249907665733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14733247626038833271777155 22099871439058249907665733)
                  ·
                    refine ⟨4143725894823421857687325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22099871439058249907665733 4143725894823421857687325)
                    ·
                      refine ⟨1553897210558783196632747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143725894823421857687325 1553897210558783196632747)
                      ·
                        rfl

theorem cell23_3026204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_3026204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026204 prefixEnd_3026204 := by exact prefixLift 3026204
  have htrace : WordTrace (prefixWord ++ tailWord_3026204) baseStart_3026204 baseEnd_3026204 := by
    simpa [prefixWord, tailWord_3026204, baseEnd_3026204] using wordTrace_append hprefix tailTrace_3026204
  have hstable : (prefixWord ++ tailWord_3026204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026204).length < 2 ^ (prefixWord ++ tailWord_3026204).sum := by decide
  have hdescent : baseEnd_3026204 < baseStart_3026204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026254 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3026254 : Nat := 118140960795 + 3026254 * 2 ^ 59
def prefixEnd_3026254 : Nat := 4983230072969 + 3 ^ 40 * 3026254 * 2
def baseEnd_3026254 : Nat := 517974294863836000335839

theorem tailTrace_3026254 : CollatzResearch.WordTrace tailWord_3026254 prefixEnd_3026254 517974294863836000335839 := by
  unfold tailWord_3026254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797068897300759485041727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73584367452270717253555877 13797068897300759485041727)
  ·
    refine ⟨20695603345951139227562591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13797068897300759485041727 20695603345951139227562591)
    ·
      refine ⟨31043405018926708841343887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20695603345951139227562591 31043405018926708841343887)
      ·
        refine ⟨46565107528390063262015831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31043405018926708841343887 46565107528390063262015831)
        ·
          refine ⟨69847661292585094893023747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46565107528390063262015831 69847661292585094893023747)
          ·
            refine ⟨104771491938877642339535621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69847661292585094893023747 104771491938877642339535621)
            ·
              refine ⟨19644654738539557938662929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104771491938877642339535621 19644654738539557938662929)
              ·
                refine ⟨14733491053904668453997197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19644654738539557938662929 14733491053904668453997197)
                ·
                  refine ⟨5525059145214250670248949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14733491053904668453997197 5525059145214250670248949)
                  ·
                    refine ⟨517974294863836000335839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5525059145214250670248949 517974294863836000335839)
                    ·
                      rfl

theorem cell23_3026254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3026254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026254 prefixEnd_3026254 := by exact prefixLift 3026254
  have htrace : WordTrace (prefixWord ++ tailWord_3026254) baseStart_3026254 baseEnd_3026254 := by
    simpa [prefixWord, tailWord_3026254, baseEnd_3026254] using wordTrace_append hprefix tailTrace_3026254
  have hstable : (prefixWord ++ tailWord_3026254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026254).length < 2 ^ (prefixWord ++ tailWord_3026254).sum := by decide
  have hdescent : baseEnd_3026254 < baseStart_3026254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026284 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_3026284 : Nat := 118140960795 + 3026284 * 2 ^ 59
def prefixEnd_3026284 : Nat := 4983230072969 + 3 ^ 40 * 3026284 * 2
def baseEnd_3026284 : Nat := 517979429670380961210793

theorem tailTrace_3026284 : CollatzResearch.WordTrace tailWord_3026284 prefixEnd_3026284 517979429670380961210793 := by
  unfold tailWord_3026284
  simp only [CollatzResearch.WordTrace]
  refine ⟨55188822684148695501962953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73585096912198260669283937 55188822684148695501962953)
  ·
    refine ⟨41391617013111521626472215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55188822684148695501962953 41391617013111521626472215)
    ·
      refine ⟨62087425519667282439708323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41391617013111521626472215 62087425519667282439708323)
      ·
        refine ⟨93131138279500923659562485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62087425519667282439708323 93131138279500923659562485)
        ·
          refine ⟨8731044213703211593083983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93131138279500923659562485 8731044213703211593083983)
          ·
            refine ⟨13096566320554817389625975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731044213703211593083983 13096566320554817389625975)
            ·
              refine ⟨19644849480832226084438963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096566320554817389625975 19644849480832226084438963)
              ·
                refine ⟨29467274221248339126658445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19644849480832226084438963 29467274221248339126658445)
                ·
                  refine ⟨11050227832968127172496917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29467274221248339126658445 11050227832968127172496917)
                  ·
                    refine ⟨517979429670380961210793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11050227832968127172496917 517979429670380961210793)
                    ·
                      rfl

theorem cell23_3026284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_3026284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026284 prefixEnd_3026284 := by exact prefixLift 3026284
  have htrace : WordTrace (prefixWord ++ tailWord_3026284) baseStart_3026284 baseEnd_3026284 := by
    simpa [prefixWord, tailWord_3026284, baseEnd_3026284] using wordTrace_append hprefix tailTrace_3026284
  have hstable : (prefixWord ++ tailWord_3026284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026284).length < 2 ^ (prefixWord ++ tailWord_3026284).sum := by decide
  have hdescent : baseEnd_3026284 < baseStart_3026284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026311 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_3026311 : Nat := 118140960795 + 3026311 * 2 ^ 59
def prefixEnd_3026311 : Nat := 4983230072969 + 3 ^ 40 * 3026311 * 2
def baseEnd_3026311 : Nat := 1553952152988814277994755

theorem tailTrace_3026311 : CollatzResearch.WordTrace tailWord_3026311 prefixEnd_3026311 1553952152988814277994755 := by
  unfold tailWord_3026311
  simp only [CollatzResearch.WordTrace]
  refine ⟨110378630139199574615158787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73585753426133049743439191 110378630139199574615158787)
  ·
    refine ⟨165567945208799361922738181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110378630139199574615158787 165567945208799361922738181)
    ·
      refine ⟨31043989726649880360513409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165567945208799361922738181 31043989726649880360513409)
      ·
        refine ⟨23282992294987410270385057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31043989726649880360513409 23282992294987410270385057)
        ·
          refine ⟨17462244221240557702788793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23282992294987410270385057 17462244221240557702788793)
          ·
            refine ⟨13096683165930418277091595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17462244221240557702788793 13096683165930418277091595)
            ·
              refine ⟨19645024748895627415637393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096683165930418277091595 19645024748895627415637393)
              ·
                refine ⟨14733768561671720561728045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19645024748895627415637393 14733768561671720561728045)
                ·
                  refine ⟨5525163210626895210648017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14733768561671720561728045 5525163210626895210648017)
                  ·
                    refine ⟨4143872407970171407986013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525163210626895210648017 4143872407970171407986013)
                    ·
                      refine ⟨1553952152988814277994755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143872407970171407986013 1553952152988814277994755)
                      ·
                        rfl

theorem cell23_3026311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_3026311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026311 prefixEnd_3026311 := by exact prefixLift 3026311
  have htrace : WordTrace (prefixWord ++ tailWord_3026311) baseStart_3026311 baseEnd_3026311 := by
    simpa [prefixWord, tailWord_3026311, baseEnd_3026311] using wordTrace_append hprefix tailTrace_3026311
  have hstable : (prefixWord ++ tailWord_3026311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026311).length < 2 ^ (prefixWord ++ tailWord_3026311).sum := by decide
  have hdescent : baseEnd_3026311 < baseStart_3026311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026318 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_3026318 : Nat := 118140960795 + 3026318 * 2 ^ 59
def prefixEnd_3026318 : Nat := 4983230072969 + 3 ^ 40 * 3026318 * 2
def baseEnd_3026318 : Nat := 517985249117798583535741

theorem tailTrace_3026318 : CollatzResearch.WordTrace tailWord_3026318 prefixEnd_3026318 517985249117798583535741 := by
  unfold tailWord_3026318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797360681271776851332951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73585923633449476540442405 13797360681271776851332951)
  ·
    refine ⟨20696041021907665276999427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13797360681271776851332951 20696041021907665276999427)
    ·
      refine ⟨31044061532861497915499141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20696041021907665276999427 31044061532861497915499141)
      ·
        refine ⟨5820761537411530859156089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31044061532861497915499141 5820761537411530859156089)
        ·
          refine ⟨4365571153058648144367067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5820761537411530859156089 4365571153058648144367067)
          ·
            refine ⟨6548356729587972216550601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4365571153058648144367067 6548356729587972216550601)
            ·
              refine ⟨4911267547190979162412951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6548356729587972216550601 4911267547190979162412951)
              ·
                refine ⟨7366901320786468743619427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4911267547190979162412951 7366901320786468743619427)
                ·
                  refine ⟨11050351981179703115429141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7366901320786468743619427 11050351981179703115429141)
                  ·
                    refine ⟨517985249117798583535741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11050351981179703115429141 517985249117798583535741)
                    ·
                      rfl

theorem cell23_3026318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_3026318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026318 prefixEnd_3026318 := by exact prefixLift 3026318
  have htrace : WordTrace (prefixWord ++ tailWord_3026318) baseStart_3026318 baseEnd_3026318 := by
    simpa [prefixWord, tailWord_3026318, baseEnd_3026318] using wordTrace_append hprefix tailTrace_3026318
  have hstable : (prefixWord ++ tailWord_3026318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026318).length < 2 ^ (prefixWord ++ tailWord_3026318).sum := by decide
  have hdescent : baseEnd_3026318 < baseStart_3026318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026354 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3026354 : Nat := 118140960795 + 3026354 * 2 ^ 59
def prefixEnd_3026354 : Nat := 4983230072969 + 3 ^ 40 * 3026354 * 2
def baseEnd_3026354 : Nat := 1553974232656957609757057

theorem tailTrace_3026354 : CollatzResearch.WordTrace tailWord_3026354 prefixEnd_3026354 1553974232656957609757057 := by
  unfold tailWord_3026354
  simp only [CollatzResearch.WordTrace]
  refine ⟨27595049619510948239743529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73586798985362528639316077 27595049619510948239743529)
  ·
    refine ⟨20696287214633211179807647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27595049619510948239743529 20696287214633211179807647)
    ·
      refine ⟨31044430821949816769711471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20696287214633211179807647 31044430821949816769711471)
      ·
        refine ⟨46566646232924725154567207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31044430821949816769711471 46566646232924725154567207)
        ·
          refine ⟨69849969349387087731850811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46566646232924725154567207 69849969349387087731850811)
          ·
            refine ⟨104774954024080631597776217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69849969349387087731850811 104774954024080631597776217)
            ·
              refine ⟨78581215518060473698332163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104774954024080631597776217 78581215518060473698332163)
              ·
                refine ⟨117871823277090710547498245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78581215518060473698332163 117871823277090710547498245)
                ·
                  refine ⟨22100966864454508227655921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117871823277090710547498245 22100966864454508227655921)
                  ·
                    refine ⟨16575725148340881170741941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22100966864454508227655921 16575725148340881170741941)
                    ·
                      refine ⟨1553974232656957609757057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16575725148340881170741941 1553974232656957609757057)
                      ·
                        rfl

theorem cell23_3026354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3026354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026354 prefixEnd_3026354 := by exact prefixLift 3026354
  have htrace : WordTrace (prefixWord ++ tailWord_3026354) baseStart_3026354 baseEnd_3026354 := by
    simpa [prefixWord, tailWord_3026354, baseEnd_3026354] using wordTrace_append hprefix tailTrace_3026354
  have hstable : (prefixWord ++ tailWord_3026354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026354).length < 2 ^ (prefixWord ++ tailWord_3026354).sum := by decide
  have hdescent : baseEnd_3026354 < baseStart_3026354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026375 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_3026375 : Nat := 118140960795 + 3026375 * 2 ^ 59
def prefixEnd_3026375 : Nat := 4983230072969 + 3 ^ 40 * 3026375 * 2
def baseEnd_3026375 : Nat := 1553985015750702027594461

theorem tailTrace_3026375 : CollatzResearch.WordTrace tailWord_3026375 prefixEnd_3026375 1553985015750702027594461 := by
  unfold tailWord_3026375
  simp only [CollatzResearch.WordTrace]
  refine ⟨110380964410967713545488579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73587309607311809030325719 110380964410967713545488579)
  ·
    refine ⟨165571446616451570318232869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110380964410967713545488579 165571446616451570318232869)
    ·
      refine ⟨31044646240584669434668663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165571446616451570318232869 31044646240584669434668663)
      ·
        refine ⟨46566969360877004152002995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31044646240584669434668663 46566969360877004152002995)
        ·
          refine ⟨69850454041315506228004493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46566969360877004152002995 69850454041315506228004493)
          ·
            refine ⟨26193920265493314835501685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69850454041315506228004493 26193920265493314835501685)
            ·
              refine ⟨2455680024889998265828283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26193920265493314835501685 2455680024889998265828283)
              ·
                refine ⟨3683520037334997398742425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455680024889998265828283 3683520037334997398742425)
                ·
                  refine ⟨2762640028001248049056819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3683520037334997398742425 2762640028001248049056819)
                  ·
                    refine ⟨4143960042001872073585229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2762640028001248049056819 4143960042001872073585229)
                    ·
                      refine ⟨1553985015750702027594461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4143960042001872073585229 1553985015750702027594461)
                      ·
                        rfl

theorem cell23_3026375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_3026375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026375 prefixEnd_3026375 := by exact prefixLift 3026375
  have htrace : WordTrace (prefixWord ++ tailWord_3026375) baseStart_3026375 baseEnd_3026375 := by
    simpa [prefixWord, tailWord_3026375, baseEnd_3026375] using wordTrace_append hprefix tailTrace_3026375
  have hstable : (prefixWord ++ tailWord_3026375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026375).length < 2 ^ (prefixWord ++ tailWord_3026375).sum := by decide
  have hdescent : baseEnd_3026375 < baseStart_3026375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026384 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_3026384 : Nat := 118140960795 + 3026384 * 2 ^ 59
def prefixEnd_3026384 : Nat := 4983230072969 + 3 ^ 40 * 3026384 * 2
def baseEnd_3026384 : Nat := 1553989637076592492381919

theorem tailTrace_3026384 : CollatzResearch.WordTrace tailWord_3026384 prefixEnd_3026384 1553989637076592492381919 := by
  unfold tailWord_3026384
  simp only [CollatzResearch.WordTrace]
  refine ⟨55190646333967554041283103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73587528445290072055044137 55190646333967554041283103)
  ·
    refine ⟨82785969500951331061924655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55190646333967554041283103 82785969500951331061924655)
    ·
      refine ⟨124178954251426996592886983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82785969500951331061924655 124178954251426996592886983)
      ·
        refine ⟨186268431377140494889330475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124178954251426996592886983 186268431377140494889330475)
        ·
          refine ⟨279402647065710742333995713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186268431377140494889330475 279402647065710742333995713)
          ·
            refine ⟨209551985299283056750496785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279402647065710742333995713 209551985299283056750496785)
            ·
              refine ⟨157163988974462292562872589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209551985299283056750496785 157163988974462292562872589)
              ·
                refine ⟨58936495865423359711077221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157163988974462292562872589 58936495865423359711077221)
                ·
                  refine ⟨11050592974766879945826979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58936495865423359711077221 11050592974766879945826979)
                  ·
                    refine ⟨16575889462150319918740469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11050592974766879945826979 16575889462150319918740469)
                    ·
                      refine ⟨1553989637076592492381919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16575889462150319918740469 1553989637076592492381919)
                      ·
                        rfl

theorem cell23_3026384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_3026384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026384 prefixEnd_3026384 := by exact prefixLift 3026384
  have htrace : WordTrace (prefixWord ++ tailWord_3026384) baseStart_3026384 baseEnd_3026384 := by
    simpa [prefixWord, tailWord_3026384, baseEnd_3026384] using wordTrace_append hprefix tailTrace_3026384
  have hstable : (prefixWord ++ tailWord_3026384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026384).length < 2 ^ (prefixWord ++ tailWord_3026384).sum := by decide
  have hdescent : baseEnd_3026384 < baseStart_3026384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026401 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_3026401 : Nat := 118140960795 + 3026401 * 2 ^ 59
def prefixEnd_3026401 : Nat := 4983230072969 + 3 ^ 40 * 3026401 * 2
def baseEnd_3026401 : Nat := 1553998366247718925869341

theorem tailTrace_3026401 : CollatzResearch.WordTrace tailWord_3026401 prefixEnd_3026401 1553998366247718925869341 := by
  unfold tailWord_3026401
  simp only [CollatzResearch.WordTrace]
  refine ⟨110381912708873519985935057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73587941805915679990623371 110381912708873519985935057)
  ·
    refine ⟨82786434531655139989451293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110381912708873519985935057 82786434531655139989451293)
    ·
      refine ⟨31044912949370677496044235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82786434531655139989451293 31044912949370677496044235)
      ·
        refine ⟨46567369424056016244066353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31044912949370677496044235 46567369424056016244066353)
        ·
          refine ⟨34925527068042012183049765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46567369424056016244066353 34925527068042012183049765)
          ·
            refine ⟨6548536325257877284321831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34925527068042012183049765 6548536325257877284321831)
            ·
              refine ⟨9822804487886815926482747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548536325257877284321831 9822804487886815926482747)
              ·
                refine ⟨14734206731830223889724121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9822804487886815926482747 14734206731830223889724121)
                ·
                  refine ⟨11050655048872667917293091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14734206731830223889724121 11050655048872667917293091)
                  ·
                    refine ⟨16575982573309001875939637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11050655048872667917293091 16575982573309001875939637)
                    ·
                      refine ⟨1553998366247718925869341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16575982573309001875939637 1553998366247718925869341)
                      ·
                        rfl

theorem cell23_3026401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_3026401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026401 prefixEnd_3026401 := by exact prefixLift 3026401
  have htrace : WordTrace (prefixWord ++ tailWord_3026401) baseStart_3026401 baseEnd_3026401 := by
    simpa [prefixWord, tailWord_3026401, baseEnd_3026401] using wordTrace_append hprefix tailTrace_3026401
  have hstable : (prefixWord ++ tailWord_3026401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026401).length < 2 ^ (prefixWord ++ tailWord_3026401).sum := by decide
  have hdescent : baseEnd_3026401 < baseStart_3026401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026404 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 9]
def baseStart_3026404 : Nat := 118140960795 + 3026404 * 2 ^ 59
def prefixEnd_3026404 : Nat := 4983230072969 + 3 ^ 40 * 3026404 * 2
def baseEnd_3026404 : Nat := 172666656298853601570203

theorem tailTrace_3026404 : CollatzResearch.WordTrace tailWord_3026404 prefixEnd_3026404 172666656298853601570203 := by
  unfold tailWord_3026404
  simp only [CollatzResearch.WordTrace]
  refine ⟨55191011063931325749147133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73588014751908434332196177 55191011063931325749147133)
  ·
    refine ⟨20696629148974247155930175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55191011063931325749147133 20696629148974247155930175)
    ·
      refine ⟨31044943723461370733895263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20696629148974247155930175 31044943723461370733895263)
      ·
        refine ⟨46567415585192056100842895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31044943723461370733895263 46567415585192056100842895)
        ·
          refine ⟨69851123377788084151264343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46567415585192056100842895 69851123377788084151264343)
          ·
            refine ⟨104776685066682126226896515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69851123377788084151264343 104776685066682126226896515)
            ·
              refine ⟨157165027600023189340344773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104776685066682126226896515 157165027600023189340344773)
              ·
                refine ⟨29468442675004348001314645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157165027600023189340344773 29468442675004348001314645)
                ·
                  refine ⟨172666656298853601570203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29468442675004348001314645 172666656298853601570203)
                  ·
                    rfl

theorem cell23_3026404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_3026404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026404 prefixEnd_3026404 := by exact prefixLift 3026404
  have htrace : WordTrace (prefixWord ++ tailWord_3026404) baseStart_3026404 baseEnd_3026404 := by
    simpa [prefixWord, tailWord_3026404, baseEnd_3026404] using wordTrace_append hprefix tailTrace_3026404
  have hstable : (prefixWord ++ tailWord_3026404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026404).length < 2 ^ (prefixWord ++ tailWord_3026404).sum := by decide
  have hdescent : baseEnd_3026404 < baseStart_3026404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026451 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 2, 5]
def baseStart_3026451 : Nat := 118140960795 + 3026451 * 2 ^ 59
def prefixEnd_3026451 : Nat := 4983230072969 + 3 ^ 40 * 3026451 * 2
def baseEnd_3026451 : Nat := 518008013426814576748037

theorem tailTrace_3026451 : CollatzResearch.WordTrace tailWord_3026451 prefixEnd_3026451 518008013426814576748037 := by
  unfold tailWord_3026451
  simp only [CollatzResearch.WordTrace]
  refine ⟨110383736358692378525255207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73589157572461585683503471 110383736358692378525255207)
  ·
    refine ⟨165575604538038567787882811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110383736358692378525255207 165575604538038567787882811)
    ·
      refine ⟨248363406807057851681824217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165575604538038567787882811 248363406807057851681824217)
      ·
        refine ⟨186272555105293388761368163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248363406807057851681824217 186272555105293388761368163)
        ·
          refine ⟨279408832657940083142052245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186272555105293388761368163 279408832657940083142052245)
          ·
            refine ⟨13097289030840941397283699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279408832657940083142052245 13097289030840941397283699)
            ·
              refine ⟨19645933546261412095925549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097289030840941397283699 19645933546261412095925549)
              ·
                refine ⟨7367225079848029535972081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19645933546261412095925549 7367225079848029535972081)
                ·
                  refine ⟨5525418809886022151979061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7367225079848029535972081 5525418809886022151979061)
                  ·
                    refine ⟨518008013426814576748037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5525418809886022151979061 518008013426814576748037)
                    ·
                      rfl

theorem cell23_3026451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 5].length) (baseStart_3026451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026451 prefixEnd_3026451 := by exact prefixLift 3026451
  have htrace : WordTrace (prefixWord ++ tailWord_3026451) baseStart_3026451 baseEnd_3026451 := by
    simpa [prefixWord, tailWord_3026451, baseEnd_3026451] using wordTrace_append hprefix tailTrace_3026451
  have hstable : (prefixWord ++ tailWord_3026451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026451).length < 2 ^ (prefixWord ++ tailWord_3026451).sum := by decide
  have hdescent : baseEnd_3026451 < baseStart_3026451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026461 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3026461 : Nat := 118140960795 + 3026461 * 2 ^ 59
def prefixEnd_3026461 : Nat := 4983230072969 + 3 ^ 40 * 3026461 * 2
def baseEnd_3026461 : Nat := 1554029175086988691119065

theorem tailTrace_3026461 : CollatzResearch.WordTrace tailWord_3026461 prefixEnd_3026461 1554029175086988691119065 := by
  unfold tailWord_3026461
  simp only [CollatzResearch.WordTrace]
  refine ⟨110384101088656150233119237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73589400725770766822079491 110384101088656150233119237)
  ·
    refine ⟨20697018954123028168709857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110384101088656150233119237 20697018954123028168709857)
    ·
      refine ⟨15522764215592271126532393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20697018954123028168709857 15522764215592271126532393)
      ·
        refine ⟨11642073161694203344899295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15522764215592271126532393 11642073161694203344899295)
        ·
          refine ⟨17463109742541305017348943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642073161694203344899295 17463109742541305017348943)
          ·
            refine ⟨26194664613811957526023415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17463109742541305017348943 26194664613811957526023415)
            ·
              refine ⟨39291996920717936289035123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26194664613811957526023415 39291996920717936289035123)
              ·
                refine ⟨58937995381076904433552685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39291996920717936289035123 58937995381076904433552685)
                ·
                  refine ⟨22101748267903839162582257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58937995381076904433552685 22101748267903839162582257)
                  ·
                    refine ⟨16576311200927879371936693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22101748267903839162582257 16576311200927879371936693)
                    ·
                      refine ⟨1554029175086988691119065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16576311200927879371936693 1554029175086988691119065)
                      ·
                        rfl

theorem cell23_3026461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3026461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026461 prefixEnd_3026461 := by exact prefixLift 3026461
  have htrace : WordTrace (prefixWord ++ tailWord_3026461) baseStart_3026461 baseEnd_3026461 := by
    simpa [prefixWord, tailWord_3026461, baseEnd_3026461] using wordTrace_append hprefix tailTrace_3026461
  have hstable : (prefixWord ++ tailWord_3026461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026461).length < 2 ^ (prefixWord ++ tailWord_3026461).sum := by decide
  have hdescent : baseEnd_3026461 < baseStart_3026461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026478 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3026478 : Nat := 118140960795 + 3026478 * 2 ^ 59
def prefixEnd_3026478 : Nat := 4983230072969 + 3 ^ 40 * 3026478 * 2
def baseEnd_3026478 : Nat := 1554037904258115124606487

theorem tailTrace_3026478 : CollatzResearch.WordTrace tailWord_3026478 prefixEnd_3026478 1554037904258115124606487 := by
  unfold tailWord_3026478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798090141199320267061011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73589814086396374757658725 13798090141199320267061011)
  ·
    refine ⟨20697135211798980400591517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13798090141199320267061011 20697135211798980400591517)
    ·
      refine ⟨7761425704424617650221819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20697135211798980400591517 7761425704424617650221819)
      ·
        refine ⟨11642138556636926475332729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7761425704424617650221819 11642138556636926475332729)
        ·
          refine ⟨8731603917477694856499547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11642138556636926475332729 8731603917477694856499547)
          ·
            refine ⟨13097405876216542284749321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731603917477694856499547 13097405876216542284749321)
            ·
              refine ⟨9823054407162406713561991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13097405876216542284749321 9823054407162406713561991)
              ·
                refine ⟨14734581610743610070342987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823054407162406713561991 14734581610743610070342987)
                ·
                  refine ⟨22101872416115415105514481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14734581610743610070342987 22101872416115415105514481)
                  ·
                    refine ⟨16576404312086561329135861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22101872416115415105514481 16576404312086561329135861)
                    ·
                      refine ⟨1554037904258115124606487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16576404312086561329135861 1554037904258115124606487)
                      ·
                        rfl

theorem cell23_3026478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3026478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026478 prefixEnd_3026478 := by exact prefixLift 3026478
  have htrace : WordTrace (prefixWord ++ tailWord_3026478) baseStart_3026478 baseEnd_3026478 := by
    simpa [prefixWord, tailWord_3026478, baseEnd_3026478] using wordTrace_append hprefix tailTrace_3026478
  have hstable : (prefixWord ++ tailWord_3026478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026478).length < 2 ^ (prefixWord ++ tailWord_3026478).sum := by decide
  have hdescent : baseEnd_3026478 < baseStart_3026478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026488 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 6, 2]
def baseStart_3026488 : Nat := 118140960795 + 3026488 * 2 ^ 59
def prefixEnd_3026488 : Nat := 4983230072969 + 3 ^ 40 * 3026488 * 2
def baseEnd_3026488 : Nat := 1554043039064660085481441

theorem tailTrace_3026488 : CollatzResearch.WordTrace tailWord_3026488 prefixEnd_3026488 1554043039064660085481441 := by
  unfold tailWord_3026488
  simp only [CollatzResearch.WordTrace]
  refine ⟨55192542929779166922176059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73590057239705555896234745 55192542929779166922176059)
  ·
    refine ⟨82788814394668750383264089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55192542929779166922176059 82788814394668750383264089)
    ·
      refine ⟨62091610796001562787448067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82788814394668750383264089 62091610796001562787448067)
      ·
        refine ⟨93137416194002344181172101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62091610796001562787448067 93137416194002344181172101)
        ·
          refine ⟨17463265536375439533969769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93137416194002344181172101 17463265536375439533969769)
          ·
            refine ⟨13097449152281579650477327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17463265536375439533969769 13097449152281579650477327)
            ·
              refine ⟨19646173728422369475715991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097449152281579650477327 19646173728422369475715991)
              ·
                refine ⟨29469260592633554213573987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19646173728422369475715991 29469260592633554213573987)
                ·
                  refine ⟨44203890888950331320360981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29469260592633554213573987 44203890888950331320360981)
                  ·
                    refine ⟨2072057385419546780641921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44203890888950331320360981 2072057385419546780641921)
                    ·
                      refine ⟨1554043039064660085481441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072057385419546780641921 1554043039064660085481441)
                      ·
                        rfl

theorem cell23_3026488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_3026488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026488 prefixEnd_3026488 := by exact prefixLift 3026488
  have htrace : WordTrace (prefixWord ++ tailWord_3026488) baseStart_3026488 baseEnd_3026488 := by
    simpa [prefixWord, tailWord_3026488, baseEnd_3026488] using wordTrace_append hprefix tailTrace_3026488
  have hstable : (prefixWord ++ tailWord_3026488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026488).length < 2 ^ (prefixWord ++ tailWord_3026488).sum := by decide
  have hdescent : baseEnd_3026488 < baseStart_3026488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026508 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3026508 : Nat := 118140960795 + 3026508 * 2 ^ 59
def prefixEnd_3026508 : Nat := 4983230072969 + 3 ^ 40 * 3026508 * 2
def baseEnd_3026508 : Nat := 1554053308677750007231349

theorem tailTrace_3026508 : CollatzResearch.WordTrace tailWord_3026508 prefixEnd_3026508 1554053308677750007231349 := by
  unfold tailWord_3026508
  simp only [CollatzResearch.WordTrace]
  refine ⟨55192907659742938630040089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73590543546323918173386785 55192907659742938630040089)
  ·
    refine ⟨41394680744807203972530067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55192907659742938630040089 41394680744807203972530067)
    ·
      refine ⟨62092021117210805958795101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41394680744807203972530067 62092021117210805958795101)
      ·
        refine ⟨23284507918954052234548163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62092021117210805958795101 23284507918954052234548163)
        ·
          refine ⟨34926761878431078351822245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23284507918954052234548163 34926761878431078351822245)
          ·
            refine ⟨6548767852205827190966671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34926761878431078351822245 6548767852205827190966671)
            ·
              refine ⟨9823151778308740786450007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548767852205827190966671 9823151778308740786450007)
              ·
                refine ⟨14734727667463111179675011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823151778308740786450007 14734727667463111179675011)
                ·
                  refine ⟨22102091501194666769512517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14734727667463111179675011 22102091501194666769512517)
                  ·
                    refine ⟨4144142156474000019283597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22102091501194666769512517 4144142156474000019283597)
                    ·
                      refine ⟨1554053308677750007231349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144142156474000019283597 1554053308677750007231349)
                      ·
                        rfl

theorem cell23_3026508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3026508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026508 prefixEnd_3026508 := by exact prefixLift 3026508
  have htrace : WordTrace (prefixWord ++ tailWord_3026508) baseStart_3026508 baseEnd_3026508 := by
    simpa [prefixWord, tailWord_3026508, baseEnd_3026508] using wordTrace_append hprefix tailTrace_3026508
  have hstable : (prefixWord ++ tailWord_3026508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026508).length < 2 ^ (prefixWord ++ tailWord_3026508).sum := by decide
  have hdescent : baseEnd_3026508 < baseStart_3026508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026521 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_3026521 : Nat := 118140960795 + 3026521 * 2 ^ 59
def prefixEnd_3026521 : Nat := 4983230072969 + 3 ^ 40 * 3026521 * 2
def baseEnd_3026521 : Nat := 1554059983926258456368789

theorem tailTrace_3026521 : CollatzResearch.WordTrace tailWord_3026521 prefixEnd_3026521 1554059983926258456368789 := by
  unfold tailWord_3026521
  simp only [CollatzResearch.WordTrace]
  refine ⟨110386289468438780480303417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73590859645625853653535611 110386289468438780480303417)
  ·
    refine ⟨82789717101329085360227563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110386289468438780480303417 82789717101329085360227563)
    ·
      refine ⟨124184575651993628040341345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82789717101329085360227563 124184575651993628040341345)
      ·
        refine ⟨93138431738995221030256009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124184575651993628040341345 93138431738995221030256009)
        ·
          refine ⟨69853823804246415772692007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93138431738995221030256009 69853823804246415772692007)
          ·
            refine ⟨104780735706369623659038011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69853823804246415772692007 104780735706369623659038011)
            ·
              refine ⟨157171103559554435488557017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104780735706369623659038011 157171103559554435488557017)
              ·
                refine ⟨117878327669665826616417763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157171103559554435488557017 117878327669665826616417763)
                ·
                  refine ⟨176817491504498739924626645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117878327669665826616417763 176817491504498739924626645)
                  ·
                    refine ⟨4144159957136689216983437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176817491504498739924626645 4144159957136689216983437)
                    ·
                      refine ⟨1554059983926258456368789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144159957136689216983437 1554059983926258456368789)
                      ·
                        rfl

theorem cell23_3026521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_3026521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026521 prefixEnd_3026521 := by exact prefixLift 3026521
  have htrace : WordTrace (prefixWord ++ tailWord_3026521) baseStart_3026521 baseEnd_3026521 := by
    simpa [prefixWord, tailWord_3026521, baseEnd_3026521] using wordTrace_append hprefix tailTrace_3026521
  have hstable : (prefixWord ++ tailWord_3026521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026521).length < 2 ^ (prefixWord ++ tailWord_3026521).sum := by decide
  have hdescent : baseEnd_3026521 < baseStart_3026521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026531 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3026531 : Nat := 118140960795 + 3026531 * 2 ^ 59
def prefixEnd_3026531 : Nat := 4983230072969 + 3 ^ 40 * 3026531 * 2
def baseEnd_3026531 : Nat := 1554065118732803417243743

theorem tailTrace_3026531 : CollatzResearch.WordTrace tailWord_3026531 prefixEnd_3026531 1554065118732803417243743 := by
  unfold tailWord_3026531
  simp only [CollatzResearch.WordTrace]
  refine ⟨110386654198402552188167447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73591102798935034792111631 110386654198402552188167447)
  ·
    refine ⟨165579981297603828282251171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110386654198402552188167447 165579981297603828282251171)
    ·
      refine ⟨248369971946405742423376757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165579981297603828282251171 248369971946405742423376757)
      ·
        refine ⟨23284684869975538352191571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248369971946405742423376757 23284684869975538352191571)
        ·
          refine ⟨34927027304963307528287357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23284684869975538352191571 34927027304963307528287357)
          ·
            refine ⟨13097635239361240323107759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34927027304963307528287357 13097635239361240323107759)
            ·
              refine ⟨19646452859041860484661639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097635239361240323107759 19646452859041860484661639)
              ·
                refine ⟨29469679288562790726992459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19646452859041860484661639 29469679288562790726992459)
                ·
                  refine ⟨44204518932844186090488689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29469679288562790726992459 44204518932844186090488689)
                  ·
                    refine ⟨33153389199633139567866517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44204518932844186090488689 33153389199633139567866517)
                    ·
                      refine ⟨1554065118732803417243743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33153389199633139567866517 1554065118732803417243743)
                      ·
                        rfl

theorem cell23_3026531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3026531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026531 prefixEnd_3026531 := by exact prefixLift 3026531
  have htrace : WordTrace (prefixWord ++ tailWord_3026531) baseStart_3026531 baseEnd_3026531 := by
    simpa [prefixWord, tailWord_3026531, baseEnd_3026531] using wordTrace_append hprefix tailTrace_3026531
  have hstable : (prefixWord ++ tailWord_3026531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026531).length < 2 ^ (prefixWord ++ tailWord_3026531).sum := by decide
  have hdescent : baseEnd_3026531 < baseStart_3026531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026565 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 2, 3, 2]
def baseStart_3026565 : Nat := 118140960795 + 3026565 * 2 ^ 59
def prefixEnd_3026565 : Nat := 4983230072969 + 3 ^ 40 * 3026565 * 2
def baseEnd_3026565 : Nat := 1554082577075056284218587

theorem tailTrace_3026565 : CollatzResearch.WordTrace tailWord_3026565 prefixEnd_3026565 1554082577075056284218587 := by
  unfold tailWord_3026565
  simp only [CollatzResearch.WordTrace]
  refine ⟨110387894280279375994905149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73591929520186250663270099 110387894280279375994905149)
  ·
    refine ⟨41395460355104765998089431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110387894280279375994905149 41395460355104765998089431)
    ·
      refine ⟨62093190532657148997134147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41395460355104765998089431 62093190532657148997134147)
      ·
        refine ⟨93139785798985723495701221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62093190532657148997134147 93139785798985723495701221)
        ·
          refine ⟨17463709837309823155443979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93139785798985723495701221 17463709837309823155443979)
          ·
            refine ⟨26195564755964734733165969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17463709837309823155443979 26195564755964734733165969)
            ·
              refine ⟨19646673566973551049874477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26195564755964734733165969 19646673566973551049874477)
              ·
                refine ⟨7367502587615081643702929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19646673566973551049874477 7367502587615081643702929)
                ·
                  refine ⟨5525626940711311232777197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7367502587615081643702929 5525626940711311232777197)
                  ·
                    refine ⟨2072110102766741712291449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5525626940711311232777197 2072110102766741712291449)
                    ·
                      refine ⟨1554082577075056284218587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072110102766741712291449 1554082577075056284218587)
                      ·
                        rfl

theorem cell23_3026565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_3026565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026565 prefixEnd_3026565 := by exact prefixLift 3026565
  have htrace : WordTrace (prefixWord ++ tailWord_3026565) baseStart_3026565 baseEnd_3026565 := by
    simpa [prefixWord, tailWord_3026565, baseEnd_3026565] using wordTrace_append hprefix tailTrace_3026565
  have hstable : (prefixWord ++ tailWord_3026565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026565).length < 2 ^ (prefixWord ++ tailWord_3026565).sum := by decide
  have hdescent : baseEnd_3026565 < baseStart_3026565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026571 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 3, 6]
def baseStart_3026571 : Nat := 118140960795 + 3026571 * 2 ^ 59
def prefixEnd_3026571 : Nat := 4983230072969 + 3 ^ 40 * 3026571 * 2
def baseEnd_3026571 : Nat := 518028552652994420247853

theorem tailTrace_3026571 : CollatzResearch.WordTrace tailWord_3026571 prefixEnd_3026571 518028552652994420247853 := by
  unfold tailWord_3026571
  simp only [CollatzResearch.WordTrace]
  refine ⟨110388113118257639019623567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73592075412171759346415711 110388113118257639019623567)
  ·
    refine ⟨165582169677386458529435351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110388113118257639019623567 165582169677386458529435351)
    ·
      refine ⟨248373254516079687794153027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165582169677386458529435351 248373254516079687794153027)
      ·
        refine ⟨372559881774119531691229541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248373254516079687794153027 372559881774119531691229541)
        ·
          refine ⟨69854977832647412192105539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372559881774119531691229541 69854977832647412192105539)
          ·
            refine ⟨104782466748971118288158309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69854977832647412192105539 104782466748971118288158309)
            ·
              refine ⟨19646712515432084679029683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104782466748971118288158309 19646712515432084679029683)
              ·
                refine ⟨29470068773148127018544525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19646712515432084679029683 29470068773148127018544525)
                ·
                  refine ⟨11051275789930547631954197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29470068773148127018544525 11051275789930547631954197)
                  ·
                    refine ⟨518028552652994420247853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11051275789930547631954197 518028552652994420247853)
                    ·
                      rfl

theorem cell23_3026571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_3026571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026571 prefixEnd_3026571 := by exact prefixLift 3026571
  have htrace : WordTrace (prefixWord ++ tailWord_3026571) baseStart_3026571 baseEnd_3026571 := by
    simpa [prefixWord, tailWord_3026571, baseEnd_3026571] using wordTrace_append hprefix tailTrace_3026571
  have hstable : (prefixWord ++ tailWord_3026571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026571).length < 2 ^ (prefixWord ++ tailWord_3026571).sum := by decide
  have hdescent : baseEnd_3026571 < baseStart_3026571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026615 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_3026615 : Nat := 118140960795 + 3026615 * 2 ^ 59
def prefixEnd_3026615 : Nat := 4983230072969 + 3 ^ 40 * 3026615 * 2
def baseEnd_3026615 : Nat := 1554108251107781088593357

theorem tailTrace_3026615 : CollatzResearch.WordTrace tailWord_3026615 prefixEnd_3026615 1554108251107781088593357 := by
  unfold tailWord_3026615
  simp only [CollatzResearch.WordTrace]
  refine ⟨110389717930098234534225299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73593145286732156356150199 110389717930098234534225299)
  ·
    refine ⟨165584576895147351801337949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110389717930098234534225299 165584576895147351801337949)
    ·
      refine ⟨62094216335680256925501731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165584576895147351801337949 62094216335680256925501731)
      ·
        refine ⟨93141324503520385388252597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62094216335680256925501731 93141324503520385388252597)
        ·
          refine ⟨8731999172205036130148681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93141324503520385388252597 8731999172205036130148681)
          ·
            refine ⟨6548999379153777097611511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8731999172205036130148681 6548999379153777097611511)
            ·
              refine ⟨9823499068730665646417267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548999379153777097611511 9823499068730665646417267)
              ·
                refine ⟨14735248603095998469625901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823499068730665646417267 14735248603095998469625901)
                ·
                  refine ⟨5525718226160999426109713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14735248603095998469625901 5525718226160999426109713)
                  ·
                    refine ⟨4144288669620749569582285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525718226160999426109713 4144288669620749569582285)
                    ·
                      refine ⟨1554108251107781088593357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144288669620749569582285 1554108251107781088593357)
                      ·
                        rfl

theorem cell23_3026615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_3026615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026615 prefixEnd_3026615 := by exact prefixLift 3026615
  have htrace : WordTrace (prefixWord ++ tailWord_3026615) baseStart_3026615 baseEnd_3026615 := by
    simpa [prefixWord, tailWord_3026615, baseEnd_3026615] using wordTrace_append hprefix tailTrace_3026615
  have hstable : (prefixWord ++ tailWord_3026615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026615).length < 2 ^ (prefixWord ++ tailWord_3026615).sum := by decide
  have hdescent : baseEnd_3026615 < baseStart_3026615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026632 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_3026632 : Nat := 118140960795 + 3026632 * 2 ^ 59
def prefixEnd_3026632 : Nat := 4983230072969 + 3 ^ 40 * 3026632 * 2
def baseEnd_3026632 : Nat := 1554116980278907522080779

theorem tailTrace_3026632 : CollatzResearch.WordTrace tailWord_3026632 prefixEnd_3026632 1554116980278907522080779 := by
  unfold tailWord_3026632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55195168985518323218797075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73593558647357764291729433 55195168985518323218797075)
  ·
    refine ⟨82792753478277484828195613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55195168985518323218797075 82792753478277484828195613)
    ·
      refine ⟨31047282554354056810573355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82792753478277484828195613 31047282554354056810573355)
      ·
        refine ⟨46570923831531085215860033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31047282554354056810573355 46570923831531085215860033)
        ·
          refine ⟨34928192873648313911895025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46570923831531085215860033 34928192873648313911895025)
          ·
            refine ⟨26196144655236235433921269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34928192873648313911895025 26196144655236235433921269)
            ·
              refine ⟨2455888561428397071930119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26196144655236235433921269 2455888561428397071930119)
              ·
                refine ⟨3683832842142595607895179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455888561428397071930119 3683832842142595607895179)
                ·
                  refine ⟨5525749263213893411842769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683832842142595607895179 5525749263213893411842769)
                  ·
                    refine ⟨4144311947410420058882077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525749263213893411842769 4144311947410420058882077)
                    ·
                      refine ⟨1554116980278907522080779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144311947410420058882077 1554116980278907522080779)
                      ·
                        rfl

theorem cell23_3026632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_3026632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026632 prefixEnd_3026632 := by exact prefixLift 3026632
  have htrace : WordTrace (prefixWord ++ tailWord_3026632) baseStart_3026632 baseEnd_3026632 := by
    simpa [prefixWord, tailWord_3026632, baseEnd_3026632] using wordTrace_append hprefix tailTrace_3026632
  have hstable : (prefixWord ++ tailWord_3026632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026632).length < 2 ^ (prefixWord ++ tailWord_3026632).sum := by decide
  have hdescent : baseEnd_3026632 < baseStart_3026632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026652 : List Nat := [2, 2, 5, 1, 2, 2, 1, 8]
def baseStart_3026652 : Nat := 118140960795 + 3026652 * 2 ^ 59
def prefixEnd_3026652 : Nat := 4983230072969 + 3 ^ 40 * 3026652 * 2
def baseEnd_3026652 : Nat := 57560268514518423845581

theorem tailTrace_3026652 : CollatzResearch.WordTrace tailWord_3026652 prefixEnd_3026652 57560268514518423845581 := by
  unfold tailWord_3026652
  simp only [CollatzResearch.WordTrace]
  refine ⟨55195533715482094926661105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73594044953976126568881473 55195533715482094926661105)
  ·
    refine ⟨41396650286611571194995829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55195533715482094926661105 41396650286611571194995829)
    ·
      refine ⟨3880935964369834799530859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41396650286611571194995829 3880935964369834799530859)
      ·
        refine ⟨5821403946554752199296289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880935964369834799530859 5821403946554752199296289)
        ·
          refine ⟨4366052959916064149472217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5821403946554752199296289 4366052959916064149472217)
          ·
            refine ⟨3274539719937048112104163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4366052959916064149472217 3274539719937048112104163)
            ·
              refine ⟨4911809579905572168156245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274539719937048112104163 4911809579905572168156245)
              ·
                refine ⟨57560268514518423845581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4911809579905572168156245 57560268514518423845581)
                ·
                  rfl

theorem cell23_3026652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 8].length) (baseStart_3026652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026652 prefixEnd_3026652 := by exact prefixLift 3026652
  have htrace : WordTrace (prefixWord ++ tailWord_3026652) baseStart_3026652 baseEnd_3026652 := by
    simpa [prefixWord, tailWord_3026652, baseEnd_3026652] using wordTrace_append hprefix tailTrace_3026652
  have hstable : (prefixWord ++ tailWord_3026652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026652).length < 2 ^ (prefixWord ++ tailWord_3026652).sum := by decide
  have hdescent : baseEnd_3026652 < baseStart_3026652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026655 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 5, 3, 2]
def baseStart_3026655 : Nat := 118140960795 + 3026655 * 2 ^ 59
def prefixEnd_3026655 : Nat := 4983230072969 + 3 ^ 40 * 3026655 * 2
def baseEnd_3026655 : Nat := 1554128790333960932093173

theorem tailTrace_3026655 : CollatzResearch.WordTrace tailWord_3026655 prefixEnd_3026655 1554128790333960932093173 := by
  unfold tailWord_3026655
  simp only [CollatzResearch.WordTrace]
  refine ⟨110391176849953321365681419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73594117899968880910454279 110391176849953321365681419)
  ·
    refine ⟨165586765274929982048522129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110391176849953321365681419 165586765274929982048522129)
    ·
      refine ⟨124190073956197486536391597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165586765274929982048522129 124190073956197486536391597)
      ·
        refine ⟨46571277733574057451146849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124190073956197486536391597 46571277733574057451146849)
        ·
          refine ⟨34928458300180543088360137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46571277733574057451146849 34928458300180543088360137)
          ·
            refine ⟨26196343725135407316270103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34928458300180543088360137 26196343725135407316270103)
            ·
              refine ⟨39294515587703110974405155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26196343725135407316270103 39294515587703110974405155)
              ·
                refine ⟨58941773381554666461607733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39294515587703110974405155 58941773381554666461607733)
                ·
                  refine ⟨5525791254520749980775725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58941773381554666461607733 5525791254520749980775725)
                  ·
                    refine ⟨2072171720445281242790897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5525791254520749980775725 2072171720445281242790897)
                    ·
                      refine ⟨1554128790333960932093173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072171720445281242790897 1554128790333960932093173)
                      ·
                        rfl

theorem cell23_3026655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_3026655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026655 prefixEnd_3026655 := by exact prefixLift 3026655
  have htrace : WordTrace (prefixWord ++ tailWord_3026655) baseStart_3026655 baseEnd_3026655 := by
    simpa [prefixWord, tailWord_3026655, baseEnd_3026655] using wordTrace_append hprefix tailTrace_3026655
  have hstable : (prefixWord ++ tailWord_3026655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026655).length < 2 ^ (prefixWord ++ tailWord_3026655).sum := by decide
  have hdescent : baseEnd_3026655 < baseStart_3026655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026685 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_3026685 : Nat := 118140960795 + 3026685 * 2 ^ 59
def prefixEnd_3026685 : Nat := 4983230072969 + 3 ^ 40 * 3026685 * 2
def baseEnd_3026685 : Nat := 1554144194753595814718035

theorem tailTrace_3026685 : CollatzResearch.WordTrace tailWord_3026685 prefixEnd_3026685 1554144194753595814718035 := by
  unfold tailWord_3026685
  simp only [CollatzResearch.WordTrace]
  refine ⟨110392271039844636489273509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73594847359896424326182339 110392271039844636489273509)
  ·
    refine ⟨20698550819970869341738783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110392271039844636489273509 20698550819970869341738783)
    ·
      refine ⟨31047826229956304012608175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20698550819970869341738783 31047826229956304012608175)
      ·
        refine ⟨46571739344934456018912263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31047826229956304012608175 46571739344934456018912263)
        ·
          refine ⟨69857609017401684028368395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46571739344934456018912263 69857609017401684028368395)
          ·
            refine ⟨104786413526102526042552593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69857609017401684028368395 104786413526102526042552593)
            ·
              refine ⟨78589810144576894531914445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104786413526102526042552593 78589810144576894531914445)
              ·
                refine ⟨29471178804216335449467917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78589810144576894531914445 29471178804216335449467917)
                ·
                  refine ⟨11051692051581125793550469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29471178804216335449467917 11051692051581125793550469)
                  ·
                    refine ⟨2072192259671461086290713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11051692051581125793550469 2072192259671461086290713)
                    ·
                      refine ⟨1554144194753595814718035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072192259671461086290713 1554144194753595814718035)
                      ·
                        rfl

theorem cell23_3026685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_3026685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026685 prefixEnd_3026685 := by exact prefixLift 3026685
  have htrace : WordTrace (prefixWord ++ tailWord_3026685) baseStart_3026685 baseEnd_3026685 := by
    simpa [prefixWord, tailWord_3026685, baseEnd_3026685] using wordTrace_append hprefix tailTrace_3026685
  have hstable : (prefixWord ++ tailWord_3026685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026685).length < 2 ^ (prefixWord ++ tailWord_3026685).sum := by decide
  have hdescent : baseEnd_3026685 < baseStart_3026685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026688 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_3026688 : Nat := 118140960795 + 3026688 * 2 ^ 59
def prefixEnd_3026688 : Nat := 4983230072969 + 3 ^ 40 * 3026688 * 2
def baseEnd_3026688 : Nat := 1554145735195559302980521

theorem tailTrace_3026688 : CollatzResearch.WordTrace tailWord_3026688 prefixEnd_3026688 1554145735195559302980521 := by
  unfold tailWord_3026688
  simp only [CollatzResearch.WordTrace]
  refine ⟨55196190229416884000816359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73594920305889178667755145 55196190229416884000816359)
  ·
    refine ⟨82794285344125326001224539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55196190229416884000816359 82794285344125326001224539)
    ·
      refine ⟨124191428016187989001836809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82794285344125326001224539 124191428016187989001836809)
      ·
        refine ⟨93143571012140991751377607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124191428016187989001836809 93143571012140991751377607)
        ·
          refine ⟨139715356518211487627066411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93143571012140991751377607 139715356518211487627066411)
          ·
            refine ⟨209573034777317231440599617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139715356518211487627066411 209573034777317231440599617)
            ·
              refine ⟨157179776082987923580449713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209573034777317231440599617 157179776082987923580449713)
              ·
                refine ⟨117884832062240942685337285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157179776082987923580449713 117884832062240942685337285)
                ·
                  refine ⟨22103406011670176753500741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117884832062240942685337285 22103406011670176753500741)
                  ·
                    refine ⟨4144388627188158141281389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22103406011670176753500741 4144388627188158141281389)
                    ·
                      refine ⟨1554145735195559302980521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144388627188158141281389 1554145735195559302980521)
                      ·
                        rfl

theorem cell23_3026688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_3026688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026688 prefixEnd_3026688 := by exact prefixLift 3026688
  have htrace : WordTrace (prefixWord ++ tailWord_3026688) baseStart_3026688 baseEnd_3026688 := by
    simpa [prefixWord, tailWord_3026688, baseEnd_3026688] using wordTrace_append hprefix tailTrace_3026688
  have hstable : (prefixWord ++ tailWord_3026688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026688).length < 2 ^ (prefixWord ++ tailWord_3026688).sum := by decide
  have hdescent : baseEnd_3026688 < baseStart_3026688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026689 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_3026689 : Nat := 118140960795 + 3026689 * 2 ^ 59
def prefixEnd_3026689 : Nat := 4983230072969 + 3 ^ 40 * 3026689 * 2
def baseEnd_3026689 : Nat := 1554146248676213799068017

theorem tailTrace_3026689 : CollatzResearch.WordTrace tailWord_3026689 prefixEnd_3026689 1554146248676213799068017 := by
  unfold tailWord_3026689
  simp only [CollatzResearch.WordTrace]
  refine ⟨110392416931830145172419121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73594944621220096781612747 110392416931830145172419121)
  ·
    refine ⟨82794312698872608879314341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110392416931830145172419121 82794312698872608879314341)
    ·
      refine ⟨15523933631038614164871439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82794312698872608879314341 15523933631038614164871439)
      ·
        refine ⟨23285900446557921247307159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15523933631038614164871439 23285900446557921247307159)
        ·
          refine ⟨34928850669836881870960739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23285900446557921247307159 34928850669836881870960739)
          ·
            refine ⟨52393276004755322806441109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34928850669836881870960739 52393276004755322806441109)
            ·
              refine ⟨2455934812722905756551927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52393276004755322806441109 2455934812722905756551927)
              ·
                refine ⟨3683902219084358634827891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455934812722905756551927 3683902219084358634827891)
                ·
                  refine ⟨5525853328626537952241837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683902219084358634827891 5525853328626537952241837)
                  ·
                    refine ⟨2072194998234951732090689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5525853328626537952241837 2072194998234951732090689)
                    ·
                      refine ⟨1554146248676213799068017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072194998234951732090689 1554146248676213799068017)
                      ·
                        rfl

theorem cell23_3026689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_3026689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026689 prefixEnd_3026689 := by exact prefixLift 3026689
  have htrace : WordTrace (prefixWord ++ tailWord_3026689) baseStart_3026689 baseEnd_3026689 := by
    simpa [prefixWord, tailWord_3026689, baseEnd_3026689] using wordTrace_append hprefix tailTrace_3026689
  have hstable : (prefixWord ++ tailWord_3026689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026689).length < 2 ^ (prefixWord ++ tailWord_3026689).sum := by decide
  have hdescent : baseEnd_3026689 < baseStart_3026689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026755 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 2, 5]
def baseStart_3026755 : Nat := 118140960795 + 3026755 * 2 ^ 59
def prefixEnd_3026755 : Nat := 4983230072969 + 3 ^ 40 * 3026755 * 2
def baseEnd_3026755 : Nat := 518060046133136846947571

theorem tailTrace_3026755 : CollatzResearch.WordTrace tailWord_3026755 prefixEnd_3026755 518060046133136846947571 := by
  unfold tailWord_3026755
  simp only [CollatzResearch.WordTrace]
  refine ⟨110394824149591038444321719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73596549433060692296214479 110394824149591038444321719)
  ·
    refine ⟨165592236224386557666482579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110394824149591038444321719 165592236224386557666482579)
    ·
      refine ⟨248388354336579836499723869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165592236224386557666482579 248388354336579836499723869)
      ·
        refine ⟨93145632876217438687396451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248388354336579836499723869 93145632876217438687396451)
        ·
          refine ⟨139718449314326158031094677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93145632876217438687396451 139718449314326158031094677)
          ·
            refine ⟨6549302311609038657707563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139718449314326158031094677 6549302311609038657707563)
            ·
              refine ⟨9823953467413557986561345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549302311609038657707563 9823953467413557986561345)
              ·
                refine ⟨7367965100560168489921009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9823953467413557986561345 7367965100560168489921009)
                ·
                  refine ⟨5525973825420126367440757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7367965100560168489921009 5525973825420126367440757)
                  ·
                    refine ⟨518060046133136846947571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5525973825420126367440757 518060046133136846947571)
                    ·
                      rfl

theorem cell23_3026755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 5].length) (baseStart_3026755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026755 prefixEnd_3026755 := by exact prefixLift 3026755
  have htrace : WordTrace (prefixWord ++ tailWord_3026755) baseStart_3026755 baseEnd_3026755 := by
    simpa [prefixWord, tailWord_3026755, baseEnd_3026755] using wordTrace_append hprefix tailTrace_3026755
  have hstable : (prefixWord ++ tailWord_3026755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026755).length < 2 ^ (prefixWord ++ tailWord_3026755).sum := by decide
  have hdescent : baseEnd_3026755 < baseStart_3026755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026785 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 5, 4]
def baseStart_3026785 : Nat := 118140960795 + 3026785 * 2 ^ 59
def prefixEnd_3026785 : Nat := 4983230072969 + 3 ^ 40 * 3026785 * 2
def baseEnd_3026785 : Nat := 518065180939681807822525

theorem tailTrace_3026785 : CollatzResearch.WordTrace tailWord_3026785 prefixEnd_3026785 518065180939681807822525 := by
  unfold tailWord_3026785
  simp only [CollatzResearch.WordTrace]
  refine ⟨110395918339482353567913809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73597278892988235711942539 110395918339482353567913809)
  ·
    refine ⟨82796938754611765175935357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110395918339482353567913809 82796938754611765175935357)
    ·
      refine ⟨31048852032979411940975759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82796938754611765175935357 31048852032979411940975759)
      ·
        refine ⟨46573278049469117911463639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31048852032979411940975759 46573278049469117911463639)
        ·
          refine ⟨69859917074203676867195459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46573278049469117911463639 69859917074203676867195459)
          ·
            refine ⟨104789875611305515300793189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69859917074203676867195459 104789875611305515300793189)
            ·
              refine ⟨19648101677119784118898723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104789875611305515300793189 19648101677119784118898723)
              ·
                refine ⟨29472152515679676178348085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19648101677119784118898723 29472152515679676178348085)
                ·
                  refine ⟨2763014298344969641720133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29472152515679676178348085 2763014298344969641720133)
                  ·
                    refine ⟨518065180939681807822525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763014298344969641720133 518065180939681807822525)
                    ·
                      rfl

theorem cell23_3026785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_3026785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026785 prefixEnd_3026785 := by exact prefixLift 3026785
  have htrace : WordTrace (prefixWord ++ tailWord_3026785) baseStart_3026785 baseEnd_3026785 := by
    simpa [prefixWord, tailWord_3026785, baseEnd_3026785] using wordTrace_append hprefix tailTrace_3026785
  have hstable : (prefixWord ++ tailWord_3026785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026785).length < 2 ^ (prefixWord ++ tailWord_3026785).sum := by decide
  have hdescent : baseEnd_3026785 < baseStart_3026785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026792 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3026792 : Nat := 118140960795 + 3026792 * 2 ^ 59
def prefixEnd_3026792 : Nat := 4983230072969 + 3 ^ 40 * 3026792 * 2
def baseEnd_3026792 : Nat := 1554199137183626896080043

theorem tailTrace_3026792 : CollatzResearch.WordTrace tailWord_3026792 prefixEnd_3026792 1554199137183626896080043 := by
  unfold tailWord_3026792
  simp only [CollatzResearch.WordTrace]
  refine ⟨55198086825228496881709315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73597449100304662508945753 55198086825228496881709315)
  ·
    refine ⟨82797130237842745322563973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55198086825228496881709315 82797130237842745322563973)
    ·
      refine ⟨15524461919595514747980745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82797130237842745322563973 15524461919595514747980745)
      ·
        refine ⟨11643346439696636060985559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15524461919595514747980745 11643346439696636060985559)
        ·
          refine ⟨17465019659544954091478339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11643346439696636060985559 17465019659544954091478339)
          ·
            refine ⟨26197529489317431137217509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17465019659544954091478339 26197529489317431137217509)
            ·
              refine ⟨4912036779247018338228283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26197529489317431137217509 4912036779247018338228283)
              ·
                refine ⟨7368055168870527507342425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912036779247018338228283 7368055168870527507342425)
                ·
                  refine ⟨5526041376652895630506819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7368055168870527507342425 5526041376652895630506819)
                  ·
                    refine ⟨8289062064979343445760229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526041376652895630506819 8289062064979343445760229)
                    ·
                      refine ⟨1554199137183626896080043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8289062064979343445760229 1554199137183626896080043)
                      ·
                        rfl

theorem cell23_3026792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3026792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026792 prefixEnd_3026792 := by exact prefixLift 3026792
  have htrace : WordTrace (prefixWord ++ tailWord_3026792) baseStart_3026792 baseEnd_3026792 := by
    simpa [prefixWord, tailWord_3026792, baseEnd_3026792] using wordTrace_append hprefix tailTrace_3026792
  have hstable : (prefixWord ++ tailWord_3026792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026792).length < 2 ^ (prefixWord ++ tailWord_3026792).sum := by decide
  have hdescent : baseEnd_3026792 < baseStart_3026792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026805 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3026805 : Nat := 118140960795 + 3026805 * 2 ^ 59
def prefixEnd_3026805 : Nat := 4983230072969 + 3 ^ 40 * 3026805 * 2
def baseEnd_3026805 : Nat := 1554205812432135345217483

theorem tailTrace_3026805 : CollatzResearch.WordTrace tailWord_3026805 prefixEnd_3026805 1554205812432135345217483 := by
  unfold tailWord_3026805
  simp only [CollatzResearch.WordTrace]
  refine ⟨110396647799409896983641869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73597765199606597989094579 110396647799409896983641869)
  ·
    refine ⟨41398742924778711368865701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110396647799409896983641869 41398742924778711368865701)
    ·
      refine ⟨7762264298396008381662319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41398742924778711368865701 7762264298396008381662319)
      ·
        refine ⟨11643396447594012572493479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762264298396008381662319 11643396447594012572493479)
        ·
          refine ⟨17465094671391018858740219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11643396447594012572493479 17465094671391018858740219)
          ·
            refine ⟨26197642007086528288110329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17465094671391018858740219 26197642007086528288110329)
            ·
              refine ⟨19648231505314896216082747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26197642007086528288110329 19648231505314896216082747)
              ·
                refine ⟨29472347257972344324124121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19648231505314896216082747 29472347257972344324124121)
                ·
                  refine ⟨22104260443479258243093091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29472347257972344324124121 22104260443479258243093091)
                  ·
                    refine ⟨33156390665218887364639637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22104260443479258243093091 33156390665218887364639637)
                    ·
                      refine ⟨1554205812432135345217483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33156390665218887364639637 1554205812432135345217483)
                      ·
                        rfl

theorem cell23_3026805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3026805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026805 prefixEnd_3026805 := by exact prefixLift 3026805
  have htrace : WordTrace (prefixWord ++ tailWord_3026805) baseStart_3026805 baseEnd_3026805 := by
    simpa [prefixWord, tailWord_3026805, baseEnd_3026805] using wordTrace_append hprefix tailTrace_3026805
  have hstable : (prefixWord ++ tailWord_3026805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026805).length < 2 ^ (prefixWord ++ tailWord_3026805).sum := by decide
  have hdescent : baseEnd_3026805 < baseStart_3026805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026819 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 1, 4]
def baseStart_3026819 : Nat := 118140960795 + 3026819 * 2 ^ 59
def prefixEnd_3026819 : Nat := 4983230072969 + 3 ^ 40 * 3026819 * 2
def baseEnd_3026819 : Nat := 518071000387099430147473

theorem tailTrace_3026819 : CollatzResearch.WordTrace tailWord_3026819 prefixEnd_3026819 518071000387099430147473 := by
  unfold tailWord_3026819
  simp only [CollatzResearch.WordTrace]
  refine ⟨110397158421359177374651511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73598105614239451583101007 110397158421359177374651511)
  ·
    refine ⟨165595737632038766061977267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110397158421359177374651511 165595737632038766061977267)
    ·
      refine ⟨248393606448058149092965901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165595737632038766061977267 248393606448058149092965901)
      ·
        refine ⟨93147602418021805909862213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248393606448058149092965901 93147602418021805909862213)
        ·
          refine ⟨17465175453379088608099165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93147602418021805909862213 17465175453379088608099165)
          ·
            refine ⟨6549440795017158228037187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17465175453379088608099165 6549440795017158228037187)
            ·
              refine ⟨9824161192525737342055781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549440795017158228037187 9824161192525737342055781)
              ·
                refine ⟨1842030223598575751635459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9824161192525737342055781 1842030223598575751635459)
                ·
                  refine ⟨2763045335397863627453189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842030223598575751635459 2763045335397863627453189)
                  ·
                    refine ⟨518071000387099430147473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763045335397863627453189 518071000387099430147473)
                    ·
                      rfl

theorem cell23_3026819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 4].length) (baseStart_3026819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026819 prefixEnd_3026819 := by exact prefixLift 3026819
  have htrace : WordTrace (prefixWord ++ tailWord_3026819) baseStart_3026819 baseEnd_3026819 := by
    simpa [prefixWord, tailWord_3026819, baseEnd_3026819] using wordTrace_append hprefix tailTrace_3026819
  have hstable : (prefixWord ++ tailWord_3026819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026819).length < 2 ^ (prefixWord ++ tailWord_3026819).sum := by decide
  have hdescent : baseEnd_3026819 < baseStart_3026819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026846 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3026846 : Nat := 118140960795 + 3026846 * 2 ^ 59
def prefixEnd_3026846 : Nat := 4983230072969 + 3 ^ 40 * 3026846 * 2
def baseEnd_3026846 : Nat := 1554226865138969684804795

theorem tailTrace_3026846 : CollatzResearch.WordTrace tailWord_3026846 prefixEnd_3026846 1554226865138969684804795 := by
  unfold tailWord_3026846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799767899032670123235549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73598762128174240657256261 13799767899032670123235549)
  ·
    refine ⟨5174912962137251296213331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13799767899032670123235549 5174912962137251296213331)
    ·
      refine ⟨7762369443205876944319997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174912962137251296213331 7762369443205876944319997)
      ·
        refine ⟨2910888541202203854119999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7762369443205876944319997 2910888541202203854119999)
        ·
          refine ⟨4366332811803305781179999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910888541202203854119999 4366332811803305781179999)
          ·
            refine ⟨6549499217704958671769999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366332811803305781179999 6549499217704958671769999)
            ·
              refine ⟨9824248826557438007654999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549499217704958671769999 9824248826557438007654999)
              ·
                refine ⟨14736373239836157011482499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824248826557438007654999 14736373239836157011482499)
                ·
                  refine ⟨22104559859754235517223749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14736373239836157011482499 22104559859754235517223749)
                  ·
                    refine ⟨4144604973703919159479453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22104559859754235517223749 4144604973703919159479453)
                    ·
                      refine ⟨1554226865138969684804795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144604973703919159479453 1554226865138969684804795)
                      ·
                        rfl

theorem cell23_3026846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3026846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026846 prefixEnd_3026846 := by exact prefixLift 3026846
  have htrace : WordTrace (prefixWord ++ tailWord_3026846) baseStart_3026846 baseEnd_3026846 := by
    simpa [prefixWord, tailWord_3026846, baseEnd_3026846] using wordTrace_append hprefix tailTrace_3026846
  have hstable : (prefixWord ++ tailWord_3026846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026846).length < 2 ^ (prefixWord ++ tailWord_3026846).sum := by decide
  have hdescent : baseEnd_3026846 < baseStart_3026846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026885 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_3026885 : Nat := 118140960795 + 3026885 * 2 ^ 59
def prefixEnd_3026885 : Nat := 4983230072969 + 3 ^ 40 * 3026885 * 2
def baseEnd_3026885 : Nat := 1554246890884495032217115

theorem tailTrace_3026885 : CollatzResearch.WordTrace tailWord_3026885 prefixEnd_3026885 1554246890884495032217115 := by
  unfold tailWord_3026885
  simp only [CollatzResearch.WordTrace]
  refine ⟨110399565639120070646554109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73599710426080047097702739 110399565639120070646554109)
  ·
    refine ⟨41399837114670026492457791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110399565639120070646554109 41399837114670026492457791)
    ·
      refine ⟨62099755672005039738686687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41399837114670026492457791 62099755672005039738686687)
      ·
        refine ⟨93149633508007559608030031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62099755672005039738686687 93149633508007559608030031)
        ·
          refine ⟨139724450262011339412045047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93149633508007559608030031 139724450262011339412045047)
          ·
            refine ⟨209586675393017009118067571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139724450262011339412045047 209586675393017009118067571)
            ·
              refine ⟨314380013089525513677101357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209586675393017009118067571 314380013089525513677101357)
              ·
                refine ⟨117892504908572067628913009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314380013089525513677101357 117892504908572067628913009)
                ·
                  refine ⟨88419378681429050721684757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117892504908572067628913009 88419378681429050721684757)
                  ·
                    refine ⟨4144658375691986752578973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88419378681429050721684757 4144658375691986752578973)
                    ·
                      refine ⟨1554246890884495032217115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144658375691986752578973 1554246890884495032217115)
                      ·
                        rfl

theorem cell23_3026885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_3026885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026885 prefixEnd_3026885 := by exact prefixLift 3026885
  have htrace : WordTrace (prefixWord ++ tailWord_3026885) baseStart_3026885 baseEnd_3026885 := by
    simpa [prefixWord, tailWord_3026885, baseEnd_3026885] using wordTrace_append hprefix tailTrace_3026885
  have hstable : (prefixWord ++ tailWord_3026885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026885).length < 2 ^ (prefixWord ++ tailWord_3026885).sum := by decide
  have hdescent : baseEnd_3026885 < baseStart_3026885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026892 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_3026892 : Nat := 118140960795 + 3026892 * 2 ^ 59
def prefixEnd_3026892 : Nat := 4983230072969 + 3 ^ 40 * 3026892 * 2
def baseEnd_3026892 : Nat := 518083495083025501609861

theorem tailTrace_3026892 : CollatzResearch.WordTrace tailWord_3026892 prefixEnd_3026892 518083495083025501609861 := by
  unfold tailWord_3026892
  simp only [CollatzResearch.WordTrace]
  refine ⟨55199910475047355421029465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73599880633396473894705953 55199910475047355421029465)
  ·
    refine ⟨41399932856285516565772099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55199910475047355421029465 41399932856285516565772099)
    ·
      refine ⟨62099899284428274848658149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41399932856285516565772099 62099899284428274848658149)
      ·
        refine ⟨11643731115830301534123403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62099899284428274848658149 11643731115830301534123403)
        ·
          refine ⟨17465596673745452301185105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11643731115830301534123403 17465596673745452301185105)
          ·
            refine ⟨13099197505309089225888829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17465596673745452301185105 13099197505309089225888829)
            ·
              refine ⟨4912199064490908459708311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13099197505309089225888829 4912199064490908459708311)
              ·
                refine ⟨7368298596736362689562467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912199064490908459708311 7368298596736362689562467)
                ·
                  refine ⟨11052447895104544034343701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368298596736362689562467 11052447895104544034343701)
                  ·
                    refine ⟨518083495083025501609861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11052447895104544034343701 518083495083025501609861)
                    ·
                      rfl

theorem cell23_3026892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_3026892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026892 prefixEnd_3026892 := by exact prefixLift 3026892
  have htrace : WordTrace (prefixWord ++ tailWord_3026892) baseStart_3026892 baseEnd_3026892 := by
    simpa [prefixWord, tailWord_3026892, baseEnd_3026892] using wordTrace_append hprefix tailTrace_3026892
  have hstable : (prefixWord ++ tailWord_3026892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026892).length < 2 ^ (prefixWord ++ tailWord_3026892).sum := by decide
  have hdescent : baseEnd_3026892 < baseStart_3026892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026895 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_3026895 : Nat := 118140960795 + 3026895 * 2 ^ 59
def prefixEnd_3026895 : Nat := 4983230072969 + 3 ^ 40 * 3026895 * 2
def baseEnd_3026895 : Nat := 1554252025691039993092069

theorem tailTrace_3026895 : CollatzResearch.WordTrace tailWord_3026895 prefixEnd_3026895 1554252025691039993092069 := by
  unfold tailWord_3026895
  simp only [CollatzResearch.WordTrace]
  refine ⟨110399930369083842354418139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73599953579389228236278759 110399930369083842354418139)
  ·
    refine ⟨165599895553625763531627209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110399930369083842354418139 165599895553625763531627209)
    ·
      refine ⟨124199921665219322648720407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165599895553625763531627209 124199921665219322648720407)
      ·
        refine ⟨186299882497828983973080611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124199921665219322648720407 186299882497828983973080611)
        ·
          refine ⟨279449823746743475959620917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186299882497828983973080611 279449823746743475959620917)
          ·
            refine ⟨26198420976257200871214461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279449823746743475959620917 26198420976257200871214461)
            ·
              refine ⟨9824407866096450326705423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26198420976257200871214461 9824407866096450326705423)
              ·
                refine ⟨14736611799144675490058135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824407866096450326705423 14736611799144675490058135)
                ·
                  refine ⟨22104917698717013235087203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14736611799144675490058135 22104917698717013235087203)
                  ·
                    refine ⟨33157376548075519852630805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22104917698717013235087203 33157376548075519852630805)
                    ·
                      refine ⟨1554252025691039993092069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33157376548075519852630805 1554252025691039993092069)
                      ·
                        rfl

theorem cell23_3026895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_3026895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026895 prefixEnd_3026895 := by exact prefixLift 3026895
  have htrace : WordTrace (prefixWord ++ tailWord_3026895) baseStart_3026895 baseEnd_3026895 := by
    simpa [prefixWord, tailWord_3026895, baseEnd_3026895] using wordTrace_append hprefix tailTrace_3026895
  have hstable : (prefixWord ++ tailWord_3026895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026895).length < 2 ^ (prefixWord ++ tailWord_3026895).sum := by decide
  have hdescent : baseEnd_3026895 < baseStart_3026895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026919 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3026919 : Nat := 118140960795 + 3026919 * 2 ^ 59
def prefixEnd_3026919 : Nat := 4983230072969 + 3 ^ 40 * 3026919 * 2
def baseEnd_3026919 : Nat := 1554264349226747899191959

theorem tailTrace_3026919 : CollatzResearch.WordTrace tailWord_3026919 prefixEnd_3026919 1554264349226747899191959 := by
  unfold tailWord_3026919
  simp only [CollatzResearch.WordTrace]
  refine ⟨110400805720996894453291811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73600537147331262968861207 110400805720996894453291811)
  ·
    refine ⟨165601208581495341679937717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110400805720996894453291811 165601208581495341679937717)
    ·
      refine ⟨15525113304515188282494161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165601208581495341679937717 15525113304515188282494161)
      ·
        refine ⟨11643834978386391211870621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15525113304515188282494161 11643834978386391211870621)
        ·
          refine ⟨4366438116894896704451483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11643834978386391211870621 4366438116894896704451483)
          ·
            refine ⟨6549657175342345056677225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366438116894896704451483 6549657175342345056677225)
            ·
              refine ⟨4912242881506758792507919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6549657175342345056677225 4912242881506758792507919)
              ·
                refine ⟨7368364322260138188761879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912242881506758792507919 7368364322260138188761879)
                ·
                  refine ⟨11052546483390207283142819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368364322260138188761879 11052546483390207283142819)
                  ·
                    refine ⟨16578819725085310924714229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11052546483390207283142819 16578819725085310924714229)
                    ·
                      refine ⟨1554264349226747899191959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16578819725085310924714229 1554264349226747899191959)
                      ·
                        rfl

theorem cell23_3026919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3026919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026919 prefixEnd_3026919 := by exact prefixLift 3026919
  have htrace : WordTrace (prefixWord ++ tailWord_3026919) baseStart_3026919 baseEnd_3026919 := by
    simpa [prefixWord, tailWord_3026919, baseEnd_3026919] using wordTrace_append hprefix tailTrace_3026919
  have hstable : (prefixWord ++ tailWord_3026919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026919).length < 2 ^ (prefixWord ++ tailWord_3026919).sum := by decide
  have hdescent : baseEnd_3026919 < baseStart_3026919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026950 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3026950 : Nat := 118140960795 + 3026950 * 2 ^ 59
def prefixEnd_3026950 : Nat := 4983230072969 + 3 ^ 40 * 3026950 * 2
def baseEnd_3026950 : Nat := 1554280267127037277904317

theorem tailTrace_3026950 : CollatzResearch.WordTrace tailWord_3026950 prefixEnd_3026950 1554280267127037277904317 := by
  unfold tailWord_3026950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450060511996393335864697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73601290922589724498446869 3450060511996393335864697)
  ·
    refine ⟨2587545383997295001898523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3450060511996393335864697 2587545383997295001898523)
    ·
      refine ⟨3881318075995942502847785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587545383997295001898523 3881318075995942502847785)
      ·
        refine ⟨2910988556996956877135839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3881318075995942502847785 2910988556996956877135839)
        ·
          refine ⟨4366482835495435315703759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910988556996956877135839 4366482835495435315703759)
          ·
            refine ⟨6549724253243152973555639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366482835495435315703759 6549724253243152973555639)
            ·
              refine ⟨9824586379864729460333459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549724253243152973555639 9824586379864729460333459)
              ·
                refine ⟨14736879569797094190500189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824586379864729460333459 14736879569797094190500189)
                ·
                  refine ⟨5526329838673910321437571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14736879569797094190500189 5526329838673910321437571)
                  ·
                    refine ⟨8289494758010865482156357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526329838673910321437571 8289494758010865482156357)
                    ·
                      refine ⟨1554280267127037277904317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8289494758010865482156357 1554280267127037277904317)
                      ·
                        rfl

theorem cell23_3026950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3026950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026950 prefixEnd_3026950 := by exact prefixLift 3026950
  have htrace : WordTrace (prefixWord ++ tailWord_3026950) baseStart_3026950 baseEnd_3026950 := by
    simpa [prefixWord, tailWord_3026950, baseEnd_3026950] using wordTrace_append hprefix tailTrace_3026950
  have hstable : (prefixWord ++ tailWord_3026950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026950).length < 2 ^ (prefixWord ++ tailWord_3026950).sum := by decide
  have hdescent : baseEnd_3026950 < baseStart_3026950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026984 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3026984 : Nat := 118140960795 + 3026984 * 2 ^ 59
def prefixEnd_3026984 : Nat := 4983230072969 + 3 ^ 40 * 3026984 * 2
def baseEnd_3026984 : Nat := 1554297725469290144879161

theorem tailTrace_3026984 : CollatzResearch.WordTrace tailWord_3026984 prefixEnd_3026984 1554297725469290144879161 := by
  unfold tailWord_3026984
  simp only [CollatzResearch.WordTrace]
  refine ⟨55201588232880705277204003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73602117643840940369605337 55201588232880705277204003)
  ·
    refine ⟨82802382349321057915806005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55201588232880705277204003 82802382349321057915806005)
    ·
      refine ⟨7762723345248849179606813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82802382349321057915806005 7762723345248849179606813)
      ·
        refine ⟨2911021254468318442352555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7762723345248849179606813 2911021254468318442352555)
        ·
          refine ⟨4366531881702477663528833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911021254468318442352555 4366531881702477663528833)
          ·
            refine ⟨3274898911276858247646625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4366531881702477663528833 3274898911276858247646625)
            ·
              refine ⟨2456174183457643685734969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274898911276858247646625 2456174183457643685734969)
              ·
                refine ⟨1842130637593232764301227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456174183457643685734969 1842130637593232764301227)
                ·
                  refine ⟨2763195956389849146451841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842130637593232764301227 2763195956389849146451841)
                  ·
                    refine ⟨2072396967292386859838881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2763195956389849146451841 2072396967292386859838881)
                    ·
                      refine ⟨1554297725469290144879161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072396967292386859838881 1554297725469290144879161)
                      ·
                        rfl

theorem cell23_3026984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3026984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026984 prefixEnd_3026984 := by exact prefixLift 3026984
  have htrace : WordTrace (prefixWord ++ tailWord_3026984) baseStart_3026984 baseEnd_3026984 := by
    simpa [prefixWord, tailWord_3026984, baseEnd_3026984] using wordTrace_append hprefix tailTrace_3026984
  have hstable : (prefixWord ++ tailWord_3026984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026984).length < 2 ^ (prefixWord ++ tailWord_3026984).sum := by decide
  have hdescent : baseEnd_3026984 < baseStart_3026984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3026992 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_3026992 : Nat := 118140960795 + 3026992 * 2 ^ 59
def prefixEnd_3026992 : Nat := 4983230072969 + 3 ^ 40 * 3026992 * 2
def baseEnd_3026992 : Nat := 1554301833314526113579123

theorem tailTrace_3026992 : CollatzResearch.WordTrace tailWord_3026992 prefixEnd_3026992 1554301833314526113579123 := by
  unfold tailWord_3026992
  simp only [CollatzResearch.WordTrace]
  refine ⟨55201734124866213960349615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73602312166488285280466153 55201734124866213960349615)
  ·
    refine ⟨82802601187299320940524423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55201734124866213960349615 82802601187299320940524423)
    ·
      refine ⟨124203901780948981410786635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82802601187299320940524423 124203901780948981410786635)
      ·
        refine ⟨186305852671423472116179953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124203901780948981410786635 186305852671423472116179953)
        ·
          refine ⟨139729389503567604087134965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186305852671423472116179953 139729389503567604087134965)
          ·
            refine ⟨13099630265959462883168903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139729389503567604087134965 13099630265959462883168903)
            ·
              refine ⟨19649445398939194324753355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13099630265959462883168903 19649445398939194324753355)
              ·
                refine ⟨29474168098408791487130033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19649445398939194324753355 29474168098408791487130033)
                ·
                  refine ⟨22105626073806593615347525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29474168098408791487130033 22105626073806593615347525)
                  ·
                    refine ⟨4144804888838736302877661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22105626073806593615347525 4144804888838736302877661)
                    ·
                      refine ⟨1554301833314526113579123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4144804888838736302877661 1554301833314526113579123)
                      ·
                        rfl

theorem cell23_3026992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_3026992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3026992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3026992 prefixEnd_3026992 := by exact prefixLift 3026992
  have htrace : WordTrace (prefixWord ++ tailWord_3026992) baseStart_3026992 baseEnd_3026992 := by
    simpa [prefixWord, tailWord_3026992, baseEnd_3026992] using wordTrace_append hprefix tailTrace_3026992
  have hstable : (prefixWord ++ tailWord_3026992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3026992).length < 2 ^ (prefixWord ++ tailWord_3026992).sum := by decide
  have hdescent : baseEnd_3026992 < baseStart_3026992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3026992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027029 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 5]
def baseStart_3027029 : Nat := 118140960795 + 3027029 * 2 ^ 59
def prefixEnd_3027029 : Nat := 4983230072969 + 3 ^ 40 * 3027029 * 2
def baseEnd_3027029 : Nat := 172702314677638052090717

theorem tailTrace_3027029 : CollatzResearch.WordTrace tailWord_3027029 prefixEnd_3027029 172702314677638052090717 := by
  unfold tailWord_3027029
  simp only [CollatzResearch.WordTrace]
  refine ⟨110404817750598383239796141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73603211833732255493197427 110404817750598383239796141)
  ·
    refine ⟨41401806656474393714923553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110404817750598383239796141 41401806656474393714923553)
    ·
      refine ⟨31051354992355795286192665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41401806656474393714923553 31051354992355795286192665)
      ·
        refine ⟨23288516244266846464644499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31051354992355795286192665 23288516244266846464644499)
        ·
          refine ⟨34932774366400269696966749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23288516244266846464644499 34932774366400269696966749)
          ·
            refine ⟨13099790387400101136362531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34932774366400269696966749 13099790387400101136362531)
            ·
              refine ⟨19649685581100151704543797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13099790387400101136362531 19649685581100151704543797)
              ·
                refine ⟨1842158023228139222300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19649685581100151704543797 1842158023228139222300981)
                ·
                  refine ⟨172702314677638052090717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1842158023228139222300981 172702314677638052090717)
                  ·
                    rfl

theorem cell23_3027029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_3027029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027029 prefixEnd_3027029 := by exact prefixLift 3027029
  have htrace : WordTrace (prefixWord ++ tailWord_3027029) baseStart_3027029 baseEnd_3027029 := by
    simpa [prefixWord, tailWord_3027029, baseEnd_3027029] using wordTrace_append hprefix tailTrace_3027029
  have hstable : (prefixWord ++ tailWord_3027029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027029).length < 2 ^ (prefixWord ++ tailWord_3027029).sum := by decide
  have hdescent : baseEnd_3027029 < baseStart_3027029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027079 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_3027079 : Nat := 118140960795 + 3027079 * 2 ^ 59
def prefixEnd_3027079 : Nat := 4983230072969 + 3 ^ 40 * 3027079 * 2
def baseEnd_3027079 : Nat := 1554346506131467273191223

theorem tailTrace_3027079 : CollatzResearch.WordTrace tailWord_3027079 prefixEnd_3027079 1554346506131467273191223 := by
  unfold tailWord_3027079
  simp only [CollatzResearch.WordTrace]
  refine ⟨110406641400417241779116291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73604427600278161186077527 110406641400417241779116291)
  ·
    refine ⟨165609962100625862668674437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110406641400417241779116291 165609962100625862668674437)
    ·
      refine ⟨31051867893867349250376457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165609962100625862668674437 31051867893867349250376457)
      ·
        refine ⟨23288900920400511937782343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31051867893867349250376457 23288900920400511937782343)
        ·
          refine ⟨34933351380600767906673515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23288900920400511937782343 34933351380600767906673515)
          ·
            refine ⟨52400027070901151860010273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34933351380600767906673515 52400027070901151860010273)
            ·
              refine ⟨39300020303175863895007705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52400027070901151860010273 39300020303175863895007705)
              ·
                refine ⟨29475015227381897921255779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39300020303175863895007705 29475015227381897921255779)
                ·
                  refine ⟨44212522841072846881883669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29475015227381897921255779 44212522841072846881883669)
                  ·
                    refine ⟨2072462008175289697588297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44212522841072846881883669 2072462008175289697588297)
                    ·
                      refine ⟨1554346506131467273191223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072462008175289697588297 1554346506131467273191223)
                      ·
                        rfl

theorem cell23_3027079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_3027079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027079 prefixEnd_3027079 := by exact prefixLift 3027079
  have htrace : WordTrace (prefixWord ++ tailWord_3027079) baseStart_3027079 baseEnd_3027079 := by
    simpa [prefixWord, tailWord_3027079, baseEnd_3027079] using wordTrace_append hprefix tailTrace_3027079
  have hstable : (prefixWord ++ tailWord_3027079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027079).length < 2 ^ (prefixWord ++ tailWord_3027079).sum := by decide
  have hdescent : baseEnd_3027079 < baseStart_3027079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027096 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3027096 : Nat := 118140960795 + 3027096 * 2 ^ 59
def prefixEnd_3027096 : Nat := 4983230072969 + 3 ^ 40 * 3027096 * 2
def baseEnd_3027096 : Nat := 1554355235302593706678645

theorem tailTrace_3027096 : CollatzResearch.WordTrace tailWord_3027096 prefixEnd_3027096 1554355235302593706678645 := by
  unfold tailWord_3027096
  simp only [CollatzResearch.WordTrace]
  refine ⟨55203630720677826841242571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73604840960903769121656761 55203630720677826841242571)
  ·
    refine ⟨82805446081016740261863857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55203630720677826841242571 82805446081016740261863857)
    ·
      refine ⟨62104084560762555196397893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82805446081016740261863857 62104084560762555196397893)
      ·
        refine ⟨11644515855142979099324605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62104084560762555196397893 11644515855142979099324605)
        ·
          refine ⟨4366693445678617162246727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11644515855142979099324605 4366693445678617162246727)
          ·
            refine ⟨6550040168517925743370091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366693445678617162246727 6550040168517925743370091)
            ·
              refine ⟨9825060252776888615055137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550040168517925743370091 9825060252776888615055137)
              ·
                refine ⟨7368795189582666461291353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9825060252776888615055137 7368795189582666461291353)
                ·
                  refine ⟨5526596392186999845968515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7368795189582666461291353 5526596392186999845968515)
                  ·
                    refine ⟨8289894588280499768952773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526596392186999845968515 8289894588280499768952773)
                    ·
                      refine ⟨1554355235302593706678645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8289894588280499768952773 1554355235302593706678645)
                      ·
                        rfl

theorem cell23_3027096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3027096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027096 prefixEnd_3027096 := by exact prefixLift 3027096
  have htrace : WordTrace (prefixWord ++ tailWord_3027096) baseStart_3027096 baseEnd_3027096 := by
    simpa [prefixWord, tailWord_3027096, baseEnd_3027096] using wordTrace_append hprefix tailTrace_3027096
  have hstable : (prefixWord ++ tailWord_3027096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027096).length < 2 ^ (prefixWord ++ tailWord_3027096).sum := by decide
  have hdescent : baseEnd_3027096 < baseStart_3027096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027139 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 5, 5, 2]
def baseStart_3027139 : Nat := 118140960795 + 3027139 * 2 ^ 59
def prefixEnd_3027139 : Nat := 4983230072969 + 3 ^ 40 * 3027139 * 2
def baseEnd_3027139 : Nat := 1554377314970737038440947

theorem tailTrace_3027139 : CollatzResearch.WordTrace tailWord_3027139 prefixEnd_3027139 1554377314970737038440947 := by
  unfold tailWord_3027139
  simp only [CollatzResearch.WordTrace]
  refine ⟨110408829780199872026300471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73605886520133248017533647 110408829780199872026300471)
  ·
    refine ⟨165613244670299808039450707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110408829780199872026300471 165613244670299808039450707)
    ·
      refine ⟨248419867005449712059176061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165613244670299808039450707 248419867005449712059176061)
      ·
        refine ⟨93157450127043642022191023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248419867005449712059176061 93157450127043642022191023)
        ·
          refine ⟨139736175190565463033286535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93157450127043642022191023 139736175190565463033286535)
          ·
            refine ⟨209604262785848194549929803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139736175190565463033286535 209604262785848194549929803)
            ·
              refine ⟨314406394178772291824894705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209604262785848194549929803 314406394178772291824894705)
              ·
                refine ⟨235804795634079218868671029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314406394178772291824894705 235804795634079218868671029)
                ·
                  refine ⟨22106699590694926768937909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235804795634079218868671029 22106699590694926768937909)
                  ·
                    refine ⟨2072503086627649384587929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22106699590694926768937909 2072503086627649384587929)
                    ·
                      refine ⟨1554377314970737038440947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072503086627649384587929 1554377314970737038440947)
                      ·
                        rfl

theorem cell23_3027139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_3027139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027139 prefixEnd_3027139 := by exact prefixLift 3027139
  have htrace : WordTrace (prefixWord ++ tailWord_3027139) baseStart_3027139 baseEnd_3027139 := by
    simpa [prefixWord, tailWord_3027139, baseEnd_3027139] using wordTrace_append hprefix tailTrace_3027139
  have hstable : (prefixWord ++ tailWord_3027139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027139).length < 2 ^ (prefixWord ++ tailWord_3027139).sum := by decide
  have hdescent : baseEnd_3027139 < baseStart_3027139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027157 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_3027157 : Nat := 118140960795 + 3027157 * 2 ^ 59
def prefixEnd_3027157 : Nat := 4983230072969 + 3 ^ 40 * 3027157 * 2
def baseEnd_3027157 : Nat := 518128852540839322671955

theorem tailTrace_3027157 : CollatzResearch.WordTrace tailWord_3027157 prefixEnd_3027157 518128852540839322671955 := by
  unfold tailWord_3027157
  simp only [CollatzResearch.WordTrace]
  refine ⟨110409486294134661100455725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73606324196089774066970483 110409486294134661100455725)
  ·
    refine ⟨41403557360300497912670897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110409486294134661100455725 41403557360300497912670897)
    ·
      refine ⟨31052668020225373434503173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41403557360300497912670897 31052668020225373434503173)
      ·
        refine ⟨5822375253792257518969345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31052668020225373434503173 5822375253792257518969345)
        ·
          refine ⟨4366781440344193139227009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822375253792257518969345 4366781440344193139227009)
          ·
            refine ⟨3275086080258144854420257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4366781440344193139227009 3275086080258144854420257)
            ·
              refine ⟨2456314560193608640815193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3275086080258144854420257 2456314560193608640815193)
              ·
                refine ⟨1842235920145206480611395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456314560193608640815193 1842235920145206480611395)
                ·
                  refine ⟨2763353880217809720917093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842235920145206480611395 2763353880217809720917093)
                  ·
                    refine ⟨518128852540839322671955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763353880217809720917093 518128852540839322671955)
                    ·
                      rfl

theorem cell23_3027157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_3027157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027157 prefixEnd_3027157 := by exact prefixLift 3027157
  have htrace : WordTrace (prefixWord ++ tailWord_3027157) baseStart_3027157 baseEnd_3027157 := by
    simpa [prefixWord, tailWord_3027157, baseEnd_3027157] using wordTrace_append hprefix tailTrace_3027157
  have hstable : (prefixWord ++ tailWord_3027157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027157).length < 2 ^ (prefixWord ++ tailWord_3027157).sum := by decide
  have hdescent : baseEnd_3027157 < baseStart_3027157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027169 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_3027169 : Nat := 118140960795 + 3027169 * 2 ^ 59
def prefixEnd_3027169 : Nat := 4983230072969 + 3 ^ 40 * 3027169 * 2
def baseEnd_3027169 : Nat := 1554392719390371921065809

theorem tailTrace_3027169 : CollatzResearch.WordTrace tailWord_3027169 prefixEnd_3027169 1554392719390371921065809 := by
  unfold tailWord_3027169
  simp only [CollatzResearch.WordTrace]
  refine ⟨110409923970091187149892561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73606615980060791433261707 110409923970091187149892561)
  ·
    refine ⟨82807442977568390362419421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110409923970091187149892561 82807442977568390362419421)
    ·
      refine ⟨31052791116588146385907283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82807442977568390362419421 31052791116588146385907283)
      ·
        refine ⟨46579186674882219578860925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31052791116588146385907283 46579186674882219578860925)
        ·
          refine ⟨17467195003080832342072847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46579186674882219578860925 17467195003080832342072847)
          ·
            refine ⟨26200792504621248513109271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17467195003080832342072847 26200792504621248513109271)
            ·
              refine ⟨39301188756931872769663907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26200792504621248513109271 39301188756931872769663907)
              ·
                refine ⟨58951783135397809154495861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39301188756931872769663907 58951783135397809154495861)
                ·
                  refine ⟨5526729668943544608233987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58951783135397809154495861 5526729668943544608233987)
                  ·
                    refine ⟨8290094503415316912350981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526729668943544608233987 8290094503415316912350981)
                    ·
                      refine ⟨1554392719390371921065809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8290094503415316912350981 1554392719390371921065809)
                      ·
                        rfl

theorem cell23_3027169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_3027169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027169 prefixEnd_3027169 := by exact prefixLift 3027169
  have htrace : WordTrace (prefixWord ++ tailWord_3027169) baseStart_3027169 baseEnd_3027169 := by
    simpa [prefixWord, tailWord_3027169, baseEnd_3027169] using wordTrace_append hprefix tailTrace_3027169
  have hstable : (prefixWord ++ tailWord_3027169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027169).length < 2 ^ (prefixWord ++ tailWord_3027169).sum := by decide
  have hdescent : baseEnd_3027169 < baseStart_3027169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027179 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 1, 6]
def baseStart_3027179 : Nat := 118140960795 + 3027179 * 2 ^ 59
def prefixEnd_3027179 : Nat := 4983230072969 + 3 ^ 40 * 3027179 * 2
def baseEnd_3027179 : Nat := 518132618065638960646921

theorem tailTrace_3027179 : CollatzResearch.WordTrace tailWord_3027179 prefixEnd_3027179 518132618065638960646921 := by
  unfold tailWord_3027179
  simp only [CollatzResearch.WordTrace]
  refine ⟨110410288700054958857756591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73606859133369972571837727 110410288700054958857756591)
  ·
    refine ⟨165615433050082438286634887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110410288700054958857756591 165615433050082438286634887)
    ·
      refine ⟨248423149575123657429952331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165615433050082438286634887 248423149575123657429952331)
      ·
        refine ⟨372634724362685486144928497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248423149575123657429952331 372634724362685486144928497)
        ·
          refine ⟨279476043272014114608696373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372634724362685486144928497 279476043272014114608696373)
          ·
            refine ⟨26200879056751323244565285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279476043272014114608696373 26200879056751323244565285)
            ·
              refine ⟨4912664823140873108355991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26200879056751323244565285 4912664823140873108355991)
              ·
                refine ⟨7368997234711309662533987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912664823140873108355991 7368997234711309662533987)
                ·
                  refine ⟨11053495852066964493800981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368997234711309662533987 11053495852066964493800981)
                  ·
                    refine ⟨518132618065638960646921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11053495852066964493800981 518132618065638960646921)
                    ·
                      rfl

theorem cell23_3027179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 6].length) (baseStart_3027179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027179 prefixEnd_3027179 := by exact prefixLift 3027179
  have htrace : WordTrace (prefixWord ++ tailWord_3027179) baseStart_3027179 baseEnd_3027179 := by
    simpa [prefixWord, tailWord_3027179, baseEnd_3027179] using wordTrace_append hprefix tailTrace_3027179
  have hstable : (prefixWord ++ tailWord_3027179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027179).length < 2 ^ (prefixWord ++ tailWord_3027179).sum := by decide
  have hdescent : baseEnd_3027179 < baseStart_3027179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027186 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3027186 : Nat := 118140960795 + 3027186 * 2 ^ 59
def prefixEnd_3027186 : Nat := 4983230072969 + 3 ^ 40 * 3027186 * 2
def baseEnd_3027186 : Nat := 1554401448561498354553231

theorem tailTrace_3027186 : CollatzResearch.WordTrace tailWord_3027186 prefixEnd_3027186 1554401448561498354553231 := by
  unfold tailWord_3027186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27602636002757399763315353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73607029340686399368840941 27602636002757399763315353)
  ·
    refine ⟨20701977002068049822486515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27602636002757399763315353 20701977002068049822486515)
    ·
      refine ⟨31052965503102074733729773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20701977002068049822486515 31052965503102074733729773)
      ·
        refine ⟨11644862063663278025148665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31052965503102074733729773 11644862063663278025148665)
        ·
          refine ⟨8733646547747458518861499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11644862063663278025148665 8733646547747458518861499)
          ·
            refine ⟨13100469821621187778292249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8733646547747458518861499 13100469821621187778292249)
            ·
              refine ⟨9825352366215890833719187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13100469821621187778292249 9825352366215890833719187)
              ·
                refine ⟨14738028549323836250578781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9825352366215890833719187 14738028549323836250578781)
                ·
                  refine ⟨5526760705996438593967043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14738028549323836250578781 5526760705996438593967043)
                  ·
                    refine ⟨8290141058994657890950565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526760705996438593967043 8290141058994657890950565)
                    ·
                      refine ⟨1554401448561498354553231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8290141058994657890950565 1554401448561498354553231)
                      ·
                        rfl

theorem cell23_3027186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3027186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027186 prefixEnd_3027186 := by exact prefixLift 3027186
  have htrace : WordTrace (prefixWord ++ tailWord_3027186) baseStart_3027186 baseEnd_3027186 := by
    simpa [prefixWord, tailWord_3027186, baseEnd_3027186] using wordTrace_append hprefix tailTrace_3027186
  have hstable : (prefixWord ++ tailWord_3027186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027186).length < 2 ^ (prefixWord ++ tailWord_3027186).sum := by decide
  have hdescent : baseEnd_3027186 < baseStart_3027186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027192 : List Nat := [2, 1, 2, 1, 1, 2, 1, 13]
def baseStart_3027192 : Nat := 118140960795 + 3027192 * 2 ^ 59
def prefixEnd_3027192 : Nat := 4983230072969 + 3 ^ 40 * 3027192 * 2
def baseEnd_3027192 : Nat := 57570538127608345595489

theorem tailTrace_3027192 : CollatzResearch.WordTrace tailWord_3027192 prefixEnd_3027192 57570538127608345595489 := by
  unfold tailWord_3027192
  simp only [CollatzResearch.WordTrace]
  refine ⟨55205381424503931038989915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73607175232671908051986553 55205381424503931038989915)
  ·
    refine ⟨82808072136755896558484873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55205381424503931038989915 82808072136755896558484873)
    ·
      refine ⟨62106054102566922418863655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82808072136755896558484873 62106054102566922418863655)
      ·
        refine ⟨93159081153850383628295483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62106054102566922418863655 93159081153850383628295483)
        ·
          refine ⟨139738621730775575442443225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93159081153850383628295483 139738621730775575442443225)
          ·
            refine ⟨104803966298081681581832419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139738621730775575442443225 104803966298081681581832419)
            ·
              refine ⟨157205949447122522372748629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104803966298081681581832419 157205949447122522372748629)
              ·
                refine ⟨57570538127608345595489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 157205949447122522372748629 57570538127608345595489)
                ·
                  rfl

theorem cell23_3027192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 13].length) (baseStart_3027192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027192 prefixEnd_3027192 := by exact prefixLift 3027192
  have htrace : WordTrace (prefixWord ++ tailWord_3027192) baseStart_3027192 baseEnd_3027192 := by
    simpa [prefixWord, tailWord_3027192, baseEnd_3027192] using wordTrace_append hprefix tailTrace_3027192
  have hstable : (prefixWord ++ tailWord_3027192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027192).length < 2 ^ (prefixWord ++ tailWord_3027192).sum := by decide
  have hdescent : baseEnd_3027192 < baseStart_3027192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027199 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_3027199 : Nat := 118140960795 + 3027199 * 2 ^ 59
def prefixEnd_3027199 : Nat := 4983230072969 + 3 ^ 40 * 3027199 * 2
def baseEnd_3027199 : Nat := 1554408123810006803690671

theorem tailTrace_3027199 : CollatzResearch.WordTrace tailWord_3027199 prefixEnd_3027199 1554408123810006803690671 := by
  unfold tailWord_3027199
  simp only [CollatzResearch.WordTrace]
  refine ⟨110411018159982502273484651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73607345439988334848989767 110411018159982502273484651)
  ·
    refine ⟨165616527239973753410226977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110411018159982502273484651 165616527239973753410226977)
    ·
      refine ⟨124212395429980315057670233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165616527239973753410226977 124212395429980315057670233)
      ·
        refine ⟨93159296572485236293252675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124212395429980315057670233 93159296572485236293252675)
        ·
          refine ⟨139738944858727854439879013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93159296572485236293252675 139738944858727854439879013)
          ·
            refine ⟨26201052161011472707477315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139738944858727854439879013 26201052161011472707477315)
            ·
              refine ⟨39301578241517209061215973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26201052161011472707477315 39301578241517209061215973)
              ·
                refine ⟨7369045920284476698977995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39301578241517209061215973 7369045920284476698977995)
                ·
                  refine ⟨11053568880426715048466993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369045920284476698977995 11053568880426715048466993)
                  ·
                    refine ⟨8290176660320036286350245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11053568880426715048466993 8290176660320036286350245)
                    ·
                      refine ⟨1554408123810006803690671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8290176660320036286350245 1554408123810006803690671)
                      ·
                        rfl

theorem cell23_3027199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_3027199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027199 prefixEnd_3027199 := by exact prefixLift 3027199
  have htrace : WordTrace (prefixWord ++ tailWord_3027199) baseStart_3027199 baseEnd_3027199 := by
    simpa [prefixWord, tailWord_3027199, baseEnd_3027199] using wordTrace_append hprefix tailTrace_3027199
  have hstable : (prefixWord ++ tailWord_3027199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027199).length < 2 ^ (prefixWord ++ tailWord_3027199).sum := by decide
  have hdescent : baseEnd_3027199 < baseStart_3027199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027219 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 3]
def baseStart_3027219 : Nat := 118140960795 + 3027219 * 2 ^ 59
def prefixEnd_3027219 : Nat := 4983230072969 + 3 ^ 40 * 3027219 * 2
def baseEnd_3027219 : Nat := 1554418393423096725440579

theorem tailTrace_3027219 : CollatzResearch.WordTrace tailWord_3027219 prefixEnd_3027219 1554418393423096725440579 := by
  unfold tailWord_3027219
  simp only [CollatzResearch.WordTrace]
  refine ⟨110411747619910045689212711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73607831746606697126141807 110411747619910045689212711)
  ·
    refine ⟨165617621429865068533819067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110411747619910045689212711 165617621429865068533819067)
    ·
      refine ⟨248426432144797602800728601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165617621429865068533819067 248426432144797602800728601)
      ·
        refine ⟨186319824108598202100546451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248426432144797602800728601 186319824108598202100546451)
        ·
          refine ⟨279479736162897303150819677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186319824108598202100546451 279479736162897303150819677)
          ·
            refine ⟨104804901061086488681557379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279479736162897303150819677 104804901061086488681557379)
            ·
              refine ⟨157207351591629733022336069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104804901061086488681557379 157207351591629733022336069)
              ·
                refine ⟨29476378423430574941688013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157207351591629733022336069 29476378423430574941688013)
                ·
                  refine ⟨11053641908786465603133005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29476378423430574941688013 11053641908786465603133005)
                  ·
                    refine ⟨4145115715794924601174877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11053641908786465603133005 4145115715794924601174877)
                    ·
                      refine ⟨1554418393423096725440579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145115715794924601174877 1554418393423096725440579)
                      ·
                        rfl

theorem cell23_3027219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_3027219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027219 prefixEnd_3027219 := by exact prefixLift 3027219
  have htrace : WordTrace (prefixWord ++ tailWord_3027219) baseStart_3027219 baseEnd_3027219 := by
    simpa [prefixWord, tailWord_3027219, baseEnd_3027219] using wordTrace_append hprefix tailTrace_3027219
  have hstable : (prefixWord ++ tailWord_3027219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027219).length < 2 ^ (prefixWord ++ tailWord_3027219).sum := by decide
  have hdescent : baseEnd_3027219 < baseStart_3027219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027230 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3027230 : Nat := 118140960795 + 3027230 * 2 ^ 59
def prefixEnd_3027230 : Nat := 4983230072969 + 3 ^ 40 * 3027230 * 2
def baseEnd_3027230 : Nat := 518141347236765394134343

theorem tailTrace_3027230 : CollatzResearch.WordTrace tailWord_3027230 prefixEnd_3027230 518141347236765394134343 := by
  unfold tailWord_3027230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801518602858774320982893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73608099215246796378575429 13801518602858774320982893)
  ·
    refine ⟨5175569476072040370368585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13801518602858774320982893 5175569476072040370368585)
    ·
      refine ⟨3881677107054030277776439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5175569476072040370368585 3881677107054030277776439)
      ·
        refine ⟨5822515660581045416664659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881677107054030277776439 5822515660581045416664659)
        ·
          refine ⟨8733773490871568124996989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822515660581045416664659 8733773490871568124996989)
          ·
            refine ⟨3275165059076838046873871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8733773490871568124996989 3275165059076838046873871)
            ·
              refine ⟨4912747588615257070310807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275165059076838046873871 4912747588615257070310807)
              ·
                refine ⟨7369121382922885605466211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912747588615257070310807 7369121382922885605466211)
                ·
                  refine ⟨11053682074384328408199317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369121382922885605466211 11053682074384328408199317)
                  ·
                    refine ⟨518141347236765394134343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11053682074384328408199317 518141347236765394134343)
                    ·
                      rfl

theorem cell23_3027230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3027230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027230 prefixEnd_3027230 := by exact prefixLift 3027230
  have htrace : WordTrace (prefixWord ++ tailWord_3027230) baseStart_3027230 baseEnd_3027230 := by
    simpa [prefixWord, tailWord_3027230, baseEnd_3027230] using wordTrace_append hprefix tailTrace_3027230
  have hstable : (prefixWord ++ tailWord_3027230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027230).length < 2 ^ (prefixWord ++ tailWord_3027230).sum := by decide
  have hdescent : baseEnd_3027230 < baseStart_3027230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027240 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3027240 : Nat := 118140960795 + 3027240 * 2 ^ 59
def prefixEnd_3027240 : Nat := 4983230072969 + 3 ^ 40 * 3027240 * 2
def baseEnd_3027240 : Nat := 1554429176516841143277983

theorem tailTrace_3027240 : CollatzResearch.WordTrace tailWord_3027240 prefixEnd_3027240 1554429176516841143277983 := by
  unfold tailWord_3027240
  simp only [CollatzResearch.WordTrace]
  refine ⟨55206256776416983137863587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73608342368555977517151449 55206256776416983137863587)
  ·
    refine ⟨82809385164625474706795381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55206256776416983137863587 82809385164625474706795381)
    ·
      refine ⟨7763379859183638253762067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82809385164625474706795381 7763379859183638253762067)
      ·
        refine ⟨11645069788775457380643101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7763379859183638253762067 11645069788775457380643101)
        ·
          refine ⟨4366901170790796517741163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11645069788775457380643101 4366901170790796517741163)
          ·
            refine ⟨6550351756186194776611745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366901170790796517741163 6550351756186194776611745)
            ·
              refine ⟨4912763817139646082458809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6550351756186194776611745 4912763817139646082458809)
              ·
                refine ⟨3684572862854734561844107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912763817139646082458809 3684572862854734561844107)
                ·
                  refine ⟨5526859294282101842766161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684572862854734561844107 5526859294282101842766161)
                  ·
                    refine ⟨4145144470711576382074621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5526859294282101842766161 4145144470711576382074621)
                    ·
                      refine ⟨1554429176516841143277983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145144470711576382074621 1554429176516841143277983)
                      ·
                        rfl

theorem cell23_3027240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3027240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027240 prefixEnd_3027240 := by exact prefixLift 3027240
  have htrace : WordTrace (prefixWord ++ tailWord_3027240) baseStart_3027240 baseEnd_3027240 := by
    simpa [prefixWord, tailWord_3027240, baseEnd_3027240] using wordTrace_append hprefix tailTrace_3027240
  have hstable : (prefixWord ++ tailWord_3027240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027240).length < 2 ^ (prefixWord ++ tailWord_3027240).sum := by decide
  have hdescent : baseEnd_3027240 < baseStart_3027240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027263 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 1, 3, 2]
def baseStart_3027263 : Nat := 118140960795 + 3027263 * 2 ^ 59
def prefixEnd_3027263 : Nat := 4983230072969 + 3 ^ 40 * 3027263 * 2
def baseEnd_3027263 : Nat := 1554440986571894553290377

theorem tailTrace_3027263 : CollatzResearch.WordTrace tailWord_3027263 prefixEnd_3027263 1554440986571894553290377 := by
  unfold tailWord_3027263
  simp only [CollatzResearch.WordTrace]
  refine ⟨110413352431750641203814443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73608901621167094135876295 110413352431750641203814443)
  ·
    refine ⟨165620028647625961805721665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110413352431750641203814443 165620028647625961805721665)
    ·
      refine ⟨124215021485719471354291249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165620028647625961805721665 124215021485719471354291249)
      ·
        refine ⟨93161266114289603515718437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124215021485719471354291249 93161266114289603515718437)
        ·
          refine ⟨17467737396429300659197207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93161266114289603515718437 17467737396429300659197207)
          ·
            refine ⟨26201606094643950988795811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17467737396429300659197207 26201606094643950988795811)
            ·
              refine ⟨39302409141965926483193717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26201606094643950988795811 39302409141965926483193717)
              ·
                refine ⟨3684600857059305607799411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39302409141965926483193717 3684600857059305607799411)
                ·
                  refine ⟨5526901285588958411699117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684600857059305607799411 5526901285588958411699117)
                  ·
                    refine ⟨2072587982095859404387169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5526901285588958411699117 2072587982095859404387169)
                    ·
                      refine ⟨1554440986571894553290377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072587982095859404387169 1554440986571894553290377)
                      ·
                        rfl

theorem cell23_3027263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_3027263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027263 prefixEnd_3027263 := by exact prefixLift 3027263
  have htrace : WordTrace (prefixWord ++ tailWord_3027263) baseStart_3027263 baseEnd_3027263 := by
    simpa [prefixWord, tailWord_3027263, baseEnd_3027263] using wordTrace_append hprefix tailTrace_3027263
  have hstable : (prefixWord ++ tailWord_3027263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027263).length < 2 ^ (prefixWord ++ tailWord_3027263).sum := by decide
  have hdescent : baseEnd_3027263 < baseStart_3027263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027289 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_3027289 : Nat := 118140960795 + 3027289 * 2 ^ 59
def prefixEnd_3027289 : Nat := 4983230072969 + 3 ^ 40 * 3027289 * 2
def baseEnd_3027289 : Nat := 1554454337068911451565257

theorem tailTrace_3027289 : CollatzResearch.WordTrace tailWord_3027289 prefixEnd_3027289 1554454337068911451565257 := by
  unfold tailWord_3027289
  simp only [CollatzResearch.WordTrace]
  refine ⟨110414300729656447644260921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73609533819770965096173947 110414300729656447644260921)
  ·
    refine ⟨82810725547242335733195691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110414300729656447644260921 82810725547242335733195691)
    ·
      refine ⟨124216088320863503599793537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82810725547242335733195691 124216088320863503599793537)
      ·
        refine ⟨93162066240647627699845153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124216088320863503599793537 93162066240647627699845153)
        ·
          refine ⟨69871549680485720774883865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93162066240647627699845153 69871549680485720774883865)
          ·
            refine ⟨52403662260364290581162899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69871549680485720774883865 52403662260364290581162899)
            ·
              refine ⟨78605493390546435871744349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52403662260364290581162899 78605493390546435871744349)
              ·
                refine ⟨29477060021454913451904131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78605493390546435871744349 29477060021454913451904131)
                ·
                  refine ⟨44215590032182370177856197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29477060021454913451904131 44215590032182370177856197)
                  ·
                    refine ⟨8290423131034194408348037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44215590032182370177856197 8290423131034194408348037)
                    ·
                      refine ⟨1554454337068911451565257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8290423131034194408348037 1554454337068911451565257)
                      ·
                        rfl

theorem cell23_3027289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_3027289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027289 prefixEnd_3027289 := by exact prefixLift 3027289
  have htrace : WordTrace (prefixWord ++ tailWord_3027289) baseStart_3027289 baseEnd_3027289 := by
    simpa [prefixWord, tailWord_3027289, baseEnd_3027289] using wordTrace_append hprefix tailTrace_3027289
  have hstable : (prefixWord ++ tailWord_3027289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027289).length < 2 ^ (prefixWord ++ tailWord_3027289).sum := by decide
  have hdescent : baseEnd_3027289 < baseStart_3027289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027299 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 9]
def baseStart_3027299 : Nat := 118140960795 + 3027299 * 2 ^ 59
def prefixEnd_3027299 : Nat := 4983230072969 + 3 ^ 40 * 3027299 * 2
def baseEnd_3027299 : Nat := 172717719097272934715579

theorem tailTrace_3027299 : CollatzResearch.WordTrace tailWord_3027299 prefixEnd_3027299 172717719097272934715579 := by
  unfold tailWord_3027299
  simp only [CollatzResearch.WordTrace]
  refine ⟨110414665459620219352124951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73609776973080146234749967 110414665459620219352124951)
  ·
    refine ⟨165621998189430329028187427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110414665459620219352124951 165621998189430329028187427)
    ·
      refine ⟨248432997284145493542281141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165621998189430329028187427 248432997284145493542281141)
      ·
        refine ⟨23290593495388640019588857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248432997284145493542281141 23290593495388640019588857)
        ·
          refine ⟨17467945121541480014691643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23290593495388640019588857 17467945121541480014691643)
          ·
            refine ⟨26201917682312220022037465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17467945121541480014691643 26201917682312220022037465)
            ·
              refine ⟨19651438261734165016528099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26201917682312220022037465 19651438261734165016528099)
              ·
                refine ⟨29477157392601247524792149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19651438261734165016528099 29477157392601247524792149)
                ·
                  refine ⟨172717719097272934715579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29477157392601247524792149 172717719097272934715579)
                  ·
                    rfl

theorem cell23_3027299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 9].length) (baseStart_3027299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027299 prefixEnd_3027299 := by exact prefixLift 3027299
  have htrace : WordTrace (prefixWord ++ tailWord_3027299) baseStart_3027299 baseEnd_3027299 := by
    simpa [prefixWord, tailWord_3027299, baseEnd_3027299] using wordTrace_append hprefix tailTrace_3027299
  have hstable : (prefixWord ++ tailWord_3027299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027299).length < 2 ^ (prefixWord ++ tailWord_3027299).sum := by decide
  have hdescent : baseEnd_3027299 < baseStart_3027299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027363 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 2, 5]
def baseStart_3027363 : Nat := 118140960795 + 3027363 * 2 ^ 59
def prefixEnd_3027363 : Nat := 4983230072969 + 3 ^ 40 * 3027363 * 2
def baseEnd_3027363 : Nat := 518164111545781387346639

theorem tailTrace_3027363 : CollatzResearch.WordTrace tailWord_3027363 prefixEnd_3027363 518164111545781387346639 := by
  unfold tailWord_3027363
  simp only [CollatzResearch.WordTrace]
  refine ⟨110416999731388358282454743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73611333154258905521636495 110416999731388358282454743)
  ·
    refine ⟨165625499597082537423682115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110416999731388358282454743 165625499597082537423682115)
    ·
      refine ⟨248438249395623806135523173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165625499597082537423682115 248438249395623806135523173)
      ·
        refine ⟨46582171761679463650410595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248438249395623806135523173 46582171761679463650410595)
        ·
          refine ⟨69873257642519195475615893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46582171761679463650410595 69873257642519195475615893)
          ·
            refine ⟨3275308951993087287919495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69873257642519195475615893 3275308951993087287919495)
            ·
              refine ⟨4912963427989630931879243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275308951993087287919495 4912963427989630931879243)
              ·
                refine ⟨7369445141984446397818865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912963427989630931879243 7369445141984446397818865)
                ·
                  refine ⟨5527083856488334798364149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7369445141984446397818865 5527083856488334798364149)
                  ·
                    refine ⟨518164111545781387346639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5527083856488334798364149 518164111545781387346639)
                    ·
                      rfl

theorem cell23_3027363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 5].length) (baseStart_3027363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027363 prefixEnd_3027363 := by exact prefixLift 3027363
  have htrace : WordTrace (prefixWord ++ tailWord_3027363) baseStart_3027363 baseEnd_3027363 := by
    simpa [prefixWord, tailWord_3027363, baseEnd_3027363] using wordTrace_append hprefix tailTrace_3027363
  have hstable : (prefixWord ++ tailWord_3027363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027363).length < 2 ^ (prefixWord ++ tailWord_3027363).sum := by decide
  have hdescent : baseEnd_3027363 < baseStart_3027363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027383 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 2, 4, 2]
def baseStart_3027383 : Nat := 118140960795 + 3027383 * 2 ^ 59
def prefixEnd_3027383 : Nat := 4983230072969 + 3 ^ 40 * 3027383 * 2
def baseEnd_3027383 : Nat := 1554502604250434083789825

theorem tailTrace_3027383 : CollatzResearch.WordTrace tailWord_3027383 prefixEnd_3027383 1554502604250434083789825 := by
  unfold tailWord_3027383
  simp only [CollatzResearch.WordTrace]
  refine ⟨110417729191315901698182803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73611819460877267798788535 110417729191315901698182803)
  ·
    refine ⟨165626593786973852547274205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110417729191315901698182803 165626593786973852547274205)
    ·
      refine ⟨62109972670115194705227827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165626593786973852547274205 62109972670115194705227827)
      ·
        refine ⟨93164959005172792057841741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62109972670115194705227827 93164959005172792057841741)
        ·
          refine ⟨34936859626939797021690653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93164959005172792057841741 34936859626939797021690653)
          ·
            refine ⟨13101322360102423883133995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34936859626939797021690653 13101322360102423883133995)
            ·
              refine ⟨19651983540153635824700993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13101322360102423883133995 19651983540153635824700993)
              ·
                refine ⟨14738987655115226868525745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19651983540153635824700993 14738987655115226868525745)
                ·
                  refine ⟨11054240741336420151394309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14738987655115226868525745 11054240741336420151394309)
                  ·
                    refine ⟨2072670139000578778386433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11054240741336420151394309 2072670139000578778386433)
                    ·
                      refine ⟨1554502604250434083789825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072670139000578778386433 1554502604250434083789825)
                      ·
                        rfl

theorem cell23_3027383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_3027383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027383 prefixEnd_3027383 := by exact prefixLift 3027383
  have htrace : WordTrace (prefixWord ++ tailWord_3027383) baseStart_3027383 baseEnd_3027383 := by
    simpa [prefixWord, tailWord_3027383, baseEnd_3027383] using wordTrace_append hprefix tailTrace_3027383
  have hstable : (prefixWord ++ tailWord_3027383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027383).length < 2 ^ (prefixWord ++ tailWord_3027383).sum := by decide
  have hdescent : baseEnd_3027383 < baseStart_3027383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027416 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3027416 : Nat := 118140960795 + 3027416 * 2 ^ 59
def prefixEnd_3027416 : Nat := 4983230072969 + 3 ^ 40 * 3027416 * 2
def baseEnd_3027416 : Nat := 1554519549112032454677173

theorem tailTrace_3027416 : CollatzResearch.WordTrace tailWord_3027416 prefixEnd_3027416 1554519549112032454677173 := by
  unfold tailWord_3027416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55209466400098174167067051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73612621866797565556089401 55209466400098174167067051)
  ·
    refine ⟨82814199600147261250600577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55209466400098174167067051 82814199600147261250600577)
    ·
      refine ⟨62110649700110445937950433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82814199600147261250600577 62110649700110445937950433)
      ·
        refine ⟨46582987275082834453462825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62110649700110445937950433 46582987275082834453462825)
        ·
          refine ⟨34937240456312125840097119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46582987275082834453462825 34937240456312125840097119)
          ·
            refine ⟨52405860684468188760145679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34937240456312125840097119 52405860684468188760145679)
            ·
              refine ⟨78608791026702283140218519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52405860684468188760145679 78608791026702283140218519)
              ·
                refine ⟨117913186540053424710327779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78608791026702283140218519 117913186540053424710327779)
                ·
                  refine ⟨176869779810080137065491669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117913186540053424710327779 176869779810080137065491669)
                  ·
                    refine ⟨4145385464298753212472461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176869779810080137065491669 4145385464298753212472461)
                    ·
                      refine ⟨1554519549112032454677173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145385464298753212472461 1554519549112032454677173)
                      ·
                        rfl

theorem cell23_3027416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3027416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027416 prefixEnd_3027416 := by exact prefixLift 3027416
  have htrace : WordTrace (prefixWord ++ tailWord_3027416) baseStart_3027416 baseEnd_3027416 := by
    simpa [prefixWord, tailWord_3027416, baseEnd_3027416] using wordTrace_append hprefix tailTrace_3027416
  have hstable : (prefixWord ++ tailWord_3027416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027416).length < 2 ^ (prefixWord ++ tailWord_3027416).sum := by decide
  have hdescent : baseEnd_3027416 < baseStart_3027416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027470 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_3027470 : Nat := 118140960795 + 3027470 * 2 ^ 59
def prefixEnd_3027470 : Nat := 4983230072969 + 3 ^ 40 * 3027470 * 2
def baseEnd_3027470 : Nat := 518182425689125081133975

theorem tailTrace_3027470 : CollatzResearch.WordTrace tailWord_3027470 prefixEnd_3027470 518182425689125081133975 := by
  unfold tailWord_3027470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802612792750089444574983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73613934894667143704399909 13802612792750089444574983)
  ·
    refine ⟨20703919189125134166862475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13802612792750089444574983 20703919189125134166862475)
    ·
      refine ⟨31055878783687701250293713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20703919189125134166862475 31055878783687701250293713)
      ·
        refine ⟨23291909087765775937720285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31055878783687701250293713 23291909087765775937720285)
        ·
          refine ⟨8734465907912165976645107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23291909087765775937720285 8734465907912165976645107)
          ·
            refine ⟨13101698861868248964967661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8734465907912165976645107 13101698861868248964967661)
            ·
              refine ⟨4913137073200593361862873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13101698861868248964967661 4913137073200593361862873)
              ·
                refine ⟨3684852804900445021397155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4913137073200593361862873 3684852804900445021397155)
                ·
                  refine ⟨5527279207350667532095733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684852804900445021397155 5527279207350667532095733)
                  ·
                    refine ⟨518182425689125081133975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5527279207350667532095733 518182425689125081133975)
                    ·
                      rfl

theorem cell23_3027470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_3027470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027470 prefixEnd_3027470 := by exact prefixLift 3027470
  have htrace : WordTrace (prefixWord ++ tailWord_3027470) baseStart_3027470 baseEnd_3027470 := by
    simpa [prefixWord, tailWord_3027470, baseEnd_3027470] using wordTrace_append hprefix tailTrace_3027470
  have hstable : (prefixWord ++ tailWord_3027470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027470).length < 2 ^ (prefixWord ++ tailWord_3027470).sum := by decide
  have hdescent : baseEnd_3027470 < baseStart_3027470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027473 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_3027473 : Nat := 118140960795 + 3027473 * 2 ^ 59
def prefixEnd_3027473 : Nat := 4983230072969 + 3 ^ 40 * 3027473 * 2
def baseEnd_3027473 : Nat := 1554548817509338731664411

theorem tailTrace_3027473 : CollatzResearch.WordTrace tailWord_3027473 prefixEnd_3027473 1554548817509338731664411 := by
  unfold tailWord_3027473
  simp only [CollatzResearch.WordTrace]
  refine ⟨110421011760989847068959073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73614007840659898045972715 110421011760989847068959073)
  ·
    refine ⟨82815758820742385301719305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110421011760989847068959073 82815758820742385301719305)
    ·
      refine ⟨62111819115556788976289479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82815758820742385301719305 62111819115556788976289479)
      ·
        refine ⟨93167728673335183464434219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62111819115556788976289479 93167728673335183464434219)
        ·
          refine ⟨139751593010002775196651329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93167728673335183464434219 139751593010002775196651329)
          ·
            refine ⟨104813694757502081397488497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139751593010002775196651329 104813694757502081397488497)
            ·
              refine ⟨78610271068126561048116373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104813694757502081397488497 78610271068126561048116373)
              ·
                refine ⟨3684856456318432549130455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78610271068126561048116373 3684856456318432549130455)
                ·
                  refine ⟨5527284684477648823695683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684856456318432549130455 5527284684477648823695683)
                  ·
                    refine ⟨8290927026716473235543525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5527284684477648823695683 8290927026716473235543525)
                    ·
                      refine ⟨1554548817509338731664411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8290927026716473235543525 1554548817509338731664411)
                      ·
                        rfl

theorem cell23_3027473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_3027473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027473 prefixEnd_3027473 := by exact prefixLift 3027473
  have htrace : WordTrace (prefixWord ++ tailWord_3027473) baseStart_3027473 baseEnd_3027473 := by
    simpa [prefixWord, tailWord_3027473, baseEnd_3027473] using wordTrace_append hprefix tailTrace_3027473
  have hstable : (prefixWord ++ tailWord_3027473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027473).length < 2 ^ (prefixWord ++ tailWord_3027473).sum := by decide
  have hdescent : baseEnd_3027473 < baseStart_3027473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027493 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_3027493 : Nat := 118140960795 + 3027493 * 2 ^ 59
def prefixEnd_3027493 : Nat := 4983230072969 + 3 ^ 40 * 3027493 * 2
def baseEnd_3027493 : Nat := 1554559087122428653414319

theorem tailTrace_3027493 : CollatzResearch.WordTrace tailWord_3027493 prefixEnd_3027493 1554559087122428653414319 := by
  unfold tailWord_3027493
  simp only [CollatzResearch.WordTrace]
  refine ⟨110421741220917390484687133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73614494147278260323124755 110421741220917390484687133)
  ·
    refine ⟨41408152957844021431757675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110421741220917390484687133 41408152957844021431757675)
    ·
      refine ⟨62112229436766032147636513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41408152957844021431757675 62112229436766032147636513)
      ·
        refine ⟨46584172077574524110727385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62112229436766032147636513 46584172077574524110727385)
        ·
          refine ⟨34938129058180893083045539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46584172077574524110727385 34938129058180893083045539)
          ·
            refine ⟨52407193587271339624568309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34938129058180893083045539 52407193587271339624568309)
            ·
              refine ⟨4913174398806688089803279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52407193587271339624568309 4913174398806688089803279)
              ·
                refine ⟨7369761598210032134704919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913174398806688089803279 7369761598210032134704919)
                ·
                  refine ⟨11054642397315048202057379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369761598210032134704919 11054642397315048202057379)
                  ·
                    refine ⟨16581963595972572303086069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11054642397315048202057379 16581963595972572303086069)
                    ·
                      refine ⟨1554559087122428653414319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16581963595972572303086069 1554559087122428653414319)
                      ·
                        rfl

theorem cell23_3027493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_3027493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027493 prefixEnd_3027493 := by exact prefixLift 3027493
  have htrace : WordTrace (prefixWord ++ tailWord_3027493) baseStart_3027493 baseEnd_3027493 := by
    simpa [prefixWord, tailWord_3027493, baseEnd_3027493] using wordTrace_append hprefix tailTrace_3027493
  have hstable : (prefixWord ++ tailWord_3027493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027493).length < 2 ^ (prefixWord ++ tailWord_3027493).sum := by decide
  have hdescent : baseEnd_3027493 < baseStart_3027493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027540 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3027540 : Nat := 118140960795 + 3027540 * 2 ^ 59
def prefixEnd_3027540 : Nat := 4983230072969 + 3 ^ 40 * 3027540 * 2
def baseEnd_3027540 : Nat := 1554583220713189969526603

theorem tailTrace_3027540 : CollatzResearch.WordTrace tailWord_3027540 prefixEnd_3027540 1554583220713189969526603 := by
  unfold tailWord_3027540
  simp only [CollatzResearch.WordTrace]
  refine ⟨55211727725873558755824037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73615636967831411674432049 55211727725873558755824037)
  ·
    refine ⟨10352198948601292266717007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55211727725873558755824037 10352198948601292266717007)
    ·
      refine ⟨15528298422901938400075511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10352198948601292266717007 15528298422901938400075511)
      ·
        refine ⟨23292447634352907600113267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15528298422901938400075511 23292447634352907600113267)
        ·
          refine ⟨34938671451529361400169901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23292447634352907600113267 34938671451529361400169901)
          ·
            refine ⟨13102001794323510525063713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34938671451529361400169901 13102001794323510525063713)
            ·
              refine ⟨9826501345742632893797785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13102001794323510525063713 9826501345742632893797785)
              ·
                refine ⟨7369876009306974670348339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9826501345742632893797785 7369876009306974670348339)
                ·
                  refine ⟨11054814013960462005522509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369876009306974670348339 11054814013960462005522509)
                  ·
                    refine ⟨4145555255235173252070941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11054814013960462005522509 4145555255235173252070941)
                    ·
                      refine ⟨1554583220713189969526603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145555255235173252070941 1554583220713189969526603)
                      ·
                        rfl

theorem cell23_3027540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3027540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027540 prefixEnd_3027540 := by exact prefixLift 3027540
  have htrace : WordTrace (prefixWord ++ tailWord_3027540) baseStart_3027540 baseEnd_3027540 := by
    simpa [prefixWord, tailWord_3027540, baseEnd_3027540] using wordTrace_append hprefix tailTrace_3027540
  have hstable : (prefixWord ++ tailWord_3027540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027540).length < 2 ^ (prefixWord ++ tailWord_3027540).sum := by decide
  have hdescent : baseEnd_3027540 < baseStart_3027540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027557 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_3027557 : Nat := 118140960795 + 3027557 * 2 ^ 59
def prefixEnd_3027557 : Nat := 4983230072969 + 3 ^ 40 * 3027557 * 2
def baseEnd_3027557 : Nat := 1554591949884316403014025

theorem tailTrace_3027557 : CollatzResearch.WordTrace tailWord_3027557 prefixEnd_3027557 1554591949884316403014025 := by
  unfold tailWord_3027557
  simp only [CollatzResearch.WordTrace]
  refine ⟨110424075492685529415016925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73616050328457019610011283 110424075492685529415016925)
  ·
    refine ⟨41409028309757073530631347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110424075492685529415016925 41409028309757073530631347)
    ·
      refine ⟨62113542464635610295947021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41409028309757073530631347 62113542464635610295947021)
      ·
        refine ⟨23292578424238353860980133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62113542464635610295947021 23292578424238353860980133)
        ·
          refine ⟨4367358454544691348933775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23292578424238353860980133 4367358454544691348933775)
          ·
            refine ⟨6551037681817037023400663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367358454544691348933775 6551037681817037023400663)
            ·
              refine ⟨9826556522725555535100995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6551037681817037023400663 9826556522725555535100995)
              ·
                refine ⟨14739834784088333302651493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9826556522725555535100995 14739834784088333302651493)
                ·
                  refine ⟨2763719022016562494247155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14739834784088333302651493 2763719022016562494247155)
                  ·
                    refine ⟨4145578533024843741370733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2763719022016562494247155 4145578533024843741370733)
                    ·
                      refine ⟨1554591949884316403014025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145578533024843741370733 1554591949884316403014025)
                      ·
                        rfl

theorem cell23_3027557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_3027557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027557 prefixEnd_3027557 := by exact prefixLift 3027557
  have htrace : WordTrace (prefixWord ++ tailWord_3027557) baseStart_3027557 baseEnd_3027557 := by
    simpa [prefixWord, tailWord_3027557, baseEnd_3027557] using wordTrace_append hprefix tailTrace_3027557
  have hstable : (prefixWord ++ tailWord_3027557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027557).length < 2 ^ (prefixWord ++ tailWord_3027557).sum := by decide
  have hdescent : baseEnd_3027557 < baseStart_3027557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027574 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3027574 : Nat := 118140960795 + 3027574 * 2 ^ 59
def prefixEnd_3027574 : Nat := 4983230072969 + 3 ^ 40 * 3027574 * 2
def baseEnd_3027574 : Nat := 1554600679055442836501447

theorem tailTrace_3027574 : CollatzResearch.WordTrace tailWord_3027574 prefixEnd_3027574 1554600679055442836501447 := by
  unfold tailWord_3027574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901543470851496332399111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73616463689082627545590517 6901543470851496332399111)
  ·
    refine ⟨10352315206277244498598667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6901543470851496332399111 10352315206277244498598667)
    ·
      refine ⟨15528472809415866747898001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10352315206277244498598667 15528472809415866747898001)
      ·
        refine ⟨11646354607061900060923501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15528472809415866747898001 11646354607061900060923501)
        ·
          refine ⟨4367382977648212522846313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11646354607061900060923501 4367382977648212522846313)
          ·
            refine ⟨3275537233236159392134735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4367382977648212522846313 3275537233236159392134735)
            ·
              refine ⟨4913305849854239088202103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275537233236159392134735 4913305849854239088202103)
              ·
                refine ⟨7369958774781358632303155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913305849854239088202103 7369958774781358632303155)
                ·
                  refine ⟨11054938162172037948454733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369958774781358632303155 11054938162172037948454733)
                  ·
                    refine ⟨4145601810814514230670525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11054938162172037948454733 4145601810814514230670525)
                    ·
                      refine ⟨1554600679055442836501447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145601810814514230670525 1554600679055442836501447)
                      ·
                        rfl

theorem cell23_3027574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3027574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027574 prefixEnd_3027574 := by exact prefixLift 3027574
  have htrace : WordTrace (prefixWord ++ tailWord_3027574) baseStart_3027574 baseEnd_3027574 := by
    simpa [prefixWord, tailWord_3027574, baseEnd_3027574] using wordTrace_append hprefix tailTrace_3027574
  have hstable : (prefixWord ++ tailWord_3027574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027574).length < 2 ^ (prefixWord ++ tailWord_3027574).sum := by decide
  have hdescent : baseEnd_3027574 < baseStart_3027574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027614 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_3027614 : Nat := 118140960795 + 3027614 * 2 ^ 59
def prefixEnd_3027614 : Nat := 4983230072969 + 3 ^ 40 * 3027614 * 2
def baseEnd_3027614 : Nat := 1554621218281622680001263

theorem tailTrace_3027614 : CollatzResearch.WordTrace tailWord_3027614 prefixEnd_3027614 1554621218281622680001263 := by
  unfold tailWord_3027614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803269306684878518730237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73617436302319352099894597 13803269306684878518730237)
  ·
    refine ⟨5176225990006829444523839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13803269306684878518730237 5176225990006829444523839)
    ·
      refine ⟨7764338985010244166785759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5176225990006829444523839 7764338985010244166785759)
      ·
        refine ⟨11646508477515366250178639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7764338985010244166785759 11646508477515366250178639)
        ·
          refine ⟨17469762716273049375267959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11646508477515366250178639 17469762716273049375267959)
          ·
            refine ⟨26204644074409574062901939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17469762716273049375267959 26204644074409574062901939)
            ·
              refine ⟨39306966111614361094352909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26204644074409574062901939 39306966111614361094352909)
              ·
                refine ⟨14740112291855385410382341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39306966111614361094352909 14740112291855385410382341)
                ·
                  refine ⟨2763771054722884764446689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14740112291855385410382341 2763771054722884764446689)
                  ·
                    refine ⟨2072828291042163573335017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2763771054722884764446689 2072828291042163573335017)
                    ·
                      refine ⟨1554621218281622680001263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072828291042163573335017 1554621218281622680001263)
                      ·
                        rfl

theorem cell23_3027614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_3027614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027614 prefixEnd_3027614 := by exact prefixLift 3027614
  have htrace : WordTrace (prefixWord ++ tailWord_3027614) baseStart_3027614 baseEnd_3027614 := by
    simpa [prefixWord, tailWord_3027614, baseEnd_3027614] using wordTrace_append hprefix tailTrace_3027614
  have hstable : (prefixWord ++ tailWord_3027614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027614).length < 2 ^ (prefixWord ++ tailWord_3027614).sum := by decide
  have hdescent : baseEnd_3027614 < baseStart_3027614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027631 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 2, 2, 2]
def baseStart_3027631 : Nat := 118140960795 + 3027631 * 2 ^ 59
def prefixEnd_3027631 : Nat := 4983230072969 + 3 ^ 40 * 3027631 * 2
def baseEnd_3027631 : Nat := 1554629947452749113488685

theorem tailTrace_3027631 : CollatzResearch.WordTrace tailWord_3027631 prefixEnd_3027631 1554629947452749113488685 := by
  unfold tailWord_3027631
  simp only [CollatzResearch.WordTrace]
  refine ⟨110426774494417440053210747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73617849662944960035473831 110426774494417440053210747)
  ·
    refine ⟨165640161741626160079816121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110426774494417440053210747 165640161741626160079816121)
    ·
      refine ⟨124230121306219620059862091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165640161741626160079816121 124230121306219620059862091)
      ·
        refine ⟨186345181959329430089793137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124230121306219620059862091 186345181959329430089793137)
        ·
          refine ⟨139758886469497072567344853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186345181959329430089793137 139758886469497072567344853)
          ·
            refine ⟨3275598901628837638297145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 139758886469497072567344853 3275598901628837638297145)
            ·
              refine ⟨2456699176221628228722859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3275598901628837638297145 2456699176221628228722859)
              ·
                refine ⟨3685048764332442343084289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456699176221628228722859 3685048764332442343084289)
                ·
                  refine ⟨2763786573249331757313217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3685048764332442343084289 2763786573249331757313217)
                  ·
                    refine ⟨2072839929936998817984913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2763786573249331757313217 2072839929936998817984913)
                    ·
                      refine ⟨1554629947452749113488685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072839929936998817984913 1554629947452749113488685)
                      ·
                        rfl

theorem cell23_3027631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 2, 2].length) (baseStart_3027631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027631 prefixEnd_3027631 := by exact prefixLift 3027631
  have htrace : WordTrace (prefixWord ++ tailWord_3027631) baseStart_3027631 baseEnd_3027631 := by
    simpa [prefixWord, tailWord_3027631, baseEnd_3027631] using wordTrace_append hprefix tailTrace_3027631
  have hstable : (prefixWord ++ tailWord_3027631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027631).length < 2 ^ (prefixWord ++ tailWord_3027631).sum := by decide
  have hdescent : baseEnd_3027631 < baseStart_3027631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027660 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3027660 : Nat := 118140960795 + 3027660 * 2 ^ 59
def prefixEnd_3027660 : Nat := 4983230072969 + 3 ^ 40 * 3027660 * 2
def baseEnd_3027660 : Nat := 1554644838391729500026051

theorem tailTrace_3027660 : CollatzResearch.WordTrace tailWord_3027660 prefixEnd_3027660 1554644838391729500026051 := by
  unfold tailWord_3027660
  simp only [CollatzResearch.WordTrace]
  refine ⟨55213916105656189003008217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73618554807541585337344289 55213916105656189003008217)
  ·
    refine ⟨41410437079242141752256163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55213916105656189003008217 41410437079242141752256163)
    ·
      refine ⟨62115655618863212628384245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41410437079242141752256163 62115655618863212628384245)
      ·
        refine ⟨5823342714268426183911023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62115655618863212628384245 5823342714268426183911023)
        ·
          refine ⟨8735014071402639275866535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823342714268426183911023 8735014071402639275866535)
          ·
            refine ⟨13102521107103958913799803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735014071402639275866535 13102521107103958913799803)
            ·
              refine ⟨19653781660655938370699705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13102521107103958913799803 19653781660655938370699705)
              ·
                refine ⟨14740336245491953778024779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19653781660655938370699705 14740336245491953778024779)
                ·
                  refine ⟨22110504368237930667037169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14740336245491953778024779 22110504368237930667037169)
                  ·
                    refine ⟨16582878276178448000277877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22110504368237930667037169 16582878276178448000277877)
                    ·
                      refine ⟨1554644838391729500026051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16582878276178448000277877 1554644838391729500026051)
                      ·
                        rfl

theorem cell23_3027660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3027660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027660 prefixEnd_3027660 := by exact prefixLift 3027660
  have htrace : WordTrace (prefixWord ++ tailWord_3027660) baseStart_3027660 baseEnd_3027660 := by
    simpa [prefixWord, tailWord_3027660, baseEnd_3027660] using wordTrace_append hprefix tailTrace_3027660
  have hstable : (prefixWord ++ tailWord_3027660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027660).length < 2 ^ (prefixWord ++ tailWord_3027660).sum := by decide
  have hdescent : baseEnd_3027660 < baseStart_3027660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027673 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_3027673 : Nat := 118140960795 + 3027673 * 2 ^ 59
def prefixEnd_3027673 : Nat := 4983230072969 + 3 ^ 40 * 3027673 * 2
def baseEnd_3027673 : Nat := 1554651513640237949163491

theorem tailTrace_3027673 : CollatzResearch.WordTrace tailWord_3027673 prefixEnd_3027673 1554651513640237949163491 := by
  unfold tailWord_3027673
  simp only [CollatzResearch.WordTrace]
  refine ⟨110428306360265281226239673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73618870906843520817493115 110428306360265281226239673)
  ·
    refine ⟨82821229770198960919679755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110428306360265281226239673 82821229770198960919679755)
    ·
      refine ⟨124231844655298441379519633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82821229770198960919679755 124231844655298441379519633)
      ·
        refine ⟨93173883491473831034639725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124231844655298441379519633 93173883491473831034639725)
        ·
          refine ⟨34940206309302686637989897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93173883491473831034639725 34940206309302686637989897)
          ·
            refine ⟨26205154731977014978492423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34940206309302686637989897 26205154731977014978492423)
            ·
              refine ⟨39307732097965522467738635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26205154731977014978492423 39307732097965522467738635)
              ·
                refine ⟨58961598146948283701607953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39307732097965522467738635 58961598146948283701607953)
                ·
                  refine ⟨44221198610211212776205965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58961598146948283701607953 44221198610211212776205965)
                  ·
                    refine ⟨16582949478829204791077237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44221198610211212776205965 16582949478829204791077237)
                    ·
                      refine ⟨1554651513640237949163491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16582949478829204791077237 1554651513640237949163491)
                      ·
                        rfl

theorem cell23_3027673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_3027673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027673 prefixEnd_3027673 := by exact prefixLift 3027673
  have htrace : WordTrace (prefixWord ++ tailWord_3027673) baseStart_3027673 baseEnd_3027673 := by
    simpa [prefixWord, tailWord_3027673, baseEnd_3027673] using wordTrace_append hprefix tailTrace_3027673
  have hstable : (prefixWord ++ tailWord_3027673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027673).length < 2 ^ (prefixWord ++ tailWord_3027673).sum := by decide
  have hdescent : baseEnd_3027673 < baseStart_3027673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027680 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 3, 4]
def baseStart_3027680 : Nat := 118140960795 + 3027680 * 2 ^ 59
def prefixEnd_3027680 : Nat := 4983230072969 + 3 ^ 40 * 3027680 * 2
def baseEnd_3027680 : Nat := 518218369334939807258653

theorem tailTrace_3027680 : CollatzResearch.WordTrace tailWord_3027680 prefixEnd_3027680 518218369334939807258653 := by
  unfold tailWord_3027680
  simp only [CollatzResearch.WordTrace]
  refine ⟨55214280835619960710872247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73619041114159947614496329 55214280835619960710872247)
  ·
    refine ⟨82821421253429941066308371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55214280835619960710872247 82821421253429941066308371)
    ·
      refine ⟨124232131880144911599462557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82821421253429941066308371 124232131880144911599462557)
      ·
        refine ⟨46587049455054341849798459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124232131880144911599462557 46587049455054341849798459)
        ·
          refine ⟨69880574182581512774697689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46587049455054341849798459 69880574182581512774697689)
          ·
            refine ⟨52410430636936134581023267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69880574182581512774697689 52410430636936134581023267)
            ·
              refine ⟨78615645955404201871534901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52410430636936134581023267 78615645955404201871534901)
              ·
                refine ⟨7370216808319143925456397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78615645955404201871534901 7370216808319143925456397)
                ·
                  refine ⟨2763831303119678972046149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7370216808319143925456397 2763831303119678972046149)
                  ·
                    refine ⟨518218369334939807258653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763831303119678972046149 518218369334939807258653)
                    ·
                      rfl

theorem cell23_3027680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_3027680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027680 prefixEnd_3027680 := by exact prefixLift 3027680
  have htrace : WordTrace (prefixWord ++ tailWord_3027680) baseStart_3027680 baseEnd_3027680 := by
    simpa [prefixWord, tailWord_3027680, baseEnd_3027680] using wordTrace_append hprefix tailTrace_3027680
  have hstable : (prefixWord ++ tailWord_3027680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027680).length < 2 ^ (prefixWord ++ tailWord_3027680).sum := by decide
  have hdescent : baseEnd_3027680 < baseStart_3027680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027690 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3027690 : Nat := 118140960795 + 3027690 * 2 ^ 59
def prefixEnd_3027690 : Nat := 4983230072969 + 3 ^ 40 * 3027690 * 2
def baseEnd_3027690 : Nat := 1554660242811364382650913

theorem tailTrace_3027690 : CollatzResearch.WordTrace tailWord_3027690 prefixEnd_3027690 1554660242811364382650913 := by
  unfold tailWord_3027690
  simp only [CollatzResearch.WordTrace]
  refine ⟨27607231600300923282402131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73619284267469128753072349 27607231600300923282402131)
  ·
    refine ⟨41410847400451384923603197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27607231600300923282402131 41410847400451384923603197)
    ·
      refine ⟨15529067775169269346351199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41410847400451384923603197 15529067775169269346351199)
      ·
        refine ⟨23293601662753904019526799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15529067775169269346351199 23293601662753904019526799)
        ·
          refine ⟨34940402494130856029290199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23293601662753904019526799 34940402494130856029290199)
          ·
            refine ⟨52410603741196284043935299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34940402494130856029290199 52410603741196284043935299)
            ·
              refine ⟨78615905611794426065902949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52410603741196284043935299 78615905611794426065902949)
              ·
                refine ⟨14740482302211454887356803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78615905611794426065902949 14740482302211454887356803)
                ·
                  refine ⟨22110723453317182331035205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14740482302211454887356803 22110723453317182331035205)
                  ·
                    refine ⟨4145760647496971687069101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22110723453317182331035205 4145760647496971687069101)
                    ·
                      refine ⟨1554660242811364382650913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145760647496971687069101 1554660242811364382650913)
                      ·
                        rfl

theorem cell23_3027690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3027690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027690 prefixEnd_3027690 := by exact prefixLift 3027690
  have htrace : WordTrace (prefixWord ++ tailWord_3027690) baseStart_3027690 baseEnd_3027690 := by
    simpa [prefixWord, tailWord_3027690, baseEnd_3027690] using wordTrace_append hprefix tailTrace_3027690
  have hstable : (prefixWord ++ tailWord_3027690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027690).length < 2 ^ (prefixWord ++ tailWord_3027690).sum := by decide
  have hdescent : baseEnd_3027690 < baseStart_3027690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027760 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_3027760 : Nat := 118140960795 + 3027760 * 2 ^ 59
def prefixEnd_3027760 : Nat := 4983230072969 + 3 ^ 40 * 3027760 * 2
def baseEnd_3027760 : Nat := 1554696186457179108775591

theorem tailTrace_3027760 : CollatzResearch.WordTrace tailWord_3027760 prefixEnd_3027760 1554696186457179108775591 := by
  unfold tailWord_3027760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55215739755475047542328367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73620986340633396723104489 55215739755475047542328367)
  ·
    refine ⟨82823609633212571313492551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55215739755475047542328367 82823609633212571313492551)
    ·
      refine ⟨124235414449818856970238827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82823609633212571313492551 124235414449818856970238827)
      ·
        refine ⟨186353121674728285455358241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124235414449818856970238827 186353121674728285455358241)
        ·
          refine ⟨139764841256046214091518681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186353121674728285455358241 139764841256046214091518681)
          ·
            refine ⟨104823630942034660568639011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139764841256046214091518681 104823630942034660568639011)
            ·
              refine ⟨157235446413051990852958517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104823630942034660568639011 157235446413051990852958517)
              ·
                refine ⟨14740823101223624142464861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157235446413051990852958517 14740823101223624142464861)
                ·
                  refine ⟨5527808662958859053424323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14740823101223624142464861 5527808662958859053424323)
                  ·
                    refine ⟨8291712994438288580136485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5527808662958859053424323 8291712994438288580136485)
                    ·
                      refine ⟨1554696186457179108775591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8291712994438288580136485 1554696186457179108775591)
                      ·
                        rfl

theorem cell23_3027760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_3027760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027760 prefixEnd_3027760 := by exact prefixLift 3027760
  have htrace : WordTrace (prefixWord ++ tailWord_3027760) baseStart_3027760 baseEnd_3027760 := by
    simpa [prefixWord, tailWord_3027760, baseEnd_3027760] using wordTrace_append hprefix tailTrace_3027760
  have hstable : (prefixWord ++ tailWord_3027760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027760).length < 2 ^ (prefixWord ++ tailWord_3027760).sum := by decide
  have hdescent : baseEnd_3027760 < baseStart_3027760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
