import V185TrunkScan23Chunk0901

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5338247 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_5338247 : Nat := 118140960795 + 5338247 * 2 ^ 59
def prefixEnd_5338247 : Nat := 4983230072969 + 3 ^ 40 * 5338247 * 2
def baseEnd_5338247 : Nat := 2741086563421880817762355

theorem tailTrace_5338247 : CollatzResearch.WordTrace tailWord_5338247 prefixEnd_5338247 2741086563421880817762355 := by
  unfold tailWord_5338247
  simp only [CollatzResearch.WordTrace]
  refine ⟨194701863491450293848564995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129801242327633529232376663 194701863491450293848564995)
  ·
    refine ⟨292052795237175440772847493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194701863491450293848564995 292052795237175440772847493)
    ·
      refine ⟨54759899106970395144908905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292052795237175440772847493 54759899106970395144908905)
      ·
        refine ⟨41069924330227796358681679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54759899106970395144908905 41069924330227796358681679)
        ·
          refine ⟨61604886495341694538022519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41069924330227796358681679 61604886495341694538022519)
          ·
            refine ⟨92407329743012541807033779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61604886495341694538022519 92407329743012541807033779)
            ·
              refine ⟨138610994614518812710550669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92407329743012541807033779 138610994614518812710550669)
              ·
                refine ⟨51979122980444554766456501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138610994614518812710550669 51979122980444554766456501)
                ·
                  refine ⟨4873042779416677009355297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51979122980444554766456501 4873042779416677009355297)
                  ·
                    refine ⟨3654782084562507757016473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4873042779416677009355297 3654782084562507757016473)
                    ·
                      refine ⟨2741086563421880817762355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3654782084562507757016473 2741086563421880817762355)
                      ·
                        rfl

theorem cell23_5338247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_5338247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338247 prefixEnd_5338247 := by exact prefixLift 5338247
  have htrace : WordTrace (prefixWord ++ tailWord_5338247) baseStart_5338247 baseEnd_5338247 := by
    simpa [prefixWord, tailWord_5338247, baseEnd_5338247] using wordTrace_append hprefix tailTrace_5338247
  have hstable : (prefixWord ++ tailWord_5338247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338247).length < 2 ^ (prefixWord ++ tailWord_5338247).sum := by decide
  have hdescent : baseEnd_5338247 < baseStart_5338247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338264 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5338264 : Nat := 118140960795 + 5338264 * 2 ^ 59
def prefixEnd_5338264 : Nat := 4983230072969 + 3 ^ 40 * 5338264 * 2
def baseEnd_5338264 : Nat := 2741095292593007251249777

theorem tailTrace_5338264 : CollatzResearch.WordTrace tailWord_5338264 prefixEnd_5338264 2741095292593007251249777 := by
  unfold tailWord_5338264
  simp only [CollatzResearch.WordTrace]
  refine ⟨97351241766194352875966923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129801655688259137167955897 97351241766194352875966923)
  ·
    refine ⟨146026862649291529313950385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97351241766194352875966923 146026862649291529313950385)
    ·
      refine ⟨109520146986968646985462789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146026862649291529313950385 109520146986968646985462789)
      ·
        refine ⟨20535027560056621309774273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109520146986968646985462789 20535027560056621309774273)
        ·
          refine ⟨15401270670042465982330705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20535027560056621309774273 15401270670042465982330705)
          ·
            refine ⟨11550953002531849486748029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15401270670042465982330705 11550953002531849486748029)
            ·
              refine ⟨4331607375949443557530511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11550953002531849486748029 4331607375949443557530511)
              ·
                refine ⟨6497411063924165336295767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4331607375949443557530511 6497411063924165336295767)
                ·
                  refine ⟨9746116595886248004443651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6497411063924165336295767 9746116595886248004443651)
                  ·
                    refine ⟨14619174893829372006665477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9746116595886248004443651 14619174893829372006665477)
                    ·
                      refine ⟨2741095292593007251249777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14619174893829372006665477 2741095292593007251249777)
                      ·
                        rfl

theorem cell23_5338264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5338264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338264 prefixEnd_5338264 := by exact prefixLift 5338264
  have htrace : WordTrace (prefixWord ++ tailWord_5338264) baseStart_5338264 baseEnd_5338264 := by
    simpa [prefixWord, tailWord_5338264, baseEnd_5338264] using wordTrace_append hprefix tailTrace_5338264
  have hstable : (prefixWord ++ tailWord_5338264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338264).length < 2 ^ (prefixWord ++ tailWord_5338264).sum := by decide
  have hdescent : baseEnd_5338264 < baseStart_5338264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338270 : List Nat := [4, 3, 1, 1, 2, 12]
def baseStart_5338270 : Nat := 118140960795 + 5338270 * 2 ^ 59
def prefixEnd_5338270 : Nat := 4983230072969 + 3 ^ 40 * 5338270 * 2
def baseEnd_5338270 : Nat := 11280240220069688180143

theorem tailTrace_5338270 : CollatzResearch.WordTrace tailWord_5338270 prefixEnd_5338270 11280240220069688180143 := by
  unfold tailWord_5338270
  simp only [CollatzResearch.WordTrace]
  refine ⟨24337837796295871097081533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129801801580244645851101509 24337837796295871097081533)
  ·
    refine ⟨9126689173610951661405575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24337837796295871097081533 9126689173610951661405575)
    ·
      refine ⟨13690033760416427492108363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9126689173610951661405575 13690033760416427492108363)
      ·
        refine ⟨20535050640624641238162545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13690033760416427492108363 20535050640624641238162545)
        ·
          refine ⟨15401287980468480928621909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20535050640624641238162545 15401287980468480928621909)
          ·
            refine ⟨11280240220069688180143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15401287980468480928621909 11280240220069688180143)
            ·
              rfl

theorem cell23_5338270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 12].length) (baseStart_5338270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338270 prefixEnd_5338270 := by exact prefixLift 5338270
  have htrace : WordTrace (prefixWord ++ tailWord_5338270) baseStart_5338270 baseEnd_5338270 := by
    simpa [prefixWord, tailWord_5338270, baseEnd_5338270] using wordTrace_append hprefix tailTrace_5338270
  have hstable : (prefixWord ++ tailWord_5338270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338270).length < 2 ^ (prefixWord ++ tailWord_5338270).sum := by decide
  have hdescent : baseEnd_5338270 < baseStart_5338270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338297 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5338297 : Nat := 118140960795 + 5338297 * 2 ^ 59
def prefixEnd_5338297 : Nat := 4983230072969 + 3 ^ 40 * 5338297 * 2
def baseEnd_5338297 : Nat := 2741112237454605622137125

theorem tailTrace_5338297 : CollatzResearch.WordTrace tailWord_5338297 prefixEnd_5338297 2741112237454605622137125 := by
  unfold tailWord_5338297
  simp only [CollatzResearch.WordTrace]
  refine ⟨194703687141269152387885145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129802458094179434925256763 194703687141269152387885145)
  ·
    refine ⟨146027765355951864290913859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194703687141269152387885145 146027765355951864290913859)
    ·
      refine ⟨219041648033927796436370789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146027765355951864290913859 219041648033927796436370789)
      ·
        refine ⟨41070309006361461831819523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219041648033927796436370789 41070309006361461831819523)
        ·
          refine ⟨61605463509542192747729285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41070309006361461831819523 61605463509542192747729285)
          ·
            refine ⟨11551024408039161140199241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61605463509542192747729285 11551024408039161140199241)
            ·
              refine ⟨8663268306029370855149431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11551024408039161140199241 8663268306029370855149431)
              ·
                refine ⟨12994902459044056282724147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8663268306029370855149431 12994902459044056282724147)
                ·
                  refine ⟨19492353688566084424086221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12994902459044056282724147 19492353688566084424086221)
                  ·
                    refine ⟨7309632633212281659032333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19492353688566084424086221 7309632633212281659032333)
                    ·
                      refine ⟨2741112237454605622137125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7309632633212281659032333 2741112237454605622137125)
                      ·
                        rfl

theorem cell23_5338297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5338297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338297 prefixEnd_5338297 := by exact prefixLift 5338297
  have htrace : WordTrace (prefixWord ++ tailWord_5338297) baseStart_5338297 baseEnd_5338297 := by
    simpa [prefixWord, tailWord_5338297, baseEnd_5338297] using wordTrace_append hprefix tailTrace_5338297
  have hstable : (prefixWord ++ tailWord_5338297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338297).length < 2 ^ (prefixWord ++ tailWord_5338297).sum := by decide
  have hdescent : baseEnd_5338297 < baseStart_5338297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338318 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_5338318 : Nat := 118140960795 + 5338318 * 2 ^ 59
def prefixEnd_5338318 : Nat := 4983230072969 + 3 ^ 40 * 5338318 * 2
def baseEnd_5338318 : Nat := 2741123020548350039974529

theorem tailTrace_5338318 : CollatzResearch.WordTrace tailWord_5338318 prefixEnd_5338318 2741123020548350039974529 := by
  unfold tailWord_5338318
  simp only [CollatzResearch.WordTrace]
  refine ⟨24338056634274134121799951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129802968716128715316266405 24338056634274134121799951)
  ·
    refine ⟨36507084951411201182699927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24338056634274134121799951 36507084951411201182699927)
    ·
      refine ⟨54760627427116801774049891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36507084951411201182699927 54760627427116801774049891)
      ·
        refine ⟨82140941140675202661074837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54760627427116801774049891 82140941140675202661074837)
        ·
          refine ⟨3850356615969150124737883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82140941140675202661074837 3850356615969150124737883)
          ·
            refine ⟨5775534923953725187106825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850356615969150124737883 5775534923953725187106825)
            ·
              refine ⟨4331651192965293890330119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5775534923953725187106825 4331651192965293890330119)
              ·
                refine ⟨6497476789447940835495179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4331651192965293890330119 6497476789447940835495179)
                ·
                  refine ⟨9746215184171911253242769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6497476789447940835495179 9746215184171911253242769)
                  ·
                    refine ⟨7309661388128933439932077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9746215184171911253242769 7309661388128933439932077)
                    ·
                      refine ⟨2741123020548350039974529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7309661388128933439932077 2741123020548350039974529)
                      ·
                        rfl

theorem cell23_5338318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_5338318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338318 prefixEnd_5338318 := by exact prefixLift 5338318
  have htrace : WordTrace (prefixWord ++ tailWord_5338318) baseStart_5338318 baseEnd_5338318 := by
    simpa [prefixWord, tailWord_5338318, baseEnd_5338318] using wordTrace_append hprefix tailTrace_5338318
  have hstable : (prefixWord ++ tailWord_5338318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338318).length < 2 ^ (prefixWord ++ tailWord_5338318).sum := by decide
  have hdescent : baseEnd_5338318 < baseStart_5338318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338340 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_5338340 : Nat := 118140960795 + 5338340 * 2 ^ 59
def prefixEnd_5338340 : Nat := 4983230072969 + 3 ^ 40 * 5338340 * 2
def baseEnd_5338340 : Nat := 2741134317122748953899427

theorem tailTrace_5338340 : CollatzResearch.WordTrace tailWord_5338340 prefixEnd_5338340 2741134317122748953899427 := by
  unfold tailWord_5338340
  simp only [CollatzResearch.WordTrace]
  refine ⟨97352627740056685365850237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129803503653408913821133649 97352627740056685365850237)
  ·
    refine ⟨36507235402521257012193839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97352627740056685365850237 36507235402521257012193839)
    ·
      refine ⟨54760853103781885518290759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36507235402521257012193839 54760853103781885518290759)
      ·
        refine ⟨82141279655672828277436139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54760853103781885518290759 82141279655672828277436139)
        ·
          refine ⟨123211919483509242416154209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82141279655672828277436139 123211919483509242416154209)
          ·
            refine ⟨92408939612631931812115657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123211919483509242416154209 92408939612631931812115657)
            ·
              refine ⟨69306704709473948859086743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92408939612631931812115657 69306704709473948859086743)
              ·
                refine ⟨103960057064210923288630115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69306704709473948859086743 103960057064210923288630115)
                ·
                  refine ⟨155940085596316384932945173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103960057064210923288630115 155940085596316384932945173)
                  ·
                    refine ⟨7309691512327330543731805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 155940085596316384932945173 7309691512327330543731805)
                    ·
                      refine ⟨2741134317122748953899427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7309691512327330543731805 2741134317122748953899427)
                      ·
                        rfl

theorem cell23_5338340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_5338340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338340 prefixEnd_5338340 := by exact prefixLift 5338340
  have htrace : WordTrace (prefixWord ++ tailWord_5338340) baseStart_5338340 baseEnd_5338340 := by
    simpa [prefixWord, tailWord_5338340, baseEnd_5338340] using wordTrace_append hprefix tailTrace_5338340
  have hstable : (prefixWord ++ tailWord_5338340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338340).length < 2 ^ (prefixWord ++ tailWord_5338340).sum := by decide
  have hdescent : baseEnd_5338340 < baseStart_5338340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338440 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_5338440 : Nat := 118140960795 + 5338440 * 2 ^ 59
def prefixEnd_5338440 : Nat := 4983230072969 + 3 ^ 40 * 5338440 * 2
def baseEnd_5338440 : Nat := 2741185665188198562648967

theorem tailTrace_5338440 : CollatzResearch.WordTrace tailWord_5338440 prefixEnd_5338440 2741185665188198562648967 := by
  unfold tailWord_5338440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97354451389875543905170387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129805935186500725206893849 97354451389875543905170387)
  ·
    refine ⟨146031677084813315857755581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97354451389875543905170387 146031677084813315857755581)
    ·
      refine ⟨54761878906804993446658343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146031677084813315857755581 54761878906804993446658343)
      ·
        refine ⟨82142818360207490169987515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54761878906804993446658343 82142818360207490169987515)
        ·
          refine ⟨123214227540311235254981273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82142818360207490169987515 123214227540311235254981273)
          ·
            refine ⟨92410670655233426441235955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123214227540311235254981273 92410670655233426441235955)
            ·
              refine ⟨138616005982850139661853933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92410670655233426441235955 138616005982850139661853933)
              ·
                refine ⟨51981002243568802373195225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138616005982850139661853933 51981002243568802373195225)
                ·
                  refine ⟨38985751682676601779896419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51981002243568802373195225 38985751682676601779896419)
                  ·
                    refine ⟨58478627524014902669844629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38985751682676601779896419 58478627524014902669844629)
                    ·
                      refine ⟨2741185665188198562648967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58478627524014902669844629 2741185665188198562648967)
                      ·
                        rfl

theorem cell23_5338440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_5338440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338440 prefixEnd_5338440 := by exact prefixLift 5338440
  have htrace : WordTrace (prefixWord ++ tailWord_5338440) baseStart_5338440 baseEnd_5338440 := by
    simpa [prefixWord, tailWord_5338440, baseEnd_5338440] using wordTrace_append hprefix tailTrace_5338440
  have hstable : (prefixWord ++ tailWord_5338440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338440).length < 2 ^ (prefixWord ++ tailWord_5338440).sum := by decide
  have hdescent : baseEnd_5338440 < baseStart_5338440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338445 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 5]
def baseStart_5338445 : Nat := 118140960795 + 5338445 * 2 ^ 59
def prefixEnd_5338445 : Nat := 4983230072969 + 3 ^ 40 * 5338445 * 2
def baseEnd_5338445 : Nat := 304576470287941227009605

theorem tailTrace_5338445 : CollatzResearch.WordTrace tailWord_5338445 prefixEnd_5338445 304576470287941227009605 := by
  unfold tailWord_5338445
  simp only [CollatzResearch.WordTrace]
  refine ⟨194709085144732973664272789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129806056763155315776181859 194709085144732973664272789)
  ·
    refine ⟨9126988366159358140512787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 194709085144732973664272789 9126988366159358140512787)
    ·
      refine ⟨13690482549239037210769181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9126988366159358140512787 13690482549239037210769181)
      ·
        refine ⟨5133930955964638954038443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13690482549239037210769181 5133930955964638954038443)
        ·
          refine ⟨7700896433946958431057665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5133930955964638954038443 7700896433946958431057665)
          ·
            refine ⟨5775672325460218823293249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7700896433946958431057665 5775672325460218823293249)
            ·
              refine ⟨4331754244095164117469937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5775672325460218823293249 4331754244095164117469937)
              ·
                refine ⟨3248815683071373088102453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4331754244095164117469937 3248815683071373088102453)
                ·
                  refine ⟨304576470287941227009605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248815683071373088102453 304576470287941227009605)
                  ·
                    rfl

theorem cell23_5338445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_5338445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338445 prefixEnd_5338445 := by exact prefixLift 5338445
  have htrace : WordTrace (prefixWord ++ tailWord_5338445) baseStart_5338445 baseEnd_5338445 := by
    simpa [prefixWord, tailWord_5338445, baseEnd_5338445] using wordTrace_append hprefix tailTrace_5338445
  have hstable : (prefixWord ++ tailWord_5338445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338445).length < 2 ^ (prefixWord ++ tailWord_5338445).sum := by decide
  have hdescent : baseEnd_5338445 < baseStart_5338445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338467 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 6]
def baseStart_5338467 : Nat := 118140960795 + 5338467 * 2 ^ 59
def prefixEnd_5338467 : Nat := 4983230072969 + 3 ^ 40 * 5338467 * 2
def baseEnd_5338467 : Nat := 304577725462874439667927

theorem tailTrace_5338467 : CollatzResearch.WordTrace tailWord_5338467 prefixEnd_5338467 304577725462874439667927 := by
  unfold tailWord_5338467
  simp only [CollatzResearch.WordTrace]
  refine ⟨194709887550653271421573655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129806591700435514281049103 194709887550653271421573655)
  ·
    refine ⟨292064831325979907132360483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194709887550653271421573655 292064831325979907132360483)
    ·
      refine ⟨438097246988969860698540725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292064831325979907132360483 438097246988969860698540725)
      ·
        refine ⟨41071616905215924440488193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 438097246988969860698540725 41071616905215924440488193)
        ·
          refine ⟨30803712678911943330366145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41071616905215924440488193 30803712678911943330366145)
          ·
            refine ⟨23102784509183957497774609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30803712678911943330366145 23102784509183957497774609)
            ·
              refine ⟨17327088381887968123330957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23102784509183957497774609 17327088381887968123330957)
              ·
                refine ⟨6497658143207988046249109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17327088381887968123330957 6497658143207988046249109)
                ·
                  refine ⟨304577725462874439667927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6497658143207988046249109 304577725462874439667927)
                  ·
                    rfl

theorem cell23_5338467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 6].length) (baseStart_5338467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338467 prefixEnd_5338467 := by exact prefixLift 5338467
  have htrace : WordTrace (prefixWord ++ tailWord_5338467) baseStart_5338467 baseEnd_5338467 := by
    simpa [prefixWord, tailWord_5338467, baseEnd_5338467] using wordTrace_append hprefix tailTrace_5338467
  have hstable : (prefixWord ++ tailWord_5338467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338467).length < 2 ^ (prefixWord ++ tailWord_5338467).sum := by decide
  have hdescent : baseEnd_5338467 < baseStart_5338467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338478 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5338478 : Nat := 118140960795 + 5338478 * 2 ^ 59
def prefixEnd_5338478 : Nat := 4983230072969 + 3 ^ 40 * 5338478 * 2
def baseEnd_5338478 : Nat := 2741205177453069413973793

theorem tailTrace_5338478 : CollatzResearch.WordTrace tailWord_5338478 prefixEnd_5338478 2741205177453069413973793 := by
  unfold tailWord_5338478
  simp only [CollatzResearch.WordTrace]
  refine ⟨24338786094201677537528011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129806859169075613533482725 24338786094201677537528011)
  ·
    refine ⟨36508179141302516306292017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24338786094201677537528011 36508179141302516306292017)
    ·
      refine ⟨27381134355976887229719013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36508179141302516306292017 27381134355976887229719013)
      ·
        refine ⟨5133962691745666355572315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27381134355976887229719013 5133962691745666355572315)
        ·
          refine ⟨7700944037618499533358473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5133962691745666355572315 7700944037618499533358473)
          ·
            refine ⟨5775708028213874650018855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7700944037618499533358473 5775708028213874650018855)
            ·
              refine ⟨8663562042320811975028283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5775708028213874650018855 8663562042320811975028283)
              ·
                refine ⟨12995343063481217962542425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8663562042320811975028283 12995343063481217962542425)
                ·
                  refine ⟨9746507297610913471906819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12995343063481217962542425 9746507297610913471906819)
                  ·
                    refine ⟨14619760946416370207860229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9746507297610913471906819 14619760946416370207860229)
                    ·
                      refine ⟨2741205177453069413973793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14619760946416370207860229 2741205177453069413973793)
                      ·
                        rfl

theorem cell23_5338478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5338478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338478 prefixEnd_5338478 := by exact prefixLift 5338478
  have htrace : WordTrace (prefixWord ++ tailWord_5338478) baseStart_5338478 baseEnd_5338478 := by
    simpa [prefixWord, tailWord_5338478, baseEnd_5338478] using wordTrace_append hprefix tailTrace_5338478
  have hstable : (prefixWord ++ tailWord_5338478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338478).length < 2 ^ (prefixWord ++ tailWord_5338478).sum := by decide
  have hdescent : baseEnd_5338478 < baseStart_5338478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338490 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_5338490 : Nat := 118140960795 + 5338490 * 2 ^ 59
def prefixEnd_5338490 : Nat := 4983230072969 + 3 ^ 40 * 5338490 * 2
def baseEnd_5338490 : Nat := 2741211339220923367023737

theorem tailTrace_5338490 : CollatzResearch.WordTrace tailWord_5338490 prefixEnd_5338490 2741211339220923367023737 := by
  unfold tailWord_5338490
  simp only [CollatzResearch.WordTrace]
  refine ⟨48677681607392486587415231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129807150953046630899773949 48677681607392486587415231)
  ·
    refine ⟨73016522411088729881122847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48677681607392486587415231 73016522411088729881122847)
    ·
      refine ⟨109524783616633094821684271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73016522411088729881122847 109524783616633094821684271)
      ·
        refine ⟨164287175424949642232526407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109524783616633094821684271 164287175424949642232526407)
        ·
          refine ⟨246430763137424463348789611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164287175424949642232526407 246430763137424463348789611)
          ·
            refine ⟨369646144706136695023184417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246430763137424463348789611 369646144706136695023184417)
            ·
              refine ⟨277234608529602521267388313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369646144706136695023184417 277234608529602521267388313)
              ·
                refine ⟨207925956397201890950541235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277234608529602521267388313 207925956397201890950541235)
                ·
                  refine ⟨311888934595802836425811853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207925956397201890950541235 311888934595802836425811853)
                  ·
                    refine ⟨116958350473426063659679445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311888934595802836425811853 116958350473426063659679445)
                    ·
                      refine ⟨2741211339220923367023737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116958350473426063659679445 2741211339220923367023737)
                      ·
                        rfl

theorem cell23_5338490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_5338490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338490 prefixEnd_5338490 := by exact prefixLift 5338490
  have htrace : WordTrace (prefixWord ++ tailWord_5338490) baseStart_5338490 baseEnd_5338490 := by
    simpa [prefixWord, tailWord_5338490, baseEnd_5338490] using wordTrace_append hprefix tailTrace_5338490
  have hstable : (prefixWord ++ tailWord_5338490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338490).length < 2 ^ (prefixWord ++ tailWord_5338490).sum := by decide
  have hdescent : baseEnd_5338490 < baseStart_5338490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338517 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_5338517 : Nat := 118140960795 + 5338517 * 2 ^ 59
def prefixEnd_5338517 : Nat := 4983230072969 + 3 ^ 40 * 5338517 * 2
def baseEnd_5338517 : Nat := 2741225203198594761386113

theorem tailTrace_5338517 : CollatzResearch.WordTrace tailWord_5338517 prefixEnd_5338517 2741225203198594761386113 := by
  unfold tailWord_5338517
  simp only [CollatzResearch.WordTrace]
  refine ⟨194711711200472129960893805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129807807466981419973929203 194711711200472129960893805)
  ·
    refine ⟨73016891700177048735335177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194711711200472129960893805 73016891700177048735335177)
    ·
      refine ⟨54762668775132786551501383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73016891700177048735335177 54762668775132786551501383)
      ·
        refine ⟨82144003162699179827252075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54762668775132786551501383 82144003162699179827252075)
        ·
          refine ⟨123216004744048769740878113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82144003162699179827252075 123216004744048769740878113)
          ·
            refine ⟨92412003558036577305658585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123216004744048769740878113 92412003558036577305658585)
            ·
              refine ⟨69309002668527432979243939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92412003558036577305658585 69309002668527432979243939)
              ·
                refine ⟨103963504002791149468865909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69309002668527432979243939 103963504002791149468865909)
                ·
                  refine ⟨9746578500261670262706179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103963504002791149468865909 9746578500261670262706179)
                  ·
                    refine ⟨14619867750392505394059269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9746578500261670262706179 14619867750392505394059269)
                    ·
                      refine ⟨2741225203198594761386113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14619867750392505394059269 2741225203198594761386113)
                      ·
                        rfl

theorem cell23_5338517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_5338517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338517 prefixEnd_5338517 := by exact prefixLift 5338517
  have htrace : WordTrace (prefixWord ++ tailWord_5338517) baseStart_5338517 baseEnd_5338517 := by
    simpa [prefixWord, tailWord_5338517, baseEnd_5338517] using wordTrace_append hprefix tailTrace_5338517
  have hstable : (prefixWord ++ tailWord_5338517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338517).length < 2 ^ (prefixWord ++ tailWord_5338517).sum := by decide
  have hdescent : baseEnd_5338517 < baseStart_5338517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338547 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4]
def baseStart_5338547 : Nat := 118140960795 + 5338547 * 2 ^ 59
def prefixEnd_5338547 : Nat := 4983230072969 + 3 ^ 40 * 5338547 * 2
def baseEnd_5338547 : Nat := 2741240607618229644010975

theorem tailTrace_5338547 : CollatzResearch.WordTrace tailWord_5338547 prefixEnd_5338547 2741240607618229644010975 := by
  unfold tailWord_5338547
  simp only [CollatzResearch.WordTrace]
  refine ⟨194712805390363445084485895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129808536926908963389657263 194712805390363445084485895)
  ·
    refine ⟨292069208085545167626728843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194712805390363445084485895 292069208085545167626728843)
    ·
      refine ⟨438103812128317751440093265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292069208085545167626728843 438103812128317751440093265)
      ·
        refine ⟨328577859096238313580069949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438103812128317751440093265 328577859096238313580069949)
        ·
          refine ⟨123216697161089367592526231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328577859096238313580069949 123216697161089367592526231)
          ·
            refine ⟨184825045741634051388789347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123216697161089367592526231 184825045741634051388789347)
            ·
              refine ⟨277237568612451077083184021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184825045741634051388789347 277237568612451077083184021)
              ·
                refine ⟨12995511028708644238274251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 277237568612451077083184021 12995511028708644238274251)
                ·
                  refine ⟨19493266543062966357411377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12995511028708644238274251 19493266543062966357411377)
                  ·
                    refine ⟨14619949907297224768058533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19493266543062966357411377 14619949907297224768058533)
                    ·
                      refine ⟨2741240607618229644010975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14619949907297224768058533 2741240607618229644010975)
                      ·
                        rfl

theorem cell23_5338547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_5338547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338547 prefixEnd_5338547 := by exact prefixLift 5338547
  have htrace : WordTrace (prefixWord ++ tailWord_5338547) baseStart_5338547 baseEnd_5338547 := by
    simpa [prefixWord, tailWord_5338547, baseEnd_5338547] using wordTrace_append hprefix tailTrace_5338547
  have hstable : (prefixWord ++ tailWord_5338547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338547).length < 2 ^ (prefixWord ++ tailWord_5338547).sum := by decide
  have hdescent : baseEnd_5338547 < baseStart_5338547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338564 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5338564 : Nat := 118140960795 + 5338564 * 2 ^ 59
def prefixEnd_5338564 : Nat := 4983230072969 + 3 ^ 40 * 5338564 * 2
def baseEnd_5338564 : Nat := 2741249336789356077498397

theorem tailTrace_5338564 : CollatzResearch.WordTrace tailWord_5338564 prefixEnd_5338564 2741249336789356077498397 := by
  unfold tailWord_5338564
  simp only [CollatzResearch.WordTrace]
  refine ⟨97356712715650928493927373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129808950287534571325236497 97356712715650928493927373)
  ·
    refine ⟨36508767268369098185222765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97356712715650928493927373 36508767268369098185222765)
    ·
      refine ⟨13690787725638411819458537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36508767268369098185222765 13690787725638411819458537)
      ·
        refine ⟨10268090794228808864593903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13690787725638411819458537 10268090794228808864593903)
        ·
          refine ⟨15402136191343213296890855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10268090794228808864593903 15402136191343213296890855)
          ·
            refine ⟨23103204287014819945336283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15402136191343213296890855 23103204287014819945336283)
            ·
              refine ⟨34654806430522229918004425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23103204287014819945336283 34654806430522229918004425)
              ·
                refine ⟨25991104822891672438503319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34654806430522229918004425 25991104822891672438503319)
                ·
                  refine ⟨38986657234337508657754979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25991104822891672438503319 38986657234337508657754979)
                  ·
                    refine ⟨58479985851506262986632469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38986657234337508657754979 58479985851506262986632469)
                    ·
                      refine ⟨2741249336789356077498397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58479985851506262986632469 2741249336789356077498397)
                      ·
                        rfl

theorem cell23_5338564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5338564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338564 prefixEnd_5338564 := by exact prefixLift 5338564
  have htrace : WordTrace (prefixWord ++ tailWord_5338564) baseStart_5338564 baseEnd_5338564 := by
    simpa [prefixWord, tailWord_5338564, baseEnd_5338564] using wordTrace_append hprefix tailTrace_5338564
  have hstable : (prefixWord ++ tailWord_5338564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338564).length < 2 ^ (prefixWord ++ tailWord_5338564).sum := by decide
  have hdescent : baseEnd_5338564 < baseStart_5338564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338605 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5338605 : Nat := 118140960795 + 5338605 * 2 ^ 59
def prefixEnd_5338605 : Nat := 4983230072969 + 3 ^ 40 * 5338605 * 2
def baseEnd_5338605 : Nat := 2741270389496190417085709

theorem tailTrace_5338605 : CollatzResearch.WordTrace tailWord_5338605 prefixEnd_5338605 2741270389496190417085709 := by
  unfold tailWord_5338605
  simp only [CollatzResearch.WordTrace]
  refine ⟨194714920824153320990097269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129809947216102213993398179 194714920824153320990097269)
  ·
    refine ⟨18254523827264373842821619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194714920824153320990097269 18254523827264373842821619)
    ·
      refine ⟨27381785740896560764232429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18254523827264373842821619 27381785740896560764232429)
      ·
        refine ⟨10268169652836210286587161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27381785740896560764232429 10268169652836210286587161)
        ·
          refine ⟨7701127239627157714940371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10268169652836210286587161 7701127239627157714940371)
          ·
            refine ⟨11551690859440736572410557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7701127239627157714940371 11551690859440736572410557)
            ·
              refine ⟨4331884072290276214653959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11551690859440736572410557 4331884072290276214653959)
              ·
                refine ⟨6497826108435414321980939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4331884072290276214653959 6497826108435414321980939)
                ·
                  refine ⟨9746739162653121482971409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6497826108435414321980939 9746739162653121482971409)
                  ·
                    refine ⟨7310054371989841112228557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9746739162653121482971409 7310054371989841112228557)
                    ·
                      refine ⟨2741270389496190417085709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7310054371989841112228557 2741270389496190417085709)
                      ·
                        rfl

theorem cell23_5338605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5338605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338605 prefixEnd_5338605 := by exact prefixLift 5338605
  have htrace : WordTrace (prefixWord ++ tailWord_5338605) baseStart_5338605 baseEnd_5338605 := by
    simpa [prefixWord, tailWord_5338605, baseEnd_5338605] using wordTrace_append hprefix tailTrace_5338605
  have hstable : (prefixWord ++ tailWord_5338605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338605).length < 2 ^ (prefixWord ++ tailWord_5338605).sum := by decide
  have hdescent : baseEnd_5338605 < baseStart_5338605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338617 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_5338617 : Nat := 118140960795 + 5338617 * 2 ^ 59
def prefixEnd_5338617 : Nat := 4983230072969 + 3 ^ 40 * 5338617 * 2
def baseEnd_5338617 : Nat := 913758850421348123378551

theorem tailTrace_5338617 : CollatzResearch.WordTrace tailWord_5338617 prefixEnd_5338617 913758850421348123378551 := by
  unfold tailWord_5338617
  simp only [CollatzResearch.WordTrace]
  refine ⟨194715358500109847039534105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129810239000073231359689403 194715358500109847039534105)
  ·
    refine ⟨146036518875082385279650579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194715358500109847039534105 146036518875082385279650579)
    ·
      refine ⟨219054778312623577919475869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146036518875082385279650579 219054778312623577919475869)
      ·
        refine ⟨82145541867233841719803451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219054778312623577919475869 82145541867233841719803451)
        ·
          refine ⟨123218312800850762579705177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82145541867233841719803451 123218312800850762579705177)
          ·
            refine ⟨92413734600638071934778883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123218312800850762579705177 92413734600638071934778883)
            ·
              refine ⟨138620601900957107902168325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92413734600638071934778883 138620601900957107902168325)
              ·
                refine ⟨25991362856429457731656561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138620601900957107902168325 25991362856429457731656561)
                ·
                  refine ⟨19493522142322093298742421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25991362856429457731656561 19493522142322093298742421)
                  ·
                    refine ⟨913758850421348123378551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19493522142322093298742421 913758850421348123378551)
                    ·
                      rfl

theorem cell23_5338617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_5338617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338617 prefixEnd_5338617 := by exact prefixLift 5338617
  have htrace : WordTrace (prefixWord ++ tailWord_5338617) baseStart_5338617 baseEnd_5338617 := by
    simpa [prefixWord, tailWord_5338617, baseEnd_5338617] using wordTrace_append hprefix tailTrace_5338617
  have hstable : (prefixWord ++ tailWord_5338617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338617).length < 2 ^ (prefixWord ++ tailWord_5338617).sum := by decide
  have hdescent : baseEnd_5338617 < baseStart_5338617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338627 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5]
def baseStart_5338627 : Nat := 118140960795 + 5338627 * 2 ^ 59
def prefixEnd_5338627 : Nat := 4983230072969 + 3 ^ 40 * 5338627 * 2
def baseEnd_5338627 : Nat := 2741281686070589331010607

theorem tailTrace_5338627 : CollatzResearch.WordTrace tailWord_5338627 prefixEnd_5338627 2741281686070589331010607 := by
  unfold tailWord_5338627
  simp only [CollatzResearch.WordTrace]
  refine ⟨194715723230073618747398135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129810482153382412498265423 194715723230073618747398135)
  ·
    refine ⟨292073584845110428121097203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194715723230073618747398135 292073584845110428121097203)
    ·
      refine ⟨438110377267665642181645805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292073584845110428121097203 438110377267665642181645805)
      ·
        refine ⟨164291391475374615818117177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438110377267665642181645805 164291391475374615818117177)
        ·
          refine ⟨123218543606530961863587883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164291391475374615818117177 123218543606530961863587883)
          ·
            refine ⟨184827815409796442795381825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123218543606530961863587883 184827815409796442795381825)
            ·
              refine ⟨138620861557347332096536369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184827815409796442795381825 138620861557347332096536369)
              ·
                refine ⟨103965646168010499072402277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138620861557347332096536369 103965646168010499072402277)
                ·
                  refine ⟨19493558656501968576075427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103965646168010499072402277 19493558656501968576075427)
                  ·
                    refine ⟨29240337984752952864113141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19493558656501968576075427 29240337984752952864113141)
                    ·
                      refine ⟨2741281686070589331010607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29240337984752952864113141 2741281686070589331010607)
                      ·
                        rfl

theorem cell23_5338627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_5338627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338627 prefixEnd_5338627 := by exact prefixLift 5338627
  have htrace : WordTrace (prefixWord ++ tailWord_5338627) baseStart_5338627 baseEnd_5338627 := by
    simpa [prefixWord, tailWord_5338627, baseEnd_5338627] using wordTrace_append hprefix tailTrace_5338627
  have hstable : (prefixWord ++ tailWord_5338627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338627).length < 2 ^ (prefixWord ++ tailWord_5338627).sum := by decide
  have hdescent : baseEnd_5338627 < baseStart_5338627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338634 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_5338634 : Nat := 118140960795 + 5338634 * 2 ^ 59
def prefixEnd_5338634 : Nat := 4983230072969 + 3 ^ 40 * 5338634 * 2
def baseEnd_5338634 : Nat := 913761760145056934541025

theorem tailTrace_5338634 : CollatzResearch.WordTrace tailWord_5338634 prefixEnd_5338634 913761760145056934541025 := by
  unfold tailWord_5338634
  simp only [CollatzResearch.WordTrace]
  refine ⟨48678994635262064735725739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129810652360698839295268637 48678994635262064735725739)
  ·
    refine ⟨73018491952893097103588609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48678994635262064735725739 73018491952893097103588609)
    ·
      refine ⟨54763868964669822827691457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73018491952893097103588609 54763868964669822827691457)
      ·
        refine ⟨41072901723502367120768593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54763868964669822827691457 41072901723502367120768593)
        ·
          refine ⟨30804676292626775340576445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41072901723502367120768593 30804676292626775340576445)
          ·
            refine ⟨11551753609735040752716167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30804676292626775340576445 11551753609735040752716167)
            ·
              refine ⟨17327630414602561129074251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11551753609735040752716167 17327630414602561129074251)
              ·
                refine ⟨25991445621903841693611377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17327630414602561129074251 25991445621903841693611377)
                ·
                  refine ⟨19493584216427881270208533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25991445621903841693611377 19493584216427881270208533)
                  ·
                    refine ⟨913761760145056934541025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19493584216427881270208533 913761760145056934541025)
                    ·
                      rfl

theorem cell23_5338634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_5338634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338634 prefixEnd_5338634 := by exact prefixLift 5338634
  have htrace : WordTrace (prefixWord ++ tailWord_5338634) baseStart_5338634 baseEnd_5338634 := by
    simpa [prefixWord, tailWord_5338634, baseEnd_5338634] using wordTrace_append hprefix tailTrace_5338634
  have hstable : (prefixWord ++ tailWord_5338634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338634).length < 2 ^ (prefixWord ++ tailWord_5338634).sum := by decide
  have hdescent : baseEnd_5338634 < baseStart_5338634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338641 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 1, 4, 2]
def baseStart_5338641 : Nat := 118140960795 + 5338641 * 2 ^ 59
def prefixEnd_5338641 : Nat := 4983230072969 + 3 ^ 40 * 5338641 * 2
def baseEnd_5338641 : Nat := 2741288874799752276235543

theorem tailTrace_5338641 : CollatzResearch.WordTrace tailWord_5338641 prefixEnd_5338641 2741288874799752276235543 := by
  unfold tailWord_5338641
  simp only [CollatzResearch.WordTrace]
  refine ⟨194716233852022899138407777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129810822568015266092271851 194716233852022899138407777)
  ·
    refine ⟨146037175389017174353805833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194716233852022899138407777 146037175389017174353805833)
    ·
      refine ⟨109527881541762880765354375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146037175389017174353805833 109527881541762880765354375)
      ·
        refine ⟨164291822312644321148031563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109527881541762880765354375 164291822312644321148031563)
        ·
          refine ⟨246437733468966481722047345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164291822312644321148031563 246437733468966481722047345)
          ·
            refine ⟨184828300101724861291535509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246437733468966481722047345 184828300101724861291535509)
            ·
              refine ⟨8663826567268352873040727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184828300101724861291535509 8663826567268352873040727)
              ·
                refine ⟨12995739850902529309561091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8663826567268352873040727 12995739850902529309561091)
                ·
                  refine ⟨19493609776353793964341637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12995739850902529309561091 19493609776353793964341637)
                  ·
                    refine ⟨3655051833066336368314057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19493609776353793964341637 3655051833066336368314057)
                    ·
                      refine ⟨2741288874799752276235543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655051833066336368314057 2741288874799752276235543)
                      ·
                        rfl

theorem cell23_5338641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_5338641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338641 prefixEnd_5338641 := by exact prefixLift 5338641
  have htrace : WordTrace (prefixWord ++ tailWord_5338641) baseStart_5338641 baseEnd_5338641 := by
    simpa [prefixWord, tailWord_5338641, baseEnd_5338641] using wordTrace_append hprefix tailTrace_5338641
  have hstable : (prefixWord ++ tailWord_5338641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338641).length < 2 ^ (prefixWord ++ tailWord_5338641).sum := by decide
  have hdescent : baseEnd_5338641 < baseStart_5338641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338675 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 2, 2, 2]
def baseStart_5338675 : Nat := 118140960795 + 5338675 * 2 ^ 59
def prefixEnd_5338675 : Nat := 4983230072969 + 3 ^ 40 * 5338675 * 2
def baseEnd_5338675 : Nat := 2741306333142005143210387

theorem tailTrace_5338675 : CollatzResearch.WordTrace tailWord_5338675 prefixEnd_5338675 2741306333142005143210387 := by
  unfold tailWord_5338675
  simp only [CollatzResearch.WordTrace]
  refine ⟨194717473933899722945145479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129811649289266481963430319 194717473933899722945145479)
  ·
    refine ⟨292076210900849584417718219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194717473933899722945145479 292076210900849584417718219)
    ·
      refine ⟨438114316351274376626577329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292076210900849584417718219 438114316351274376626577329)
      ·
        refine ⟨328585737263455782469932997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438114316351274376626577329 328585737263455782469932997)
        ·
          refine ⟨61609825736897959213112437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328585737263455782469932997 61609825736897959213112437)
          ·
            refine ⟨5775921162834183676229291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61609825736897959213112437 5775921162834183676229291)
            ·
              refine ⟨8663881744251275514343937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5775921162834183676229291 8663881744251275514343937)
              ·
                refine ⟨6497911308188456635757953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8663881744251275514343937 6497911308188456635757953)
                ·
                  refine ⟨4873433481141342476818465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6497911308188456635757953 4873433481141342476818465)
                  ·
                    refine ⟨3655075110856006857613849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4873433481141342476818465 3655075110856006857613849)
                    ·
                      refine ⟨2741306333142005143210387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655075110856006857613849 2741306333142005143210387)
                      ·
                        rfl

theorem cell23_5338675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 2, 2].length) (baseStart_5338675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338675 prefixEnd_5338675 := by exact prefixLift 5338675
  have htrace : WordTrace (prefixWord ++ tailWord_5338675) baseStart_5338675 baseEnd_5338675 := by
    simpa [prefixWord, tailWord_5338675, baseEnd_5338675] using wordTrace_append hprefix tailTrace_5338675
  have hstable : (prefixWord ++ tailWord_5338675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338675).length < 2 ^ (prefixWord ++ tailWord_5338675).sum := by decide
  have hdescent : baseEnd_5338675 < baseStart_5338675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338681 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 5]
def baseStart_5338681 : Nat := 118140960795 + 5338681 * 2 ^ 59
def prefixEnd_5338681 : Nat := 4983230072969 + 3 ^ 40 * 5338681 * 2
def baseEnd_5338681 : Nat := 304589934891770235526151

theorem tailTrace_5338681 : CollatzResearch.WordTrace tailWord_5338681 prefixEnd_5338681 304589934891770235526151 := by
  unfold tailWord_5338681
  simp only [CollatzResearch.WordTrace]
  refine ⟨194717692771877985969863897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129811795181251990646575931 194717692771877985969863897)
  ·
    refine ⟨146038269578908489477397923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194717692771877985969863897 146038269578908489477397923)
    ·
      refine ⟨219057404368362734216096885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146038269578908489477397923 219057404368362734216096885)
      ·
        refine ⟨20536631659534006332759083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219057404368362734216096885 20536631659534006332759083)
        ·
          refine ⟨30804947489301009499138625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20536631659534006332759083 30804947489301009499138625)
          ·
            refine ⟨23103710616975757124353969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30804947489301009499138625 23103710616975757124353969)
            ·
              refine ⟨17327782962731817843265477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23103710616975757124353969 17327782962731817843265477)
              ·
                refine ⟨3248959305512215845612277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17327782962731817843265477 3248959305512215845612277)
                ·
                  refine ⟨304589934891770235526151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248959305512215845612277 304589934891770235526151)
                  ·
                    rfl

theorem cell23_5338681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 5].length) (baseStart_5338681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338681 prefixEnd_5338681 := by exact prefixLift 5338681
  have htrace : WordTrace (prefixWord ++ tailWord_5338681) baseStart_5338681 baseEnd_5338681 := by
    simpa [prefixWord, tailWord_5338681, baseEnd_5338681] using wordTrace_append hprefix tailTrace_5338681
  have hstable : (prefixWord ++ tailWord_5338681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338681).length < 2 ^ (prefixWord ++ tailWord_5338681).sum := by decide
  have hdescent : baseEnd_5338681 < baseStart_5338681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338714 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5338714 : Nat := 118140960795 + 5338714 * 2 ^ 59
def prefixEnd_5338714 : Nat := 4983230072969 + 3 ^ 40 * 5338714 * 2
def baseEnd_5338714 : Nat := 2741326358887530490622707

theorem tailTrace_5338714 : CollatzResearch.WordTrace tailWord_5338714 prefixEnd_5338714 2741326358887530490622707 := by
  unfold tailWord_5338714
  simp only [CollatzResearch.WordTrace]
  refine ⟨48679724095189608151453799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129812597587172288403876797 48679724095189608151453799)
  ·
    refine ⟨73019586142784412227180699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48679724095189608151453799 73019586142784412227180699)
    ·
      refine ⟨109529379214176618340771049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73019586142784412227180699 109529379214176618340771049)
      ·
        refine ⟨82147034410632463755578287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109529379214176618340771049 82147034410632463755578287)
        ·
          refine ⟨123220551615948695633367431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82147034410632463755578287 123220551615948695633367431)
          ·
            refine ⟨184830827423923043450051147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123220551615948695633367431 184830827423923043450051147)
            ·
              refine ⟨277246241135884565175076721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184830827423923043450051147 277246241135884565175076721)
              ·
                refine ⟨207934680851913423881307541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277246241135884565175076721 207934680851913423881307541)
                ·
                  refine ⟨9746938164933441744436291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207934680851913423881307541 9746938164933441744436291)
                  ·
                    refine ⟨14620407247400162616654437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9746938164933441744436291 14620407247400162616654437)
                    ·
                      refine ⟨2741326358887530490622707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14620407247400162616654437 2741326358887530490622707)
                      ·
                        rfl

theorem cell23_5338714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5338714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338714 prefixEnd_5338714 := by exact prefixLift 5338714
  have htrace : WordTrace (prefixWord ++ tailWord_5338714) baseStart_5338714 baseEnd_5338714 := by
    simpa [prefixWord, tailWord_5338714, baseEnd_5338714] using wordTrace_append hprefix tailTrace_5338714
  have hstable : (prefixWord ++ tailWord_5338714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338714).length < 2 ^ (prefixWord ++ tailWord_5338714).sum := by decide
  have hdescent : baseEnd_5338714 < baseStart_5338714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338821 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 6, 2]
def baseStart_5338821 : Nat := 118140960795 + 5338821 * 2 ^ 59
def prefixEnd_5338821 : Nat := 4983230072969 + 3 ^ 40 * 5338821 * 2
def baseEnd_5338821 : Nat := 2741381301317561571984715

theorem tailTrace_5338821 : CollatzResearch.WordTrace tailWord_5338821 prefixEnd_5338821 2741381301317561571984715 := by
  unfold tailWord_5338821
  simp only [CollatzResearch.WordTrace]
  refine ⟨194722798991370789879960317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129815199327580526586640211 194722798991370789879960317)
  ·
    refine ⟨73021049621764046204985119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194722798991370789879960317 73021049621764046204985119)
    ·
      refine ⟨109531574432646069307477679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73021049621764046204985119 109531574432646069307477679)
      ·
        refine ⟨164297361648969103961216519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109531574432646069307477679 164297361648969103961216519)
        ·
          refine ⟨246446042473453655941824779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164297361648969103961216519 246446042473453655941824779)
          ·
            refine ⟨369669063710180483912737169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246446042473453655941824779 369669063710180483912737169)
            ·
              refine ⟨277251797782635362934552877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369669063710180483912737169 277251797782635362934552877)
              ·
                refine ⟨103969424168488261100457329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277251797782635362934552877 103969424168488261100457329)
                ·
                  refine ⟨77977068126366195825342997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103969424168488261100457329 77977068126366195825342997)
                  ·
                    refine ⟨3655175068423415429312953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77977068126366195825342997 3655175068423415429312953)
                    ·
                      refine ⟨2741381301317561571984715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655175068423415429312953 2741381301317561571984715)
                      ·
                        rfl

theorem cell23_5338821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_5338821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338821 prefixEnd_5338821 := by exact prefixLift 5338821
  have htrace : WordTrace (prefixWord ++ tailWord_5338821) baseStart_5338821 baseEnd_5338821 := by
    simpa [prefixWord, tailWord_5338821, baseEnd_5338821] using wordTrace_append hprefix tailTrace_5338821
  have hstable : (prefixWord ++ tailWord_5338821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338821).length < 2 ^ (prefixWord ++ tailWord_5338821).sum := by decide
  have hdescent : baseEnd_5338821 < baseStart_5338821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338848 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 2, 4]
def baseStart_5338848 : Nat := 118140960795 + 5338848 * 2 ^ 59
def prefixEnd_5338848 : Nat := 4983230072969 + 3 ^ 40 * 5338848 * 2
def baseEnd_5338848 : Nat := 913798388431744322115697

theorem tailTrace_5338848 : CollatzResearch.WordTrace tailWord_5338848 prefixEnd_5338848 913798388431744322115697 := by
  unfold tailWord_5338848
  simp only [CollatzResearch.WordTrace]
  refine ⟨97361891881136486745596599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129815855841515315660795465 97361891881136486745596599)
  ·
    refine ⟨146042837821704730118394899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97361891881136486745596599 146042837821704730118394899)
    ·
      refine ⟨219064256732557095177592349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146042837821704730118394899 219064256732557095177592349)
      ·
        refine ⟨82149096274708910691597131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219064256732557095177592349 82149096274708910691597131)
        ·
          refine ⟨123223644412063366037395697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82149096274708910691597131 123223644412063366037395697)
          ·
            refine ⟨92417733309047524528046773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123223644412063366037395697 92417733309047524528046773)
            ·
              refine ⟨8664162497723205424504385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92417733309047524528046773 8664162497723205424504385)
              ·
                refine ⟨6498121873292404068378289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8664162497723205424504385 6498121873292404068378289)
                ·
                  refine ⟨4873591404969303051283717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498121873292404068378289 4873591404969303051283717)
                  ·
                    refine ⟨913798388431744322115697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4873591404969303051283717 913798388431744322115697)
                    ·
                      rfl

theorem cell23_5338848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_5338848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338848 prefixEnd_5338848 := by exact prefixLift 5338848
  have htrace : WordTrace (prefixWord ++ tailWord_5338848) baseStart_5338848 baseEnd_5338848 := by
    simpa [prefixWord, tailWord_5338848, baseEnd_5338848] using wordTrace_append hprefix tailTrace_5338848
  have hstable : (prefixWord ++ tailWord_5338848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338848).length < 2 ^ (prefixWord ++ tailWord_5338848).sum := by decide
  have hdescent : baseEnd_5338848 < baseStart_5338848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338864 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_5338864 : Nat := 118140960795 + 5338864 * 2 ^ 59
def prefixEnd_5338864 : Nat := 4983230072969 + 3 ^ 40 * 5338864 * 2
def baseEnd_5338864 : Nat := 2741403380985704903747017

theorem tailTrace_5338864 : CollatzResearch.WordTrace tailWord_5338864 prefixEnd_5338864 2741403380985704903747017 := by
  unfold tailWord_5338864
  simp only [CollatzResearch.WordTrace]
  refine ⟨97362183665107504111887823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129816244886810005482517097 97362183665107504111887823)
  ·
    refine ⟨146043275497661256167831735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97362183665107504111887823 146043275497661256167831735)
    ·
      refine ⟨219064913246491884251747603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146043275497661256167831735 219064913246491884251747603)
      ·
        refine ⟨328597369869737826377621405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219064913246491884251747603 328597369869737826377621405)
        ·
          refine ⟨123224013701151684891608027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328597369869737826377621405 123224013701151684891608027)
          ·
            refine ⟨184836020551727527337412041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123224013701151684891608027 184836020551727527337412041)
            ·
              refine ⟨138627015413795645503059031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184836020551727527337412041 138627015413795645503059031)
              ·
                refine ⟨207940523120693468254588547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138627015413795645503059031 207940523120693468254588547)
                ·
                  refine ⟨311910784681040202381882821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207940523120693468254588547 311910784681040202381882821)
                  ·
                    refine ⟨58483272127695037946603029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311910784681040202381882821 58483272127695037946603029)
                    ·
                      refine ⟨2741403380985704903747017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58483272127695037946603029 2741403380985704903747017)
                      ·
                        rfl

theorem cell23_5338864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_5338864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338864 prefixEnd_5338864 := by exact prefixLift 5338864
  have htrace : WordTrace (prefixWord ++ tailWord_5338864) baseStart_5338864 baseEnd_5338864 := by
    simpa [prefixWord, tailWord_5338864, baseEnd_5338864] using wordTrace_append hprefix tailTrace_5338864
  have hstable : (prefixWord ++ tailWord_5338864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338864).length < 2 ^ (prefixWord ++ tailWord_5338864).sum := by decide
  have hdescent : baseEnd_5338864 < baseStart_5338864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338865 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 2, 4]
def baseStart_5338865 : Nat := 118140960795 + 5338865 * 2 ^ 59
def prefixEnd_5338865 : Nat := 4983230072969 + 3 ^ 40 * 5338865 * 2
def baseEnd_5338865 : Nat := 913801298155453133278171

theorem tailTrace_5338865 : CollatzResearch.WordTrace tailWord_5338865 prefixEnd_5338865 913801298155453133278171 := by
  unfold tailWord_5338865
  simp only [CollatzResearch.WordTrace]
  refine ⟨194724403803211385394562049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129816269202140923596374699 194724403803211385394562049)
  ·
    refine ⟨146043302852408539045921537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194724403803211385394562049 146043302852408539045921537)
    ·
      refine ⟨109532477139306404284441153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146043302852408539045921537 109532477139306404284441153)
      ·
        refine ⟨82149357854479803213330865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109532477139306404284441153 82149357854479803213330865)
        ·
          refine ⟨61612018390859852409998149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82149357854479803213330865 61612018390859852409998149)
          ·
            refine ⟨11552253448286222326874653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61612018390859852409998149 11552253448286222326874653)
            ·
              refine ⟨4332095043107333372577995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11552253448286222326874653 4332095043107333372577995)
              ·
                refine ⟨6498142564661000058866993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332095043107333372577995 6498142564661000058866993)
                ·
                  refine ⟨4873606923495750044150245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498142564661000058866993 4873606923495750044150245)
                  ·
                    refine ⟨913801298155453133278171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4873606923495750044150245 913801298155453133278171)
                    ·
                      rfl

theorem cell23_5338865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_5338865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338865 prefixEnd_5338865 := by exact prefixLift 5338865
  have htrace : WordTrace (prefixWord ++ tailWord_5338865) baseStart_5338865 baseEnd_5338865 := by
    simpa [prefixWord, tailWord_5338865, baseEnd_5338865] using wordTrace_append hprefix tailTrace_5338865
  have hstable : (prefixWord ++ tailWord_5338865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338865).length < 2 ^ (prefixWord ++ tailWord_5338865).sum := by decide
  have hdescent : baseEnd_5338865 < baseStart_5338865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338878 : List Nat := [4, 2, 2, 1, 3, 1, 1, 9]
def baseStart_5338878 : Nat := 118140960795 + 5338878 * 2 ^ 59
def prefixEnd_5338878 : Nat := 4983230072969 + 3 ^ 40 * 5338878 * 2
def baseEnd_5338878 : Nat := 101533724804254364776739

theorem tailTrace_5338878 : CollatzResearch.WordTrace tailWord_5338878 prefixEnd_5338878 101533724804254364776739 := by
  unfold tailWord_5338878
  simp only [CollatzResearch.WordTrace]
  refine ⟨24340609744020536076848161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129816585301442859076523525 24340609744020536076848161)
  ·
    refine ⟨18255457308015402057636121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24340609744020536076848161 18255457308015402057636121)
    ·
      refine ⟨13691592981011551543227091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18255457308015402057636121 13691592981011551543227091)
      ·
        refine ⟨20537389471517327314840637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13691592981011551543227091 20537389471517327314840637)
        ·
          refine ⟨7701521051818997743065239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20537389471517327314840637 7701521051818997743065239)
          ·
            refine ⟨11552281577728496614597859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7701521051818997743065239 11552281577728496614597859)
            ·
              refine ⟨17328422366592744921896789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11552281577728496614597859 17328422366592744921896789)
              ·
                refine ⟨101533724804254364776739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17328422366592744921896789 101533724804254364776739)
                ·
                  rfl

theorem cell23_5338878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_5338878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338878 prefixEnd_5338878 := by exact prefixLift 5338878
  have htrace : WordTrace (prefixWord ++ tailWord_5338878) baseStart_5338878 baseEnd_5338878 := by
    simpa [prefixWord, tailWord_5338878, baseEnd_5338878] using wordTrace_append hprefix tailTrace_5338878
  have hstable : (prefixWord ++ tailWord_5338878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338878).length < 2 ^ (prefixWord ++ tailWord_5338878).sum := by decide
  have hdescent : baseEnd_5338878 < baseStart_5338878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338888 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_5338888 : Nat := 118140960795 + 5338888 * 2 ^ 59
def prefixEnd_5338888 : Nat := 4983230072969 + 3 ^ 40 * 5338888 * 2
def baseEnd_5338888 : Nat := 2741415704521412809846907

theorem tailTrace_5338888 : CollatzResearch.WordTrace tailWord_5338888 prefixEnd_5338888 2741415704521412809846907 := by
  unfold tailWord_5338888
  simp only [CollatzResearch.WordTrace]
  refine ⟨97362621341064030161324659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129816828454752040215099545 97362621341064030161324659)
  ·
    refine ⟨146043932011596045241986989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97362621341064030161324659 146043932011596045241986989)
    ·
      refine ⟨54766474504348516965745121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146043932011596045241986989 54766474504348516965745121)
      ·
        refine ⟨41074855878261387724308841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54766474504348516965745121 41074855878261387724308841)
        ·
          refine ⟨30806141908696040793231631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41074855878261387724308841 30806141908696040793231631)
          ·
            refine ⟨46209212863044061189847447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30806141908696040793231631 46209212863044061189847447)
            ·
              refine ⟨69313819294566091784771171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46209212863044061189847447 69313819294566091784771171)
              ·
                refine ⟨103970728941849137677156757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69313819294566091784771171 103970728941849137677156757)
                ·
                  refine ⟨4873627919149178328616723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103970728941849137677156757 4873627919149178328616723)
                  ·
                    refine ⟨7310441878723767492925085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4873627919149178328616723 7310441878723767492925085)
                    ·
                      refine ⟨2741415704521412809846907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7310441878723767492925085 2741415704521412809846907)
                      ·
                        rfl

theorem cell23_5338888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_5338888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338888 prefixEnd_5338888 := by exact prefixLift 5338888
  have htrace : WordTrace (prefixWord ++ tailWord_5338888) baseStart_5338888 baseEnd_5338888 := by
    simpa [prefixWord, tailWord_5338888, baseEnd_5338888] using wordTrace_append hprefix tailTrace_5338888
  have hstable : (prefixWord ++ tailWord_5338888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338888).length < 2 ^ (prefixWord ++ tailWord_5338888).sum := by decide
  have hdescent : baseEnd_5338888 < baseStart_5338888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338911 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_5338911 : Nat := 118140960795 + 5338911 * 2 ^ 59
def prefixEnd_5338911 : Nat := 4983230072969 + 3 ^ 40 * 5338911 * 2
def baseEnd_5338911 : Nat := 2741427514576466219859301

theorem tailTrace_5338911 : CollatzResearch.WordTrace tailWord_5338911 prefixEnd_5338911 2741427514576466219859301 := by
  unfold tailWord_5338911
  simp only [CollatzResearch.WordTrace]
  refine ⟨194726081561044735250736587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129817387707363156833824391 194726081561044735250736587)
  ·
    refine ⟨292089122341567102876104881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194726081561044735250736587 292089122341567102876104881)
    ·
      refine ⟨219066841756175327157078661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292089122341567102876104881 219066841756175327157078661)
      ·
        refine ⟨41075032829282873841952249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219066841756175327157078661 41075032829282873841952249)
        ·
          refine ⟨30806274621962155381464187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41075032829282873841952249 30806274621962155381464187)
          ·
            refine ⟨46209411932943233072196281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30806274621962155381464187 46209411932943233072196281)
            ·
              refine ⟨34657058949707424804147211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46209411932943233072196281 34657058949707424804147211)
              ·
                refine ⟨51985588424561137206220817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34657058949707424804147211 51985588424561137206220817)
                ·
                  refine ⟨38989191318420852904665613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51985588424561137206220817 38989191318420852904665613)
                  ·
                    refine ⟨14620946744407819839249605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38989191318420852904665613 14620946744407819839249605)
                    ·
                      refine ⟨2741427514576466219859301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14620946744407819839249605 2741427514576466219859301)
                      ·
                        rfl

theorem cell23_5338911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_5338911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338911 prefixEnd_5338911 := by exact prefixLift 5338911
  have htrace : WordTrace (prefixWord ++ tailWord_5338911) baseStart_5338911 baseEnd_5338911 := by
    simpa [prefixWord, tailWord_5338911, baseEnd_5338911] using wordTrace_append hprefix tailTrace_5338911
  have hstable : (prefixWord ++ tailWord_5338911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338911).length < 2 ^ (prefixWord ++ tailWord_5338911).sum := by decide
  have hdescent : baseEnd_5338911 < baseStart_5338911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338932 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_5338932 : Nat := 118140960795 + 5338932 * 2 ^ 59
def prefixEnd_5338932 : Nat := 4983230072969 + 3 ^ 40 * 5338932 * 2
def baseEnd_5338932 : Nat := 2741438297670210637696705

theorem tailTrace_5338932 : CollatzResearch.WordTrace tailWord_5338932 prefixEnd_5338932 2741438297670210637696705 := by
  unfold tailWord_5338932
  simp only [CollatzResearch.WordTrace]
  refine ⟨97363423746984327918625525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129817898329312437224834033 97363423746984327918625525)
  ·
    refine ⟨9127820976279780742371143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97363423746984327918625525 9127820976279780742371143)
    ·
      refine ⟨13691731464419671113556715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9127820976279780742371143 13691731464419671113556715)
      ·
        refine ⟨20537597196629506670335073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13691731464419671113556715 20537597196629506670335073)
        ·
          refine ⟨15403197897472130002751305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20537597196629506670335073 15403197897472130002751305)
          ·
            refine ⟨11552398423104097502063479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15403197897472130002751305 11552398423104097502063479)
            ·
              refine ⟨17328597634656146253095219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11552398423104097502063479 17328597634656146253095219)
              ·
                refine ⟨25992896451984219379642829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17328597634656146253095219 25992896451984219379642829)
                ·
                  refine ⟨9747336169494082267366061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25992896451984219379642829 9747336169494082267366061)
                  ·
                    refine ⟨3655251063560280850262273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9747336169494082267366061 3655251063560280850262273)
                    ·
                      refine ⟨2741438297670210637696705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655251063560280850262273 2741438297670210637696705)
                      ·
                        rfl

theorem cell23_5338932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_5338932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338932 prefixEnd_5338932 := by exact prefixLift 5338932
  have htrace : WordTrace (prefixWord ++ tailWord_5338932) baseStart_5338932 baseEnd_5338932 := by
    simpa [prefixWord, tailWord_5338932, baseEnd_5338932] using wordTrace_append hprefix tailTrace_5338932
  have hstable : (prefixWord ++ tailWord_5338932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338932).length < 2 ^ (prefixWord ++ tailWord_5338932).sum := by decide
  have hdescent : baseEnd_5338932 < baseStart_5338932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338962 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_5338962 : Nat := 118140960795 + 5338962 * 2 ^ 59
def prefixEnd_5338962 : Nat := 4983230072969 + 3 ^ 40 * 5338962 * 2
def baseEnd_5338962 : Nat := 2741453702089845520321567

theorem tailTrace_5338962 : CollatzResearch.WordTrace tailWord_5338962 prefixEnd_5338962 2741453702089845520321567 := by
  unfold tailWord_5338962
  simp only [CollatzResearch.WordTrace]
  refine ⟨48681985420964992740210785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129818627789239980640562093 48681985420964992740210785)
  ·
    refine ⟨36511489065723744555158089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48681985420964992740210785 36511489065723744555158089)
    ·
      refine ⟨27383616799292808416368567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36511489065723744555158089 27383616799292808416368567)
      ·
        refine ⟨41075425198939212624552851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27383616799292808416368567 41075425198939212624552851)
        ·
          refine ⟨61613137798408818936829277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41075425198939212624552851 61613137798408818936829277)
          ·
            refine ⟨23104926674403307101310979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61613137798408818936829277 23104926674403307101310979)
            ·
              refine ⟨34657390011604960651966469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23104926674403307101310979 34657390011604960651966469)
              ·
                refine ⟨6498260627175930122243713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34657390011604960651966469 6498260627175930122243713)
                ·
                  refine ⟨4873695470381947591682785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498260627175930122243713 4873695470381947591682785)
                  ·
                    refine ⟨3655271602786460693762089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4873695470381947591682785 3655271602786460693762089)
                    ·
                      refine ⟨2741453702089845520321567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655271602786460693762089 2741453702089845520321567)
                      ·
                        rfl

theorem cell23_5338962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_5338962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338962 prefixEnd_5338962 := by exact prefixLift 5338962
  have htrace : WordTrace (prefixWord ++ tailWord_5338962) baseStart_5338962 baseEnd_5338962 := by
    simpa [prefixWord, tailWord_5338962, baseEnd_5338962] using wordTrace_append hprefix tailTrace_5338962
  have hstable : (prefixWord ++ tailWord_5338962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338962).length < 2 ^ (prefixWord ++ tailWord_5338962).sum := by decide
  have hdescent : baseEnd_5338962 < baseStart_5338962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5338981 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_5338981 : Nat := 118140960795 + 5338981 * 2 ^ 59
def prefixEnd_5338981 : Nat := 4983230072969 + 3 ^ 40 * 5338981 * 2
def baseEnd_5338981 : Nat := 913821152740760315327993

theorem tailTrace_5338981 : CollatzResearch.WordTrace tailWord_5338981 prefixEnd_5338981 913821152740760315327993 := by
  unfold tailWord_5338981
  simp only [CollatzResearch.WordTrace]
  refine ⟨194728634670791137205784797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129819089780527424803856531 194728634670791137205784797)
  ·
    refine ⟨73023238001546676452169299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194728634670791137205784797 73023238001546676452169299)
    ·
      refine ⟨109534857002320014678253949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73023238001546676452169299 109534857002320014678253949)
      ·
        refine ⟨41075571375870005504345231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109534857002320014678253949 41075571375870005504345231)
        ·
          refine ⟨61613357063805008256517847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41075571375870005504345231 61613357063805008256517847)
          ·
            refine ⟨92420035595707512384776771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61613357063805008256517847 92420035595707512384776771)
            ·
              refine ⟨138630053393561268577165157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92420035595707512384776771 138630053393561268577165157)
              ·
                refine ⟨25993135011292737858218467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138630053393561268577165157 25993135011292737858218467)
                ·
                  refine ⟨38989702516939106787327701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25993135011292737858218467 38989702516939106787327701)
                  ·
                    refine ⟨913821152740760315327993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38989702516939106787327701 913821152740760315327993)
                    ·
                      rfl

theorem cell23_5338981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_5338981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5338981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5338981 prefixEnd_5338981 := by exact prefixLift 5338981
  have htrace : WordTrace (prefixWord ++ tailWord_5338981) baseStart_5338981 baseEnd_5338981 := by
    simpa [prefixWord, tailWord_5338981, baseEnd_5338981] using wordTrace_append hprefix tailTrace_5338981
  have hstable : (prefixWord ++ tailWord_5338981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5338981).length < 2 ^ (prefixWord ++ tailWord_5338981).sum := by decide
  have hdescent : baseEnd_5338981 < baseStart_5338981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5338981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339030 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5339030 : Nat := 118140960795 + 5339030 * 2 ^ 59
def prefixEnd_5339030 : Nat := 4983230072969 + 3 ^ 40 * 5339030 * 2
def baseEnd_5339030 : Nat := 2741488618774351254271255

theorem tailTrace_5339030 : CollatzResearch.WordTrace tailWord_5339030 prefixEnd_5339030 2741488618774351254271255 := by
  unfold tailWord_5339030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12170651365475851160894909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129820281231742412382879029 12170651365475851160894909)
  ·
    refine ⟨4563994262053444185335591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12170651365475851160894909 4563994262053444185335591)
    ·
      refine ⟨6845991393080166278003387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563994262053444185335591 6845991393080166278003387)
      ·
        refine ⟨10268987089620249417005081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6845991393080166278003387 10268987089620249417005081)
        ·
          refine ⟨7701740317215187062753811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10268987089620249417005081 7701740317215187062753811)
          ·
            refine ⟨11552610475822780594130717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7701740317215187062753811 11552610475822780594130717)
            ·
              refine ⟨4332228928433542722799019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11552610475822780594130717 4332228928433542722799019)
              ·
                refine ⟨6498343392650314084198529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332228928433542722799019 6498343392650314084198529)
                ·
                  refine ⟨4873757544487735563148897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498343392650314084198529 4873757544487735563148897)
                  ·
                    refine ⟨3655318158365801672361673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4873757544487735563148897 3655318158365801672361673)
                    ·
                      refine ⟨2741488618774351254271255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655318158365801672361673 2741488618774351254271255)
                      ·
                        rfl

theorem cell23_5339030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5339030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339030 prefixEnd_5339030 := by exact prefixLift 5339030
  have htrace : WordTrace (prefixWord ++ tailWord_5339030) baseStart_5339030 baseEnd_5339030 := by
    simpa [prefixWord, tailWord_5339030, baseEnd_5339030] using wordTrace_append hprefix tailTrace_5339030
  have hstable : (prefixWord ++ tailWord_5339030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339030).length < 2 ^ (prefixWord ++ tailWord_5339030).sum := by decide
  have hdescent : baseEnd_5339030 < baseStart_5339030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339091 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_5339091 : Nat := 118140960795 + 5339091 * 2 ^ 59
def prefixEnd_5339091 : Nat := 4983230072969 + 3 ^ 40 * 5339091 * 2
def baseEnd_5339091 : Nat := 2741519941094275515608473

theorem tailTrace_5339091 : CollatzResearch.WordTrace tailWord_5339091 prefixEnd_5339091 2741519941094275515608473 := by
  unfold tailWord_5339091
  simp only [CollatzResearch.WordTrace]
  refine ⟨194732646700392625992289127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129821764466928417328192751 194732646700392625992289127)
  ·
    refine ⟨292098970050588938988433691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194732646700392625992289127 292098970050588938988433691)
    ·
      refine ⟨438148455075883408482650537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292098970050588938988433691 438148455075883408482650537)
      ·
        refine ⟨328611341306912556361987903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438148455075883408482650537 328611341306912556361987903)
        ·
          refine ⟨492917011960368834542981855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328611341306912556361987903 492917011960368834542981855)
          ·
            refine ⟨739375517940553251814472783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492917011960368834542981855 739375517940553251814472783)
            ·
              refine ⟨1109063276910829877721709175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739375517940553251814472783 1109063276910829877721709175)
              ·
                refine ⟨1663594915366244816582563763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109063276910829877721709175 1663594915366244816582563763)
                ·
                  refine ⟨2495392373049367224873845645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663594915366244816582563763 2495392373049367224873845645)
                  ·
                    refine ⟨935772139893512709327692117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495392373049367224873845645 935772139893512709327692117)
                    ·
                      refine ⟨2741519941094275515608473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 935772139893512709327692117 2741519941094275515608473)
                      ·
                        rfl

theorem cell23_5339091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_5339091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339091 prefixEnd_5339091 := by exact prefixLift 5339091
  have htrace : WordTrace (prefixWord ++ tailWord_5339091) baseStart_5339091 baseEnd_5339091 := by
    simpa [prefixWord, tailWord_5339091, baseEnd_5339091] using wordTrace_append hprefix tailTrace_5339091
  have hstable : (prefixWord ++ tailWord_5339091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339091).length < 2 ^ (prefixWord ++ tailWord_5339091).sum := by decide
  have hdescent : baseEnd_5339091 < baseStart_5339091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339095 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 4, 3, 2]
def baseStart_5339095 : Nat := 118140960795 + 5339095 * 2 ^ 59
def prefixEnd_5339095 : Nat := 4983230072969 + 3 ^ 40 * 5339095 * 2
def baseEnd_5339095 : Nat := 2741521995016893499958455

theorem tailTrace_5339095 : CollatzResearch.WordTrace tailWord_5339095 prefixEnd_5339095 2741521995016893499958455 := by
  unfold tailWord_5339095
  simp only [CollatzResearch.WordTrace]
  refine ⟨194732792592378134675434739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129821861728252089783623159 194732792592378134675434739)
  ·
    refine ⟨292099188888567202013152109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194732792592378134675434739 292099188888567202013152109)
    ·
      refine ⟨109537195833212700754932041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292099188888567202013152109 109537195833212700754932041)
      ·
        refine ⟨82152896874909525566199031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109537195833212700754932041 82152896874909525566199031)
        ·
          refine ⟨123229345312364288349298547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82152896874909525566199031 123229345312364288349298547)
          ·
            refine ⟨184844017968546432523947821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123229345312364288349298547 184844017968546432523947821)
            ·
              refine ⟨69316506738204912196480433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184844017968546432523947821 69316506738204912196480433)
              ·
                refine ⟨51987380053653684147360325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69316506738204912196480433 51987380053653684147360325)
                ·
                  refine ⟨9747633760060065777630061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51987380053653684147360325 9747633760060065777630061)
                  ·
                    refine ⟨3655362660022524666611273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9747633760060065777630061 3655362660022524666611273)
                    ·
                      refine ⟨2741521995016893499958455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655362660022524666611273 2741521995016893499958455)
                      ·
                        rfl

theorem cell23_5339095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_5339095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339095 prefixEnd_5339095 := by exact prefixLift 5339095
  have htrace : WordTrace (prefixWord ++ tailWord_5339095) baseStart_5339095 baseEnd_5339095 := by
    simpa [prefixWord, tailWord_5339095, baseEnd_5339095] using wordTrace_append hprefix tailTrace_5339095
  have hstable : (prefixWord ++ tailWord_5339095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339095).length < 2 ^ (prefixWord ++ tailWord_5339095).sum := by decide
  have hdescent : baseEnd_5339095 < baseStart_5339095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339105 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 1, 5]
def baseStart_5339105 : Nat := 118140960795 + 5339105 * 2 ^ 59
def prefixEnd_5339105 : Nat := 4983230072969 + 3 ^ 40 * 5339105 * 2
def baseEnd_5339105 : Nat := 913842376607812820277803

theorem tailTrace_5339105 : CollatzResearch.WordTrace tailWord_5339105 prefixEnd_5339105 913842376607812820277803 := by
  unfold tailWord_5339105
  simp only [CollatzResearch.WordTrace]
  refine ⟨194733157322341906383298769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129822104881561270922199179 194733157322341906383298769)
  ·
    refine ⟨146049867991756429787474077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194733157322341906383298769 146049867991756429787474077)
    ·
      refine ⟨54768700496908661170302779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146049867991756429787474077 54768700496908661170302779)
      ·
        refine ⟨82153050745362991755454169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54768700496908661170302779 82153050745362991755454169)
        ·
          refine ⟨61614788059022243816590627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82153050745362991755454169 61614788059022243816590627)
          ·
            refine ⟨92422182088533365724885941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61614788059022243816590627 92422182088533365724885941)
            ·
              refine ⟨8664579570800003036708057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92422182088533365724885941 8664579570800003036708057)
              ·
                refine ⟨6498434678100002277531043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8664579570800003036708057 6498434678100002277531043)
                ·
                  refine ⟨9747652017150003416296565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6498434678100002277531043 9747652017150003416296565)
                  ·
                    refine ⟨913842376607812820277803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9747652017150003416296565 913842376607812820277803)
                    ·
                      rfl

theorem cell23_5339105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_5339105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339105 prefixEnd_5339105 := by exact prefixLift 5339105
  have htrace : WordTrace (prefixWord ++ tailWord_5339105) baseStart_5339105 baseEnd_5339105 := by
    simpa [prefixWord, tailWord_5339105, baseEnd_5339105] using wordTrace_append hprefix tailTrace_5339105
  have hstable : (prefixWord ++ tailWord_5339105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339105).length < 2 ^ (prefixWord ++ tailWord_5339105).sum := by decide
  have hdescent : baseEnd_5339105 < baseStart_5339105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339208 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_5339208 : Nat := 118140960795 + 5339208 * 2 ^ 59
def prefixEnd_5339208 : Nat := 4983230072969 + 3 ^ 40 * 5339208 * 2
def baseEnd_5339208 : Nat := 913860006110283852615145

theorem tailTrace_5339208 : CollatzResearch.WordTrace tailWord_5339208 prefixEnd_5339208 913860006110283852615145 := by
  unfold tailWord_5339208
  simp only [CollatzResearch.WordTrace]
  refine ⟨97368457020484377487149139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129824609360645836649532185 97368457020484377487149139)
  ·
    refine ⟨146052685530726566230723709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97368457020484377487149139 146052685530726566230723709)
    ·
      refine ⟨54769757074022462336521391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146052685530726566230723709 54769757074022462336521391)
      ·
        refine ⟨82154635611033693504782087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54769757074022462336521391 82154635611033693504782087)
        ·
          refine ⟨123231953416550540257173131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82154635611033693504782087 123231953416550540257173131)
          ·
            refine ⟨184847930124825810385759697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123231953416550540257173131 184847930124825810385759697)
            ·
              refine ⟨138635947593619357789319773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184847930124825810385759697 138635947593619357789319773)
              ·
                refine ⟨51988480347607259170994915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138635947593619357789319773 51988480347607259170994915)
                ·
                  refine ⟨77982720521410888756492373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51988480347607259170994915 77982720521410888756492373)
                  ·
                    refine ⟨913860006110283852615145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77982720521410888756492373 913860006110283852615145)
                    ·
                      rfl

theorem cell23_5339208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_5339208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339208 prefixEnd_5339208 := by exact prefixLift 5339208
  have htrace : WordTrace (prefixWord ++ tailWord_5339208) baseStart_5339208 baseEnd_5339208 := by
    simpa [prefixWord, tailWord_5339208, baseEnd_5339208] using wordTrace_append hprefix tailTrace_5339208
  have hstable : (prefixWord ++ tailWord_5339208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339208).length < 2 ^ (prefixWord ++ tailWord_5339208).sum := by decide
  have hdescent : baseEnd_5339208 < baseStart_5339208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339209 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 2, 1, 3]
def baseStart_5339209 : Nat := 118140960795 + 5339209 * 2 ^ 59
def prefixEnd_5339209 : Nat := 4983230072969 + 3 ^ 40 * 5339209 * 2
def baseEnd_5339209 : Nat := 2741580531811506053932931

theorem tailTrace_5339209 : CollatzResearch.WordTrace tailWord_5339209 prefixEnd_5339209 2741580531811506053932931 := by
  unfold tailWord_5339209
  simp only [CollatzResearch.WordTrace]
  refine ⟨194736950513965132145084681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129824633675976754763389787 194736950513965132145084681)
  ·
    refine ⟨146052712885473849108813511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194736950513965132145084681 146052712885473849108813511)
    ·
      refine ⟨219079069328210773663220267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146052712885473849108813511 219079069328210773663220267)
      ·
        refine ⟨328618603992316160494830401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219079069328210773663220267 328618603992316160494830401)
        ·
          refine ⟨246463952994237120371122801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328618603992316160494830401 246463952994237120371122801)
          ·
            refine ⟨184847964745677840278342101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246463952994237120371122801 184847964745677840278342101)
            ·
              refine ⟨4332374173726824381523643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184847964745677840278342101 4332374173726824381523643)
              ·
                refine ⟨6498561260590236572285465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332374173726824381523643 6498561260590236572285465)
                ·
                  refine ⟨4873920945442677429214099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498561260590236572285465 4873920945442677429214099)
                  ·
                    refine ⟨7310881418164016143821149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4873920945442677429214099 7310881418164016143821149)
                    ·
                      refine ⟨2741580531811506053932931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7310881418164016143821149 2741580531811506053932931)
                      ·
                        rfl

theorem cell23_5339209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 1, 3].length) (baseStart_5339209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339209 prefixEnd_5339209 := by exact prefixLift 5339209
  have htrace : WordTrace (prefixWord ++ tailWord_5339209) baseStart_5339209 baseEnd_5339209 := by
    simpa [prefixWord, tailWord_5339209, baseEnd_5339209] using wordTrace_append hprefix tailTrace_5339209
  have hstable : (prefixWord ++ tailWord_5339209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339209).length < 2 ^ (prefixWord ++ tailWord_5339209).sum := by decide
  have hdescent : baseEnd_5339209 < baseStart_5339209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339249 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 2, 2, 2]
def baseStart_5339249 : Nat := 118140960795 + 5339249 * 2 ^ 59
def prefixEnd_5339249 : Nat := 4983230072969 + 3 ^ 40 * 5339249 * 2
def baseEnd_5339249 : Nat := 2741601071037685897432747

theorem tailTrace_5339249 : CollatzResearch.WordTrace tailWord_5339249 prefixEnd_5339249 2741601071037685897432747 := by
  unfold tailWord_5339249
  simp only [CollatzResearch.WordTrace]
  refine ⟨194738409433820218976540801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129825606289213479317693867 194738409433820218976540801)
  ·
    refine ⟨146053807075365164232405601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194738409433820218976540801 146053807075365164232405601)
    ·
      refine ⟨109540355306523873174304201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146053807075365164232405601 109540355306523873174304201)
      ·
        refine ⟨82155266479892904880728151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109540355306523873174304201 82155266479892904880728151)
        ·
          refine ⟨123232899719839357321092227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82155266479892904880728151 123232899719839357321092227)
          ·
            refine ⟨184849349579759035981638341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123232899719839357321092227 184849349579759035981638341)
            ·
              refine ⟨34659253046204819246557189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184849349579759035981638341 34659253046204819246557189)
              ·
                refine ⟨6498609946163403608729473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34659253046204819246557189 6498609946163403608729473)
                ·
                  refine ⟨4873957459622552706547105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498609946163403608729473 4873957459622552706547105)
                  ·
                    refine ⟨3655468094716914529910329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4873957459622552706547105 3655468094716914529910329)
                    ·
                      refine ⟨2741601071037685897432747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655468094716914529910329 2741601071037685897432747)
                      ·
                        rfl

theorem cell23_5339249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_5339249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339249 prefixEnd_5339249 := by exact prefixLift 5339249
  have htrace : WordTrace (prefixWord ++ tailWord_5339249) baseStart_5339249 baseEnd_5339249 := by
    simpa [prefixWord, tailWord_5339249, baseEnd_5339249] using wordTrace_append hprefix tailTrace_5339249
  have hstable : (prefixWord ++ tailWord_5339249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339249).length < 2 ^ (prefixWord ++ tailWord_5339249).sum := by decide
  have hdescent : baseEnd_5339249 < baseStart_5339249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339255 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 7]
def baseStart_5339255 : Nat := 118140960795 + 5339255 * 2 ^ 59
def prefixEnd_5339255 : Nat := 4983230072969 + 3 ^ 40 * 5339255 * 2
def baseEnd_5339255 : Nat := 304622683546845874884191

theorem tailTrace_5339255 : CollatzResearch.WordTrace tailWord_5339255 prefixEnd_5339255 304622683546845874884191 := by
  unfold tailWord_5339255
  simp only [CollatzResearch.WordTrace]
  refine ⟨194738628271798482001259219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129825752181198988000839479 194738628271798482001259219)
  ·
    refine ⟨292107942407697723001888829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194738628271798482001259219 292107942407697723001888829)
    ·
      refine ⟨109540478402886646125708311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292107942407697723001888829 109540478402886646125708311)
      ·
        refine ⟨164310717604329969188562467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109540478402886646125708311 164310717604329969188562467)
        ·
          refine ⟨246466076406494953782843701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164310717604329969188562467 246466076406494953782843701)
          ·
            refine ⟨23106194663108901917141597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246466076406494953782843701 23106194663108901917141597)
            ·
              refine ⟨8664822998665838218928099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23106194663108901917141597 8664822998665838218928099)
              ·
                refine ⟨12997234497998757328392149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8664822998665838218928099 12997234497998757328392149)
                ·
                  refine ⟨304622683546845874884191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12997234497998757328392149 304622683546845874884191)
                  ·
                    rfl

theorem cell23_5339255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 7].length) (baseStart_5339255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339255 prefixEnd_5339255 := by exact prefixLift 5339255
  have htrace : WordTrace (prefixWord ++ tailWord_5339255) baseStart_5339255 baseEnd_5339255 := by
    simpa [prefixWord, tailWord_5339255, baseEnd_5339255] using wordTrace_append hprefix tailTrace_5339255
  have hstable : (prefixWord ++ tailWord_5339255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339255).length < 2 ^ (prefixWord ++ tailWord_5339255).sum := by decide
  have hdescent : baseEnd_5339255 < baseStart_5339255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339306 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_5339306 : Nat := 118140960795 + 5339306 * 2 ^ 59
def prefixEnd_5339306 : Nat := 4983230072969 + 3 ^ 40 * 5339306 * 2
def baseEnd_5339306 : Nat := 304625593270554686046665

theorem tailTrace_5339306 : CollatzResearch.WordTrace tailWord_5339306 prefixEnd_5339306 304625593270554686046665 := by
  unfold tailWord_5339306
  simp only [CollatzResearch.WordTrace]
  refine ⟨48685122098653429427841443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129826992263075811807577181 48685122098653429427841443)
  ·
    refine ⟨73027683147980144141762165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48685122098653429427841443 73027683147980144141762165)
    ·
      refine ⟨6846345295123138513290203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73027683147980144141762165 6846345295123138513290203)
      ·
        refine ⟨10269517942684707769935305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6846345295123138513290203 10269517942684707769935305)
        ·
          refine ⟨7702138457013530827451479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10269517942684707769935305 7702138457013530827451479)
          ·
            refine ⟨11553207685520296241177219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7702138457013530827451479 11553207685520296241177219)
            ·
              refine ⟨17329811528280444361765829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11553207685520296241177219 17329811528280444361765829)
              ·
                refine ⟨3249339661552583317831093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17329811528280444361765829 3249339661552583317831093)
                ·
                  refine ⟨304625593270554686046665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3249339661552583317831093 304625593270554686046665)
                  ·
                    rfl

theorem cell23_5339306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_5339306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339306 prefixEnd_5339306 := by exact prefixLift 5339306
  have htrace : WordTrace (prefixWord ++ tailWord_5339306) baseStart_5339306 baseEnd_5339306 := by
    simpa [prefixWord, tailWord_5339306, baseEnd_5339306] using wordTrace_append hprefix tailTrace_5339306
  have hstable : (prefixWord ++ tailWord_5339306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339306).length < 2 ^ (prefixWord ++ tailWord_5339306).sum := by decide
  have hdescent : baseEnd_5339306 < baseStart_5339306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339309 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_5339309 : Nat := 118140960795 + 5339309 * 2 ^ 59
def prefixEnd_5339309 : Nat := 4983230072969 + 3 ^ 40 * 5339309 * 2
def baseEnd_5339309 : Nat := 2741631879876955662682471

theorem tailTrace_5339309 : CollatzResearch.WordTrace tailWord_5339309 prefixEnd_5339309 2741631879876955662682471 := by
  unfold tailWord_5339309
  simp only [CollatzResearch.WordTrace]
  refine ⟨194740597813602849223724981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129827065209068566149149987 194740597813602849223724981)
  ·
    refine ⟨18256931045025267114724217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194740597813602849223724981 18256931045025267114724217)
    ·
      refine ⟨13692698283768950336043163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18256931045025267114724217 13692698283768950336043163)
      ·
        refine ⟨20539047425653425504064745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13692698283768950336043163 20539047425653425504064745)
        ·
          refine ⟨15404285569240069128048559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20539047425653425504064745 15404285569240069128048559)
          ·
            refine ⟨23106428353860103692072839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15404285569240069128048559 23106428353860103692072839)
            ·
              refine ⟨34659642530790155538109259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23106428353860103692072839 34659642530790155538109259)
              ·
                refine ⟨51989463796185233307163889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34659642530790155538109259 51989463796185233307163889)
                ·
                  refine ⟨38992097847138924980372917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51989463796185233307163889 38992097847138924980372917)
                  ·
                    refine ⟨3655509173169274216909961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38992097847138924980372917 3655509173169274216909961)
                    ·
                      refine ⟨2741631879876955662682471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655509173169274216909961 2741631879876955662682471)
                      ·
                        rfl

theorem cell23_5339309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_5339309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339309 prefixEnd_5339309 := by exact prefixLift 5339309
  have htrace : WordTrace (prefixWord ++ tailWord_5339309) baseStart_5339309 baseEnd_5339309 := by
    simpa [prefixWord, tailWord_5339309, baseEnd_5339309] using wordTrace_append hprefix tailTrace_5339309
  have hstable : (prefixWord ++ tailWord_5339309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339309).length < 2 ^ (prefixWord ++ tailWord_5339309).sum := by decide
  have hdescent : baseEnd_5339309 < baseStart_5339309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339322 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2]
def baseStart_5339322 : Nat := 118140960795 + 5339322 * 2 ^ 59
def prefixEnd_5339322 : Nat := 4983230072969 + 3 ^ 40 * 5339322 * 2
def baseEnd_5339322 : Nat := 2741638555125464111819911

theorem tailTrace_5339322 : CollatzResearch.WordTrace tailWord_5339322 prefixEnd_5339322 2741638555125464111819911 := by
  unfold tailWord_5339322
  simp only [CollatzResearch.WordTrace]
  refine ⟨48685267990638938110987055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129827381308370501629298813 48685267990638938110987055)
  ·
    refine ⟨73027901985958407166480583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48685267990638938110987055 73027901985958407166480583)
    ·
      refine ⟨109541852978937610749720875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73027901985958407166480583 109541852978937610749720875)
      ·
        refine ⟨164312779468406416124581313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109541852978937610749720875 164312779468406416124581313)
        ·
          refine ⟨123234584601304812093435985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164312779468406416124581313 123234584601304812093435985)
          ·
            refine ⟨92425938450978609070076989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123234584601304812093435985 92425938450978609070076989)
            ·
              refine ⟨34659726919116978401278871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92425938450978609070076989 34659726919116978401278871)
              ·
                refine ⟨51989590378675467601918307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34659726919116978401278871 51989590378675467601918307)
                ·
                  refine ⟨77984385568013201402877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51989590378675467601918307 77984385568013201402877461)
                  ·
                    refine ⟨3655518073500618815759881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77984385568013201402877461 3655518073500618815759881)
                    ·
                      refine ⟨2741638555125464111819911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655518073500618815759881 2741638555125464111819911)
                      ·
                        rfl

theorem cell23_5339322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_5339322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339322 prefixEnd_5339322 := by exact prefixLift 5339322
  have htrace : WordTrace (prefixWord ++ tailWord_5339322) baseStart_5339322 baseEnd_5339322 := by
    simpa [prefixWord, tailWord_5339322, baseEnd_5339322] using wordTrace_append hprefix tailTrace_5339322
  have hstable : (prefixWord ++ tailWord_5339322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339322).length < 2 ^ (prefixWord ++ tailWord_5339322).sum := by decide
  have hdescent : baseEnd_5339322 < baseStart_5339322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339392 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 1, 5]
def baseStart_5339392 : Nat := 118140960795 + 5339392 * 2 ^ 59
def prefixEnd_5339392 : Nat := 4983230072969 + 3 ^ 40 * 5339392 * 2
def baseEnd_5339392 : Nat := 913891499590426279314863

theorem tailTrace_5339392 : CollatzResearch.WordTrace tailWord_5339392 prefixEnd_5339392 913891499590426279314863 := by
  unfold tailWord_5339392
  simp only [CollatzResearch.WordTrace]
  refine ⟨97371812536151077199498215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129829083381534769599330953 97371812536151077199498215)
  ·
    refine ⟨146057718804226615799247323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97371812536151077199498215 146057718804226615799247323)
    ·
      refine ⟨219086578206339923698870985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146057718804226615799247323 219086578206339923698870985)
      ·
        refine ⟨164314933654754942774153239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219086578206339923698870985 164314933654754942774153239)
        ·
          refine ⟨246472400482132414161229859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164314933654754942774153239 246472400482132414161229859)
          ·
            refine ⟨369708600723198621241844789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246472400482132414161229859 369708600723198621241844789)
            ·
              refine ⟨34660181317799870741422949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 369708600723198621241844789 34660181317799870741422949)
              ·
                refine ⟨6498783997087475764016803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34660181317799870741422949 6498783997087475764016803)
                ·
                  refine ⟨9748175995631213646025205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6498783997087475764016803 9748175995631213646025205)
                  ·
                    refine ⟨913891499590426279314863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9748175995631213646025205 913891499590426279314863)
                    ·
                      rfl

theorem cell23_5339392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_5339392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339392 prefixEnd_5339392 := by exact prefixLift 5339392
  have htrace : WordTrace (prefixWord ++ tailWord_5339392) baseStart_5339392 baseEnd_5339392 := by
    simpa [prefixWord, tailWord_5339392, baseEnd_5339392] using wordTrace_append hprefix tailTrace_5339392
  have hstable : (prefixWord ++ tailWord_5339392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339392).length < 2 ^ (prefixWord ++ tailWord_5339392).sum := by decide
  have hdescent : baseEnd_5339392 < baseStart_5339392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339463 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_5339463 : Nat := 118140960795 + 5339463 * 2 ^ 59
def prefixEnd_5339463 : Nat := 4983230072969 + 3 ^ 40 * 5339463 * 2
def baseEnd_5339463 : Nat := 2741710955897748060156763

theorem tailTrace_5339463 : CollatzResearch.WordTrace tailWord_5339463 prefixEnd_5339463 2741710955897748060156763 := by
  unfold tailWord_5339463
  simp only [CollatzResearch.WordTrace]
  refine ⟨194746214655044933524831043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129830809770029955683220695 194746214655044933524831043)
  ·
    refine ⟨292119321982567400287246565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194746214655044933524831043 292119321982567400287246565)
    ·
      refine ⟨54772372871731387553858731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292119321982567400287246565 54772372871731387553858731)
      ·
        refine ⟨82158559307597081330788097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54772372871731387553858731 82158559307597081330788097)
        ·
          refine ⟨61618919480697810998091073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82158559307597081330788097 61618919480697810998091073)
          ·
            refine ⟨46214189610523358248568305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61618919480697810998091073 46214189610523358248568305)
            ·
              refine ⟨34660642207892518686426229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46214189610523358248568305 34660642207892518686426229)
              ·
                refine ⟨3249435206989923626852459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34660642207892518686426229 3249435206989923626852459)
                ·
                  refine ⟨4874152810484885440278689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249435206989923626852459 4874152810484885440278689)
                  ·
                    refine ⟨3655614607863664080209017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4874152810484885440278689 3655614607863664080209017)
                    ·
                      refine ⟨2741710955897748060156763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655614607863664080209017 2741710955897748060156763)
                      ·
                        rfl

theorem cell23_5339463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_5339463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339463 prefixEnd_5339463 := by exact prefixLift 5339463
  have htrace : WordTrace (prefixWord ++ tailWord_5339463) baseStart_5339463 baseEnd_5339463 := by
    simpa [prefixWord, tailWord_5339463, baseEnd_5339463] using wordTrace_append hprefix tailTrace_5339463
  have hstable : (prefixWord ++ tailWord_5339463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339463).length < 2 ^ (prefixWord ++ tailWord_5339463).sum := by decide
  have hdescent : baseEnd_5339463 < baseStart_5339463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339496 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_5339496 : Nat := 118140960795 + 5339496 * 2 ^ 59
def prefixEnd_5339496 : Nat := 4983230072969 + 3 ^ 40 * 5339496 * 2
def baseEnd_5339496 : Nat := 2741727900759346431044111

theorem tailTrace_5339496 : CollatzResearch.WordTrace tailWord_5339496 prefixEnd_5339496 2741727900759346431044111 := by
  unfold tailWord_5339496
  simp only [CollatzResearch.WordTrace]
  refine ⟨97373709131962690080391171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129831612175950253440521561 97373709131962690080391171)
  ·
    refine ⟨146060563697944035120586757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97373709131962690080391171 146060563697944035120586757)
    ·
      refine ⟨27386355693364506585110017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146060563697944035120586757 27386355693364506585110017)
      ·
        refine ⟨20539766770023379938832513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27386355693364506585110017 20539766770023379938832513)
        ·
          refine ⟨15404825077517534954124385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20539766770023379938832513 15404825077517534954124385)
          ·
            refine ⟨11553618808138151215593289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15404825077517534954124385 11553618808138151215593289)
            ·
              refine ⟨8665214106103613411694967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11553618808138151215593289 8665214106103613411694967)
              ·
                refine ⟨12997821159155420117542451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8665214106103613411694967 12997821159155420117542451)
                ·
                  refine ⟨19496731738733130176313677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12997821159155420117542451 19496731738733130176313677)
                  ·
                    refine ⟨7311274402024923816117629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19496731738733130176313677 7311274402024923816117629)
                    ·
                      refine ⟨2741727900759346431044111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7311274402024923816117629 2741727900759346431044111)
                      ·
                        rfl

theorem cell23_5339496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_5339496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339496 prefixEnd_5339496 := by exact prefixLift 5339496
  have htrace : WordTrace (prefixWord ++ tailWord_5339496) baseStart_5339496 baseEnd_5339496 := by
    simpa [prefixWord, tailWord_5339496, baseEnd_5339496] using wordTrace_append hprefix tailTrace_5339496
  have hstable : (prefixWord ++ tailWord_5339496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339496).length < 2 ^ (prefixWord ++ tailWord_5339496).sum := by decide
  have hdescent : baseEnd_5339496 < baseStart_5339496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339506 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_5339506 : Nat := 118140960795 + 5339506 * 2 ^ 59
def prefixEnd_5339506 : Nat := 4983230072969 + 3 ^ 40 * 5339506 * 2
def baseEnd_5339506 : Nat := 2741733035565891391919065

theorem tailTrace_5339506 : CollatzResearch.WordTrace tailWord_5339506 prefixEnd_5339506 2741733035565891391919065 := by
  unfold tailWord_5339506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48686945748472287967161593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129831855329259434579097581 48686945748472287967161593)
  ·
    refine ⟨36515209311354215975371195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48686945748472287967161593 36515209311354215975371195)
    ·
      refine ⟨54772813967031323963056793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36515209311354215975371195 54772813967031323963056793)
      ·
        refine ⟨41079610475273492972292595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54772813967031323963056793 41079610475273492972292595)
        ·
          refine ⟨61619415712910239458438893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41079610475273492972292595 61619415712910239458438893)
          ·
            refine ⟨23107280892341339796914585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61619415712910239458438893 23107280892341339796914585)
            ·
              refine ⟨17330460669256004847685939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23107280892341339796914585 17330460669256004847685939)
              ·
                refine ⟨25995691003884007271528909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17330460669256004847685939 25995691003884007271528909)
                ·
                  refine ⟨9748384126456502726823341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25995691003884007271528909 9748384126456502726823341)
                  ·
                    refine ⟨3655644047421188522558753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9748384126456502726823341 3655644047421188522558753)
                    ·
                      refine ⟨2741733035565891391919065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655644047421188522558753 2741733035565891391919065)
                      ·
                        rfl

theorem cell23_5339506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_5339506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339506 prefixEnd_5339506 := by exact prefixLift 5339506
  have htrace : WordTrace (prefixWord ++ tailWord_5339506) baseStart_5339506 baseEnd_5339506 := by
    simpa [prefixWord, tailWord_5339506, baseEnd_5339506] using wordTrace_append hprefix tailTrace_5339506
  have hstable : (prefixWord ++ tailWord_5339506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339506).length < 2 ^ (prefixWord ++ tailWord_5339506).sum := by decide
  have hdescent : baseEnd_5339506 < baseStart_5339506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339523 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 1, 3, 2]
def baseStart_5339523 : Nat := 118140960795 + 5339523 * 2 ^ 59
def prefixEnd_5339523 : Nat := 4983230072969 + 3 ^ 40 * 5339523 * 2
def baseEnd_5339523 : Nat := 2741741764737017825406487

theorem tailTrace_5339523 : CollatzResearch.WordTrace tailWord_5339523 prefixEnd_5339523 2741741764737017825406487 := by
  unfold tailWord_5339523
  simp only [CollatzResearch.WordTrace]
  refine ⟨194748403034827563772015223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129832268689885042514676815 194748403034827563772015223)
  ·
    refine ⟨292122604552241345658022835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194748403034827563772015223 292122604552241345658022835)
    ·
      refine ⟨438183906828362018487034253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292122604552241345658022835 438183906828362018487034253)
      ·
        refine ⟨164318965060635756932637845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438183906828362018487034253 164318965060635756932637845)
        ·
          refine ⟨7702451487217301106217399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164318965060635756932637845 7702451487217301106217399)
          ·
            refine ⟨11553677230825951659326099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7702451487217301106217399 11553677230825951659326099)
            ·
              refine ⟨17330515846238927488989149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11553677230825951659326099 17330515846238927488989149)
              ·
                refine ⟨6498943442339597808370931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17330515846238927488989149 6498943442339597808370931)
                ·
                  refine ⟨9748415163509396712556397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6498943442339597808370931 9748415163509396712556397)
                  ·
                    refine ⟨3655655686316023767208649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9748415163509396712556397 3655655686316023767208649)
                    ·
                      refine ⟨2741741764737017825406487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655655686316023767208649 2741741764737017825406487)
                      ·
                        rfl

theorem cell23_5339523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_5339523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339523 prefixEnd_5339523 := by exact prefixLift 5339523
  have htrace : WordTrace (prefixWord ++ tailWord_5339523) baseStart_5339523 baseEnd_5339523 := by
    simpa [prefixWord, tailWord_5339523, baseEnd_5339523] using wordTrace_append hprefix tailTrace_5339523
  have hstable : (prefixWord ++ tailWord_5339523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339523).length < 2 ^ (prefixWord ++ tailWord_5339523).sum := by decide
  have hdescent : baseEnd_5339523 < baseStart_5339523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339559 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 7]
def baseStart_5339559 : Nat := 118140960795 + 5339559 * 2 ^ 59
def prefixEnd_5339559 : Nat := 4983230072969 + 3 ^ 40 * 5339559 * 2
def baseEnd_5339559 : Nat := 304640027782286631617369

theorem tailTrace_5339559 : CollatzResearch.WordTrace tailWord_5339559 prefixEnd_5339559 304640027782286631617369 := by
  unfold tailWord_5339559
  simp only [CollatzResearch.WordTrace]
  refine ⟨194749716062697141920325731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129833144041798094613550487 194749716062697141920325731)
  ·
    refine ⟨292124574094045712880488597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194749716062697141920325731 292124574094045712880488597)
    ·
      refine ⟨13693339410658392791272903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 292124574094045712880488597 13693339410658392791272903)
      ·
        refine ⟨20540009115987589186909355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13693339410658392791272903 20540009115987589186909355)
        ·
          refine ⟨30810013673981383780364033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20540009115987589186909355 30810013673981383780364033)
          ·
            refine ⟨23107510255486037835273025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30810013673981383780364033 23107510255486037835273025)
            ·
              refine ⟨17330632691614528376454769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23107510255486037835273025 17330632691614528376454769)
              ·
                refine ⟨12997974518710896282341077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17330632691614528376454769 12997974518710896282341077)
                ·
                  refine ⟨304640027782286631617369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12997974518710896282341077 304640027782286631617369)
                  ·
                    rfl

theorem cell23_5339559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 7].length) (baseStart_5339559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339559 prefixEnd_5339559 := by exact prefixLift 5339559
  have htrace : WordTrace (prefixWord ++ tailWord_5339559) baseStart_5339559 baseEnd_5339559 := by
    simpa [prefixWord, tailWord_5339559, baseEnd_5339559] using wordTrace_append hprefix tailTrace_5339559
  have hstable : (prefixWord ++ tailWord_5339559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339559).length < 2 ^ (prefixWord ++ tailWord_5339559).sum := by decide
  have hdescent : baseEnd_5339559 < baseStart_5339559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339579 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 6, 5, 2]
def baseStart_5339579 : Nat := 118140960795 + 5339579 * 2 ^ 59
def prefixEnd_5339579 : Nat := 4983230072969 + 3 ^ 40 * 5339579 * 2
def baseEnd_5339579 : Nat := 2741770519653669606306229

theorem tailTrace_5339579 : CollatzResearch.WordTrace tailWord_5339579 prefixEnd_5339579 2741770519653669606306229 := by
  unfold tailWord_5339579
  simp only [CollatzResearch.WordTrace]
  refine ⟨194750445522624685336053791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129833630348416456890702527 194750445522624685336053791)
  ·
    refine ⟨292125668283937028004080687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194750445522624685336053791 292125668283937028004080687)
    ·
      refine ⟨438188502425905542006121031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292125668283937028004080687 438188502425905542006121031)
      ·
        refine ⟨657282753638858313009181547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438188502425905542006121031 657282753638858313009181547)
        ·
          refine ⟨985924130458287469513772321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657282753638858313009181547 985924130458287469513772321)
          ·
            refine ⟨739443097843715602135329241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985924130458287469513772321 739443097843715602135329241)
            ·
              refine ⟨554582323382786701601496931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739443097843715602135329241 554582323382786701601496931)
              ·
                refine ⟨831873485074180052402245397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554582323382786701601496931 831873485074180052402245397)
                ·
                  refine ⟨38994069612852189956355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 831873485074180052402245397 38994069612852189956355253)
                  ·
                    refine ⟨3655694026204892808408305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38994069612852189956355253 3655694026204892808408305)
                    ·
                      refine ⟨2741770519653669606306229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655694026204892808408305 2741770519653669606306229)
                      ·
                        rfl

theorem cell23_5339579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5, 2].length) (baseStart_5339579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339579 prefixEnd_5339579 := by exact prefixLift 5339579
  have htrace : WordTrace (prefixWord ++ tailWord_5339579) baseStart_5339579 baseEnd_5339579 := by
    simpa [prefixWord, tailWord_5339579, baseEnd_5339579] using wordTrace_append hprefix tailTrace_5339579
  have hstable : (prefixWord ++ tailWord_5339579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339579).length < 2 ^ (prefixWord ++ tailWord_5339579).sum := by decide
  have hdescent : baseEnd_5339579 < baseStart_5339579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339606 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_5339606 : Nat := 118140960795 + 5339606 * 2 ^ 59
def prefixEnd_5339606 : Nat := 4983230072969 + 3 ^ 40 * 5339606 * 2
def baseEnd_5339606 : Nat := 913928127877113666889535

theorem tailTrace_5339606 : CollatzResearch.WordTrace tailWord_5339606 prefixEnd_5339606 913928127877113666889535 := by
  unfold tailWord_5339606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12171964393345429309205417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129834286862351245964857781 12171964393345429309205417)
  ·
    refine ⟨9128973295009071981904063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12171964393345429309205417 9128973295009071981904063)
    ·
      refine ⟨13693459942513607972856095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9128973295009071981904063 13693459942513607972856095)
      ·
        refine ⟨20540189913770411959284143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13693459942513607972856095 20540189913770411959284143)
        ·
          refine ⟨30810284870655617938926215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20540189913770411959284143 30810284870655617938926215)
          ·
            refine ⟨46215427305983426908389323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30810284870655617938926215 46215427305983426908389323)
            ·
              refine ⟨69323140958975140362583985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46215427305983426908389323 69323140958975140362583985)
              ·
                refine ⟨51992355719231355271937989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69323140958975140362583985 51992355719231355271937989)
                ·
                  refine ⟨9748566697355879113488373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51992355719231355271937989 9748566697355879113488373)
                  ·
                    refine ⟨913928127877113666889535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9748566697355879113488373 913928127877113666889535)
                    ·
                      rfl

theorem cell23_5339606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_5339606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339606 prefixEnd_5339606 := by exact prefixLift 5339606
  have htrace : WordTrace (prefixWord ++ tailWord_5339606) baseStart_5339606 baseEnd_5339606 := by
    simpa [prefixWord, tailWord_5339606, baseEnd_5339606] using wordTrace_append hprefix tailTrace_5339606
  have hstable : (prefixWord ++ tailWord_5339606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339606).length < 2 ^ (prefixWord ++ tailWord_5339606).sum := by decide
  have hdescent : baseEnd_5339606 < baseStart_5339606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339609 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_5339609 : Nat := 118140960795 + 5339609 * 2 ^ 59
def prefixEnd_5339609 : Nat := 4983230072969 + 3 ^ 40 * 5339609 * 2
def baseEnd_5339609 : Nat := 2741785924073304488931091

theorem tailTrace_5339609 : CollatzResearch.WordTrace tailWord_5339609 prefixEnd_5339609 2741785924073304488931091 := by
  unfold tailWord_5339609
  simp only [CollatzResearch.WordTrace]
  refine ⟨194751539712516000459645881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129834359808344000306430587 194751539712516000459645881)
  ·
    refine ⟨146063654784387000344734411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194751539712516000459645881 146063654784387000344734411)
    ·
      refine ⟨219095482176580500517101617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146063654784387000344734411 219095482176580500517101617)
      ·
        refine ⟨164321611632435375387826213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219095482176580500517101617 164321611632435375387826213)
        ·
          refine ⟨30810302181081632885217415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164321611632435375387826213 30810302181081632885217415)
          ·
            refine ⟨46215453271622449327826123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30810302181081632885217415 46215453271622449327826123)
            ·
              refine ⟨69323179907433673991739185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46215453271622449327826123 69323179907433673991739185)
              ·
                refine ⟨51992384930575255493804389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69323179907433673991739185 51992384930575255493804389)
                ·
                  refine ⟨9748572174482860405088323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51992384930575255493804389 9748572174482860405088323)
                  ·
                    refine ⟨14622858261724290607632485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9748572174482860405088323 14622858261724290607632485)
                    ·
                      refine ⟨2741785924073304488931091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14622858261724290607632485 2741785924073304488931091)
                      ·
                        rfl

theorem cell23_5339609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_5339609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339609 prefixEnd_5339609 := by exact prefixLift 5339609
  have htrace : WordTrace (prefixWord ++ tailWord_5339609) baseStart_5339609 baseEnd_5339609 := by
    simpa [prefixWord, tailWord_5339609, baseEnd_5339609] using wordTrace_append hprefix tailTrace_5339609
  have hstable : (prefixWord ++ tailWord_5339609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339609).length < 2 ^ (prefixWord ++ tailWord_5339609).sum := by decide
  have hdescent : baseEnd_5339609 < baseStart_5339609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339626 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_5339626 : Nat := 118140960795 + 5339626 * 2 ^ 59
def prefixEnd_5339626 : Nat := 4983230072969 + 3 ^ 40 * 5339626 * 2
def baseEnd_5339626 : Nat := 2741794653244430922418513

theorem tailTrace_5339626 : CollatzResearch.WordTrace tailWord_5339626 prefixEnd_5339626 2741794653244430922418513 := by
  unfold tailWord_5339626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48688039938363603090753683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129834773168969608242009821 48688039938363603090753683)
  ·
    refine ⟨73032059907545404636130525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48688039938363603090753683 73032059907545404636130525)
    ·
      refine ⟨27387022465329526738548947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73032059907545404636130525 27387022465329526738548947)
      ·
        refine ⟨41080533697994290107823421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27387022465329526738548947 41080533697994290107823421)
        ·
          refine ⟨15405200136747858790433783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41080533697994290107823421 15405200136747858790433783)
          ·
            refine ⟨23107800205121788185650675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15405200136747858790433783 23107800205121788185650675)
            ·
              refine ⟨34661700307682682278476013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23107800205121788185650675 34661700307682682278476013)
              ·
                refine ⟨12998137615381005854428505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34661700307682682278476013 12998137615381005854428505)
                ·
                  refine ⟨9748603211535754390821379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12998137615381005854428505 9748603211535754390821379)
                  ·
                    refine ⟨14622904817303631586232069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9748603211535754390821379 14622904817303631586232069)
                    ·
                      refine ⟨2741794653244430922418513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14622904817303631586232069 2741794653244430922418513)
                      ·
                        rfl

theorem cell23_5339626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_5339626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339626 prefixEnd_5339626 := by exact prefixLift 5339626
  have htrace : WordTrace (prefixWord ++ tailWord_5339626) baseStart_5339626 baseEnd_5339626 := by
    simpa [prefixWord, tailWord_5339626, baseEnd_5339626] using wordTrace_append hprefix tailTrace_5339626
  have hstable : (prefixWord ++ tailWord_5339626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339626).length < 2 ^ (prefixWord ++ tailWord_5339626).sum := by decide
  have hdescent : baseEnd_5339626 < baseStart_5339626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339680 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5339680 : Nat := 118140960795 + 5339680 * 2 ^ 59
def prefixEnd_5339680 : Nat := 4983230072969 + 3 ^ 40 * 5339680 * 2
def baseEnd_5339680 : Nat := 2741822381199773711143265

theorem tailTrace_5339680 : CollatzResearch.WordTrace tailWord_5339680 prefixEnd_5339680 2741822381199773711143265 := by
  unfold tailWord_5339680
  simp only [CollatzResearch.WordTrace]
  refine ⟨97377064647629389792740247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129836086196839186390320329 97377064647629389792740247)
  ·
    refine ⟨146065596971444084689110371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97377064647629389792740247 146065596971444084689110371)
    ·
      refine ⟨219098395457166127033665557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146065596971444084689110371 219098395457166127033665557)
      ·
        refine ⟨10270237287054662204703073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 219098395457166127033665557 10270237287054662204703073)
        ·
          refine ⟨7702677965290996653527305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10270237287054662204703073 7702677965290996653527305)
          ·
            refine ⟨5777008473968247490145479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7702677965290996653527305 5777008473968247490145479)
            ·
              refine ⟨8665512710952371235218219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5777008473968247490145479 8665512710952371235218219)
              ·
                refine ⟨12998269066428556852827329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8665512710952371235218219 12998269066428556852827329)
                ·
                  refine ⟨9748701799821417639620497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12998269066428556852827329 9748701799821417639620497)
                  ·
                    refine ⟨7311526349866063229715373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9748701799821417639620497 7311526349866063229715373)
                    ·
                      refine ⟨2741822381199773711143265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7311526349866063229715373 2741822381199773711143265)
                      ·
                        rfl

theorem cell23_5339680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5339680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339680 prefixEnd_5339680 := by exact prefixLift 5339680
  have htrace : WordTrace (prefixWord ++ tailWord_5339680) baseStart_5339680 baseEnd_5339680 := by
    simpa [prefixWord, tailWord_5339680, baseEnd_5339680] using wordTrace_append hprefix tailTrace_5339680
  have hstable : (prefixWord ++ tailWord_5339680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339680).length < 2 ^ (prefixWord ++ tailWord_5339680).sum := by decide
  have hdescent : baseEnd_5339680 < baseStart_5339680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339726 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_5339726 : Nat := 118140960795 + 5339726 * 2 ^ 59
def prefixEnd_5339726 : Nat := 4983230072969 + 3 ^ 40 * 5339726 * 2
def baseEnd_5339726 : Nat := 913948667103293510389351

theorem tailTrace_5339726 : CollatzResearch.WordTrace tailWord_5339726 prefixEnd_5339726 913948667103293510389351 := by
  unfold tailWord_5339726
  simp only [CollatzResearch.WordTrace]
  refine ⟨24344475881636516180206879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129837204702061419627770021 24344475881636516180206879)
  ·
    refine ⟨36516713822454774270310319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24344475881636516180206879 36516713822454774270310319)
    ·
      refine ⟨54775070733682161405465479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36516713822454774270310319 54775070733682161405465479)
      ·
        refine ⟨82162606100523242108198219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54775070733682161405465479 82162606100523242108198219)
        ·
          refine ⟨123243909150784863162297329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82162606100523242108198219 123243909150784863162297329)
          ·
            refine ⟨92432931863088647371722997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123243909150784863162297329 92432931863088647371722997)
            ·
              refine ⟨8665587362164560691099031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92432931863088647371722997 8665587362164560691099031)
              ·
                refine ⟨12998381043246841036648547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8665587362164560691099031 12998381043246841036648547)
                ·
                  refine ⟨19497571564870261554972821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12998381043246841036648547 19497571564870261554972821)
                  ·
                    refine ⟨913948667103293510389351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19497571564870261554972821 913948667103293510389351)
                    ·
                      rfl

theorem cell23_5339726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_5339726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339726 prefixEnd_5339726 := by exact prefixLift 5339726
  have htrace : WordTrace (prefixWord ++ tailWord_5339726) baseStart_5339726 baseEnd_5339726 := by
    simpa [prefixWord, tailWord_5339726, baseEnd_5339726] using wordTrace_append hprefix tailTrace_5339726
  have hstable : (prefixWord ++ tailWord_5339726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339726).length < 2 ^ (prefixWord ++ tailWord_5339726).sum := by decide
  have hdescent : baseEnd_5339726 < baseStart_5339726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339736 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_5339736 : Nat := 118140960795 + 5339736 * 2 ^ 59
def prefixEnd_5339736 : Nat := 4983230072969 + 3 ^ 40 * 5339736 * 2
def baseEnd_5339736 : Nat := 2741851136116425492043007

theorem tailTrace_5339736 : CollatzResearch.WordTrace tailWord_5339736 prefixEnd_5339736 2741851136116425492043007 := by
  unfold tailWord_5339736
  simp only [CollatzResearch.WordTrace]
  refine ⟨97378085891527950574759531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129837447855370600766346041 97378085891527950574759531)
  ·
    refine ⟨146067128837291925862139297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97378085891527950574759531 146067128837291925862139297)
    ·
      refine ⟨109550346627968944396604473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146067128837291925862139297 109550346627968944396604473)
      ·
        refine ⟨82162759970976708297453355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109550346627968944396604473 82162759970976708297453355)
        ·
          refine ⟨123244139956465062446180033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82162759970976708297453355 123244139956465062446180033)
          ·
            refine ⟨92433104967348796834635025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123244139956465062446180033 92433104967348796834635025)
            ·
              refine ⟨69324828725511597625976269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92433104967348796834635025 69324828725511597625976269)
              ·
                refine ⟨25996810772066849109741101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69324828725511597625976269 25996810772066849109741101)
                ·
                  refine ⟨9748804039525068416152913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25996810772066849109741101 9748804039525068416152913)
                  ·
                    refine ⟨7311603029643801312114685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9748804039525068416152913 7311603029643801312114685)
                    ·
                      refine ⟨2741851136116425492043007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7311603029643801312114685 2741851136116425492043007)
                      ·
                        rfl

theorem cell23_5339736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_5339736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339736 prefixEnd_5339736 := by exact prefixLift 5339736
  have htrace : WordTrace (prefixWord ++ tailWord_5339736) baseStart_5339736 baseEnd_5339736 := by
    simpa [prefixWord, tailWord_5339736, baseEnd_5339736] using wordTrace_append hprefix tailTrace_5339736
  have hstable : (prefixWord ++ tailWord_5339736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339736).length < 2 ^ (prefixWord ++ tailWord_5339736).sum := by decide
  have hdescent : baseEnd_5339736 < baseStart_5339736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339840 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 1, 4, 2]
def baseStart_5339840 : Nat := 118140960795 + 5339840 * 2 ^ 59
def prefixEnd_5339840 : Nat := 4983230072969 + 3 ^ 40 * 5339840 * 2
def baseEnd_5339840 : Nat := 2741904538104493085142529

theorem tailTrace_5339840 : CollatzResearch.WordTrace tailWord_5339840 prefixEnd_5339840 2741904538104493085142529 := by
  unfold tailWord_5339840
  simp only [CollatzResearch.WordTrace]
  refine ⟨97379982487339563455652487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129839976649786084607536649 97379982487339563455652487)
  ·
    refine ⟨146069973731009345183478731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97379982487339563455652487 146069973731009345183478731)
    ·
      refine ⟨219104960596514017775218097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146069973731009345183478731 219104960596514017775218097)
      ·
        refine ⟨164328720447385513331413573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219104960596514017775218097 164328720447385513331413573)
        ·
          refine ⟨30811635083884783749640045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164328720447385513331413573 30811635083884783749640045)
          ·
            refine ⟨11554363156456793906115017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30811635083884783749640045 11554363156456793906115017)
            ·
              refine ⟨8665772367342595429586263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11554363156456793906115017 8665772367342595429586263)
              ·
                refine ⟨12998658551013893144379395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8665772367342595429586263 12998658551013893144379395)
                ·
                  refine ⟨19497987826520839716569093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12998658551013893144379395 19497987826520839716569093)
                  ·
                    refine ⟨3655872717472657446856705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19497987826520839716569093 3655872717472657446856705)
                    ·
                      refine ⟨2741904538104493085142529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655872717472657446856705 2741904538104493085142529)
                      ·
                        rfl

theorem cell23_5339840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_5339840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339840 prefixEnd_5339840 := by exact prefixLift 5339840
  have htrace : WordTrace (prefixWord ++ tailWord_5339840) baseStart_5339840 baseEnd_5339840 := by
    simpa [prefixWord, tailWord_5339840, baseEnd_5339840] using wordTrace_append hprefix tailTrace_5339840
  have hstable : (prefixWord ++ tailWord_5339840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339840).length < 2 ^ (prefixWord ++ tailWord_5339840).sum := by decide
  have hdescent : baseEnd_5339840 < baseStart_5339840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339861 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5339861 : Nat := 118140960795 + 5339861 * 2 ^ 59
def prefixEnd_5339861 : Nat := 4983230072969 + 3 ^ 40 * 5339861 * 2
def baseEnd_5339861 : Nat := 2741915321198237502979933

theorem tailTrace_5339861 : CollatzResearch.WordTrace tailWord_5339861 prefixEnd_5339861 2741915321198237502979933 := by
  unfold tailWord_5339861
  simp only [CollatzResearch.WordTrace]
  refine ⟨194760730907603047497819437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129840487271735364998546291 194760730907603047497819437)
  ·
    refine ⟨73035274090351142811682289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194760730907603047497819437 73035274090351142811682289)
    ·
      refine ⟨54776455567763357108761717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73035274090351142811682289 54776455567763357108761717)
      ·
        refine ⟨5135292709477814728946411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54776455567763357108761717 5135292709477814728946411)
        ·
          refine ⟨7702939064216722093419617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135292709477814728946411 7702939064216722093419617)
          ·
            refine ⟨5777204298162541570064713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7702939064216722093419617 5777204298162541570064713)
            ·
              refine ⟨4332903223621906177548535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777204298162541570064713 4332903223621906177548535)
              ·
                refine ⟨6499354835432859266322803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332903223621906177548535 6499354835432859266322803)
                ·
                  refine ⟨9749032253149288899484205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6499354835432859266322803 9749032253149288899484205)
                  ·
                    refine ⟨3655887094930983337306577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9749032253149288899484205 3655887094930983337306577)
                    ·
                      refine ⟨2741915321198237502979933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655887094930983337306577 2741915321198237502979933)
                      ·
                        rfl

theorem cell23_5339861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5339861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339861 prefixEnd_5339861 := by exact prefixLift 5339861
  have htrace : WordTrace (prefixWord ++ tailWord_5339861) baseStart_5339861 baseEnd_5339861 := by
    simpa [prefixWord, tailWord_5339861, baseEnd_5339861] using wordTrace_append hprefix tailTrace_5339861
  have hstable : (prefixWord ++ tailWord_5339861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339861).length < 2 ^ (prefixWord ++ tailWord_5339861).sum := by decide
  have hdescent : baseEnd_5339861 < baseStart_5339861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339863 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 5]
def baseStart_5339863 : Nat := 118140960795 + 5339863 * 2 ^ 59
def prefixEnd_5339863 : Nat := 4983230072969 + 3 ^ 40 * 5339863 * 2
def baseEnd_5339863 : Nat := 304657372017727388350547

theorem tailTrace_5339863 : CollatzResearch.WordTrace tailWord_5339863 prefixEnd_5339863 304657372017727388350547 := by
  unfold tailWord_5339863
  simp only [CollatzResearch.WordTrace]
  refine ⟨194760803853595801839392243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129840535902397201226261495 194760803853595801839392243)
  ·
    refine ⟨292141205780393702759088365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194760803853595801839392243 292141205780393702759088365)
    ·
      refine ⟨109552952167647638534658137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292141205780393702759088365 109552952167647638534658137)
      ·
        refine ⟨82164714125735728900993603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109552952167647638534658137 82164714125735728900993603)
        ·
          refine ⟨123247071188603593351490405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82164714125735728900993603 123247071188603593351490405)
          ·
            refine ⟨23108825847863173753404451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123247071188603593351490405 23108825847863173753404451)
            ·
              refine ⟨34663238771794760630106677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23108825847863173753404451 34663238771794760630106677)
              ·
                refine ⟨3249678634855758809072501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34663238771794760630106677 3249678634855758809072501)
                ·
                  refine ⟨304657372017727388350547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3249678634855758809072501 304657372017727388350547)
                  ·
                    rfl

theorem cell23_5339863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 5].length) (baseStart_5339863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339863 prefixEnd_5339863 := by exact prefixLift 5339863
  have htrace : WordTrace (prefixWord ++ tailWord_5339863) baseStart_5339863 baseEnd_5339863 := by
    simpa [prefixWord, tailWord_5339863, baseEnd_5339863] using wordTrace_append hprefix tailTrace_5339863
  have hstable : (prefixWord ++ tailWord_5339863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339863).length < 2 ^ (prefixWord ++ tailWord_5339863).sum := by decide
  have hdescent : baseEnd_5339863 < baseStart_5339863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339873 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_5339873 : Nat := 118140960795 + 5339873 * 2 ^ 59
def prefixEnd_5339873 : Nat := 4983230072969 + 3 ^ 40 * 5339873 * 2
def baseEnd_5339873 : Nat := 2741921482966091456029877

theorem tailTrace_5339873 : CollatzResearch.WordTrace tailWord_5339873 prefixEnd_5339873 2741921482966091456029877 := by
  unfold tailWord_5339873
  simp only [CollatzResearch.WordTrace]
  refine ⟨194761168583559573547256273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129840779055706382364837515 194761168583559573547256273)
  ·
    refine ⟨146070876437669680160442205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194761168583559573547256273 146070876437669680160442205)
    ·
      refine ⟨54776578664126130060165827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146070876437669680160442205 54776578664126130060165827)
      ·
        refine ⟨82164867996189195090248741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54776578664126130060165827 82164867996189195090248741)
        ·
          refine ⟨15405912749285474079421639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82164867996189195090248741 15405912749285474079421639)
          ·
            refine ⟨23108869123928211119132459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15405912749285474079421639 23108869123928211119132459)
            ·
              refine ⟨34663303685892316678698689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23108869123928211119132459 34663303685892316678698689)
              ·
                refine ⟨25997477764419237509024017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34663303685892316678698689 25997477764419237509024017)
                ·
                  refine ⟨19498108323314428131768013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25997477764419237509024017 19498108323314428131768013)
                  ·
                    refine ⟨7311790621242910549413005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19498108323314428131768013 7311790621242910549413005)
                    ·
                      refine ⟨2741921482966091456029877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7311790621242910549413005 2741921482966091456029877)
                      ·
                        rfl

theorem cell23_5339873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_5339873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339873 prefixEnd_5339873 := by exact prefixLift 5339873
  have htrace : WordTrace (prefixWord ++ tailWord_5339873) baseStart_5339873 baseEnd_5339873 := by
    simpa [prefixWord, tailWord_5339873, baseEnd_5339873] using wordTrace_append hprefix tailTrace_5339873
  have hstable : (prefixWord ++ tailWord_5339873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339873).length < 2 ^ (prefixWord ++ tailWord_5339873).sum := by decide
  have hdescent : baseEnd_5339873 < baseStart_5339873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339896 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_5339896 : Nat := 118140960795 + 5339896 * 2 ^ 59
def prefixEnd_5339896 : Nat := 4983230072969 + 3 ^ 40 * 5339896 * 2
def baseEnd_5339896 : Nat := 2741933293021144866042271

theorem tailTrace_5339896 : CollatzResearch.WordTrace tailWord_5339896 prefixEnd_5339896 2741933293021144866042271 := by
  unfold tailWord_5339896
  simp only [CollatzResearch.WordTrace]
  refine ⟨97381003731238124237671771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129841338308317498983562361 97381003731238124237671771)
  ·
    refine ⟨146071505596857186356507657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97381003731238124237671771 146071505596857186356507657)
    ·
      refine ⟨109553629197642889767380743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146071505596857186356507657 109553629197642889767380743)
      ·
        refine ⟨164330443796464334651071115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109553629197642889767380743 164330443796464334651071115)
        ·
          refine ⟨246495665694696501976606673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164330443796464334651071115 246495665694696501976606673)
          ·
            refine ⟨184871749271022376482455005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246495665694696501976606673 184871749271022376482455005)
            ·
              refine ⟨69326905976633391180920627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184871749271022376482455005 69326905976633391180920627)
              ·
                refine ⟨103990358964950086771380941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69326905976633391180920627 103990358964950086771380941)
                ·
                  refine ⟨38996384611856282539267853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103990358964950086771380941 38996384611856282539267853)
                  ·
                    refine ⟨14623644229446105952225445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38996384611856282539267853 14623644229446105952225445)
                    ·
                      refine ⟨2741933293021144866042271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14623644229446105952225445 2741933293021144866042271)
                      ·
                        rfl

theorem cell23_5339896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_5339896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339896 prefixEnd_5339896 := by exact prefixLift 5339896
  have htrace : WordTrace (prefixWord ++ tailWord_5339896) baseStart_5339896 baseEnd_5339896 := by
    simpa [prefixWord, tailWord_5339896, baseEnd_5339896] using wordTrace_append hprefix tailTrace_5339896
  have hstable : (prefixWord ++ tailWord_5339896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339896).length < 2 ^ (prefixWord ++ tailWord_5339896).sum := by decide
  have hdescent : baseEnd_5339896 < baseStart_5339896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339913 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 6, 2]
def baseStart_5339913 : Nat := 118140960795 + 5339913 * 2 ^ 59
def prefixEnd_5339913 : Nat := 4983230072969 + 3 ^ 40 * 5339913 * 2
def baseEnd_5339913 : Nat := 2741942022192271299529693

theorem tailTrace_5339913 : CollatzResearch.WordTrace tailWord_5339913 prefixEnd_5339913 2741942022192271299529693 := by
  unfold tailWord_5339913
  simp only [CollatzResearch.WordTrace]
  refine ⟨194762627503414660378712393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129841751668943106919141595 194762627503414660378712393)
  ·
    refine ⟨146071970627560995284034295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194762627503414660378712393 146071970627560995284034295)
    ·
      refine ⟨219107955941341492926051443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146071970627560995284034295 219107955941341492926051443)
      ·
        refine ⟨328661933912012239389077165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219107955941341492926051443 328661933912012239389077165)
        ·
          refine ⟨123248225217004589770903937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328661933912012239389077165 123248225217004589770903937)
          ·
            refine ⟨92436168912753442328177953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123248225217004589770903937 92436168912753442328177953)
            ·
              refine ⟨69327126684565081746133465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92436168912753442328177953 69327126684565081746133465)
              ·
                refine ⟨51995345013423811309600099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69327126684565081746133465 51995345013423811309600099)
                ·
                  refine ⟨77993017520135716964400149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51995345013423811309600099 77993017520135716964400149)
                  ·
                    refine ⟨3655922696256361732706257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77993017520135716964400149 3655922696256361732706257)
                    ·
                      refine ⟨2741942022192271299529693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3655922696256361732706257 2741942022192271299529693)
                      ·
                        rfl

theorem cell23_5339913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 6, 2].length) (baseStart_5339913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339913 prefixEnd_5339913 := by exact prefixLift 5339913
  have htrace : WordTrace (prefixWord ++ tailWord_5339913) baseStart_5339913 baseEnd_5339913 := by
    simpa [prefixWord, tailWord_5339913, baseEnd_5339913] using wordTrace_append hprefix tailTrace_5339913
  have hstable : (prefixWord ++ tailWord_5339913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339913).length < 2 ^ (prefixWord ++ tailWord_5339913).sum := by decide
  have hdescent : baseEnd_5339913 < baseStart_5339913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339916 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_5339916 : Nat := 118140960795 + 5339916 * 2 ^ 59
def prefixEnd_5339916 : Nat := 4983230072969 + 3 ^ 40 * 5339916 * 2
def baseEnd_5339916 : Nat := 2741943562634234787792179

theorem tailTrace_5339916 : CollatzResearch.WordTrace tailWord_5339916 prefixEnd_5339916 2741943562634234787792179 := by
  unfold tailWord_5339916
  simp only [CollatzResearch.WordTrace]
  refine ⟨97381368461201895945535801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129841824614935861260714401 97381368461201895945535801)
  ·
    refine ⟨73036026345901421959151851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97381368461201895945535801 73036026345901421959151851)
    ·
      refine ⟨109554039518852132938727777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73036026345901421959151851 109554039518852132938727777)
      ·
        refine ⟨82165529639139099704045833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109554039518852132938727777 82165529639139099704045833)
        ·
          refine ⟨61624147229354324778034375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82165529639139099704045833 61624147229354324778034375)
          ·
            refine ⟨92436220844031487167051563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61624147229354324778034375 92436220844031487167051563)
            ·
              refine ⟨138654331266047230750577345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92436220844031487167051563 138654331266047230750577345)
              ·
                refine ⟨103990748449535423062933009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138654331266047230750577345 103990748449535423062933009)
                ·
                  refine ⟨77993061337151567297199757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103990748449535423062933009 77993061337151567297199757)
                  ·
                    refine ⟨29247398001431837736449909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77993061337151567297199757 29247398001431837736449909)
                    ·
                      refine ⟨2741943562634234787792179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29247398001431837736449909 2741943562634234787792179)
                      ·
                        rfl

theorem cell23_5339916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_5339916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339916 prefixEnd_5339916 := by exact prefixLift 5339916
  have htrace : WordTrace (prefixWord ++ tailWord_5339916) baseStart_5339916 baseEnd_5339916 := by
    simpa [prefixWord, tailWord_5339916, baseEnd_5339916] using wordTrace_append hprefix tailTrace_5339916
  have hstable : (prefixWord ++ tailWord_5339916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339916).length < 2 ^ (prefixWord ++ tailWord_5339916).sum := by decide
  have hdescent : baseEnd_5339916 < baseStart_5339916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5339953 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 6]
def baseStart_5339953 : Nat := 118140960795 + 5339953 * 2 ^ 59
def prefixEnd_5339953 : Nat := 4983230072969 + 3 ^ 40 * 5339953 * 2
def baseEnd_5339953 : Nat := 304662506824272349225501

theorem tailTrace_5339953 : CollatzResearch.WordTrace tailWord_5339953 prefixEnd_5339953 304662506824272349225501 := by
  unfold tailWord_5339953
  simp only [CollatzResearch.WordTrace]
  refine ⟨194764086423269747210168513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129842724282179831473445675 194764086423269747210168513)
  ·
    refine ⟨146073064817452310407626385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194764086423269747210168513 146073064817452310407626385)
    ·
      refine ⟨109554798613089232805719789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146073064817452310407626385 109554798613089232805719789)
      ·
        refine ⟨41083049479908462302144921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109554798613089232805719789 41083049479908462302144921)
        ·
          refine ⟨30812287109931346726608691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41083049479908462302144921 30812287109931346726608691)
          ·
            refine ⟨46218430664897020089913037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30812287109931346726608691 46218430664897020089913037)
            ·
              refine ⟨17331911499336382533717389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46218430664897020089913037 17331911499336382533717389)
              ·
                refine ⟨6499466812251143450144021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17331911499336382533717389 6499466812251143450144021)
                ·
                  refine ⟨304662506824272349225501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6499466812251143450144021 304662506824272349225501)
                  ·
                    rfl

theorem cell23_5339953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 6].length) (baseStart_5339953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5339953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5339953 prefixEnd_5339953 := by exact prefixLift 5339953
  have htrace : WordTrace (prefixWord ++ tailWord_5339953) baseStart_5339953 baseEnd_5339953 := by
    simpa [prefixWord, tailWord_5339953, baseEnd_5339953] using wordTrace_append hprefix tailTrace_5339953
  have hstable : (prefixWord ++ tailWord_5339953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5339953).length < 2 ^ (prefixWord ++ tailWord_5339953).sum := by decide
  have hdescent : baseEnd_5339953 < baseStart_5339953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5339953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340014 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_5340014 : Nat := 118140960795 + 5340014 * 2 ^ 59
def prefixEnd_5340014 : Nat := 4983230072969 + 3 ^ 40 * 5340014 * 2
def baseEnd_5340014 : Nat := 2741993883738375404366729

theorem tailTrace_5340014 : CollatzResearch.WordTrace tailWord_5340014 prefixEnd_5340014 2741993883738375404366729 := by
  unfold tailWord_5340014
  simp only [CollatzResearch.WordTrace]
  refine ⟨24345788909506094328517387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129844207517365836418759397 24345788909506094328517387)
  ·
    refine ⟨36518683364259141492776081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24345788909506094328517387 36518683364259141492776081)
    ·
      refine ⟨27389012523194356119582061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36518683364259141492776081 27389012523194356119582061)
      ·
        refine ⟨10270879696197883544843273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27389012523194356119582061 10270879696197883544843273)
        ·
          refine ⟨7703159772148412658632455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10270879696197883544843273 7703159772148412658632455)
          ·
            refine ⟨11554739658222618987948683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703159772148412658632455 11554739658222618987948683)
            ·
              refine ⟨17332109487333928481923025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11554739658222618987948683 17332109487333928481923025)
              ·
                refine ⟨12999082115500446361442269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17332109487333928481923025 12999082115500446361442269)
                ·
                  refine ⟨4874655793312667385540851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12999082115500446361442269 4874655793312667385540851)
                  ·
                    refine ⟨7311983689969001078311277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4874655793312667385540851 7311983689969001078311277)
                    ·
                      refine ⟨2741993883738375404366729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7311983689969001078311277 2741993883738375404366729)
                      ·
                        rfl

theorem cell23_5340014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_5340014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340014 prefixEnd_5340014 := by exact prefixLift 5340014
  have htrace : WordTrace (prefixWord ++ tailWord_5340014) baseStart_5340014 baseEnd_5340014 := by
    simpa [prefixWord, tailWord_5340014, baseEnd_5340014] using wordTrace_append hprefix tailTrace_5340014
  have hstable : (prefixWord ++ tailWord_5340014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340014).length < 2 ^ (prefixWord ++ tailWord_5340014).sum := by decide
  have hdescent : baseEnd_5340014 < baseStart_5340014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340037 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 1, 1, 4]
def baseStart_5340037 : Nat := 118140960795 + 5340037 * 2 ^ 59
def prefixEnd_5340037 : Nat := 4983230072969 + 3 ^ 40 * 5340037 * 2
def baseEnd_5340037 : Nat := 2742005693793428814379123

theorem tailTrace_5340037 : CollatzResearch.WordTrace tailWord_5340037 prefixEnd_5340037 2742005693793428814379123 := by
  unfold tailWord_5340037
  simp only [CollatzResearch.WordTrace]
  refine ⟨194767150154965429556226365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129844766769976953037484243 194767150154965429556226365)
  ·
    refine ⟨73037681308112036083584887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194767150154965429556226365 73037681308112036083584887)
    ·
      refine ⟨109556521962168054125377331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73037681308112036083584887 109556521962168054125377331)
      ·
        refine ⟨164334782943252081188065997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109556521962168054125377331 164334782943252081188065997)
        ·
          refine ⟨61625543603719530445524749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164334782943252081188065997 61625543603719530445524749)
          ·
            refine ⟨23109578851394823917071781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61625543603719530445524749 23109578851394823917071781)
            ·
              refine ⟨4333046034636529484450959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23109578851394823917071781 4333046034636529484450959)
              ·
                refine ⟨6499569051954794226676439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333046034636529484450959 6499569051954794226676439)
                ·
                  refine ⟨9749353577932191340014659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6499569051954794226676439 9749353577932191340014659)
                  ·
                    refine ⟨14624030366898287010021989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9749353577932191340014659 14624030366898287010021989)
                    ·
                      refine ⟨2742005693793428814379123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14624030366898287010021989 2742005693793428814379123)
                      ·
                        rfl

theorem cell23_5340037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_5340037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340037 prefixEnd_5340037 := by exact prefixLift 5340037
  have htrace : WordTrace (prefixWord ++ tailWord_5340037) baseStart_5340037 baseEnd_5340037 := by
    simpa [prefixWord, tailWord_5340037, baseEnd_5340037] using wordTrace_append hprefix tailTrace_5340037
  have hstable : (prefixWord ++ tailWord_5340037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340037).length < 2 ^ (prefixWord ++ tailWord_5340037).sum := by decide
  have hdescent : baseEnd_5340037 < baseStart_5340037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340077 : List Nat := [1, 5, 2, 3, 1, 1, 1, 9]
def baseStart_5340077 : Nat := 118140960795 + 5340077 * 2 ^ 59
def prefixEnd_5340077 : Nat := 4983230072969 + 3 ^ 40 * 5340077 * 2
def baseEnd_5340077 : Nat := 101556527148874394736257

theorem tailTrace_5340077 : CollatzResearch.WordTrace tailWord_5340077 prefixEnd_5340077 101556527148874394736257 := by
  unfold tailWord_5340077
  simp only [CollatzResearch.WordTrace]
  refine ⟨194768609074820516387682485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129845739383213677591788323 194768609074820516387682485)
  ·
    refine ⟨18259557100764423411345233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194768609074820516387682485 18259557100764423411345233)
    ·
      refine ⟨13694667825573317558508925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18259557100764423411345233 13694667825573317558508925)
      ·
        refine ⟨5135500434589994084440847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13694667825573317558508925 5135500434589994084440847)
        ·
          refine ⟨7703250651884991126661271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135500434589994084440847 7703250651884991126661271)
          ·
            refine ⟨11554875977827486689991907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703250651884991126661271 11554875977827486689991907)
            ·
              refine ⟨17332313966741230034987861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11554875977827486689991907 17332313966741230034987861)
              ·
                refine ⟨101556527148874394736257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17332313966741230034987861 101556527148874394736257)
                ·
                  rfl

theorem cell23_5340077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 9].length) (baseStart_5340077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340077 prefixEnd_5340077 := by exact prefixLift 5340077
  have htrace : WordTrace (prefixWord ++ tailWord_5340077) baseStart_5340077 baseEnd_5340077 := by
    simpa [prefixWord, tailWord_5340077, baseEnd_5340077] using wordTrace_append hprefix tailTrace_5340077
  have hstable : (prefixWord ++ tailWord_5340077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340077).length < 2 ^ (prefixWord ++ tailWord_5340077).sum := by decide
  have hdescent : baseEnd_5340077 < baseStart_5340077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340103 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 4, 6]
def baseStart_5340103 : Nat := 118140960795 + 5340103 * 2 ^ 59
def prefixEnd_5340103 : Nat := 4983230072969 + 3 ^ 40 * 5340103 * 2
def baseEnd_5340103 : Nat := 914013194505541852051273

theorem tailTrace_5340103 : CollatzResearch.WordTrace tailWord_5340103 prefixEnd_5340103 914013194505541852051273 := by
  unfold tailWord_5340103
  simp only [CollatzResearch.WordTrace]
  refine ⟨194769557372726322828128963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129846371581817548552085975 194769557372726322828128963)
  ·
    refine ⟨292154336059089484242193445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194769557372726322828128963 292154336059089484242193445)
    ·
      refine ⟨54778938011079278295411271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292154336059089484242193445 54778938011079278295411271)
      ·
        refine ⟨82168407016618917443116907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54778938011079278295411271 82168407016618917443116907)
        ·
          refine ⟨123252610524928376164675361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82168407016618917443116907 123252610524928376164675361)
          ·
            refine ⟨92439457893696282123506521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123252610524928376164675361 92439457893696282123506521)
            ·
              refine ⟨69329593420272211592629891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92439457893696282123506521 69329593420272211592629891)
              ·
                refine ⟨103994390130408317388944837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69329593420272211592629891 103994390130408317388944837)
                ·
                  refine ⟨19498948149451559510427157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103994390130408317388944837 19498948149451559510427157)
                  ·
                    refine ⟨914013194505541852051273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19498948149451559510427157 914013194505541852051273)
                    ·
                      rfl

theorem cell23_5340103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_5340103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340103 prefixEnd_5340103 := by exact prefixLift 5340103
  have htrace : WordTrace (prefixWord ++ tailWord_5340103) baseStart_5340103 baseEnd_5340103 := by
    simpa [prefixWord, tailWord_5340103, baseEnd_5340103] using wordTrace_append hprefix tailTrace_5340103
  have hstable : (prefixWord ++ tailWord_5340103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340103).length < 2 ^ (prefixWord ++ tailWord_5340103).sum := by decide
  have hdescent : baseEnd_5340103 < baseStart_5340103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340113 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_5340113 : Nat := 118140960795 + 5340113 * 2 ^ 59
def prefixEnd_5340113 : Nat := 4983230072969 + 3 ^ 40 * 5340113 * 2
def baseEnd_5340113 : Nat := 2742044718323170517028773

theorem tailTrace_5340113 : CollatzResearch.WordTrace tailWord_5340113 prefixEnd_5340113 2742044718323170517028773 := by
  unfold tailWord_5340113
  simp only [CollatzResearch.WordTrace]
  refine ⟨194769922102690094535992993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129846614735126729690661995 194769922102690094535992993)
  ·
    refine ⟨146077441577017570901994745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194769922102690094535992993 146077441577017570901994745)
    ·
      refine ⟨109558081182763178176496059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146077441577017570901994745 109558081182763178176496059)
      ·
        refine ⟨164337121774144767264744089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109558081182763178176496059 164337121774144767264744089)
        ·
          refine ⟨123252841330608575448558067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164337121774144767264744089 123252841330608575448558067)
          ·
            refine ⟨184879261995912863172837101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123252841330608575448558067 184879261995912863172837101)
            ·
              refine ⟨69329723248467323689813913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184879261995912863172837101 69329723248467323689813913)
              ·
                refine ⟨51997292436350492767360435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69329723248467323689813913 51997292436350492767360435)
                ·
                  refine ⟨77995938654525739151040653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51997292436350492767360435 77995938654525739151040653)
                  ·
                    refine ⟨29248476995447152181640245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77995938654525739151040653 29248476995447152181640245)
                    ·
                      refine ⟨2742044718323170517028773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29248476995447152181640245 2742044718323170517028773)
                      ·
                        rfl

theorem cell23_5340113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_5340113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340113 prefixEnd_5340113 := by exact prefixLift 5340113
  have htrace : WordTrace (prefixWord ++ tailWord_5340113) baseStart_5340113 baseEnd_5340113 := by
    simpa [prefixWord, tailWord_5340113, baseEnd_5340113] using wordTrace_append hprefix tailTrace_5340113
  have hstable : (prefixWord ++ tailWord_5340113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340113).length < 2 ^ (prefixWord ++ tailWord_5340113).sum := by decide
  have hdescent : baseEnd_5340113 < baseStart_5340113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340121 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 2, 1, 3]
def baseStart_5340121 : Nat := 118140960795 + 5340121 * 2 ^ 59
def prefixEnd_5340121 : Nat := 4983230072969 + 3 ^ 40 * 5340121 * 2
def baseEnd_5340121 : Nat := 2742048826168406485728737

theorem tailTrace_5340121 : CollatzResearch.WordTrace tailWord_5340121 prefixEnd_5340121 2742048826168406485728737 := by
  unfold tailWord_5340121
  simp only [CollatzResearch.WordTrace]
  refine ⟨194770213886661111902284217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129846809257774074601522811 194770213886661111902284217)
  ·
    refine ⟨146077660414995833926713163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194770213886661111902284217 146077660414995833926713163)
    ·
      refine ⟨219116490622493750890069745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146077660414995833926713163 219116490622493750890069745)
      ·
        refine ⟨164337367966870313167552309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219116490622493750890069745 164337367966870313167552309)
        ·
          refine ⟨15406628246894091859458029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164337367966870313167552309 15406628246894091859458029)
          ·
            refine ⟨5777485592585284447296761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15406628246894091859458029 5777485592585284447296761)
            ·
              refine ⟨4333114194438963335472571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777485592585284447296761 4333114194438963335472571)
              ·
                refine ⟨6499671291658445003208857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333114194438963335472571 6499671291658445003208857)
                ·
                  refine ⟨4874753468743833752406643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6499671291658445003208857 4874753468743833752406643)
                  ·
                    refine ⟨7312130203115750628609965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4874753468743833752406643 7312130203115750628609965)
                    ·
                      refine ⟨2742048826168406485728737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7312130203115750628609965 2742048826168406485728737)
                      ·
                        rfl

theorem cell23_5340121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_5340121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340121 prefixEnd_5340121 := by exact prefixLift 5340121
  have htrace : WordTrace (prefixWord ++ tailWord_5340121) baseStart_5340121 baseEnd_5340121 := by
    simpa [prefixWord, tailWord_5340121, baseEnd_5340121] using wordTrace_append hprefix tailTrace_5340121
  have hstable : (prefixWord ++ tailWord_5340121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340121).length < 2 ^ (prefixWord ++ tailWord_5340121).sum := by decide
  have hdescent : baseEnd_5340121 < baseStart_5340121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340161 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_5340161 : Nat := 118140960795 + 5340161 * 2 ^ 59
def prefixEnd_5340161 : Nat := 4983230072969 + 3 ^ 40 * 5340161 * 2
def baseEnd_5340161 : Nat := 2742069365394586329228553

theorem tailTrace_5340161 : CollatzResearch.WordTrace tailWord_5340161 prefixEnd_5340161 2742069365394586329228553 := by
  unfold tailWord_5340161
  simp only [CollatzResearch.WordTrace]
  refine ⟨194771672806516198733740337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129847781871010799155826891 194771672806516198733740337)
  ·
    refine ⟨146078754604887149050305253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194771672806516198733740337 146078754604887149050305253)
    ·
      refine ⟨27389766488416340446932235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146078754604887149050305253 27389766488416340446932235)
      ·
        refine ⟨41084649732624510670398353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27389766488416340446932235 41084649732624510670398353)
        ·
          refine ⟨30813487299468383002798765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41084649732624510670398353 30813487299468383002798765)
          ·
            refine ⟨11555057737300643626049537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30813487299468383002798765 11555057737300643626049537)
            ·
              refine ⟨8666293302975482719537153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11555057737300643626049537 8666293302975482719537153)
              ·
                refine ⟨6499719977231612039652865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8666293302975482719537153 6499719977231612039652865)
                ·
                  refine ⟨4874789982923709029739649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6499719977231612039652865 4874789982923709029739649)
                  ·
                    refine ⟨3656092487192781772304737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4874789982923709029739649 3656092487192781772304737)
                    ·
                      refine ⟨2742069365394586329228553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656092487192781772304737 2742069365394586329228553)
                      ·
                        rfl

theorem cell23_5340161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_5340161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340161 prefixEnd_5340161 := by exact prefixLift 5340161
  have htrace : WordTrace (prefixWord ++ tailWord_5340161) baseStart_5340161 baseEnd_5340161 := by
    simpa [prefixWord, tailWord_5340161, baseEnd_5340161] using wordTrace_append hprefix tailTrace_5340161
  have hstable : (prefixWord ++ tailWord_5340161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340161).length < 2 ^ (prefixWord ++ tailWord_5340161).sum := by decide
  have hdescent : baseEnd_5340161 < baseStart_5340161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340163 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 5, 7]
def baseStart_5340163 : Nat := 118140960795 + 5340163 * 2 ^ 59
def prefixEnd_5340163 : Nat := 4983230072969 + 3 ^ 40 * 5340163 * 2
def baseEnd_5340163 : Nat := 914023464118631773801181

theorem tailTrace_5340163 : CollatzResearch.WordTrace tailWord_5340163 prefixEnd_5340163 914023464118631773801181 := by
  unfold tailWord_5340163
  simp only [CollatzResearch.WordTrace]
  refine ⟨194771745752508953075313143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129847830501672635383542095 194771745752508953075313143)
  ·
    refine ⟨292157618628763429612969715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194771745752508953075313143 292157618628763429612969715)
    ·
      refine ⟨438236427943145144419454573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292157618628763429612969715 438236427943145144419454573)
      ·
        refine ⟨164338660478679429157295465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438236427943145144419454573 164338660478679429157295465)
        ·
          refine ⟨123253995359009571867971599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164338660478679429157295465 123253995359009571867971599)
          ·
            refine ⟨184880993038514357801957399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123253995359009571867971599 184880993038514357801957399)
            ·
              refine ⟨277321489557771536702936099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184880993038514357801957399 277321489557771536702936099)
              ·
                refine ⟨415982234336657305054404149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277321489557771536702936099 415982234336657305054404149)
                ·
                  refine ⟨38998334469061622348850389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415982234336657305054404149 38998334469061622348850389)
                  ·
                    refine ⟨914023464118631773801181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38998334469061622348850389 914023464118631773801181)
                    ·
                      rfl

theorem cell23_5340163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_5340163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340163 prefixEnd_5340163 := by exact prefixLift 5340163
  have htrace : WordTrace (prefixWord ++ tailWord_5340163) baseStart_5340163 baseEnd_5340163 := by
    simpa [prefixWord, tailWord_5340163, baseEnd_5340163] using wordTrace_append hprefix tailTrace_5340163
  have hstable : (prefixWord ++ tailWord_5340163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340163).length < 2 ^ (prefixWord ++ tailWord_5340163).sum := by decide
  have hdescent : baseEnd_5340163 < baseStart_5340163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340167 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 5]
def baseStart_5340167 : Nat := 118140960795 + 5340167 * 2 ^ 59
def prefixEnd_5340167 : Nat := 4983230072969 + 3 ^ 40 * 5340167 * 2
def baseEnd_5340167 : Nat := 304674716253168145083725

theorem tailTrace_5340167 : CollatzResearch.WordTrace tailWord_5340167 prefixEnd_5340167 304674716253168145083725 := by
  unfold tailWord_5340167
  simp only [CollatzResearch.WordTrace]
  refine ⟨194771891644494461758458755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129847927762996307838972503 194771891644494461758458755)
  ·
    refine ⟨292157837466741692637688133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194771891644494461758458755 292157837466741692637688133)
    ·
      refine ⟨54779594525014067369566525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292157837466741692637688133 54779594525014067369566525)
      ·
        refine ⟨20542347946880275263587447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54779594525014067369566525 20542347946880275263587447)
        ·
          refine ⟨30813521920320412895381171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20542347946880275263587447 30813521920320412895381171)
          ·
            refine ⟨46220282880480619343071757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30813521920320412895381171 46220282880480619343071757)
            ·
              refine ⟨17332606080180232253651909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46220282880480619343071757 17332606080180232253651909)
              ·
                refine ⟨3249863640033793547559733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17332606080180232253651909 3249863640033793547559733)
                ·
                  refine ⟨304674716253168145083725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3249863640033793547559733 304674716253168145083725)
                  ·
                    rfl

theorem cell23_5340167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 5].length) (baseStart_5340167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340167 prefixEnd_5340167 := by exact prefixLift 5340167
  have htrace : WordTrace (prefixWord ++ tailWord_5340167) baseStart_5340167 baseEnd_5340167 := by
    simpa [prefixWord, tailWord_5340167, baseEnd_5340167] using wordTrace_append hprefix tailTrace_5340167
  have hstable : (prefixWord ++ tailWord_5340167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340167).length < 2 ^ (prefixWord ++ tailWord_5340167).sum := by decide
  have hdescent : baseEnd_5340167 < baseStart_5340167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340227 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 3, 4]
def baseStart_5340227 : Nat := 118140960795 + 5340227 * 2 ^ 59
def prefixEnd_5340227 : Nat := 4983230072969 + 3 ^ 40 * 5340227 * 2
def baseEnd_5340227 : Nat := 914034418372594357001083

theorem tailTrace_5340227 : CollatzResearch.WordTrace tailWord_5340227 prefixEnd_5340227 914034418372594357001083 := by
  unfold tailWord_5340227
  simp only [CollatzResearch.WordTrace]
  refine ⟨194774080024277092005642935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129849386682851394670428623 194774080024277092005642935)
  ·
    refine ⟨292161120036415638008464403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194774080024277092005642935 292161120036415638008464403)
    ·
      refine ⟨438241680054623457012696605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292161120036415638008464403 438241680054623457012696605)
      ·
        refine ⟨164340630020483796379761227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438241680054623457012696605 164340630020483796379761227)
        ·
          refine ⟨246510945030725694569641841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164340630020483796379761227 246510945030725694569641841)
          ·
            refine ⟨184883208773044270927231381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246510945030725694569641841 184883208773044270927231381)
            ·
              refine ⟨8666400411236450199713971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184883208773044270927231381 8666400411236450199713971)
              ·
                refine ⟨12999600616854675299570957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8666400411236450199713971 12999600616854675299570957)
                ·
                  refine ⟨4874850231320503237339109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12999600616854675299570957 4874850231320503237339109)
                  ·
                    refine ⟨914034418372594357001083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4874850231320503237339109 914034418372594357001083)
                    ·
                      rfl

theorem cell23_5340227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 4].length) (baseStart_5340227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340227 prefixEnd_5340227 := by exact prefixLift 5340227
  have htrace : WordTrace (prefixWord ++ tailWord_5340227) baseStart_5340227 baseEnd_5340227 := by
    simpa [prefixWord, tailWord_5340227, baseEnd_5340227] using wordTrace_append hprefix tailTrace_5340227
  have hstable : (prefixWord ++ tailWord_5340227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340227).length < 2 ^ (prefixWord ++ tailWord_5340227).sum := by decide
  have hdescent : baseEnd_5340227 < baseStart_5340227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340240 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 6]
def baseStart_5340240 : Nat := 118140960795 + 5340240 * 2 ^ 59
def prefixEnd_5340240 : Nat := 4983230072969 + 3 ^ 40 * 5340240 * 2
def baseEnd_5340240 : Nat := 304678881151810168904521

theorem tailTrace_5340240 : CollatzResearch.WordTrace tailWord_5340240 prefixEnd_5340240 304678881151810168904521 := by
  unfold tailWord_5340240
  simp only [CollatzResearch.WordTrace]
  refine ⟨97387277086614997612933087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129849702782153330150577449 97387277086614997612933087)
  ·
    refine ⟨146080915629922496419399631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97387277086614997612933087 146080915629922496419399631)
    ·
      refine ⟨219121373444883744629099447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146080915629922496419399631 219121373444883744629099447)
      ·
        refine ⟨328682060167325616943649171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219121373444883744629099447 328682060167325616943649171)
        ·
          refine ⟨493023090250988425415473757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328682060167325616943649171 493023090250988425415473757)
          ·
            refine ⟨184883658844120659530802659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493023090250988425415473757 184883658844120659530802659)
            ·
              refine ⟨277325488266180989296203989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184883658844120659530802659 277325488266180989296203989)
              ·
                refine ⟨6499816131238616936629781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 277325488266180989296203989 6499816131238616936629781)
                ·
                  refine ⟨304678881151810168904521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6499816131238616936629781 304678881151810168904521)
                  ·
                    rfl

theorem cell23_5340240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_5340240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340240 prefixEnd_5340240 := by exact prefixLift 5340240
  have htrace : WordTrace (prefixWord ++ tailWord_5340240) baseStart_5340240 baseEnd_5340240 := by
    simpa [prefixWord, tailWord_5340240, baseEnd_5340240] using wordTrace_append hprefix tailTrace_5340240
  have hstable : (prefixWord ++ tailWord_5340240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340240).length < 2 ^ (prefixWord ++ tailWord_5340240).sum := by decide
  have hdescent : baseEnd_5340240 < baseStart_5340240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340278 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_5340278 : Nat := 118140960795 + 5340278 * 2 ^ 59
def prefixEnd_5340278 : Nat := 4983230072969 + 3 ^ 40 * 5340278 * 2
def baseEnd_5340278 : Nat := 914043147543720790488505

theorem tailTrace_5340278 : CollatzResearch.WordTrace tailWord_5340278 prefixEnd_5340278 914043147543720790488505 := by
  unfold tailWord_5340278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12173496259193270482234343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129850626764728218477166325 12173496259193270482234343)
  ·
    refine ⟨18260244388789905723351515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12173496259193270482234343 18260244388789905723351515)
    ·
      refine ⟨27390366583184858585027273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18260244388789905723351515 27390366583184858585027273)
      ·
        refine ⟨20542774937388643938770455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27390366583184858585027273 20542774937388643938770455)
        ·
          refine ⟨30814162406082965908155683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20542774937388643938770455 30814162406082965908155683)
          ·
            refine ⟨46221243609124448862233525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30814162406082965908155683 46221243609124448862233525)
            ·
              refine ⟨4333241588355417080834393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46221243609124448862233525 4333241588355417080834393)
              ·
                refine ⟨3249931191266562810625795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333241588355417080834393 3249931191266562810625795)
                ·
                  refine ⟨4874896786899844215938693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249931191266562810625795 4874896786899844215938693)
                  ·
                    refine ⟨914043147543720790488505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4874896786899844215938693 914043147543720790488505)
                    ·
                      rfl

theorem cell23_5340278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_5340278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340278 prefixEnd_5340278 := by exact prefixLift 5340278
  have htrace : WordTrace (prefixWord ++ tailWord_5340278) baseStart_5340278 baseEnd_5340278 := by
    simpa [prefixWord, tailWord_5340278, baseEnd_5340278] using wordTrace_append hprefix tailTrace_5340278
  have hstable : (prefixWord ++ tailWord_5340278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340278).length < 2 ^ (prefixWord ++ tailWord_5340278).sum := by decide
  have hdescent : baseEnd_5340278 < baseStart_5340278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340300 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_5340300 : Nat := 118140960795 + 5340300 * 2 ^ 59
def prefixEnd_5340300 : Nat := 4983230072969 + 3 ^ 40 * 5340300 * 2
def baseEnd_5340300 : Nat := 914046913068520428463471

theorem tailTrace_5340300 : CollatzResearch.WordTrace tailWord_5340300 prefixEnd_5340300 914046913068520428463471 := by
  unfold tailWord_5340300
  simp only [CollatzResearch.WordTrace]
  refine ⟨97388371276506312736525177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129851161702008416982033569 97388371276506312736525177)
  ·
    refine ⟨73041278457379734552393883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97388371276506312736525177 73041278457379734552393883)
    ·
      refine ⟨109561917686069601828590825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73041278457379734552393883 109561917686069601828590825)
      ·
        refine ⟨82171438264552201371443119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109561917686069601828590825 82171438264552201371443119)
        ·
          refine ⟨123257157396828302057164679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82171438264552201371443119 123257157396828302057164679)
          ·
            refine ⟨184885736095242453085747019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123257157396828302057164679 184885736095242453085747019)
            ·
              refine ⟨277328604142863679628620529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184885736095242453085747019 277328604142863679628620529)
              ·
                refine ⟨207996453107147759721465397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277328604142863679628620529 207996453107147759721465397)
                ·
                  refine ⟨19499667478795102473887381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207996453107147759721465397 19499667478795102473887381)
                  ·
                    refine ⟨914046913068520428463471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19499667478795102473887381 914046913068520428463471)
                    ·
                      rfl

theorem cell23_5340300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_5340300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340300 prefixEnd_5340300 := by exact prefixLift 5340300
  have htrace : WordTrace (prefixWord ++ tailWord_5340300) baseStart_5340300 baseEnd_5340300 := by
    simpa [prefixWord, tailWord_5340300, baseEnd_5340300] using wordTrace_append hprefix tailTrace_5340300
  have hstable : (prefixWord ++ tailWord_5340300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340300).length < 2 ^ (prefixWord ++ tailWord_5340300).sum := by decide
  have hdescent : baseEnd_5340300 < baseStart_5340300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340307 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 6, 2]
def baseStart_5340307 : Nat := 118140960795 + 5340307 * 2 ^ 59
def prefixEnd_5340307 : Nat := 4983230072969 + 3 ^ 40 * 5340307 * 2
def baseEnd_5340307 : Nat := 2742144333570142758002881

theorem tailTrace_5340307 : CollatzResearch.WordTrace tailWord_5340307 prefixEnd_5340307 2742144333570142758002881 := by
  unfold tailWord_5340307
  simp only [CollatzResearch.WordTrace]
  refine ⟨194776997863987265668555175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129851331909324843779036783 194776997863987265668555175)
  ·
    refine ⟨292165496795980898502832763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194776997863987265668555175 292165496795980898502832763)
    ·
      refine ⟨438248245193971347754249145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292165496795980898502832763 438248245193971347754249145)
      ·
        refine ⟨328686183895478510815686859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438248245193971347754249145 328686183895478510815686859)
        ·
          refine ⟨493029275843217766223530289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328686183895478510815686859 493029275843217766223530289)
          ·
            refine ⟨369771956882413324667647717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493029275843217766223530289 369771956882413324667647717)
            ·
              refine ⟨69332241915452498375183947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369771956882413324667647717 69332241915452498375183947)
              ·
                refine ⟨103998362873178747562775921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69332241915452498375183947 103998362873178747562775921)
                ·
                  refine ⟨77998772154884060672081941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103998362873178747562775921 77998772154884060672081941)
                  ·
                    refine ⟨3656192444760190344003841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77998772154884060672081941 3656192444760190344003841)
                    ·
                      refine ⟨2742144333570142758002881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656192444760190344003841 2742144333570142758002881)
                      ·
                        rfl

theorem cell23_5340307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6, 2].length) (baseStart_5340307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340307 prefixEnd_5340307 := by exact prefixLift 5340307
  have htrace : WordTrace (prefixWord ++ tailWord_5340307) baseStart_5340307 baseEnd_5340307 := by
    simpa [prefixWord, tailWord_5340307, baseEnd_5340307] using wordTrace_append hprefix tailTrace_5340307
  have hstable : (prefixWord ++ tailWord_5340307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340307).length < 2 ^ (prefixWord ++ tailWord_5340307).sum := by decide
  have hdescent : baseEnd_5340307 < baseStart_5340307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340311 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 2, 3, 2]
def baseStart_5340311 : Nat := 118140960795 + 5340311 * 2 ^ 59
def prefixEnd_5340311 : Nat := 4983230072969 + 3 ^ 40 * 5340311 * 2
def baseEnd_5340311 : Nat := 2742146387492760742352863

theorem tailTrace_5340311 : CollatzResearch.WordTrace tailWord_5340311 prefixEnd_5340311 2742146387492760742352863 := by
  unfold tailWord_5340311
  simp only [CollatzResearch.WordTrace]
  refine ⟨194777143755972774351700787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129851429170648516234467191 194777143755972774351700787)
  ·
    refine ⟨292165715633959161527551181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194777143755972774351700787 292165715633959161527551181)
    ·
      refine ⟨109562143362734685572831693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292165715633959161527551181 109562143362734685572831693)
      ·
        refine ⟨41085803761025507089811885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109562143362734685572831693 41085803761025507089811885)
        ·
          refine ⟨15407176410384565158679457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41085803761025507089811885 15407176410384565158679457)
          ·
            refine ⟨11555382307788423869009593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15407176410384565158679457 11555382307788423869009593)
            ·
              refine ⟨8666536730841317901757195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11555382307788423869009593 8666536730841317901757195)
              ·
                refine ⟨12999805096261976852635793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8666536730841317901757195 12999805096261976852635793)
                ·
                  refine ⟨9749853822196482639476845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12999805096261976852635793 9749853822196482639476845)
                  ·
                    refine ⟨3656195183323680989803817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9749853822196482639476845 3656195183323680989803817)
                    ·
                      refine ⟨2742146387492760742352863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656195183323680989803817 2742146387492760742352863)
                      ·
                        rfl

theorem cell23_5340311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_5340311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340311 prefixEnd_5340311 := by exact prefixLift 5340311
  have htrace : WordTrace (prefixWord ++ tailWord_5340311) baseStart_5340311 baseEnd_5340311 := by
    simpa [prefixWord, tailWord_5340311, baseEnd_5340311] using wordTrace_append hprefix tailTrace_5340311
  have hstable : (prefixWord ++ tailWord_5340311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340311).length < 2 ^ (prefixWord ++ tailWord_5340311).sum := by decide
  have hdescent : baseEnd_5340311 < baseStart_5340311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340317 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_5340317 : Nat := 118140960795 + 5340317 * 2 ^ 59
def prefixEnd_5340317 : Nat := 4983230072969 + 3 ^ 40 * 5340317 * 2
def baseEnd_5340317 : Nat := 914049822792229239625945

theorem tailTrace_5340317 : CollatzResearch.WordTrace tailWord_5340317 prefixEnd_5340317 914049822792229239625945 := by
  unfold tailWord_5340317
  simp only [CollatzResearch.WordTrace]
  refine ⟨194777362593951037376419205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129851575062634024917612803 194777362593951037376419205)
  ·
    refine ⟨36520755486365819508078601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194777362593951037376419205 36520755486365819508078601)
    ·
      refine ⟨27390566614774364631058951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36520755486365819508078601 27390566614774364631058951)
      ·
        refine ⟨41085849922161546946588427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27390566614774364631058951 41085849922161546946588427)
        ·
          refine ⟨61628774883242320419882641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41085849922161546946588427 61628774883242320419882641)
          ·
            refine ⟨46221581162431740314911981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61628774883242320419882641 46221581162431740314911981)
            ·
              refine ⟨17333092935911902618091993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46221581162431740314911981 17333092935911902618091993)
              ·
                refine ⟨12999819701933926963568995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17333092935911902618091993 12999819701933926963568995)
                ·
                  refine ⟨19499729552900890445353493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12999819701933926963568995 19499729552900890445353493)
                  ·
                    refine ⟨914049822792229239625945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19499729552900890445353493 914049822792229239625945)
                    ·
                      rfl

theorem cell23_5340317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_5340317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340317 prefixEnd_5340317 := by exact prefixLift 5340317
  have htrace : WordTrace (prefixWord ++ tailWord_5340317) baseStart_5340317 baseEnd_5340317 := by
    simpa [prefixWord, tailWord_5340317, baseEnd_5340317] using wordTrace_append hprefix tailTrace_5340317
  have hstable : (prefixWord ++ tailWord_5340317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340317).length < 2 ^ (prefixWord ++ tailWord_5340317).sum := by decide
  have hdescent : baseEnd_5340317 < baseStart_5340317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340465 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 2, 2, 2]
def baseStart_5340465 : Nat := 118140960795 + 5340465 * 2 ^ 59
def prefixEnd_5340465 : Nat := 4983230072969 + 3 ^ 40 * 5340465 * 2
def baseEnd_5340465 : Nat := 2742225463513553139827155

theorem tailTrace_5340465 : CollatzResearch.WordTrace tailWord_5340465 prefixEnd_5340465 2742225463513553139827155 := by
  unfold tailWord_5340465
  simp only [CollatzResearch.WordTrace]
  refine ⟨194782760597414858652806849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129855173731609905768537899 194782760597414858652806849)
  ·
    refine ⟨146087070448061143989605137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194782760597414858652806849 146087070448061143989605137)
    ·
      refine ⟨109565302836045857992203853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146087070448061143989605137 109565302836045857992203853)
      ·
        refine ⟨41086988563517196747076445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109565302836045857992203853 41086988563517196747076445)
        ·
          refine ⟨15407620711318948780153667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41086988563517196747076445 15407620711318948780153667)
          ·
            refine ⟨23111431066978423170230501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15407620711318948780153667 23111431066978423170230501)
            ·
              refine ⟨4333393325058454344418219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23111431066978423170230501 4333393325058454344418219)
              ·
                refine ⟨6500089987587681516627329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333393325058454344418219 6500089987587681516627329)
                ·
                  refine ⟨4875067490690761137470497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500089987587681516627329 4875067490690761137470497)
                  ·
                    refine ⟨3656300618018070853102873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4875067490690761137470497 3656300618018070853102873)
                    ·
                      refine ⟨2742225463513553139827155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656300618018070853102873 2742225463513553139827155)
                      ·
                        rfl

theorem cell23_5340465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_5340465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340465 prefixEnd_5340465 := by exact prefixLift 5340465
  have htrace : WordTrace (prefixWord ++ tailWord_5340465) baseStart_5340465 baseEnd_5340465 := by
    simpa [prefixWord, tailWord_5340465, baseEnd_5340465] using wordTrace_append hprefix tailTrace_5340465
  have hstable : (prefixWord ++ tailWord_5340465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340465).length < 2 ^ (prefixWord ++ tailWord_5340465).sum := by decide
  have hdescent : baseEnd_5340465 < baseStart_5340465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340504 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_5340504 : Nat := 118140960795 + 5340504 * 2 ^ 59
def prefixEnd_5340504 : Nat := 4983230072969 + 3 ^ 40 * 5340504 * 2
def baseEnd_5340504 : Nat := 2742245489259078487239475

theorem tailTrace_5340504 : CollatzResearch.WordTrace tailWord_5340504 prefixEnd_5340504 2742245489259078487239475 := by
  unfold tailWord_5340504
  simp only [CollatzResearch.WordTrace]
  refine ⟨97392091522136784156738283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129856122029515712208984377 97392091522136784156738283)
  ·
    refine ⟨146088137283205176235107425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97392091522136784156738283 146088137283205176235107425)
    ·
      refine ⟨109566102962403882176330569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146088137283205176235107425 109566102962403882176330569)
      ·
        refine ⟨82174577221802911632247927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109566102962403882176330569 82174577221802911632247927)
        ·
          refine ⟨123261865832704367448371891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82174577221802911632247927 123261865832704367448371891)
          ·
            refine ⟨184892798749056551172557837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123261865832704367448371891 184892798749056551172557837)
            ·
              refine ⟨69334799530896206689709189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184892798749056551172557837 69334799530896206689709189)
              ·
                refine ⟨13000274912043038754320473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69334799530896206689709189 13000274912043038754320473)
                ·
                  refine ⟨9750206184032279065740355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13000274912043038754320473 9750206184032279065740355)
                  ·
                    refine ⟨14625309276048418598610533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9750206184032279065740355 14625309276048418598610533)
                    ·
                      refine ⟨2742245489259078487239475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14625309276048418598610533 2742245489259078487239475)
                      ·
                        rfl

theorem cell23_5340504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_5340504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340504 prefixEnd_5340504 := by exact prefixLift 5340504
  have htrace : WordTrace (prefixWord ++ tailWord_5340504) baseStart_5340504 baseEnd_5340504 := by
    simpa [prefixWord, tailWord_5340504, baseEnd_5340504] using wordTrace_append hprefix tailTrace_5340504
  have hstable : (prefixWord ++ tailWord_5340504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340504).length < 2 ^ (prefixWord ++ tailWord_5340504).sum := by decide
  have hdescent : baseEnd_5340504 < baseStart_5340504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340548 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_5340548 : Nat := 118140960795 + 5340548 * 2 ^ 59
def prefixEnd_5340548 : Nat := 4983230072969 + 3 ^ 40 * 5340548 * 2
def baseEnd_5340548 : Nat := 914089360802625438363091

theorem tailTrace_5340548 : CollatzResearch.WordTrace tailWord_5340548 prefixEnd_5340548 914089360802625438363091 := by
  unfold tailWord_5340548
  simp only [CollatzResearch.WordTrace]
  refine ⟨97392893928057081914039149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129857191904076109218718865 97392893928057081914039149)
  ·
    refine ⟨36522335223021405717764681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97392893928057081914039149 36522335223021405717764681)
    ·
      refine ⟨27391751417266054288323511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36522335223021405717764681 27391751417266054288323511)
      ·
        refine ⟨41087627125899081432485267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27391751417266054288323511 41087627125899081432485267)
        ·
          refine ⟨61631440688848622148727901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41087627125899081432485267 61631440688848622148727901)
          ·
            refine ⟨23111790258318233305772963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61631440688848622148727901 23111790258318233305772963)
            ·
              refine ⟨34667685387477349958659445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23111790258318233305772963 34667685387477349958659445)
              ·
                refine ⟨3250095505076001558624323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34667685387477349958659445 3250095505076001558624323)
                ·
                  refine ⟨4875143257614002337936485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250095505076001558624323 4875143257614002337936485)
                  ·
                    refine ⟨914089360802625438363091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875143257614002337936485 914089360802625438363091)
                    ·
                      rfl

theorem cell23_5340548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_5340548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340548 prefixEnd_5340548 := by exact prefixLift 5340548
  have htrace : WordTrace (prefixWord ++ tailWord_5340548) baseStart_5340548 baseEnd_5340548 := by
    simpa [prefixWord, tailWord_5340548, baseEnd_5340548] using wordTrace_append hprefix tailTrace_5340548
  have hstable : (prefixWord ++ tailWord_5340548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340548).length < 2 ^ (prefixWord ++ tailWord_5340548).sum := by decide
  have hdescent : baseEnd_5340548 < baseStart_5340548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340578 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_5340578 : Nat := 118140960795 + 5340578 * 2 ^ 59
def prefixEnd_5340578 : Nat := 4983230072969 + 3 ^ 40 * 5340578 * 2
def baseEnd_5340578 : Nat := 304698165203056799746015

theorem tailTrace_5340578 : CollatzResearch.WordTrace tailWord_5340578 prefixEnd_5340578 304698165203056799746015 := by
  unfold tailWord_5340578
  simp only [CollatzResearch.WordTrace]
  refine ⟨48696720511501369737917597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129857921364003652634446925 48696720511501369737917597)
  ·
    refine ⟨18261270191813013651719099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48696720511501369737917597 18261270191813013651719099)
    ·
      refine ⟨27391905287719520477578649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18261270191813013651719099 27391905287719520477578649)
      ·
        refine ⟨20543928965789640358183987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27391905287719520477578649 20543928965789640358183987)
        ·
          refine ⟨30815893448684460537275981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20543928965789640358183987 30815893448684460537275981)
          ·
            refine ⟨11555960043256672701478493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30815893448684460537275981 11555960043256672701478493)
            ·
              refine ⟨4333485016221252263054435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11555960043256672701478493 4333485016221252263054435)
              ·
                refine ⟨6500227524331878394581653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333485016221252263054435 6500227524331878394581653)
                ·
                  refine ⟨304698165203056799746015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6500227524331878394581653 304698165203056799746015)
                  ·
                    rfl

theorem cell23_5340578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_5340578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340578 prefixEnd_5340578 := by exact prefixLift 5340578
  have htrace : WordTrace (prefixWord ++ tailWord_5340578) baseStart_5340578 baseEnd_5340578 := by
    simpa [prefixWord, tailWord_5340578, baseEnd_5340578] using wordTrace_append hprefix tailTrace_5340578
  have hstable : (prefixWord ++ tailWord_5340578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340578).length < 2 ^ (prefixWord ++ tailWord_5340578).sum := by decide
  have hdescent : baseEnd_5340578 < baseStart_5340578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340581 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 6, 3, 2]
def baseStart_5340581 : Nat := 118140960795 + 5340581 * 2 ^ 59
def prefixEnd_5340581 : Nat := 4983230072969 + 3 ^ 40 * 5340581 * 2
def baseEnd_5340581 : Nat := 2742285027269474685976621

theorem tailTrace_5340581 : CollatzResearch.WordTrace tailWord_5340581 prefixEnd_5340581 2742285027269474685976621 := by
  unfold tailWord_5340581
  simp only [CollatzResearch.WordTrace]
  refine ⟨194786991464994610464029597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129857994309996406976019731 194786991464994610464029597)
  ·
    refine ⟨73045121799372978924011099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194786991464994610464029597 73045121799372978924011099)
    ·
      refine ⟨109567682699059468386016649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73045121799372978924011099 109567682699059468386016649)
      ·
        refine ⟨82175762024294601289512487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109567682699059468386016649 82175762024294601289512487)
        ·
          refine ⟨123263643036441901934268731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82175762024294601289512487 123263643036441901934268731)
          ·
            refine ⟨184895464554662852901403097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123263643036441901934268731 184895464554662852901403097)
            ·
              refine ⟨138671598415997139676052323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184895464554662852901403097 138671598415997139676052323)
              ·
                refine ⟨208007397623995709514078485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138671598415997139676052323 208007397623995709514078485)
                ·
                  refine ⟨9750346763624798883472429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208007397623995709514078485 9750346763624798883472429)
                  ·
                    refine ⟨3656380036359299581302161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9750346763624798883472429 3656380036359299581302161)
                    ·
                      refine ⟨2742285027269474685976621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656380036359299581302161 2742285027269474685976621)
                      ·
                        rfl

theorem cell23_5340581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_5340581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340581 prefixEnd_5340581 := by exact prefixLift 5340581
  have htrace : WordTrace (prefixWord ++ tailWord_5340581) baseStart_5340581 baseEnd_5340581 := by
    simpa [prefixWord, tailWord_5340581, baseEnd_5340581] using wordTrace_append hprefix tailTrace_5340581
  have hstable : (prefixWord ++ tailWord_5340581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340581).length < 2 ^ (prefixWord ++ tailWord_5340581).sum := by decide
  have hdescent : baseEnd_5340581 < baseStart_5340581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340611 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 4]
def baseStart_5340611 : Nat := 118140960795 + 5340611 * 2 ^ 59
def prefixEnd_5340611 : Nat := 4983230072969 + 3 ^ 40 * 5340611 * 2
def baseEnd_5340611 : Nat := 2742300431689109568601483

theorem tailTrace_5340611 : CollatzResearch.WordTrace tailWord_5340611 prefixEnd_5340611 2742300431689109568601483 := by
  unfold tailWord_5340611
  simp only [CollatzResearch.WordTrace]
  refine ⟨194788085654885925587621687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129858723769923950391747791 194788085654885925587621687)
  ·
    refine ⟨292182128482328888381432531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194788085654885925587621687 292182128482328888381432531)
    ·
      refine ⟨438273192723493332572148797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292182128482328888381432531 438273192723493332572148797)
      ·
        refine ⟨164352447271309999714555799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438273192723493332572148797 164352447271309999714555799)
        ·
          refine ⟨246528670906964999571833699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164352447271309999714555799 246528670906964999571833699)
          ·
            refine ⟨369793006360447499357750549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246528670906964999571833699 369793006360447499357750549)
            ·
              refine ⟨17334047173145976532394557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 369793006360447499357750549 17334047173145976532394557)
              ·
                refine ⟨6500267689929741199647959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17334047173145976532394557 6500267689929741199647959)
                ·
                  refine ⟨9750401534894611799471939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6500267689929741199647959 9750401534894611799471939)
                  ·
                    refine ⟨14625602302341917699207909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9750401534894611799471939 14625602302341917699207909)
                    ·
                      refine ⟨2742300431689109568601483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14625602302341917699207909 2742300431689109568601483)
                      ·
                        rfl

theorem cell23_5340611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_5340611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340611 prefixEnd_5340611 := by exact prefixLift 5340611
  have htrace : WordTrace (prefixWord ++ tailWord_5340611) baseStart_5340611 baseEnd_5340611 := by
    simpa [prefixWord, tailWord_5340611, baseEnd_5340611] using wordTrace_append hprefix tailTrace_5340611
  have hstable : (prefixWord ++ tailWord_5340611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340611).length < 2 ^ (prefixWord ++ tailWord_5340611).sum := by decide
  have hdescent : baseEnd_5340611 < baseStart_5340611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340624 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_5340624 : Nat := 118140960795 + 5340624 * 2 ^ 59
def prefixEnd_5340624 : Nat := 4983230072969 + 3 ^ 40 * 5340624 * 2
def baseEnd_5340624 : Nat := 2742307106937618017738923

theorem tailTrace_5340624 : CollatzResearch.WordTrace tailWord_5340624 prefixEnd_5340624 2742307106937618017738923 := by
  unfold tailWord_5340624
  simp only [CollatzResearch.WordTrace]
  refine ⟨97394279901919414403922463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129859039869225885871896617 97394279901919414403922463)
  ·
    refine ⟨146091419852879121605883695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97394279901919414403922463 146091419852879121605883695)
    ·
      refine ⟨219137129779318682408825543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146091419852879121605883695 219137129779318682408825543)
      ·
        refine ⟨328705694668978023613238315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219137129779318682408825543 328705694668978023613238315)
        ·
          refine ⟨493058542003467035419857473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328705694668978023613238315 493058542003467035419857473)
          ·
            refine ⟨369793906502600276564893105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493058542003467035419857473 369793906502600276564893105)
            ·
              refine ⟨277345429876950207423669829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369793906502600276564893105 277345429876950207423669829)
              ·
                refine ⟨52002268101928163891938093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277345429876950207423669829 52002268101928163891938093)
                ·
                  refine ⟨19500850538223061459476785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52002268101928163891938093 19500850538223061459476785)
                  ·
                    refine ⟨14625637903667296094607589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19500850538223061459476785 14625637903667296094607589)
                    ·
                      refine ⟨2742307106937618017738923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14625637903667296094607589 2742307106937618017738923)
                      ·
                        rfl

theorem cell23_5340624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_5340624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340624 prefixEnd_5340624 := by exact prefixLift 5340624
  have htrace : WordTrace (prefixWord ++ tailWord_5340624) baseStart_5340624 baseEnd_5340624 := by
    simpa [prefixWord, tailWord_5340624, baseEnd_5340624] using wordTrace_append hprefix tailTrace_5340624
  have hstable : (prefixWord ++ tailWord_5340624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340624).length < 2 ^ (prefixWord ++ tailWord_5340624).sum := by decide
  have hdescent : baseEnd_5340624 < baseStart_5340624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340634 : List Nat := [3, 1, 1, 2, 3, 2, 1, 10]
def baseStart_5340634 : Nat := 118140960795 + 5340634 * 2 ^ 59
def prefixEnd_5340634 : Nat := 4983230072969 + 3 ^ 40 * 5340634 * 2
def baseEnd_5340634 : Nat := 101567120064598628837551

theorem tailTrace_5340634 : CollatzResearch.WordTrace tailWord_5340634 prefixEnd_5340634 101567120064598628837551 := by
  unfold tailWord_5340634
  simp only [CollatzResearch.WordTrace]
  refine ⟨48697231133450650128927239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129859283022535067010472637 48697231133450650128927239)
  ·
    refine ⟨73045846700175975193390859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48697231133450650128927239 73045846700175975193390859)
    ·
      refine ⟨109568770050263962790086289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73045846700175975193390859 109568770050263962790086289)
      ·
        refine ⟨82176577537697972092564717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109568770050263962790086289 82176577537697972092564717)
        ·
          refine ⟨30816216576636739534711769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82176577537697972092564717 30816216576636739534711769)
          ·
            refine ⟨23112162432477554651033827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30816216576636739534711769 23112162432477554651033827)
            ·
              refine ⟨34668243648716331976550741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23112162432477554651033827 34668243648716331976550741)
              ·
                refine ⟨101567120064598628837551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34668243648716331976550741 101567120064598628837551)
                ·
                  rfl

theorem cell23_5340634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_5340634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340634 prefixEnd_5340634 := by exact prefixLift 5340634
  have htrace : WordTrace (prefixWord ++ tailWord_5340634) baseStart_5340634 baseEnd_5340634 := by
    simpa [prefixWord, tailWord_5340634, baseEnd_5340634] using wordTrace_append hprefix tailTrace_5340634
  have hstable : (prefixWord ++ tailWord_5340634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340634).length < 2 ^ (prefixWord ++ tailWord_5340634).sum := by decide
  have hdescent : baseEnd_5340634 < baseStart_5340634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340645 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5340645 : Nat := 118140960795 + 5340645 * 2 ^ 59
def prefixEnd_5340645 : Nat := 4983230072969 + 3 ^ 40 * 5340645 * 2
def baseEnd_5340645 : Nat := 2742317890031362435576327

theorem tailTrace_5340645 : CollatzResearch.WordTrace tailWord_5340645 prefixEnd_5340645 2742317890031362435576327 := by
  unfold tailWord_5340645
  simp only [CollatzResearch.WordTrace]
  refine ⟨194789325736762749394359389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129859550491175166262906259 194789325736762749394359389)
  ·
    refine ⟨73045997151286031022884771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194789325736762749394359389 73045997151286031022884771)
    ·
      refine ⟨109568995726929046534327157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73045997151286031022884771 109568995726929046534327157)
      ·
        refine ⟨10272093349399598112593171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109568995726929046534327157 10272093349399598112593171)
        ·
          refine ⟨15408140024099397168889757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10272093349399598112593171 15408140024099397168889757)
          ·
            refine ⟨5778052509037273938333659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15408140024099397168889757 5778052509037273938333659)
            ·
              refine ⟨8667078763555910907500489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778052509037273938333659 8667078763555910907500489)
              ·
                refine ⟨6500309072666933180625367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8667078763555910907500489 6500309072666933180625367)
                ·
                  refine ⟨9750463609000399770938051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6500309072666933180625367 9750463609000399770938051)
                  ·
                    refine ⟨14625695413500599656407077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9750463609000399770938051 14625695413500599656407077)
                    ·
                      refine ⟨2742317890031362435576327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14625695413500599656407077 2742317890031362435576327)
                      ·
                        rfl

theorem cell23_5340645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5340645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340645 prefixEnd_5340645 := by exact prefixLift 5340645
  have htrace : WordTrace (prefixWord ++ tailWord_5340645) baseStart_5340645 baseEnd_5340645 := by
    simpa [prefixWord, tailWord_5340645, baseEnd_5340645] using wordTrace_append hprefix tailTrace_5340645
  have hstable : (prefixWord ++ tailWord_5340645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340645).length < 2 ^ (prefixWord ++ tailWord_5340645).sum := by decide
  have hdescent : baseEnd_5340645 < baseStart_5340645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340658 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5340658 : Nat := 118140960795 + 5340658 * 2 ^ 59
def prefixEnd_5340658 : Nat := 4983230072969 + 3 ^ 40 * 5340658 * 2
def baseEnd_5340658 : Nat := 2742324565279870884713767

theorem tailTrace_5340658 : CollatzResearch.WordTrace tailWord_5340658 prefixEnd_5340658 2742324565279870884713767 := by
  unfold tailWord_5340658
  simp only [CollatzResearch.WordTrace]
  refine ⟨48697449971428913153645657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129859866590477101743055085 48697449971428913153645657)
  ·
    refine ⟨36523087478571684865234243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48697449971428913153645657 36523087478571684865234243)
    ·
      refine ⟨54784631217857527297851365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36523087478571684865234243 54784631217857527297851365)
      ·
        refine ⟨10272118353348286368347131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54784631217857527297851365 10272118353348286368347131)
        ·
          refine ⟨15408177530022429552520697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10272118353348286368347131 15408177530022429552520697)
          ·
            refine ⟨11556133147516822164390523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15408177530022429552520697 11556133147516822164390523)
            ·
              refine ⟨17334199721275233246585785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11556133147516822164390523 17334199721275233246585785)
              ·
                refine ⟨13000649790956424934939339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17334199721275233246585785 13000649790956424934939339)
                ·
                  refine ⟨19500974686434637402409009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13000649790956424934939339 19500974686434637402409009)
                  ·
                    refine ⟨14625731014825978051806757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19500974686434637402409009 14625731014825978051806757)
                    ·
                      refine ⟨2742324565279870884713767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14625731014825978051806757 2742324565279870884713767)
                      ·
                        rfl

theorem cell23_5340658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5340658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340658 prefixEnd_5340658 := by exact prefixLift 5340658
  have htrace : WordTrace (prefixWord ++ tailWord_5340658) baseStart_5340658 baseEnd_5340658 := by
    simpa [prefixWord, tailWord_5340658, baseEnd_5340658] using wordTrace_append hprefix tailTrace_5340658
  have hstable : (prefixWord ++ tailWord_5340658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340658).length < 2 ^ (prefixWord ++ tailWord_5340658).sum := by decide
  have hdescent : baseEnd_5340658 < baseStart_5340658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340679 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_5340679 : Nat := 118140960795 + 5340679 * 2 ^ 59
def prefixEnd_5340679 : Nat := 4983230072969 + 3 ^ 40 * 5340679 * 2
def baseEnd_5340679 : Nat := 2742335348373615302551171

theorem tailTrace_5340679 : CollatzResearch.WordTrace tailWord_5340679 prefixEnd_5340679 2742335348373615302551171 := by
  unfold tailWord_5340679
  simp only [CollatzResearch.WordTrace]
  refine ⟨194790565818639573201097091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129860377212426382134064727 194790565818639573201097091)
  ·
    refine ⟨292185848727959359801645637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194790565818639573201097091 292185848727959359801645637)
    ·
      refine ⟨54784846636492379962808557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292185848727959359801645637 54784846636492379962808557)
      ·
        refine ⟨20544317488684642486053209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54784846636492379962808557 20544317488684642486053209)
        ·
          refine ⟨15408238116513481864539907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20544317488684642486053209 15408238116513481864539907)
          ·
            refine ⟨23112357174770222796809861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15408238116513481864539907 23112357174770222796809861)
            ·
              refine ⟨4333566970269416774401849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23112357174770222796809861 4333566970269416774401849)
              ·
                refine ⟨3250175227702062580801387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333566970269416774401849 3250175227702062580801387)
                ·
                  refine ⟨4875262841553093871202081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250175227702062580801387 4875262841553093871202081)
                  ·
                    refine ⟨3656447131164820403401561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4875262841553093871202081 3656447131164820403401561)
                    ·
                      refine ⟨2742335348373615302551171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656447131164820403401561 2742335348373615302551171)
                      ·
                        rfl

theorem cell23_5340679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_5340679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340679 prefixEnd_5340679 := by exact prefixLift 5340679
  have htrace : WordTrace (prefixWord ++ tailWord_5340679) baseStart_5340679 baseEnd_5340679 := by
    simpa [prefixWord, tailWord_5340679, baseEnd_5340679] using wordTrace_append hprefix tailTrace_5340679
  have hstable : (prefixWord ++ tailWord_5340679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340679).length < 2 ^ (prefixWord ++ tailWord_5340679).sum := by decide
  have hdescent : baseEnd_5340679 < baseStart_5340679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340701 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5340701 : Nat := 118140960795 + 5340701 * 2 ^ 59
def prefixEnd_5340701 : Nat := 4983230072969 + 3 ^ 40 * 5340701 * 2
def baseEnd_5340701 : Nat := 2742346644948014216476069

theorem tailTrace_5340701 : CollatzResearch.WordTrace tailWord_5340701 prefixEnd_5340701 2742346644948014216476069 := by
  unfold tailWord_5340701
  simp only [CollatzResearch.WordTrace]
  refine ⟨194791368224559870958397957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129860912149706580638931971 194791368224559870958397957)
  ·
    refine ⟨36523381542104975804699617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194791368224559870958397957 36523381542104975804699617)
    ·
      refine ⟨27392536156578731853524713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36523381542104975804699617 27392536156578731853524713)
      ·
        refine ⟨20544402117434048890143535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27392536156578731853524713 20544402117434048890143535)
        ·
          refine ⟨30816603176151073335215303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20544402117434048890143535 30816603176151073335215303)
          ·
            refine ⟨46224904764226610002822955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30816603176151073335215303 46224904764226610002822955)
            ·
              refine ⟨69337357146339915004234433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46224904764226610002822955 69337357146339915004234433)
              ·
                refine ⟨52003017859754936253175825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69337357146339915004234433 52003017859754936253175825)
                ·
                  refine ⟨39002263394816202189881869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52003017859754936253175825 39002263394816202189881869)
                  ·
                    refine ⟨14625848773056075821205701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39002263394816202189881869 14625848773056075821205701)
                    ·
                      refine ⟨2742346644948014216476069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14625848773056075821205701 2742346644948014216476069)
                      ·
                        rfl

theorem cell23_5340701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5340701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340701 prefixEnd_5340701 := by exact prefixLift 5340701
  have htrace : WordTrace (prefixWord ++ tailWord_5340701) baseStart_5340701 baseEnd_5340701 := by
    simpa [prefixWord, tailWord_5340701, baseEnd_5340701] using wordTrace_append hprefix tailTrace_5340701
  have hstable : (prefixWord ++ tailWord_5340701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340701).length < 2 ^ (prefixWord ++ tailWord_5340701).sum := by decide
  have hdescent : baseEnd_5340701 < baseStart_5340701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340735 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 4, 2, 2]
def baseStart_5340735 : Nat := 118140960795 + 5340735 * 2 ^ 59
def prefixEnd_5340735 : Nat := 4983230072969 + 3 ^ 40 * 5340735 * 2
def baseEnd_5340735 : Nat := 2742364103290267083450913

theorem tailTrace_5340735 : CollatzResearch.WordTrace tailWord_5340735 prefixEnd_5340735 2742364103290267083450913 := by
  unfold tailWord_5340735
  simp only [CollatzResearch.WordTrace]
  refine ⟨194792608306436694765135659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129861738870957796510090439 194792608306436694765135659)
  ·
    refine ⟨292188912459655042147703489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194792608306436694765135659 292188912459655042147703489)
    ·
      refine ⟨219141684344741281610777617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292188912459655042147703489 219141684344741281610777617)
      ·
        refine ⟨164356263258555961208083213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219141684344741281610777617 164356263258555961208083213)
        ·
          refine ⟨61633598721958485453031205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164356263258555961208083213 61633598721958485453031205)
          ·
            refine ⟨11556299760367216022443351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61633598721958485453031205 11556299760367216022443351)
            ·
              refine ⟨17334449640550824033665027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11556299760367216022443351 17334449640550824033665027)
              ·
                refine ⟨26001674460826236050497541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17334449640550824033665027 26001674460826236050497541)
                ·
                  refine ⟨4875313961404919259468289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26001674460826236050497541 4875313961404919259468289)
                  ·
                    refine ⟨3656485471053689444601217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4875313961404919259468289 3656485471053689444601217)
                    ·
                      refine ⟨2742364103290267083450913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656485471053689444601217 2742364103290267083450913)
                      ·
                        rfl

theorem cell23_5340735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_5340735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340735 prefixEnd_5340735 := by exact prefixLift 5340735
  have htrace : WordTrace (prefixWord ++ tailWord_5340735) baseStart_5340735 baseEnd_5340735 := by
    simpa [prefixWord, tailWord_5340735, baseEnd_5340735] using wordTrace_append hprefix tailTrace_5340735
  have hstable : (prefixWord ++ tailWord_5340735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340735).length < 2 ^ (prefixWord ++ tailWord_5340735).sum := by decide
  have hdescent : baseEnd_5340735 < baseStart_5340735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340741 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 7]
def baseStart_5340741 : Nat := 118140960795 + 5340741 * 2 ^ 59
def prefixEnd_5340741 : Nat := 4983230072969 + 3 ^ 40 * 5340741 * 2
def baseEnd_5340741 : Nat := 304707464908243784441765

theorem tailTrace_5340741 : CollatzResearch.WordTrace tailWord_5340741 prefixEnd_5340741 304707464908243784441765 := by
  unfold tailWord_5340741
  simp only [CollatzResearch.WordTrace]
  refine ⟨194792827144414957789854077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129861884762943305193236051 194792827144414957789854077)
  ·
    refine ⟨73047310179155609171195279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194792827144414957789854077 73047310179155609171195279)
    ·
      refine ⟨109570965268733413756792919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73047310179155609171195279 109570965268733413756792919)
      ·
        refine ⟨164356447903100120635189379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109570965268733413756792919 164356447903100120635189379)
        ·
          refine ⟨246534671854650180952784069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164356447903100120635189379 246534671854650180952784069)
          ·
            refine ⟨46225250972746908928647013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246534671854650180952784069 46225250972746908928647013)
            ·
              refine ⟨8667234557390045424121315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46225250972746908928647013 8667234557390045424121315)
              ·
                refine ⟨13000851836085068136181973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667234557390045424121315 13000851836085068136181973)
                ·
                  refine ⟨304707464908243784441765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13000851836085068136181973 304707464908243784441765)
                  ·
                    rfl

theorem cell23_5340741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_5340741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340741 prefixEnd_5340741 := by exact prefixLift 5340741
  have htrace : WordTrace (prefixWord ++ tailWord_5340741) baseStart_5340741 baseEnd_5340741 := by
    simpa [prefixWord, tailWord_5340741, baseEnd_5340741] using wordTrace_append hprefix tailTrace_5340741
  have hstable : (prefixWord ++ tailWord_5340741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340741).length < 2 ^ (prefixWord ++ tailWord_5340741).sum := by decide
  have hdescent : baseEnd_5340741 < baseStart_5340741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340752 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 2, 2, 2]
def baseStart_5340752 : Nat := 118140960795 + 5340752 * 2 ^ 59
def prefixEnd_5340752 : Nat := 4983230072969 + 3 ^ 40 * 5340752 * 2
def baseEnd_5340752 : Nat := 2742372832461393516938335

theorem tailTrace_5340752 : CollatzResearch.WordTrace tailWord_5340752 prefixEnd_5340752 2742372832461393516938335 := by
  unfold tailWord_5340752
  simp only [CollatzResearch.WordTrace]
  refine ⟨97396614173687553334252255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129862152231583404445669673 97396614173687553334252255)
  ·
    refine ⟨146094921260531330001378383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97396614173687553334252255 146094921260531330001378383)
    ·
      refine ⟨219142381890796995002067575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146094921260531330001378383 219142381890796995002067575)
      ·
        refine ⟨328713572836195492503101363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219142381890796995002067575 328713572836195492503101363)
        ·
          refine ⟨493070359254293238754652045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328713572836195492503101363 493070359254293238754652045)
          ·
            refine ⟨184901384720359964532994517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493070359254293238754652045 184901384720359964532994517)
            ·
              refine ⟨4333626204383436668742059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184901384720359964532994517 4333626204383436668742059)
              ·
                refine ⟨6500439306575155003113089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333626204383436668742059 6500439306575155003113089)
                ·
                  refine ⟨4875329479931366252334817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500439306575155003113089 4875329479931366252334817)
                  ·
                    refine ⟨3656497109948524689251113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4875329479931366252334817 3656497109948524689251113)
                    ·
                      refine ⟨2742372832461393516938335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656497109948524689251113 2742372832461393516938335)
                      ·
                        rfl

theorem cell23_5340752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 2, 2].length) (baseStart_5340752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340752 prefixEnd_5340752 := by exact prefixLift 5340752
  have htrace : WordTrace (prefixWord ++ tailWord_5340752) baseStart_5340752 baseEnd_5340752 := by
    simpa [prefixWord, tailWord_5340752, baseEnd_5340752] using wordTrace_append hprefix tailTrace_5340752
  have hstable : (prefixWord ++ tailWord_5340752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340752).length < 2 ^ (prefixWord ++ tailWord_5340752).sum := by decide
  have hdescent : baseEnd_5340752 < baseStart_5340752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340771 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 1, 7]
def baseStart_5340771 : Nat := 118140960795 + 5340771 * 2 ^ 59
def prefixEnd_5340771 : Nat := 4983230072969 + 3 ^ 40 * 5340771 * 2
def baseEnd_5340771 : Nat := 914127529531276314200249

theorem tailTrace_5340771 : CollatzResearch.WordTrace tailWord_5340771 prefixEnd_5340771 914127529531276314200249 := by
  unfold tailWord_5340771
  simp only [CollatzResearch.WordTrace]
  refine ⟨194793921334306272913446167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129862614222870848608964111 194793921334306272913446167)
  ·
    refine ⟨292190882001459409370169251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194793921334306272913446167 292190882001459409370169251)
    ·
      refine ⟨438286323002189114055253877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292190882001459409370169251 438286323002189114055253877)
      ·
        refine ⟨41089342781455229442680051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 438286323002189114055253877 41089342781455229442680051)
        ·
          refine ⟨61634014172182844164020077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41089342781455229442680051 61634014172182844164020077)
          ·
            refine ⟨23112755314568566561507529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61634014172182844164020077 23112755314568566561507529)
            ·
              refine ⟨17334566485926424921130647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23112755314568566561507529 17334566485926424921130647)
              ·
                refine ⟨26001849728889637381695971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17334566485926424921130647 26001849728889637381695971)
                ·
                  refine ⟨39002774593334456072543957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26001849728889637381695971 39002774593334456072543957)
                  ·
                    refine ⟨914127529531276314200249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39002774593334456072543957 914127529531276314200249)
                    ·
                      rfl

theorem cell23_5340771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 7].length) (baseStart_5340771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340771 prefixEnd_5340771 := by exact prefixLift 5340771
  have htrace : WordTrace (prefixWord ++ tailWord_5340771) baseStart_5340771 baseEnd_5340771 := by
    simpa [prefixWord, tailWord_5340771, baseEnd_5340771] using wordTrace_append hprefix tailTrace_5340771
  have hstable : (prefixWord ++ tailWord_5340771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340771).length < 2 ^ (prefixWord ++ tailWord_5340771).sum := by decide
  have hdescent : baseEnd_5340771 < baseStart_5340771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340821 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_5340821 : Nat := 118140960795 + 5340821 * 2 ^ 59
def prefixEnd_5340821 : Nat := 4983230072969 + 3 ^ 40 * 5340821 * 2
def baseEnd_5340821 : Nat := 2742408262626553746975517

theorem tailTrace_5340821 : CollatzResearch.WordTrace tailWord_5340821 prefixEnd_5340821 2742408262626553746975517 := by
  unfold tailWord_5340821
  simp only [CollatzResearch.WordTrace]
  refine ⟨194795744984125131452766317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129863829989416754301844211 194795744984125131452766317)
  ·
    refine ⟨73048404369046924294787369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194795744984125131452766317 73048404369046924294787369)
    ·
      refine ⟨54786303276785193221090527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73048404369046924294787369 54786303276785193221090527)
      ·
        refine ⟨82179454915177789831635791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54786303276785193221090527 82179454915177789831635791)
        ·
          refine ⟨123269182372766684747453687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82179454915177789831635791 123269182372766684747453687)
          ·
            refine ⟨184903773559150027121180531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123269182372766684747453687 184903773559150027121180531)
            ·
              refine ⟨277355660338725040681770797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184903773559150027121180531 277355660338725040681770797)
              ·
                refine ⟨104008372627021890255664049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277355660338725040681770797 104008372627021890255664049)
                ·
                  refine ⟨78006279470266417691748037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104008372627021890255664049 78006279470266417691748037)
                  ·
                    refine ⟨14626177400674953317202757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78006279470266417691748037 14626177400674953317202757)
                    ·
                      refine ⟨2742408262626553746975517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14626177400674953317202757 2742408262626553746975517)
                      ·
                        rfl

theorem cell23_5340821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_5340821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340821 prefixEnd_5340821 := by exact prefixLift 5340821
  have htrace : WordTrace (prefixWord ++ tailWord_5340821) baseStart_5340821 baseEnd_5340821 := by
    simpa [prefixWord, tailWord_5340821, baseEnd_5340821] using wordTrace_append hprefix tailTrace_5340821
  have hstable : (prefixWord ++ tailWord_5340821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340821).length < 2 ^ (prefixWord ++ tailWord_5340821).sum := by decide
  have hdescent : baseEnd_5340821 < baseStart_5340821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340835 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 1, 4]
def baseStart_5340835 : Nat := 118140960795 + 5340835 * 2 ^ 59
def prefixEnd_5340835 : Nat := 4983230072969 + 3 ^ 40 * 5340835 * 2
def baseEnd_5340835 : Nat := 914138483785238897400151

theorem tailTrace_5340835 : CollatzResearch.WordTrace tailWord_5340835 prefixEnd_5340835 914138483785238897400151 := by
  unfold tailWord_5340835
  simp only [CollatzResearch.WordTrace]
  refine ⟨194796255606074411843775959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129864170404049607895850639 194796255606074411843775959)
  ·
    refine ⟨292194383409111617765663939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194796255606074411843775959 292194383409111617765663939)
    ·
      refine ⟨438291575113667426648495909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292194383409111617765663939 438291575113667426648495909)
      ·
        refine ⟨82179670333812642496592983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 438291575113667426648495909 82179670333812642496592983)
        ·
          refine ⟨123269505500718963744889475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82179670333812642496592983 123269505500718963744889475)
          ·
            refine ⟨184904258251078445617334213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123269505500718963744889475 184904258251078445617334213)
            ·
              refine ⟨34669548422077208553250165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184904258251078445617334213 34669548422077208553250165)
              ·
                refine ⟨3250270164569738301867203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34669548422077208553250165 3250270164569738301867203)
                ·
                  refine ⟨4875405246854607452800805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250270164569738301867203 4875405246854607452800805)
                  ·
                    refine ⟨914138483785238897400151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875405246854607452800805 914138483785238897400151)
                    ·
                      rfl

theorem cell23_5340835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 4].length) (baseStart_5340835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340835 prefixEnd_5340835 := by exact prefixLift 5340835
  have htrace : WordTrace (prefixWord ++ tailWord_5340835) baseStart_5340835 baseEnd_5340835 := by
    simpa [prefixWord, tailWord_5340835, baseEnd_5340835] using wordTrace_append hprefix tailTrace_5340835
  have hstable : (prefixWord ++ tailWord_5340835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340835).length < 2 ^ (prefixWord ++ tailWord_5340835).sum := by decide
  have hdescent : baseEnd_5340835 < baseStart_5340835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340845 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_5340845 : Nat := 118140960795 + 5340845 * 2 ^ 59
def prefixEnd_5340845 : Nat := 4983230072969 + 3 ^ 40 * 5340845 * 2
def baseEnd_5340845 : Nat := 2742420586162261653075407

theorem tailTrace_5340845 : CollatzResearch.WordTrace tailWord_5340845 prefixEnd_5340845 2742420586162261653075407 := by
  unfold tailWord_5340845
  simp only [CollatzResearch.WordTrace]
  refine ⟨194796620336038183551639989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129864413557358789034426659 194796620336038183551639989)
  ·
    refine ⟨18262183156503579707966249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194796620336038183551639989 18262183156503579707966249)
    ·
      refine ⟨13696637367377684780974687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18262183156503579707966249 13696637367377684780974687)
      ·
        refine ⟨20544956051066527171462031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13696637367377684780974687 20544956051066527171462031)
        ·
          refine ⟨30817434076599790757193047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20544956051066527171462031 30817434076599790757193047)
          ·
            refine ⟨46226151114899686135789571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30817434076599790757193047 46226151114899686135789571)
            ·
              refine ⟨69339226672349529203684357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46226151114899686135789571 69339226672349529203684357)
              ·
                refine ⟨13001105001065536725690817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69339226672349529203684357 13001105001065536725690817)
                ·
                  refine ⟨9750828750799152544268113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13001105001065536725690817 9750828750799152544268113)
                  ·
                    refine ⟨7313121563099364408201085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9750828750799152544268113 7313121563099364408201085)
                    ·
                      refine ⟨2742420586162261653075407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313121563099364408201085 2742420586162261653075407)
                      ·
                        rfl

theorem cell23_5340845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_5340845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340845 prefixEnd_5340845 := by exact prefixLift 5340845
  have htrace : WordTrace (prefixWord ++ tailWord_5340845) baseStart_5340845 baseEnd_5340845 := by
    simpa [prefixWord, tailWord_5340845, baseEnd_5340845] using wordTrace_append hprefix tailTrace_5340845
  have hstable : (prefixWord ++ tailWord_5340845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340845).length < 2 ^ (prefixWord ++ tailWord_5340845).sum := by decide
  have hdescent : baseEnd_5340845 < baseStart_5340845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340851 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_5340851 : Nat := 118140960795 + 5340851 * 2 ^ 59
def prefixEnd_5340851 : Nat := 4983230072969 + 3 ^ 40 * 5340851 * 2
def baseEnd_5340851 : Nat := 2742423667046188629600379

theorem tailTrace_5340851 : CollatzResearch.WordTrace tailWord_5340851 prefixEnd_5340851 2742423667046188629600379 := by
  unfold tailWord_5340851
  simp only [CollatzResearch.WordTrace]
  refine ⟨194796839174016446576358407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129864559449344297717572271 194796839174016446576358407)
  ·
    refine ⟨292195258761024669864537611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194796839174016446576358407 292195258761024669864537611)
    ·
      refine ⟨438292888141537004796806417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292195258761024669864537611 438292888141537004796806417)
      ·
        refine ⟨328719666106152753597604813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438292888141537004796806417 328719666106152753597604813)
        ·
          refine ⟨123269874789807282599101805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328719666106152753597604813 123269874789807282599101805)
          ·
            refine ⟨46226203046177730974663177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123269874789807282599101805 46226203046177730974663177)
            ·
              refine ⟨34669652284633298230997383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46226203046177730974663177 34669652284633298230997383)
              ·
                refine ⟨52004478426949947346496075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34669652284633298230997383 52004478426949947346496075)
                ·
                  refine ⟨78006717640424921019744113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52004478426949947346496075 78006717640424921019744113)
                  ·
                    refine ⟨58505038230318690764808085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78006717640424921019744113 58505038230318690764808085)
                    ·
                      refine ⟨2742423667046188629600379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58505038230318690764808085 2742423667046188629600379)
                      ·
                        rfl

theorem cell23_5340851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_5340851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340851 prefixEnd_5340851 := by exact prefixLift 5340851
  have htrace : WordTrace (prefixWord ++ tailWord_5340851) baseStart_5340851 baseEnd_5340851 := by
    simpa [prefixWord, tailWord_5340851, baseEnd_5340851] using wordTrace_append hprefix tailTrace_5340851
  have hstable : (prefixWord ++ tailWord_5340851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340851).length < 2 ^ (prefixWord ++ tailWord_5340851).sum := by decide
  have hdescent : baseEnd_5340851 < baseStart_5340851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340871 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_5340871 : Nat := 118140960795 + 5340871 * 2 ^ 59
def prefixEnd_5340871 : Nat := 4983230072969 + 3 ^ 40 * 5340871 * 2
def baseEnd_5340871 : Nat := 2742433936659278551350287

theorem tailTrace_5340871 : CollatzResearch.WordTrace tailWord_5340871 prefixEnd_5340871 2742433936659278551350287 := by
  unfold tailWord_5340871
  simp only [CollatzResearch.WordTrace]
  refine ⟨194797568633943989992086467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129865045755962659994724311 194797568633943989992086467)
  ·
    refine ⟨292196352950915984988129701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194797568633943989992086467 292196352950915984988129701)
    ·
      refine ⟨54786816178296747185274319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292196352950915984988129701 54786816178296747185274319)
      ·
        refine ⟨82180224267445120777911479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54786816178296747185274319 82180224267445120777911479)
        ·
          refine ⟨123270336401167681166867219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82180224267445120777911479 123270336401167681166867219)
          ·
            refine ⟨184905504601751521750300829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123270336401167681166867219 184905504601751521750300829)
            ·
              refine ⟨69339564225656820656362811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184905504601751521750300829 69339564225656820656362811)
              ·
                refine ⟨104009346338485230984544217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69339564225656820656362811 104009346338485230984544217)
                ·
                  refine ⟨78007009753863923238408163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104009346338485230984544217 78007009753863923238408163)
                  ·
                    refine ⟨117010514630795884857612245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78007009753863923238408163 117010514630795884857612245)
                    ·
                      refine ⟨2742433936659278551350287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117010514630795884857612245 2742433936659278551350287)
                      ·
                        rfl

theorem cell23_5340871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_5340871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340871 prefixEnd_5340871 := by exact prefixLift 5340871
  have htrace : WordTrace (prefixWord ++ tailWord_5340871) baseStart_5340871 baseEnd_5340871 := by
    simpa [prefixWord, tailWord_5340871, baseEnd_5340871] using wordTrace_append hprefix tailTrace_5340871
  have hstable : (prefixWord ++ tailWord_5340871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340871).length < 2 ^ (prefixWord ++ tailWord_5340871).sum := by decide
  have hdescent : baseEnd_5340871 < baseStart_5340871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340878 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_5340878 : Nat := 118140960795 + 5340878 * 2 ^ 59
def prefixEnd_5340878 : Nat := 4983230072969 + 3 ^ 40 * 5340878 * 2
def baseEnd_5340878 : Nat := 914145843674620007987585

theorem tailTrace_5340878 : CollatzResearch.WordTrace tailWord_5340878 prefixEnd_5340878 914145843674620007987585 := by
  unfold tailWord_5340878
  simp only [CollatzResearch.WordTrace]
  refine ⟨24349727993114828773448911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129865215963279086791727525 24349727993114828773448911)
  ·
    refine ⟨36524591989672243160173367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24349727993114828773448911 36524591989672243160173367)
    ·
      refine ⟨54786887984508364740260051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36524591989672243160173367 54786887984508364740260051)
      ·
        refine ⟨82180331976762547110390077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54786887984508364740260051 82180331976762547110390077)
        ·
          refine ⟨30817624491285955166396279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82180331976762547110390077 30817624491285955166396279)
          ·
            refine ⟨46226436736928932749594419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30817624491285955166396279 46226436736928932749594419)
            ·
              refine ⟨69339655105393399124391629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46226436736928932749594419 69339655105393399124391629)
              ·
                refine ⟨26002370664522524671646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69339655105393399124391629 26002370664522524671646861)
                ·
                  refine ⟨9750888999195946751867573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26002370664522524671646861 9750888999195946751867573)
                  ·
                    refine ⟨914145843674620007987585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9750888999195946751867573 914145843674620007987585)
                    ·
                      rfl

theorem cell23_5340878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_5340878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340878 prefixEnd_5340878 := by exact prefixLift 5340878
  have htrace : WordTrace (prefixWord ++ tailWord_5340878) baseStart_5340878 baseEnd_5340878 := by
    simpa [prefixWord, tailWord_5340878, baseEnd_5340878] using wordTrace_append hprefix tailTrace_5340878
  have hstable : (prefixWord ++ tailWord_5340878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340878).length < 2 ^ (prefixWord ++ tailWord_5340878).sum := by decide
  have hdescent : baseEnd_5340878 < baseStart_5340878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340909 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5340909 : Nat := 118140960795 + 5340909 * 2 ^ 59
def prefixEnd_5340909 : Nat := 4983230072969 + 3 ^ 40 * 5340909 * 2
def baseEnd_5340909 : Nat := 2742453448924149402675113

theorem tailTrace_5340909 : CollatzResearch.WordTrace tailWord_5340909 prefixEnd_5340909 2742453448924149402675113 := by
  unfold tailWord_5340909
  simp only [CollatzResearch.WordTrace]
  refine ⟨194798954607806322481969781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129865969738537548321313187 194798954607806322481969781)
  ·
    refine ⟨18262401994481842732684667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194798954607806322481969781 18262401994481842732684667)
    ·
      refine ⟨27393602991722764099027001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18262401994481842732684667 27393602991722764099027001)
      ·
        refine ⟨20545202243792073074270251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27393602991722764099027001 20545202243792073074270251)
        ·
          refine ⟨30817803365688109611405377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20545202243792073074270251 30817803365688109611405377)
          ·
            refine ⟨23113352524266082208554033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30817803365688109611405377 23113352524266082208554033)
            ·
              refine ⟨17335014393199561656415525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23113352524266082208554033 17335014393199561656415525)
              ·
                refine ⟨3250315198724917810577911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17335014393199561656415525 3250315198724917810577911)
                ·
                  refine ⟨4875472798087376715866867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250315198724917810577911 4875472798087376715866867)
                  ·
                    refine ⟨7313209197131065073800301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4875472798087376715866867 7313209197131065073800301)
                    ·
                      refine ⟨2742453448924149402675113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313209197131065073800301 2742453448924149402675113)
                      ·
                        rfl

theorem cell23_5340909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5340909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340909 prefixEnd_5340909 := by exact prefixLift 5340909
  have htrace : WordTrace (prefixWord ++ tailWord_5340909) baseStart_5340909 baseEnd_5340909 := by
    simpa [prefixWord, tailWord_5340909, baseEnd_5340909] using wordTrace_append hprefix tailTrace_5340909
  have hstable : (prefixWord ++ tailWord_5340909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340909).length < 2 ^ (prefixWord ++ tailWord_5340909).sum := by decide
  have hdescent : baseEnd_5340909 < baseStart_5340909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340932 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_5340932 : Nat := 118140960795 + 5340932 * 2 ^ 59
def prefixEnd_5340932 : Nat := 4983230072969 + 3 ^ 40 * 5340932 * 2
def baseEnd_5340932 : Nat := 2742465258979202812687507

theorem tailTrace_5340932 : CollatzResearch.WordTrace tailWord_5340932 prefixEnd_5340932 2742465258979202812687507 := by
  unfold tailWord_5340932
  simp only [CollatzResearch.WordTrace]
  refine ⟨97399896743361498705028525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129866528991148664940038033 97399896743361498705028525)
  ·
    refine ⟨36524961278760562014385697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97399896743361498705028525 36524961278760562014385697)
    ·
      refine ⟨27393720959070421510789273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36524961278760562014385697 27393720959070421510789273)
      ·
        refine ⟨20545290719302816133091955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27393720959070421510789273 20545290719302816133091955)
        ·
          refine ⟨30817936078954224199637933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20545290719302816133091955 30817936078954224199637933)
          ·
            refine ⟨11556726029607834074864225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30817936078954224199637933 11556726029607834074864225)
            ·
              refine ⟨8667544522205875556148169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11556726029607834074864225 8667544522205875556148169)
              ·
                refine ⟨6500658391654406667111127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8667544522205875556148169 6500658391654406667111127)
                ·
                  refine ⟨9750987587481610000666691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6500658391654406667111127 9750987587481610000666691)
                  ·
                    refine ⟨14626481381222415001000037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9750987587481610000666691 14626481381222415001000037)
                    ·
                      refine ⟨2742465258979202812687507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14626481381222415001000037 2742465258979202812687507)
                      ·
                        rfl

theorem cell23_5340932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_5340932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340932 prefixEnd_5340932 := by exact prefixLift 5340932
  have htrace : WordTrace (prefixWord ++ tailWord_5340932) baseStart_5340932 baseEnd_5340932 := by
    simpa [prefixWord, tailWord_5340932, baseEnd_5340932] using wordTrace_append hprefix tailTrace_5340932
  have hstable : (prefixWord ++ tailWord_5340932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340932).length < 2 ^ (prefixWord ++ tailWord_5340932).sum := by decide
  have hdescent : baseEnd_5340932 < baseStart_5340932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340938 : List Nat := [3, 1, 2, 2, 1, 4, 1, 9]
def baseStart_5340938 : Nat := 118140960795 + 5340938 * 2 ^ 59
def prefixEnd_5340938 : Nat := 4983230072969 + 3 ^ 40 * 5340938 * 2
def baseEnd_5340938 : Nat := 101572901476412214415277

theorem tailTrace_5340938 : CollatzResearch.WordTrace tailWord_5340938 prefixEnd_5340938 101572901476412214415277 := by
  unfold tailWord_5340938
  simp only [CollatzResearch.WordTrace]
  refine ⟨48700003081175315108693867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129866674883134173623183645 48700003081175315108693867)
  ·
    refine ⟨73050004621762972663040801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48700003081175315108693867 73050004621762972663040801)
    ·
      refine ⟨54787503466322229497280601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73050004621762972663040801 54787503466322229497280601)
      ·
        refine ⟨41090627599741672122960451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54787503466322229497280601 41090627599741672122960451)
        ·
          refine ⟨61635941399612508184440677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41090627599741672122960451 61635941399612508184440677)
          ·
            refine ⟨11556739012427345284582627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61635941399612508184440677 11556739012427345284582627)
            ·
              refine ⟨17335108518641017926873941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11556739012427345284582627 17335108518641017926873941)
              ·
                refine ⟨101572901476412214415277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17335108518641017926873941 101572901476412214415277)
                ·
                  rfl

theorem cell23_5340938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_5340938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340938 prefixEnd_5340938 := by exact prefixLift 5340938
  have htrace : WordTrace (prefixWord ++ tailWord_5340938) baseStart_5340938 baseEnd_5340938 := by
    simpa [prefixWord, tailWord_5340938, baseEnd_5340938] using wordTrace_append hprefix tailTrace_5340938
  have hstable : (prefixWord ++ tailWord_5340938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340938).length < 2 ^ (prefixWord ++ tailWord_5340938).sum := by decide
  have hdescent : baseEnd_5340938 < baseStart_5340938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5340975 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 5, 3, 2]
def baseStart_5340975 : Nat := 118140960795 + 5340975 * 2 ^ 59
def prefixEnd_5340975 : Nat := 4983230072969 + 3 ^ 40 * 5340975 * 2
def baseEnd_5340975 : Nat := 2742487338647346144449809

theorem tailTrace_5340975 : CollatzResearch.WordTrace tailWord_5340975 prefixEnd_5340975 2742487338647346144449809 := by
  unfold tailWord_5340975
  simp only [CollatzResearch.WordTrace]
  refine ⟨194801361825567215753872379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129867574550378143835914919 194801361825567215753872379)
  ·
    refine ⟨292202042738350823630808569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194801361825567215753872379 292202042738350823630808569)
    ·
      refine ⟨219151532053763117723106427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292202042738350823630808569 219151532053763117723106427)
      ·
        refine ⟨328727298080644676584659641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219151532053763117723106427 328727298080644676584659641)
        ·
          refine ⟨246545473560483507438494731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328727298080644676584659641 246545473560483507438494731)
          ·
            refine ⟨369818210340725261157742097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246545473560483507438494731 369818210340725261157742097)
            ·
              refine ⟨277363657755543945868306573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369818210340725261157742097 277363657755543945868306573)
              ·
                refine ⟨104011371658328979700614965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277363657755543945868306573 104011371658328979700614965)
                ·
                  refine ⟨9751066092968341846932653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104011371658328979700614965 9751066092968341846932653)
                  ·
                    refine ⟨3656649784863128192599745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9751066092968341846932653 3656649784863128192599745)
                    ·
                      refine ⟨2742487338647346144449809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656649784863128192599745 2742487338647346144449809)
                      ·
                        rfl

theorem cell23_5340975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3, 2].length) (baseStart_5340975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5340975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5340975 prefixEnd_5340975 := by exact prefixLift 5340975
  have htrace : WordTrace (prefixWord ++ tailWord_5340975) baseStart_5340975 baseEnd_5340975 := by
    simpa [prefixWord, tailWord_5340975, baseEnd_5340975] using wordTrace_append hprefix tailTrace_5340975
  have hstable : (prefixWord ++ tailWord_5340975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5340975).length < 2 ^ (prefixWord ++ tailWord_5340975).sum := by decide
  have hdescent : baseEnd_5340975 < baseStart_5340975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5340975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341045 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 7]
def baseStart_5341045 : Nat := 118140960795 + 5341045 * 2 ^ 59
def prefixEnd_5341045 : Nat := 4983230072969 + 3 ^ 40 * 5341045 * 2
def baseEnd_5341045 : Nat := 304724809143684541174943

theorem tailTrace_5341045 : CollatzResearch.WordTrace tailWord_5341045 prefixEnd_5341045 304724809143684541174943 := by
  unfold tailWord_5341045
  simp only [CollatzResearch.WordTrace]
  refine ⟨194803914935313617708920589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129869276623542411805947059 194803914935313617708920589)
  ·
    refine ⟨73051468100742606640845221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194803914935313617708920589 73051468100742606640845221)
    ·
      refine ⟨13697150268889238745158479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73051468100742606640845221 13697150268889238745158479)
      ·
        refine ⟨20545725403333858117737719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13697150268889238745158479 20545725403333858117737719)
        ·
          refine ⟨30818588105000787176606579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20545725403333858117737719 30818588105000787176606579)
          ·
            refine ⟨46227882157501180764909869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30818588105000787176606579 46227882157501180764909869)
            ·
              refine ⟨17335455809062942786841201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46227882157501180764909869 17335455809062942786841201)
              ·
                refine ⟨13001591856797207090130901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17335455809062942786841201 13001591856797207090130901)
                ·
                  refine ⟨304724809143684541174943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13001591856797207090130901 304724809143684541174943)
                  ·
                    rfl

theorem cell23_5341045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_5341045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341045 prefixEnd_5341045 := by exact prefixLift 5341045
  have htrace : WordTrace (prefixWord ++ tailWord_5341045) baseStart_5341045 baseEnd_5341045 := by
    simpa [prefixWord, tailWord_5341045, baseEnd_5341045] using wordTrace_append hprefix tailTrace_5341045
  have hstable : (prefixWord ++ tailWord_5341045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341045).length < 2 ^ (prefixWord ++ tailWord_5341045).sum := by decide
  have hdescent : baseEnd_5341045 < baseStart_5341045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341132 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5341132 : Nat := 118140960795 + 5341132 * 2 ^ 59
def prefixEnd_5341132 : Nat := 4983230072969 + 3 ^ 40 * 5341132 * 2
def baseEnd_5341132 : Nat := 2742567955110102030186587

theorem tailTrace_5341132 : CollatzResearch.WordTrace tailWord_5341132 prefixEnd_5341132 2742567955110102030186587 := by
  unfold tailWord_5341132
  simp only [CollatzResearch.WordTrace]
  refine ⟨97403544042999215783668825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129871392057332287711558433 97403544042999215783668825)
  ·
    refine ⟨73052658032249411837751619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97403544042999215783668825 73052658032249411837751619)
    ·
      refine ⟨109578987048374117756627429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73052658032249411837751619 109578987048374117756627429)
      ·
        refine ⟨20546060071570147079367643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109578987048374117756627429 20546060071570147079367643)
        ·
          refine ⟨30819090107355220619051465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20546060071570147079367643 30819090107355220619051465)
          ·
            refine ⟨23114317580516415464288599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30819090107355220619051465 23114317580516415464288599)
            ·
              refine ⟨34671476370774623196432899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23114317580516415464288599 34671476370774623196432899)
              ·
                refine ⟨52007214556161934794649349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34671476370774623196432899 52007214556161934794649349)
                ·
                  refine ⟨9751352729280362773996753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52007214556161934794649349 9751352729280362773996753)
                  ·
                    refine ⟨7313514546960272080497565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9751352729280362773996753 7313514546960272080497565)
                    ·
                      refine ⟨2742567955110102030186587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313514546960272080497565 2742567955110102030186587)
                      ·
                        rfl

theorem cell23_5341132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5341132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341132 prefixEnd_5341132 := by exact prefixLift 5341132
  have htrace : WordTrace (prefixWord ++ tailWord_5341132) baseStart_5341132 baseEnd_5341132 := by
    simpa [prefixWord, tailWord_5341132, baseEnd_5341132] using wordTrace_append hprefix tailTrace_5341132
  have hstable : (prefixWord ++ tailWord_5341132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341132).length < 2 ^ (prefixWord ++ tailWord_5341132).sum := by decide
  have hdescent : baseEnd_5341132 < baseStart_5341132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341135 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 6]
def baseStart_5341135 : Nat := 118140960795 + 5341135 * 2 ^ 59
def prefixEnd_5341135 : Nat := 4983230072969 + 3 ^ 40 * 5341135 * 2
def baseEnd_5341135 : Nat := 304729943950229502049897

theorem tailTrace_5341135 : CollatzResearch.WordTrace tailWord_5341135 prefixEnd_5341135 304729943950229502049897 := by
  unfold tailWord_5341135
  simp only [CollatzResearch.WordTrace]
  refine ⟨194807197504987563079696859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129871465003325042053131239 194807197504987563079696859)
  ·
    refine ⟨292210796257481344619545289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194807197504987563079696859 292210796257481344619545289)
    ·
      refine ⟨219158097193111008464658967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292210796257481344619545289 219158097193111008464658967)
      ·
        refine ⟨328737145789666512696988451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219158097193111008464658967 328737145789666512696988451)
        ·
          refine ⟨493105718684499769045482677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328737145789666512696988451 493105718684499769045482677)
          ·
            refine ⟨46228661126671853348014001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 493105718684499769045482677 46228661126671853348014001)
            ·
              refine ⟨34671495845003890011010501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46228661126671853348014001 34671495845003890011010501)
              ·
                refine ⟨6500905470938229377064469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34671495845003890011010501 6500905470938229377064469)
                ·
                  refine ⟨304729943950229502049897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6500905470938229377064469 304729943950229502049897)
                  ·
                    rfl

theorem cell23_5341135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 6].length) (baseStart_5341135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341135 prefixEnd_5341135 := by exact prefixLift 5341135
  have htrace : WordTrace (prefixWord ++ tailWord_5341135) baseStart_5341135 baseEnd_5341135 := by
    simpa [prefixWord, tailWord_5341135, baseEnd_5341135] using wordTrace_append hprefix tailTrace_5341135
  have hstable : (prefixWord ++ tailWord_5341135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341135).length < 2 ^ (prefixWord ++ tailWord_5341135).sum := by decide
  have hdescent : baseEnd_5341135 < baseStart_5341135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341189 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 2, 3, 2]
def baseStart_5341189 : Nat := 118140960795 + 5341189 * 2 ^ 59
def prefixEnd_5341189 : Nat := 4983230072969 + 3 ^ 40 * 5341189 * 2
def baseEnd_5341189 : Nat := 2742597223507408307173825

theorem tailTrace_5341189 : CollatzResearch.WordTrace tailWord_5341189 prefixEnd_5341189 2742597223507408307173825 := by
  unfold tailWord_5341189
  simp only [CollatzResearch.WordTrace]
  refine ⟨194809167046791930302162621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129872778031194620201441747 194809167046791930302162621)
  ·
    refine ⟨73053437642546973863310983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194809167046791930302162621 73053437642546973863310983)
    ·
      refine ⟨109580156463820460794966475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73053437642546973863310983 109580156463820460794966475)
      ·
        refine ⟨164370234695730691192449713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109580156463820460794966475 164370234695730691192449713)
        ·
          refine ⟨123277676021798018394337285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164370234695730691192449713 123277676021798018394337285)
          ·
            refine ⟨23114564254087128448938241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123277676021798018394337285 23114564254087128448938241)
            ·
              refine ⟨17335923190565346336703681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23114564254087128448938241 17335923190565346336703681)
              ·
                refine ⟨13001942392924009752527761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17335923190565346336703681 13001942392924009752527761)
                ·
                  refine ⟨9751456794693007314395821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13001942392924009752527761 9751456794693007314395821)
                  ·
                    refine ⟨3656796298009877742898433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9751456794693007314395821 3656796298009877742898433)
                    ·
                      refine ⟨2742597223507408307173825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656796298009877742898433 2742597223507408307173825)
                      ·
                        rfl

theorem cell23_5341189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_5341189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341189 prefixEnd_5341189 := by exact prefixLift 5341189
  have htrace : WordTrace (prefixWord ++ tailWord_5341189) baseStart_5341189 baseEnd_5341189 := by
    simpa [prefixWord, tailWord_5341189, baseEnd_5341189] using wordTrace_append hprefix tailTrace_5341189
  have hstable : (prefixWord ++ tailWord_5341189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341189).length < 2 ^ (prefixWord ++ tailWord_5341189).sum := by decide
  have hdescent : baseEnd_5341189 < baseStart_5341189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341195 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 3, 6]
def baseStart_5341195 : Nat := 118140960795 + 5341195 * 2 ^ 59
def prefixEnd_5341195 : Nat := 4983230072969 + 3 ^ 40 * 5341195 * 2
def baseEnd_5341195 : Nat := 914200101463778427899599

theorem tailTrace_5341195 : CollatzResearch.WordTrace tailWord_5341195 prefixEnd_5341195 914200101463778427899599 := by
  unfold tailWord_5341195
  simp only [CollatzResearch.WordTrace]
  refine ⟨194809385884770193326881039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129872923923180128884587359 194809385884770193326881039)
  ·
    refine ⟨292214078827155289990321559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194809385884770193326881039 292214078827155289990321559)
    ·
      refine ⟨438321118240732934985482339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292214078827155289990321559 438321118240732934985482339)
      ·
        refine ⟨657481677361099402478223509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438321118240732934985482339 657481677361099402478223509)
        ·
          refine ⟨30819453626301534491166727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 657481677361099402478223509 30819453626301534491166727)
          ·
            refine ⟨46229180439452301736750091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30819453626301534491166727 46229180439452301736750091)
            ·
              refine ⟨69343770659178452605125137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46229180439452301736750091 69343770659178452605125137)
              ·
                refine ⟨52007827994383839453843853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69343770659178452605125137 52007827994383839453843853)
                ·
                  refine ⟨19502935497893939795191445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52007827994383839453843853 19502935497893939795191445)
                  ·
                    refine ⟨914200101463778427899599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19502935497893939795191445 914200101463778427899599)
                    ·
                      rfl

theorem cell23_5341195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_5341195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341195 prefixEnd_5341195 := by exact prefixLift 5341195
  have htrace : WordTrace (prefixWord ++ tailWord_5341195) baseStart_5341195 baseEnd_5341195 := by
    simpa [prefixWord, tailWord_5341195, baseEnd_5341195] using wordTrace_append hprefix tailTrace_5341195
  have hstable : (prefixWord ++ tailWord_5341195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341195).length < 2 ^ (prefixWord ++ tailWord_5341195).sum := by decide
  have hdescent : baseEnd_5341195 < baseStart_5341195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341196 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 1, 1, 3]
def baseStart_5341196 : Nat := 118140960795 + 5341196 * 2 ^ 59
def prefixEnd_5341196 : Nat := 4983230072969 + 3 ^ 40 * 5341196 * 2
def baseEnd_5341196 : Nat := 2742600817871989779786293

theorem tailTrace_5341196 : CollatzResearch.WordTrace tailWord_5341196 prefixEnd_5341196 2742600817871989779786293 := by
  unfold tailWord_5341196
  simp only [CollatzResearch.WordTrace]
  refine ⟨97404711178883285248833721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129872948238511046998444961 97404711178883285248833721)
  ·
    refine ⟨73053533384162463936625291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97404711178883285248833721 73053533384162463936625291)
    ·
      refine ⟨109580300076243695904937937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73053533384162463936625291 109580300076243695904937937)
      ·
        refine ⟨82185225057182771928703453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109580300076243695904937937 82185225057182771928703453)
        ·
          refine ⟨30819459396443539473263795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82185225057182771928703453 30819459396443539473263795)
          ·
            refine ⟨46229189094665309209895693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30819459396443539473263795 46229189094665309209895693)
            ·
              refine ⟨17335945910499490953710885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46229189094665309209895693 17335945910499490953710885)
              ·
                refine ⟨3250489858218654553820791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17335945910499490953710885 3250489858218654553820791)
                ·
                  refine ⟨4875734787327981830731187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250489858218654553820791 4875734787327981830731187)
                  ·
                    refine ⟨7313602180991972746096781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4875734787327981830731187 7313602180991972746096781)
                    ·
                      refine ⟨2742600817871989779786293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313602180991972746096781 2742600817871989779786293)
                      ·
                        rfl

theorem cell23_5341196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_5341196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341196 prefixEnd_5341196 := by exact prefixLift 5341196
  have htrace : WordTrace (prefixWord ++ tailWord_5341196) baseStart_5341196 baseEnd_5341196 := by
    simpa [prefixWord, tailWord_5341196, baseEnd_5341196] using wordTrace_append hprefix tailTrace_5341196
  have hstable : (prefixWord ++ tailWord_5341196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341196).length < 2 ^ (prefixWord ++ tailWord_5341196).sum := by decide
  have hdescent : baseEnd_5341196 < baseStart_5341196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341212 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5341212 : Nat := 118140960795 + 5341212 * 2 ^ 59
def prefixEnd_5341212 : Nat := 4983230072969 + 3 ^ 40 * 5341212 * 2
def baseEnd_5341212 : Nat := 914203011187487239062073

theorem tailTrace_5341212 : CollatzResearch.WordTrace tailWord_5341212 prefixEnd_5341212 914203011187487239062073 := by
  unfold tailWord_5341212
  simp only [CollatzResearch.WordTrace]
  refine ⟨97405002962854302615124945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129873337283805736820166593 97405002962854302615124945)
  ·
    refine ⟨73053752222140726961343709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97405002962854302615124945 73053752222140726961343709)
    ·
      refine ⟨27395157083302772610503891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73053752222140726961343709 27395157083302772610503891)
      ·
        refine ⟨41092735624954158915755837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27395157083302772610503891 41092735624954158915755837)
        ·
          refine ⟨15409775859357809593408439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41092735624954158915755837 15409775859357809593408439)
          ·
            refine ⟨23114663789036714390112659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15409775859357809593408439 23114663789036714390112659)
            ·
              refine ⟨34671995683555071585168989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23114663789036714390112659 34671995683555071585168989)
              ·
                refine ⟨13001998381333151844438371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34671995683555071585168989 13001998381333151844438371)
                ·
                  refine ⟨19502997571999727766657557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13001998381333151844438371 19502997571999727766657557)
                  ·
                    refine ⟨914203011187487239062073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19502997571999727766657557 914203011187487239062073)
                    ·
                      rfl

theorem cell23_5341212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5341212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341212 prefixEnd_5341212 := by exact prefixLift 5341212
  have htrace : WordTrace (prefixWord ++ tailWord_5341212) baseStart_5341212 baseEnd_5341212 := by
    simpa [prefixWord, tailWord_5341212, baseEnd_5341212] using wordTrace_append hprefix tailTrace_5341212
  have hstable : (prefixWord ++ tailWord_5341212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341212).length < 2 ^ (prefixWord ++ tailWord_5341212).sum := by decide
  have hdescent : baseEnd_5341212 < baseStart_5341212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341232 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_5341232 : Nat := 118140960795 + 5341232 * 2 ^ 59
def prefixEnd_5341232 : Nat := 4983230072969 + 3 ^ 40 * 5341232 * 2
def baseEnd_5341232 : Nat := 2742619303175551638936127

theorem tailTrace_5341232 : CollatzResearch.WordTrace tailWord_5341232 prefixEnd_5341232 2742619303175551638936127 := by
  unfold tailWord_5341232
  simp only [CollatzResearch.WordTrace]
  refine ⟨97405367692818074322988975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129873823590424099097318633 97405367692818074322988975)
  ·
    refine ⟨146108051539227111484483463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97405367692818074322988975 146108051539227111484483463)
    ·
      refine ⟨219162077308840667226725195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146108051539227111484483463 219162077308840667226725195)
      ·
        refine ⟨328743115963261000840087793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219162077308840667226725195 328743115963261000840087793)
        ·
          refine ⟨246557336972445750630065845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328743115963261000840087793 246557336972445750630065845)
          ·
            refine ⟨23114750341166789121568673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246557336972445750630065845 23114750341166789121568673)
            ·
              refine ⟨17336062755875091841176505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23114750341166789121568673 17336062755875091841176505)
              ·
                refine ⟨13002047066906318880882379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17336062755875091841176505 13002047066906318880882379)
                ·
                  refine ⟨19503070600359478321323569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13002047066906318880882379 19503070600359478321323569)
                  ·
                    refine ⟨14627302950269608740992677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19503070600359478321323569 14627302950269608740992677)
                    ·
                      refine ⟨2742619303175551638936127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14627302950269608740992677 2742619303175551638936127)
                      ·
                        rfl

theorem cell23_5341232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_5341232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341232 prefixEnd_5341232 := by exact prefixLift 5341232
  have htrace : WordTrace (prefixWord ++ tailWord_5341232) baseStart_5341232 baseEnd_5341232 := by
    simpa [prefixWord, tailWord_5341232, baseEnd_5341232] using wordTrace_append hprefix tailTrace_5341232
  have hstable : (prefixWord ++ tailWord_5341232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341232).length < 2 ^ (prefixWord ++ tailWord_5341232).sum := by decide
  have hdescent : baseEnd_5341232 < baseStart_5341232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341246 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_5341246 : Nat := 118140960795 + 5341246 * 2 ^ 59
def prefixEnd_5341246 : Nat := 4983230072969 + 3 ^ 40 * 5341246 * 2
def baseEnd_5341246 : Nat := 914208830634904861387021

theorem tailTrace_5341246 : CollatzResearch.WordTrace tailWord_5341246 prefixEnd_5341246 914208830634904861387021 := by
  unfold tailWord_5341246
  simp only [CollatzResearch.WordTrace]
  refine ⟨24351405750948178629623449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129874164005056952691325061 24351405750948178629623449)
  ·
    refine ⟨18263554313211133972217587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24351405750948178629623449 18263554313211133972217587)
    ·
      refine ⟨27395331469816700958326381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18263554313211133972217587 27395331469816700958326381)
      ·
        refine ⟨10273249301181262859372393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27395331469816700958326381 10273249301181262859372393)
        ·
          refine ⟨7704936975885947144529295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10273249301181262859372393 7704936975885947144529295)
          ·
            refine ⟨11557405463828920716793943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7704936975885947144529295 11557405463828920716793943)
            ·
              refine ⟨17336108195743381075190915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11557405463828920716793943 17336108195743381075190915)
              ·
                refine ⟨26004162293615071612786373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17336108195743381075190915 26004162293615071612786373)
                ·
                  refine ⟨4875780430052825927397445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26004162293615071612786373 4875780430052825927397445)
                  ·
                    refine ⟨914208830634904861387021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875780430052825927397445 914208830634904861387021)
                    ·
                      rfl

theorem cell23_5341246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_5341246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341246 prefixEnd_5341246 := by exact prefixLift 5341246
  have htrace : WordTrace (prefixWord ++ tailWord_5341246) baseStart_5341246 baseEnd_5341246 := by
    simpa [prefixWord, tailWord_5341246, baseEnd_5341246] using wordTrace_append hprefix tailTrace_5341246
  have hstable : (prefixWord ++ tailWord_5341246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341246).length < 2 ^ (prefixWord ++ tailWord_5341246).sum := by decide
  have hdescent : baseEnd_5341246 < baseStart_5341246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341266 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_5341266 : Nat := 118140960795 + 5341266 * 2 ^ 59
def prefixEnd_5341266 : Nat := 4983230072969 + 3 ^ 40 * 5341266 * 2
def baseEnd_5341266 : Nat := 2742636761517804505910971

theorem tailTrace_5341266 : CollatzResearch.WordTrace tailWord_5341266 prefixEnd_5341266 2742636761517804505910971 := by
  unfold tailWord_5341266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48702993866878243113178913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129874650311675314968477101 48702993866878243113178913)
  ·
    refine ⟨36527245400158682334884185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48702993866878243113178913 36527245400158682334884185)
    ·
      refine ⟨27395434050119011751163139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36527245400158682334884185 27395434050119011751163139)
      ·
        refine ⟨41093151075178517626744709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27395434050119011751163139 41093151075178517626744709)
        ·
          refine ⟨7704965826595972055014633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41093151075178517626744709 7704965826595972055014633)
          ·
            refine ⟨5778724369946979041260975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704965826595972055014633 5778724369946979041260975)
            ·
              refine ⟨8668086554920468561891463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778724369946979041260975 8668086554920468561891463)
              ·
                refine ⟨13002129832380702842837195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668086554920468561891463 13002129832380702842837195)
                ·
                  refine ⟨19503194748571054264255793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13002129832380702842837195 19503194748571054264255793)
                  ·
                    refine ⟨14627396061428290698191845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19503194748571054264255793 14627396061428290698191845)
                    ·
                      refine ⟨2742636761517804505910971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14627396061428290698191845 2742636761517804505910971)
                      ·
                        rfl

theorem cell23_5341266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_5341266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341266 prefixEnd_5341266 := by exact prefixLift 5341266
  have htrace : WordTrace (prefixWord ++ tailWord_5341266) baseStart_5341266 baseEnd_5341266 := by
    simpa [prefixWord, tailWord_5341266, baseEnd_5341266] using wordTrace_append hprefix tailTrace_5341266
  have hstable : (prefixWord ++ tailWord_5341266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341266).length < 2 ^ (prefixWord ++ tailWord_5341266).sum := by decide
  have hdescent : baseEnd_5341266 < baseStart_5341266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341269 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_5341269 : Nat := 118140960795 + 5341269 * 2 ^ 59
def prefixEnd_5341269 : Nat := 4983230072969 + 3 ^ 40 * 5341269 * 2
def baseEnd_5341269 : Nat := 2742638301959767994173457

theorem tailTrace_5341269 : CollatzResearch.WordTrace tailWord_5341269 prefixEnd_5341269 2742638301959767994173457 := by
  unfold tailWord_5341269
  simp only [CollatzResearch.WordTrace]
  refine ⟨194812084886502103965074861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129874723257668069310049907 194812084886502103965074861)
  ·
    refine ⟨73054531832438288986903073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194812084886502103965074861 73054531832438288986903073)
    ·
      refine ⟨54790898874328716740177305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73054531832438288986903073 54790898874328716740177305)
      ·
        refine ⟨41093174155746537555132979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54790898874328716740177305 41093174155746537555132979)
        ·
          refine ⟨61639761233619806332699469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41093174155746537555132979 61639761233619806332699469)
          ·
            refine ⟨23114910462607427374762301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61639761233619806332699469 23114910462607427374762301)
            ·
              refine ⟨8668091423477785265535863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23114910462607427374762301 8668091423477785265535863)
              ·
                refine ⟨13002137135216677898303795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668091423477785265535863 13002137135216677898303795)
                ·
                  refine ⟨19503205702825016847455693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13002137135216677898303795 19503205702825016847455693)
                  ·
                    refine ⟨7313702138559381317795885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19503205702825016847455693 7313702138559381317795885)
                    ·
                      refine ⟨2742638301959767994173457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313702138559381317795885 2742638301959767994173457)
                      ·
                        rfl

theorem cell23_5341269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_5341269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341269 prefixEnd_5341269 := by exact prefixLift 5341269
  have htrace : WordTrace (prefixWord ++ tailWord_5341269) baseStart_5341269 baseEnd_5341269 := by
    simpa [prefixWord, tailWord_5341269, baseEnd_5341269] using wordTrace_append hprefix tailTrace_5341269
  have hstable : (prefixWord ++ tailWord_5341269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341269).length < 2 ^ (prefixWord ++ tailWord_5341269).sum := by decide
  have hdescent : baseEnd_5341269 < baseStart_5341269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341270 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5341270 : Nat := 118140960795 + 5341270 * 2 ^ 59
def prefixEnd_5341270 : Nat := 4983230072969 + 3 ^ 40 * 5341270 * 2
def baseEnd_5341270 : Nat := 2742638815440422490260953

theorem tailTrace_5341270 : CollatzResearch.WordTrace tailWord_5341270 prefixEnd_5341270 2742638815440422490260953 := by
  unfold tailWord_5341270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175757584968655070991329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129874747572998987423907509 12175757584968655070991329)
  ·
    refine ⟨9131818188726491303243497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12175757584968655070991329 9131818188726491303243497)
    ·
      refine ⟨6848863641544868477432623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9131818188726491303243497 6848863641544868477432623)
      ·
        refine ⟨10273295462317302716148935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848863641544868477432623 10273295462317302716148935)
        ·
          refine ⟨15409943193475954074223403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10273295462317302716148935 15409943193475954074223403)
          ·
            refine ⟨23114914790213931111335105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15409943193475954074223403 23114914790213931111335105)
            ·
              refine ⟨17336186092660448333501329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23114914790213931111335105 17336186092660448333501329)
              ·
                refine ⟨13002139569495336250125997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17336186092660448333501329 13002139569495336250125997)
                ·
                  refine ⟨4875802338560751093797249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13002139569495336250125997 4875802338560751093797249)
                  ·
                    refine ⟨3656851753920563320347937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4875802338560751093797249 3656851753920563320347937)
                    ·
                      refine ⟨2742638815440422490260953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656851753920563320347937 2742638815440422490260953)
                      ·
                        rfl

theorem cell23_5341270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5341270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341270 prefixEnd_5341270 := by exact prefixLift 5341270
  have htrace : WordTrace (prefixWord ++ tailWord_5341270) baseStart_5341270 baseEnd_5341270 := by
    simpa [prefixWord, tailWord_5341270, baseEnd_5341270] using wordTrace_append hprefix tailTrace_5341270
  have hstable : (prefixWord ++ tailWord_5341270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341270).length < 2 ^ (prefixWord ++ tailWord_5341270).sum := by decide
  have hdescent : baseEnd_5341270 < baseStart_5341270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341296 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 1, 3, 2]
def baseStart_5341296 : Nat := 118140960795 + 5341296 * 2 ^ 59
def prefixEnd_5341296 : Nat := 4983230072969 + 3 ^ 40 * 5341296 * 2
def baseEnd_5341296 : Nat := 2742652165937439388535833

theorem tailTrace_5341296 : CollatzResearch.WordTrace tailWord_5341296 prefixEnd_5341296 2742652165937439388535833 := by
  unfold tailWord_5341296
  simp only [CollatzResearch.WordTrace]
  refine ⟨97406534828702143788153871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129875379771602858384205161 97406534828702143788153871)
  ·
    refine ⟨146109802243053215682230807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97406534828702143788153871 146109802243053215682230807)
    ·
      refine ⟨219164703364579823523346211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146109802243053215682230807 219164703364579823523346211)
      ·
        refine ⟨328747055046869735285019317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219164703364579823523346211 328747055046869735285019317)
        ·
          refine ⟨30820036410644037682970561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 328747055046869735285019317 30820036410644037682970561)
          ·
            refine ⟨23115027307983028262227921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30820036410644037682970561 23115027307983028262227921)
            ·
              refine ⟨17336270480987271196670941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23115027307983028262227921 17336270480987271196670941)
              ·
                refine ⟨6501101430370226698751603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17336270480987271196670941 6501101430370226698751603)
                ·
                  refine ⟨9751652145555340048127405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6501101430370226698751603 9751652145555340048127405)
                  ·
                    refine ⟨3656869554583252518047777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9751652145555340048127405 3656869554583252518047777)
                    ·
                      refine ⟨2742652165937439388535833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656869554583252518047777 2742652165937439388535833)
                      ·
                        rfl

theorem cell23_5341296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 3, 2].length) (baseStart_5341296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341296 prefixEnd_5341296 := by exact prefixLift 5341296
  have htrace : WordTrace (prefixWord ++ tailWord_5341296) baseStart_5341296 baseEnd_5341296 := by
    simpa [prefixWord, tailWord_5341296, baseEnd_5341296] using wordTrace_append hprefix tailTrace_5341296
  have hstable : (prefixWord ++ tailWord_5341296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341296).length < 2 ^ (prefixWord ++ tailWord_5341296).sum := by decide
  have hdescent : baseEnd_5341296 < baseStart_5341296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341312 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_5341312 : Nat := 118140960795 + 5341312 * 2 ^ 59
def prefixEnd_5341312 : Nat := 4983230072969 + 3 ^ 40 * 5341312 * 2
def baseEnd_5341312 : Nat := 2742660381627911325935759

theorem tailTrace_5341312 : CollatzResearch.WordTrace tailWord_5341312 prefixEnd_5341312 2742660381627911325935759 := by
  unfold tailWord_5341312
  simp only [CollatzResearch.WordTrace]
  refine ⟨97406826612673161154445095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129875768816897548205926793 97406826612673161154445095)
  ·
    refine ⟨146110239919009741731667643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97406826612673161154445095 146110239919009741731667643)
    ·
      refine ⟨219165359878514612597501465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146110239919009741731667643 219165359878514612597501465)
      ·
        refine ⟨164374019908885959448126099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219165359878514612597501465 164374019908885959448126099)
        ·
          refine ⟨246561029863328939172189149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164374019908885959448126099 246561029863328939172189149)
          ·
            refine ⟨92460386198748352189570931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246561029863328939172189149 92460386198748352189570931)
            ·
              refine ⟨138690579298122528284356397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92460386198748352189570931 138690579298122528284356397)
              ·
                refine ⟨52008967236795948106633649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138690579298122528284356397 52008967236795948106633649)
                ·
                  refine ⟨39006725427596961079975237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52008967236795948106633649 39006725427596961079975237)
                  ·
                    refine ⟨7313761017674430202495357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39006725427596961079975237 7313761017674430202495357)
                    ·
                      refine ⟨2742660381627911325935759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313761017674430202495357 2742660381627911325935759)
                      ·
                        rfl

theorem cell23_5341312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_5341312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341312 prefixEnd_5341312 := by exact prefixLift 5341312
  have htrace : WordTrace (prefixWord ++ tailWord_5341312) baseStart_5341312 baseEnd_5341312 := by
    simpa [prefixWord, tailWord_5341312, baseEnd_5341312] using wordTrace_append hprefix tailTrace_5341312
  have hstable : (prefixWord ++ tailWord_5341312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341312).length < 2 ^ (prefixWord ++ tailWord_5341312).sum := by decide
  have hdescent : baseEnd_5341312 < baseStart_5341312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341320 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5341320 : Nat := 118140960795 + 5341320 * 2 ^ 59
def prefixEnd_5341320 : Nat := 4983230072969 + 3 ^ 40 * 5341320 * 2
def baseEnd_5341320 : Nat := 2742664489473147294635723

theorem tailTrace_5341320 : CollatzResearch.WordTrace tailWord_5341320 prefixEnd_5341320 2742664489473147294635723 := by
  unfold tailWord_5341320
  simp only [CollatzResearch.WordTrace]
  refine ⟨97406972504658669837590707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129875963339544893116787609 97406972504658669837590707)
  ·
    refine ⟨146110458756988004756386061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97406972504658669837590707 146110458756988004756386061)
    ·
      refine ⟨54791422033870501783644773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146110458756988004756386061 54791422033870501783644773)
      ·
        refine ⟨10273391631350719084433395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54791422033870501783644773 10273391631350719084433395)
        ·
          refine ⟨15410087447026078626650093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10273391631350719084433395 15410087447026078626650093)
          ·
            refine ⟨5778782792634779484993785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15410087447026078626650093 5778782792634779484993785)
            ·
              refine ⟨4334087094476084613745339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778782792634779484993785 4334087094476084613745339)
              ·
                refine ⟨6501130641714126920618009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334087094476084613745339 6501130641714126920618009)
                ·
                  refine ⟨4875847981285595190463507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6501130641714126920618009 4875847981285595190463507)
                  ·
                    refine ⟨7313771971928392785695261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4875847981285595190463507 7313771971928392785695261)
                    ·
                      refine ⟨2742664489473147294635723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313771971928392785695261 2742664489473147294635723)
                      ·
                        rfl

theorem cell23_5341320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5341320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341320 prefixEnd_5341320 := by exact prefixLift 5341320
  have htrace : WordTrace (prefixWord ++ tailWord_5341320) baseStart_5341320 baseEnd_5341320 := by
    simpa [prefixWord, tailWord_5341320, baseEnd_5341320] using wordTrace_append hprefix tailTrace_5341320
  have hstable : (prefixWord ++ tailWord_5341320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341320).length < 2 ^ (prefixWord ++ tailWord_5341320).sum := by decide
  have hdescent : baseEnd_5341320 < baseStart_5341320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341349 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 5]
def baseStart_5341349 : Nat := 118140960795 + 5341349 * 2 ^ 59
def prefixEnd_5341349 : Nat := 4983230072969 + 3 ^ 40 * 5341349 * 2
def baseEnd_5341349 : Nat := 304742153379125297908121

theorem tailTrace_5341349 : CollatzResearch.WordTrace tailWord_5341349 prefixEnd_5341349 304742153379125297908121 := by
  unfold tailWord_5341349
  simp only [CollatzResearch.WordTrace]
  refine ⟨194815002726212277627987101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129876668484141518418658067 194815002726212277627987101)
  ·
    refine ⟨73055626022329604110495163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194815002726212277627987101 73055626022329604110495163)
    ·
      refine ⟨109583439033494406165742745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73055626022329604110495163 109583439033494406165742745)
      ·
        refine ⟨82187579275120804624307059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109583439033494406165742745 82187579275120804624307059)
        ·
          refine ⟨123281368912681206936460589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82187579275120804624307059 123281368912681206936460589)
          ·
            refine ⟨46230513342255452601172721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123281368912681206936460589 46230513342255452601172721)
            ·
              refine ⟨34672885006691589450879541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46230513342255452601172721 34672885006691589450879541)
              ·
                refine ⟨3250582969377336511019957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34672885006691589450879541 3250582969377336511019957)
                ·
                  refine ⟨304742153379125297908121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3250582969377336511019957 304742153379125297908121)
                  ·
                    rfl

theorem cell23_5341349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_5341349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341349 prefixEnd_5341349 := by exact prefixLift 5341349
  have htrace : WordTrace (prefixWord ++ tailWord_5341349) baseStart_5341349 baseEnd_5341349 := by
    simpa [prefixWord, tailWord_5341349, baseEnd_5341349] using wordTrace_append hprefix tailTrace_5341349
  have hstable : (prefixWord ++ tailWord_5341349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341349).length < 2 ^ (prefixWord ++ tailWord_5341349).sum := by decide
  have hdescent : baseEnd_5341349 < baseStart_5341349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341369 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5341369 : Nat := 118140960795 + 5341369 * 2 ^ 59
def prefixEnd_5341369 : Nat := 4983230072969 + 3 ^ 40 * 5341369 * 2
def baseEnd_5341369 : Nat := 2742689650025217602922997

theorem tailTrace_5341369 : CollatzResearch.WordTrace tailWord_5341369 prefixEnd_5341369 2742689650025217602922997 := by
  unfold tailWord_5341369
  simp only [CollatzResearch.WordTrace]
  refine ⟨194815732186139821043715161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129877154790759880695810107 194815732186139821043715161)
  ·
    refine ⟨146111799139604865782786371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194815732186139821043715161 146111799139604865782786371)
    ·
      refine ⟨219167698709407298674179557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146111799139604865782786371 219167698709407298674179557)
      ·
        refine ⟨41093943508013868501408667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219167698709407298674179557 41093943508013868501408667)
        ·
          refine ⟨61640915262020802752113001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41093943508013868501408667 61640915262020802752113001)
          ·
            refine ⟨46230686446515602064084751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61640915262020802752113001 46230686446515602064084751)
            ·
              refine ⟨69346029669773403096127127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46230686446515602064084751 69346029669773403096127127)
              ·
                refine ⟨104019044504660104644190691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69346029669773403096127127 104019044504660104644190691)
                ·
                  refine ⟨156028566756990156966286037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104019044504660104644190691 156028566756990156966286037)
                  ·
                    refine ⟨3656919533366956803897329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 156028566756990156966286037 3656919533366956803897329)
                    ·
                      refine ⟨2742689650025217602922997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656919533366956803897329 2742689650025217602922997)
                      ·
                        rfl

theorem cell23_5341369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5341369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341369 prefixEnd_5341369 := by exact prefixLift 5341369
  have htrace : WordTrace (prefixWord ++ tailWord_5341369) baseStart_5341369 baseEnd_5341369 := by
    simpa [prefixWord, tailWord_5341369, baseEnd_5341369] using wordTrace_append hprefix tailTrace_5341369
  have hstable : (prefixWord ++ tailWord_5341369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341369).length < 2 ^ (prefixWord ++ tailWord_5341369).sum := by decide
  have hdescent : baseEnd_5341369 < baseStart_5341369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341399 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 6, 2]
def baseStart_5341399 : Nat := 118140960795 + 5341399 * 2 ^ 59
def prefixEnd_5341399 : Nat := 4983230072969 + 3 ^ 40 * 5341399 * 2
def baseEnd_5341399 : Nat := 2742705054444852485547859

theorem tailTrace_5341399 : CollatzResearch.WordTrace tailWord_5341399 prefixEnd_5341399 2742705054444852485547859 := by
  unfold tailWord_5341399
  simp only [CollatzResearch.WordTrace]
  refine ⟨194816826376031136167307251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129877884250687424111538167 194816826376031136167307251)
  ·
    refine ⟨292225239564046704250960877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194816826376031136167307251 292225239564046704250960877)
    ·
      refine ⟨109584464836517514094110329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292225239564046704250960877 109584464836517514094110329)
      ·
        refine ⟨82188348627388135570582747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109584464836517514094110329 82188348627388135570582747)
        ·
          refine ⟨123282522941082203355874121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82188348627388135570582747 123282522941082203355874121)
          ·
            refine ⟨92461892205811652516905591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123282522941082203355874121 92461892205811652516905591)
            ·
              refine ⟨138692838308717478775358387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92461892205811652516905591 138692838308717478775358387)
              ·
                refine ⟨208039257463076218163037581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138692838308717478775358387 208039257463076218163037581)
                ·
                  refine ⟨78014721548653581811139093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208039257463076218163037581 78014721548653581811139093)
                  ·
                    refine ⟨3656940072593136647397145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78014721548653581811139093 3656940072593136647397145)
                    ·
                      refine ⟨2742705054444852485547859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656940072593136647397145 2742705054444852485547859)
                      ·
                        rfl

theorem cell23_5341399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_5341399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341399 prefixEnd_5341399 := by exact prefixLift 5341399
  have htrace : WordTrace (prefixWord ++ tailWord_5341399) baseStart_5341399 baseEnd_5341399 := by
    simpa [prefixWord, tailWord_5341399, baseEnd_5341399] using wordTrace_append hprefix tailTrace_5341399
  have hstable : (prefixWord ++ tailWord_5341399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341399).length < 2 ^ (prefixWord ++ tailWord_5341399).sum := by decide
  have hdescent : baseEnd_5341399 < baseStart_5341399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341409 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 5, 4]
def baseStart_5341409 : Nat := 118140960795 + 5341409 * 2 ^ 59
def prefixEnd_5341409 : Nat := 4983230072969 + 3 ^ 40 * 5341409 * 2
def baseEnd_5341409 : Nat := 914236729750465815474271

theorem tailTrace_5341409 : CollatzResearch.WordTrace tailWord_5341409 prefixEnd_5341409 914236729750465815474271 := by
  unfold tailWord_5341409
  simp only [CollatzResearch.WordTrace]
  refine ⟨194817191105994907875171281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129878127403996605250114187 194817191105994907875171281)
  ·
    refine ⟨146112893329496180906378461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194817191105994907875171281 146112893329496180906378461)
    ·
      refine ⟨54792334998561067839891923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146112893329496180906378461 54792334998561067839891923)
      ·
        refine ⟨82188502497841601759837885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54792334998561067839891923 82188502497841601759837885)
        ·
          refine ⟨30820688436690600659939207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82188502497841601759837885 30820688436690600659939207)
          ·
            refine ⟨46231032655035900989908811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30820688436690600659939207 46231032655035900989908811)
            ·
              refine ⟨69346548982553851484863217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46231032655035900989908811 69346548982553851484863217)
              ·
                refine ⟨52009911736915388613647413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69346548982553851484863217 52009911736915388613647413)
                ·
                  refine ⟨4875929225335817682529445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52009911736915388613647413 4875929225335817682529445)
                  ·
                    refine ⟨914236729750465815474271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875929225335817682529445 914236729750465815474271)
                    ·
                      rfl

theorem cell23_5341409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_5341409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341409 prefixEnd_5341409 := by exact prefixLift 5341409
  have htrace : WordTrace (prefixWord ++ tailWord_5341409) baseStart_5341409 baseEnd_5341409 := by
    simpa [prefixWord, tailWord_5341409, baseEnd_5341409] using wordTrace_append hprefix tailTrace_5341409
  have hstable : (prefixWord ++ tailWord_5341409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341409).length < 2 ^ (prefixWord ++ tailWord_5341409).sum := by decide
  have hdescent : baseEnd_5341409 < baseStart_5341409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341416 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_5341416 : Nat := 118140960795 + 5341416 * 2 ^ 59
def prefixEnd_5341416 : Nat := 4983230072969 + 3 ^ 40 * 5341416 * 2
def baseEnd_5341416 : Nat := 2742713783615978919035281

theorem tailTrace_5341416 : CollatzResearch.WordTrace tailWord_5341416 prefixEnd_5341416 2742713783615978919035281 := by
  unfold tailWord_5341416
  simp only [CollatzResearch.WordTrace]
  refine ⟨97408723208484774035338051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129878297611313032047117401 97408723208484774035338051)
  ·
    refine ⟨146113084812727161053007077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97408723208484774035338051 146113084812727161053007077)
    ·
      refine ⟨27396203402386342697438827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146113084812727161053007077 27396203402386342697438827)
      ·
        refine ⟨41094305103579514046158241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27396203402386342697438827 41094305103579514046158241)
        ·
          refine ⟨30820728827684635534618681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41094305103579514046158241 30820728827684635534618681)
          ·
            refine ⟨23115546620763476650964011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30820728827684635534618681 23115546620763476650964011)
            ·
              refine ⟨34673319931145214976446017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23115546620763476650964011 34673319931145214976446017)
              ·
                refine ⟨26004989948358911232334513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34673319931145214976446017 26004989948358911232334513)
                ·
                  refine ⟨19503742461269183424250885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26004989948358911232334513 19503742461269183424250885)
                  ·
                    refine ⟨3656951711487971892047041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19503742461269183424250885 3656951711487971892047041)
                    ·
                      refine ⟨2742713783615978919035281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3656951711487971892047041 2742713783615978919035281)
                      ·
                        rfl

theorem cell23_5341416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_5341416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341416 prefixEnd_5341416 := by exact prefixLift 5341416
  have htrace : WordTrace (prefixWord ++ tailWord_5341416) baseStart_5341416 baseEnd_5341416 := by
    simpa [prefixWord, tailWord_5341416, baseEnd_5341416] using wordTrace_append hprefix tailTrace_5341416
  have hstable : (prefixWord ++ tailWord_5341416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341416).length < 2 ^ (prefixWord ++ tailWord_5341416).sum := by decide
  have hdescent : baseEnd_5341416 < baseStart_5341416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341419 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 3]
def baseStart_5341419 : Nat := 118140960795 + 5341419 * 2 ^ 59
def prefixEnd_5341419 : Nat := 4983230072969 + 3 ^ 40 * 5341419 * 2
def baseEnd_5341419 : Nat := 2742715324057942407297767

theorem tailTrace_5341419 : CollatzResearch.WordTrace tailWord_5341419 prefixEnd_5341419 2742715324057942407297767 := by
  unfold tailWord_5341419
  simp only [CollatzResearch.WordTrace]
  refine ⟨194817555835958679583035311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129878370557305786388690207 194817555835958679583035311)
  ·
    refine ⟨292226333753938019374552967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194817555835958679583035311 292226333753938019374552967)
    ·
      refine ⟨438339500630907029061829451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292226333753938019374552967 438339500630907029061829451)
      ·
        refine ⟨657509250946360543592744177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438339500630907029061829451 657509250946360543592744177)
        ·
          refine ⟨493131938209770407694558133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657509250946360543592744177 493131938209770407694558133)
          ·
            refine ⟨46231119207165975721364825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 493131938209770407694558133 46231119207165975721364825)
            ·
              refine ⟨34673339405374481791023619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46231119207165975721364825 34673339405374481791023619)
              ·
                refine ⟨52010009108061722686535429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34673339405374481791023619 52010009108061722686535429)
                ·
                  refine ⟨9751876707761573003725393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52010009108061722686535429 9751876707761573003725393)
                  ·
                    refine ⟨7313907530821179752794045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9751876707761573003725393 7313907530821179752794045)
                    ·
                      refine ⟨2742715324057942407297767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313907530821179752794045 2742715324057942407297767)
                      ·
                        rfl

theorem cell23_5341419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 3].length) (baseStart_5341419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341419 prefixEnd_5341419 := by exact prefixLift 5341419
  have htrace : WordTrace (prefixWord ++ tailWord_5341419) baseStart_5341419 baseEnd_5341419 := by
    simpa [prefixWord, tailWord_5341419, baseEnd_5341419] using wordTrace_append hprefix tailTrace_5341419
  have hstable : (prefixWord ++ tailWord_5341419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341419).length < 2 ^ (prefixWord ++ tailWord_5341419).sum := by decide
  have hdescent : baseEnd_5341419 < baseStart_5341419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341426 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_5341426 : Nat := 118140960795 + 5341426 * 2 ^ 59
def prefixEnd_5341426 : Nat := 4983230072969 + 3 ^ 40 * 5341426 * 2
def baseEnd_5341426 : Nat := 914239639474174626636745

theorem tailTrace_5341426 : CollatzResearch.WordTrace tailWord_5341426 prefixEnd_5341426 914239639474174626636745 := by
  unfold tailWord_5341426
  simp only [CollatzResearch.WordTrace]
  refine ⟨48704452786733329944635033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129878540764622213185693421 48704452786733329944635033)
  ·
    refine ⟨36528339590049997458476275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48704452786733329944635033 36528339590049997458476275)
    ·
      refine ⟨54792509385074996187714413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36528339590049997458476275 54792509385074996187714413)
      ·
        refine ⟨20547191019403123570392905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54792509385074996187714413 20547191019403123570392905)
        ·
          refine ⟨15410393264552342677794679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20547191019403123570392905 15410393264552342677794679)
          ·
            refine ⟨23115589896828514016692019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15410393264552342677794679 23115589896828514016692019)
            ·
              refine ⟨34673384845242771025038029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23115589896828514016692019 34673384845242771025038029)
              ·
                refine ⟨13002519316966039134389261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34673384845242771025038029 13002519316966039134389261)
                ·
                  refine ⟨4875944743862264675395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13002519316966039134389261 4875944743862264675395973)
                  ·
                    refine ⟨914239639474174626636745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4875944743862264675395973 914239639474174626636745)
                    ·
                      rfl

theorem cell23_5341426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_5341426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341426 prefixEnd_5341426 := by exact prefixLift 5341426
  have htrace : WordTrace (prefixWord ++ tailWord_5341426) baseStart_5341426 baseEnd_5341426 := by
    simpa [prefixWord, tailWord_5341426, baseEnd_5341426] using wordTrace_append hprefix tailTrace_5341426
  have hstable : (prefixWord ++ tailWord_5341426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341426).length < 2 ^ (prefixWord ++ tailWord_5341426).sum := by decide
  have hdescent : baseEnd_5341426 < baseStart_5341426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341470 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5341470 : Nat := 118140960795 + 5341470 * 2 ^ 59
def prefixEnd_5341470 : Nat := 4983230072969 + 3 ^ 40 * 5341470 * 2
def baseEnd_5341470 : Nat := 2742741511571321707760033

theorem tailTrace_5341470 : CollatzResearch.WordTrace tailWord_5341470 prefixEnd_5341470 2742741511571321707760033 := by
  unfold tailWord_5341470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24352426994846739411642733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129879610639182610195427909 24352426994846739411642733)
  ·
    refine ⟨9132160123067527279366025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24352426994846739411642733 9132160123067527279366025)
    ·
      refine ⟨6849120092300645459524519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9132160123067527279366025 6849120092300645459524519)
      ·
        refine ⟨10273680138450968189286779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6849120092300645459524519 10273680138450968189286779)
        ·
          refine ⟨15410520207676452283930169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10273680138450968189286779 15410520207676452283930169)
          ·
            refine ⟨11557890155757339212947627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15410520207676452283930169 11557890155757339212947627)
            ·
              refine ⟨17336835233636008819421441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11557890155757339212947627 17336835233636008819421441)
              ·
                refine ⟨13002626425227006614566081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17336835233636008819421441 13002626425227006614566081)
                ·
                  refine ⟨9751969818920254960924561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13002626425227006614566081 9751969818920254960924561)
                  ·
                    refine ⟨7313977364190191220693421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9751969818920254960924561 7313977364190191220693421)
                    ·
                      refine ⟨2742741511571321707760033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7313977364190191220693421 2742741511571321707760033)
                      ·
                        rfl

theorem cell23_5341470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5341470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341470 prefixEnd_5341470 := by exact prefixLift 5341470
  have htrace : WordTrace (prefixWord ++ tailWord_5341470) baseStart_5341470 baseEnd_5341470 := by
    simpa [prefixWord, tailWord_5341470, baseEnd_5341470] using wordTrace_append hprefix tailTrace_5341470
  have hstable : (prefixWord ++ tailWord_5341470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341470).length < 2 ^ (prefixWord ++ tailWord_5341470).sum := by decide
  have hdescent : baseEnd_5341470 < baseStart_5341470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341490 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_5341490 : Nat := 118140960795 + 5341490 * 2 ^ 59
def prefixEnd_5341490 : Nat := 4983230072969 + 3 ^ 40 * 5341490 * 2
def baseEnd_5341490 : Nat := 304750197909379069945549

theorem tailTrace_5341490 : CollatzResearch.WordTrace tailWord_5341490 prefixEnd_5341490 304750197909379069945549 := by
  unfold tailWord_5341490
  simp only [CollatzResearch.WordTrace]
  refine ⟨48705036354675364677217481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129880096945800972472579949 48705036354675364677217481)
  ·
    refine ⟨36528777266006523507913111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48705036354675364677217481 36528777266006523507913111)
    ·
      refine ⟨54793165899009785261869667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36528777266006523507913111 54793165899009785261869667)
      ·
        refine ⟨82189748848514677892804501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54793165899009785261869667 82189748848514677892804501)
        ·
          refine ⟨3852644477274125526225211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82189748848514677892804501 3852644477274125526225211)
          ·
            refine ⟨5778966715911188289337817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852644477274125526225211 5778966715911188289337817)
            ·
              refine ⟨4334225036933391217003363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778966715911188289337817 4334225036933391217003363)
              ·
                refine ⟨6501337555400086825505045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334225036933391217003363 6501337555400086825505045)
                ·
                  refine ⟨304750197909379069945549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6501337555400086825505045 304750197909379069945549)
                  ·
                    rfl

theorem cell23_5341490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_5341490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341490 prefixEnd_5341490 := by exact prefixLift 5341490
  have htrace : WordTrace (prefixWord ++ tailWord_5341490) baseStart_5341490 baseEnd_5341490 := by
    simpa [prefixWord, tailWord_5341490, baseEnd_5341490] using wordTrace_append hprefix tailTrace_5341490
  have hstable : (prefixWord ++ tailWord_5341490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341490).length < 2 ^ (prefixWord ++ tailWord_5341490).sum := by decide
  have hdescent : baseEnd_5341490 < baseStart_5341490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341546 : List Nat := [3, 1, 3, 3, 1, 1, 3, 8]
def baseStart_5341546 : Nat := 118140960795 + 5341546 * 2 ^ 59
def prefixEnd_5341546 : Nat := 4983230072969 + 3 ^ 40 * 5341546 * 2
def baseEnd_5341546 : Nat := 101584464300039385570729

theorem tailTrace_5341546 : CollatzResearch.WordTrace tailWord_5341546 prefixEnd_5341546 101584464300039385570729 := by
  unfold tailWord_5341546
  simp only [CollatzResearch.WordTrace]
  refine ⟨48705546976624645068227123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129881458604332386848605661 48705546976624645068227123)
  ·
    refine ⟨73058320464936967602340685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48705546976624645068227123 73058320464936967602340685)
    ·
      refine ⟨27396870174351362850877757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73058320464936967602340685 27396870174351362850877757)
      ·
        refine ⟨10273826315381761069079159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27396870174351362850877757 10273826315381761069079159)
        ·
          refine ⟨15410739473072641603618739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10273826315381761069079159 15410739473072641603618739)
          ·
            refine ⟨23116109209608962405428109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15410739473072641603618739 23116109209608962405428109)
            ·
              refine ⟨8668540953603360902035541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23116109209608962405428109 8668540953603360902035541)
              ·
                refine ⟨101584464300039385570729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8668540953603360902035541 101584464300039385570729)
                ·
                  rfl

theorem cell23_5341546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_5341546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341546 prefixEnd_5341546 := by exact prefixLift 5341546
  have htrace : WordTrace (prefixWord ++ tailWord_5341546) baseStart_5341546 baseEnd_5341546 := by
    simpa [prefixWord, tailWord_5341546, baseEnd_5341546] using wordTrace_append hprefix tailTrace_5341546
  have hstable : (prefixWord ++ tailWord_5341546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341546).length < 2 ^ (prefixWord ++ tailWord_5341546).sum := by decide
  have hdescent : baseEnd_5341546 < baseStart_5341546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341607 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_5341607 : Nat := 118140960795 + 5341607 * 2 ^ 59
def prefixEnd_5341607 : Nat := 4983230072969 + 3 ^ 40 * 5341607 * 2
def baseEnd_5341607 : Nat := 2742811858420987671746903

theorem tailTrace_5341607 : CollatzResearch.WordTrace tailWord_5341607 prefixEnd_5341607 2742811858420987671746903 := by
  unfold tailWord_5341607
  simp only [CollatzResearch.WordTrace]
  refine ⟨194824412759277587690879075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129882941839518391793919383 194824412759277587690879075)
  ·
    refine ⟨292236619138916381536318613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194824412759277587690879075 292236619138916381536318613)
    ·
      refine ⟨13698591522136705384514935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 292236619138916381536318613 13698591522136705384514935)
      ·
        refine ⟨20547887283205058076772403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13698591522136705384514935 20547887283205058076772403)
        ·
          refine ⟨30821830924807587115158605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20547887283205058076772403 30821830924807587115158605)
          ·
            refine ⟨11558186596802845168184477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30821830924807587115158605 11558186596802845168184477)
            ·
              refine ⟨4334319973801066938069179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11558186596802845168184477 4334319973801066938069179)
              ·
                refine ⟨6501479960701600407103769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334319973801066938069179 6501479960701600407103769)
                ·
                  refine ⟨4876109970526200305327827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6501479960701600407103769 4876109970526200305327827)
                  ·
                    refine ⟨7314164955789300457991741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4876109970526200305327827 7314164955789300457991741)
                    ·
                      refine ⟨2742811858420987671746903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7314164955789300457991741 2742811858420987671746903)
                      ·
                        rfl

theorem cell23_5341607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_5341607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341607 prefixEnd_5341607 := by exact prefixLift 5341607
  have htrace : WordTrace (prefixWord ++ tailWord_5341607) baseStart_5341607 baseEnd_5341607 := by
    simpa [prefixWord, tailWord_5341607, baseEnd_5341607] using wordTrace_append hprefix tailTrace_5341607
  have hstable : (prefixWord ++ tailWord_5341607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341607).length < 2 ^ (prefixWord ++ tailWord_5341607).sum := by decide
  have hdescent : baseEnd_5341607 < baseStart_5341607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341630 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_5341630 : Nat := 118140960795 + 5341630 * 2 ^ 59
def prefixEnd_5341630 : Nat := 4983230072969 + 3 ^ 40 * 5341630 * 2
def baseEnd_5341630 : Nat := 2742823668476041081759297

theorem tailTrace_5341630 : CollatzResearch.WordTrace tailWord_5341630 prefixEnd_5341630 2742823668476041081759297 := by
  unfold tailWord_5341630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24353156454774282827370793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129883501092129508412644229 24353156454774282827370793)
  ·
    refine ⟨18264867341080712120528095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24353156454774282827370793 18264867341080712120528095)
    ·
      refine ⟨27397301011621068180792143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18264867341080712120528095 27397301011621068180792143)
      ·
        refine ⟨41095951517431602271188215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27397301011621068180792143 41095951517431602271188215)
        ·
          refine ⟨61643927276147403406782323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41095951517431602271188215 61643927276147403406782323)
          ·
            refine ⟨92465890914221105110173485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61643927276147403406782323 92465890914221105110173485)
            ·
              refine ⟨34674709092832914416315057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92465890914221105110173485 34674709092832914416315057)
              ·
                refine ⟨26006031819624685812236293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34674709092832914416315057 26006031819624685812236293)
                ·
                  refine ⟨4876130966179628589794305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26006031819624685812236293 4876130966179628589794305)
                  ·
                    refine ⟨3657098224634721442345729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4876130966179628589794305 3657098224634721442345729)
                    ·
                      refine ⟨2742823668476041081759297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657098224634721442345729 2742823668476041081759297)
                      ·
                        rfl

theorem cell23_5341630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_5341630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341630 prefixEnd_5341630 := by exact prefixLift 5341630
  have htrace : WordTrace (prefixWord ++ tailWord_5341630) baseStart_5341630 baseEnd_5341630 := by
    simpa [prefixWord, tailWord_5341630, baseEnd_5341630] using wordTrace_append hprefix tailTrace_5341630
  have hstable : (prefixWord ++ tailWord_5341630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341630).length < 2 ^ (prefixWord ++ tailWord_5341630).sum := by decide
  have hdescent : baseEnd_5341630 < baseStart_5341630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341653 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 7]
def baseStart_5341653 : Nat := 118140960795 + 5341653 * 2 ^ 59
def prefixEnd_5341653 : Nat := 4983230072969 + 3 ^ 40 * 5341653 * 2
def baseEnd_5341653 : Nat := 304759497614566054641299

theorem tailTrace_5341653 : CollatzResearch.WordTrace tailWord_5341653 prefixEnd_5341653 304759497614566054641299 := by
  unfold tailWord_5341653
  simp only [CollatzResearch.WordTrace]
  refine ⟨194826090517110937547053613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129884060344740625031369075 194826090517110937547053613)
  ·
    refine ⟨73059783943916601580145105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194826090517110937547053613 73059783943916601580145105)
    ·
      refine ⟨54794837957937451185108829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73059783943916601580145105 54794837957937451185108829)
      ·
        refine ⟨20548064234226544194415811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54794837957937451185108829 20548064234226544194415811)
        ·
          refine ⟨30822096351339816291623717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20548064234226544194415811 30822096351339816291623717)
          ·
            refine ⟨5779143065876215554679447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30822096351339816291623717 5779143065876215554679447)
            ·
              refine ⟨8668714598814323332019171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779143065876215554679447 8668714598814323332019171)
              ·
                refine ⟨13003071898221484998028757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668714598814323332019171 13003071898221484998028757)
                ·
                  refine ⟨304759497614566054641299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13003071898221484998028757 304759497614566054641299)
                  ·
                    rfl

theorem cell23_5341653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_5341653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341653 prefixEnd_5341653 := by exact prefixLift 5341653
  have htrace : WordTrace (prefixWord ++ tailWord_5341653) baseStart_5341653 baseEnd_5341653 := by
    simpa [prefixWord, tailWord_5341653, baseEnd_5341653] using wordTrace_append hprefix tailTrace_5341653
  have hstable : (prefixWord ++ tailWord_5341653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341653).length < 2 ^ (prefixWord ++ tailWord_5341653).sum := by decide
  have hdescent : baseEnd_5341653 < baseStart_5341653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341706 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5341706 : Nat := 118140960795 + 5341706 * 2 ^ 59
def prefixEnd_5341706 : Nat := 4983230072969 + 3 ^ 40 * 5341706 * 2
def baseEnd_5341706 : Nat := 2742862693005782784408947

theorem tailTrace_5341706 : CollatzResearch.WordTrace tailWord_5341706 prefixEnd_5341706 2742862693005782784408947 := by
  unfold tailWord_5341706
  simp only [CollatzResearch.WordTrace]
  refine ⟨48707005896479731899683243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129885349057279285065821981 48707005896479731899683243)
  ·
    refine ⟨73060508844719597849524865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48707005896479731899683243 73060508844719597849524865)
    ·
      refine ⟨54795381633539698387143649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73060508844719597849524865 54795381633539698387143649)
      ·
        refine ⟨41096536225154773790357737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54795381633539698387143649 41096536225154773790357737)
        ·
          refine ⟨30822402168866080342768303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41096536225154773790357737 30822402168866080342768303)
          ·
            refine ⟨46233603253299120514152455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30822402168866080342768303 46233603253299120514152455)
            ·
              refine ⟨69350404879948680771228683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46233603253299120514152455 69350404879948680771228683)
              ·
                refine ⟨104025607319923021156843025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69350404879948680771228683 104025607319923021156843025)
                ·
                  refine ⟨78019205489942265867632269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104025607319923021156843025 78019205489942265867632269)
                  ·
                    refine ⟨29257202058728349700362101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78019205489942265867632269 29257202058728349700362101)
                    ·
                      refine ⟨2742862693005782784408947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29257202058728349700362101 2742862693005782784408947)
                      ·
                        rfl

theorem cell23_5341706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5341706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341706 prefixEnd_5341706 := by exact prefixLift 5341706
  have htrace : WordTrace (prefixWord ++ tailWord_5341706) baseStart_5341706 baseEnd_5341706 := by
    simpa [prefixWord, tailWord_5341706, baseEnd_5341706] using wordTrace_append hprefix tailTrace_5341706
  have hstable : (prefixWord ++ tailWord_5341706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341706).length < 2 ^ (prefixWord ++ tailWord_5341706).sum := by decide
  have hdescent : baseEnd_5341706 < baseStart_5341706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341720 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 2, 4, 2]
def baseStart_5341720 : Nat := 118140960795 + 5341720 * 2 ^ 59
def prefixEnd_5341720 : Nat := 4983230072969 + 3 ^ 40 * 5341720 * 2
def baseEnd_5341720 : Nat := 2742869881734945729633883

theorem tailTrace_5341720 : CollatzResearch.WordTrace tailWord_5341720 prefixEnd_5341720 2742869881734945729633883 := by
  unfold tailWord_5341720
  simp only [CollatzResearch.WordTrace]
  refine ⟨97414267103934103994871307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129885689471912138659828409 97414267103934103994871307)
  ·
    refine ⟨146121400655901155992306961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97414267103934103994871307 146121400655901155992306961)
    ·
      refine ⟨109591050491925866994230221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146121400655901155992306961 109591050491925866994230221)
      ·
        refine ⟨41096643934472200122836333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109591050491925866994230221 41096643934472200122836333)
        ·
          refine ⟨15411241475427075046063625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41096643934472200122836333 15411241475427075046063625)
          ·
            refine ⟨11558431106570306284547719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15411241475427075046063625 11558431106570306284547719)
            ·
              refine ⟨17337646659855459426821579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11558431106570306284547719 17337646659855459426821579)
              ·
                refine ⟨26006469989783189140232369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17337646659855459426821579 26006469989783189140232369)
                ·
                  refine ⟨19504852492337391855174277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26006469989783189140232369 19504852492337391855174277)
                  ·
                    refine ⟨3657159842313260972845177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19504852492337391855174277 3657159842313260972845177)
                    ·
                      refine ⟨2742869881734945729633883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657159842313260972845177 2742869881734945729633883)
                      ·
                        rfl

theorem cell23_5341720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_5341720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341720 prefixEnd_5341720 := by exact prefixLift 5341720
  have htrace : WordTrace (prefixWord ++ tailWord_5341720) baseStart_5341720 baseEnd_5341720 := by
    simpa [prefixWord, tailWord_5341720, baseEnd_5341720] using wordTrace_append hprefix tailTrace_5341720
  have hstable : (prefixWord ++ tailWord_5341720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341720).length < 2 ^ (prefixWord ++ tailWord_5341720).sum := by decide
  have hdescent : baseEnd_5341720 < baseStart_5341720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341770 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_5341770 : Nat := 118140960795 + 5341770 * 2 ^ 59
def prefixEnd_5341770 : Nat := 4983230072969 + 3 ^ 40 * 5341770 * 2
def baseEnd_5341770 : Nat := 2742895555767670534008653

theorem tailTrace_5341770 : CollatzResearch.WordTrace tailWord_5341770 prefixEnd_5341770 2742895555767670534008653 := by
  unfold tailWord_5341770
  simp only [CollatzResearch.WordTrace]
  refine ⟨48707589464421766632265691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129886905238458044352708509 48707589464421766632265691)
  ·
    refine ⟨73061384196632649948398537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48707589464421766632265691 73061384196632649948398537)
    ·
      refine ⟨54796038147474487461298903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73061384196632649948398537 54796038147474487461298903)
      ·
        refine ⟨82194057221211731191948355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54796038147474487461298903 82194057221211731191948355)
        ·
          refine ⟨123291085831817596787922533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82194057221211731191948355 123291085831817596787922533)
          ·
            refine ⟨23117078593465799397735475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123291085831817596787922533 23117078593465799397735475)
            ·
              refine ⟨34675617890198699096603213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23117078593465799397735475 34675617890198699096603213)
              ·
                refine ⟨13003356708824512161226205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34675617890198699096603213 13003356708824512161226205)
                ·
                  refine ⟨4876258765809192060459827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13003356708824512161226205 4876258765809192060459827)
                  ·
                    refine ⟨7314388148713788090689741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4876258765809192060459827 7314388148713788090689741)
                    ·
                      refine ⟨2742895555767670534008653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7314388148713788090689741 2742895555767670534008653)
                      ·
                        rfl

theorem cell23_5341770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_5341770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341770 prefixEnd_5341770 := by exact prefixLift 5341770
  have htrace : WordTrace (prefixWord ++ tailWord_5341770) baseStart_5341770 baseEnd_5341770 := by
    simpa [prefixWord, tailWord_5341770, baseEnd_5341770] using wordTrace_append hprefix tailTrace_5341770
  have hstable : (prefixWord ++ tailWord_5341770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341770).length < 2 ^ (prefixWord ++ tailWord_5341770).sum := by decide
  have hdescent : baseEnd_5341770 < baseStart_5341770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341776 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_5341776 : Nat := 118140960795 + 5341776 * 2 ^ 59
def prefixEnd_5341776 : Nat := 4983230072969 + 3 ^ 40 * 5341776 * 2
def baseEnd_5341776 : Nat := 2742898636651597510533625

theorem tailTrace_5341776 : CollatzResearch.WordTrace tailWord_5341776 prefixEnd_5341776 2742898636651597510533625 := by
  unfold tailWord_5341776
  simp only [CollatzResearch.WordTrace]
  refine ⟨97415288347832664776890591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129887051130443553035854121 97415288347832664776890591)
  ·
    refine ⟨146122932521748997165335887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97415288347832664776890591 146122932521748997165335887)
    ·
      refine ⟨219184398782623495748003831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146122932521748997165335887 219184398782623495748003831)
      ·
        refine ⟨328776598173935243622005747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219184398782623495748003831 328776598173935243622005747)
        ·
          refine ⟨493164897260902865433008621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328776598173935243622005747 493164897260902865433008621)
          ·
            refine ⟨184936836472838574537378233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493164897260902865433008621 184936836472838574537378233)
            ·
              refine ⟨138702627354628930903033675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184936836472838574537378233 138702627354628930903033675)
              ·
                refine ⟨208053941031943396354550513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138702627354628930903033675 208053941031943396354550513)
                ·
                  refine ⟨156040455773957547265912885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208053941031943396354550513 156040455773957547265912885)
                  ·
                    refine ⟨14628792728808520056179333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 156040455773957547265912885 14628792728808520056179333)
                    ·
                      refine ⟨2742898636651597510533625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14628792728808520056179333 2742898636651597510533625)
                      ·
                        rfl

theorem cell23_5341776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_5341776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341776 prefixEnd_5341776 := by exact prefixLift 5341776
  have htrace : WordTrace (prefixWord ++ tailWord_5341776) baseStart_5341776 baseEnd_5341776 := by
    simpa [prefixWord, tailWord_5341776, baseEnd_5341776] using wordTrace_append hprefix tailTrace_5341776
  have hstable : (prefixWord ++ tailWord_5341776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341776).length < 2 ^ (prefixWord ++ tailWord_5341776).sum := by decide
  have hdescent : baseEnd_5341776 < baseStart_5341776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341780 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_5341780 : Nat := 118140960795 + 5341780 * 2 ^ 59
def prefixEnd_5341780 : Nat := 4983230072969 + 3 ^ 40 * 5341780 * 2
def baseEnd_5341780 : Nat := 2742900690574215494883607

theorem tailTrace_5341780 : CollatzResearch.WordTrace tailWord_5341780 prefixEnd_5341780 2742900690574215494883607 := by
  unfold tailWord_5341780
  simp only [CollatzResearch.WordTrace]
  refine ⟨97415361293825419118463397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129887148391767225491284529 97415361293825419118463397)
  ·
    refine ⟨18265380242592266084711887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97415361293825419118463397 18265380242592266084711887)
    ·
      refine ⟨27398070363888399127067831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18265380242592266084711887 27398070363888399127067831)
      ·
        refine ⟨41097105545832598690601747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27398070363888399127067831 41097105545832598690601747)
        ·
          refine ⟨61645658318748898035902621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41097105545832598690601747 61645658318748898035902621)
          ·
            refine ⟨23117121869530836763463483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61645658318748898035902621 23117121869530836763463483)
            ·
              refine ⟨34675682804296255145195225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23117121869530836763463483 34675682804296255145195225)
              ·
                refine ⟨26006762103222191358896419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34675682804296255145195225 26006762103222191358896419)
                ·
                  refine ⟨39010143154833287038344629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26006762103222191358896419 39010143154833287038344629)
                  ·
                    refine ⟨3657200920765620659844809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39010143154833287038344629 3657200920765620659844809)
                    ·
                      refine ⟨2742900690574215494883607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657200920765620659844809 2742900690574215494883607)
                      ·
                        rfl

theorem cell23_5341780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_5341780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341780 prefixEnd_5341780 := by exact prefixLift 5341780
  have htrace : WordTrace (prefixWord ++ tailWord_5341780) baseStart_5341780 baseEnd_5341780 := by
    simpa [prefixWord, tailWord_5341780, baseEnd_5341780] using wordTrace_append hprefix tailTrace_5341780
  have hstable : (prefixWord ++ tailWord_5341780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341780).length < 2 ^ (prefixWord ++ tailWord_5341780).sum := by decide
  have hdescent : baseEnd_5341780 < baseStart_5341780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341814 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5341814 : Nat := 118140960795 + 5341814 * 2 ^ 59
def prefixEnd_5341814 : Nat := 4983230072969 + 3 ^ 40 * 5341814 * 2
def baseEnd_5341814 : Nat := 2742918148916468361858451

theorem tailTrace_5341814 : CollatzResearch.WordTrace tailWord_5341814 prefixEnd_5341814 2742918148916468361858451 := by
  unfold tailWord_5341814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12176997666845478877729031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129887975113018441362442997 12176997666845478877729031)
  ·
    refine ⟨18265496500268218316593547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12176997666845478877729031 18265496500268218316593547)
    ·
      refine ⟨27398244750402327474890321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18265496500268218316593547 27398244750402327474890321)
      ·
        refine ⟨20548683562801745606167741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27398244750402327474890321 20548683562801745606167741)
        ·
          refine ⟨7705756336050654602312903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20548683562801745606167741 7705756336050654602312903)
          ·
            refine ⟨11558634504075981903469355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705756336050654602312903 11558634504075981903469355)
            ·
              refine ⟨17337951756113972855204033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11558634504075981903469355 17337951756113972855204033)
              ·
                refine ⟨13003463817085479641403025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17337951756113972855204033 13003463817085479641403025)
                ·
                  refine ⟨9752597862814109731052269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13003463817085479641403025 9752597862814109731052269)
                  ·
                    refine ⟨3657224198555291149144601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9752597862814109731052269 3657224198555291149144601)
                    ·
                      refine ⟨2742918148916468361858451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657224198555291149144601 2742918148916468361858451)
                      ·
                        rfl

theorem cell23_5341814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5341814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341814 prefixEnd_5341814 := by exact prefixLift 5341814
  have htrace : WordTrace (prefixWord ++ tailWord_5341814) baseStart_5341814 baseEnd_5341814 := by
    simpa [prefixWord, tailWord_5341814, baseEnd_5341814] using wordTrace_append hprefix tailTrace_5341814
  have hstable : (prefixWord ++ tailWord_5341814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341814).length < 2 ^ (prefixWord ++ tailWord_5341814).sum := by decide
  have hdescent : baseEnd_5341814 < baseStart_5341814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341821 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_5341821 : Nat := 118140960795 + 5341821 * 2 ^ 59
def prefixEnd_5341821 : Nat := 4983230072969 + 3 ^ 40 * 5341821 * 2
def baseEnd_5341821 : Nat := 2742921743281049834470919

theorem tailTrace_5341821 : CollatzResearch.WordTrace tailWord_5341821 prefixEnd_5341821 2742921743281049834470919 := by
  unfold tailWord_5341821
  simp only [CollatzResearch.WordTrace]
  refine ⟨194832217980502302239169317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129888145320334868159446211 194832217980502302239169317)
  ·
    refine ⟨36531040871344181669844247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194832217980502302239169317 36531040871344181669844247)
    ·
      refine ⟨54796561307016272504766371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36531040871344181669844247 54796561307016272504766371)
      ·
        refine ⟨82194841960524408757149557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54796561307016272504766371 82194841960524408757149557)
        ·
          refine ⟨7705766433799163320982771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82194841960524408757149557 7705766433799163320982771)
          ·
            refine ⟨11558649650698744981474157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705766433799163320982771 11558649650698744981474157)
            ·
              refine ⟨4334493619012029368052809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11558649650698744981474157 4334493619012029368052809)
              ·
                refine ⟨3250870214259022026039607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4334493619012029368052809 3250870214259022026039607)
                ·
                  refine ⟨4876305321388533039059411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250870214259022026039607 4876305321388533039059411)
                  ·
                    refine ⟨7314457982082799558589117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4876305321388533039059411 7314457982082799558589117)
                    ·
                      refine ⟨2742921743281049834470919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7314457982082799558589117 2742921743281049834470919)
                      ·
                        rfl

theorem cell23_5341821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_5341821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341821 prefixEnd_5341821 := by exact prefixLift 5341821
  have htrace : WordTrace (prefixWord ++ tailWord_5341821) baseStart_5341821 baseEnd_5341821 := by
    simpa [prefixWord, tailWord_5341821, baseEnd_5341821] using wordTrace_append hprefix tailTrace_5341821
  have hstable : (prefixWord ++ tailWord_5341821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341821).length < 2 ^ (prefixWord ++ tailWord_5341821).sum := by decide
  have hdescent : baseEnd_5341821 < baseStart_5341821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341827 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 3, 2, 2]
def baseStart_5341827 : Nat := 118140960795 + 5341827 * 2 ^ 59
def prefixEnd_5341827 : Nat := 4983230072969 + 3 ^ 40 * 5341827 * 2
def baseEnd_5341827 : Nat := 2742924824164976810995891

theorem tailTrace_5341827 : CollatzResearch.WordTrace tailWord_5341827 prefixEnd_5341827 2742924824164976810995891 := by
  unfold tailWord_5341827
  simp only [CollatzResearch.WordTrace]
  refine ⟨194832436818480565263887735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129888291212320376842591823 194832436818480565263887735)
  ·
    refine ⟨292248655227720847895831603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194832436818480565263887735 292248655227720847895831603)
    ·
      refine ⟨438372982841581271843747405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292248655227720847895831603 438372982841581271843747405)
      ·
        refine ⟨164389868565592976941405277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438372982841581271843747405 164389868565592976941405277)
        ·
          refine ⟨61646200712097366353026979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164389868565592976941405277 61646200712097366353026979)
          ·
            refine ⟨92469301068146049529540469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61646200712097366353026979 92469301068146049529540469)
            ·
              refine ⟨8668996975138692143394419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92469301068146049529540469 8668996975138692143394419)
              ·
                refine ⟨13003495462708038215091629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8668996975138692143394419 13003495462708038215091629)
                ·
                  refine ⟨4876310798515514330659361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13003495462708038215091629 4876310798515514330659361)
                  ·
                    refine ⟨3657233098886635747994521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4876310798515514330659361 3657233098886635747994521)
                    ·
                      refine ⟨2742924824164976810995891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657233098886635747994521 2742924824164976810995891)
                      ·
                        rfl

theorem cell23_5341827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_5341827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341827 prefixEnd_5341827 := by exact prefixLift 5341827
  have htrace : WordTrace (prefixWord ++ tailWord_5341827) baseStart_5341827 baseEnd_5341827 := by
    simpa [prefixWord, tailWord_5341827, baseEnd_5341827] using wordTrace_append hprefix tailTrace_5341827
  have hstable : (prefixWord ++ tailWord_5341827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341827).length < 2 ^ (prefixWord ++ tailWord_5341827).sum := by decide
  have hdescent : baseEnd_5341827 < baseStart_5341827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341844 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5341844 : Nat := 118140960795 + 5341844 * 2 ^ 59
def prefixEnd_5341844 : Nat := 4983230072969 + 3 ^ 40 * 5341844 * 2
def baseEnd_5341844 : Nat := 2742933553336103244483313

theorem tailTrace_5341844 : CollatzResearch.WordTrace tailWord_5341844 prefixEnd_5341844 2742933553336103244483313 := by
  unfold tailWord_5341844
  simp only [CollatzResearch.WordTrace]
  refine ⟨97416528429709488583628293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129888704572945984778171057 97416528429709488583628293)
  ·
    refine ⟨18265599080570529109430305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97416528429709488583628293 18265599080570529109430305)
    ·
      refine ⟨13699199310427896832072729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18265599080570529109430305 13699199310427896832072729)
      ·
        refine ⟨10274399482820922624054547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13699199310427896832072729 10274399482820922624054547)
        ·
          refine ⟨15411599224231383936081821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10274399482820922624054547 15411599224231383936081821)
          ·
            refine ⟨5779349709086768976030683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15411599224231383936081821 5779349709086768976030683)
            ·
              refine ⟨8669024563630153464046025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779349709086768976030683 8669024563630153464046025)
              ·
                refine ⟨6501768422722615098034519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8669024563630153464046025 6501768422722615098034519)
                ·
                  refine ⟨9752652634083922647051779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6501768422722615098034519 9752652634083922647051779)
                  ·
                    refine ⟨14628978951125883970577669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9752652634083922647051779 14628978951125883970577669)
                    ·
                      refine ⟨2742933553336103244483313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14628978951125883970577669 2742933553336103244483313)
                      ·
                        rfl

theorem cell23_5341844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5341844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341844 prefixEnd_5341844 := by exact prefixLift 5341844
  have htrace : WordTrace (prefixWord ++ tailWord_5341844) baseStart_5341844 baseEnd_5341844 := by
    simpa [prefixWord, tailWord_5341844, baseEnd_5341844] using wordTrace_append hprefix tailTrace_5341844
  have hstable : (prefixWord ++ tailWord_5341844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341844).length < 2 ^ (prefixWord ++ tailWord_5341844).sum := by decide
  have hdescent : baseEnd_5341844 < baseStart_5341844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341860 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_5341860 : Nat := 118140960795 + 5341860 * 2 ^ 59
def prefixEnd_5341860 : Nat := 4983230072969 + 3 ^ 40 * 5341860 * 2
def baseEnd_5341860 : Nat := 2742941769026575181883239

theorem tailTrace_5341860 : CollatzResearch.WordTrace tailWord_5341860 prefixEnd_5341860 2742941769026575181883239 := by
  unfold tailWord_5341860
  simp only [CollatzResearch.WordTrace]
  refine ⟨97416820213680505949919517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129889093618240674599892689 97416820213680505949919517)
  ·
    refine ⟨36531307580130189731219819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97416820213680505949919517 36531307580130189731219819)
    ·
      refine ⟨54796961370195284596829729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36531307580130189731219819 54796961370195284596829729)
      ·
        refine ⟨41097721027646463447622297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54796961370195284596829729 41097721027646463447622297)
        ·
          refine ⟨30823290770734847585716723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41097721027646463447622297 30823290770734847585716723)
          ·
            refine ⟨46234936156102271378575085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30823290770734847585716723 46234936156102271378575085)
            ·
              refine ⟨17338101058538351766965657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46234936156102271378575085 17338101058538351766965657)
              ·
                refine ⟨13003575793903763825224243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17338101058538351766965657 13003575793903763825224243)
                ·
                  refine ⟨19505363690855645737836365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13003575793903763825224243 19505363690855645737836365)
                  ·
                    refine ⟨7314511384070867151688637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19505363690855645737836365 7314511384070867151688637)
                    ·
                      refine ⟨2742941769026575181883239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7314511384070867151688637 2742941769026575181883239)
                      ·
                        rfl

theorem cell23_5341860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_5341860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341860 prefixEnd_5341860 := by exact prefixLift 5341860
  have htrace : WordTrace (prefixWord ++ tailWord_5341860) baseStart_5341860 baseEnd_5341860 := by
    simpa [prefixWord, tailWord_5341860, baseEnd_5341860] using wordTrace_append hprefix tailTrace_5341860
  have hstable : (prefixWord ++ tailWord_5341860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341860).length < 2 ^ (prefixWord ++ tailWord_5341860).sum := by decide
  have hdescent : baseEnd_5341860 < baseStart_5341860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341913 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_5341913 : Nat := 118140960795 + 5341913 * 2 ^ 59
def prefixEnd_5341913 : Nat := 4983230072969 + 3 ^ 40 * 5341913 * 2
def baseEnd_5341913 : Nat := 2742968983501263474520495

theorem tailTrace_5341913 : CollatzResearch.WordTrace tailWord_5341913 prefixEnd_5341913 2742968983501263474520495 := by
  unfold tailWord_5341913
  simp only [CollatzResearch.WordTrace]
  refine ⟨194835573496169001951518393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129890382330779334634345595 194835573496169001951518393)
  ·
    refine ⟨146126680122126751463638795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194835573496169001951518393 146126680122126751463638795)
    ·
      refine ⟨219190020183190127195458193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146126680122126751463638795 219190020183190127195458193)
      ·
        refine ⟨164392515137392595396593645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219190020183190127195458193 164392515137392595396593645)
        ·
          refine ⟨61647193176522223273722617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164392515137392595396593645 61647193176522223273722617)
          ·
            refine ⟨46235394882391667455291963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61647193176522223273722617 46235394882391667455291963)
            ·
              refine ⟨69353092323587501182937945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46235394882391667455291963 69353092323587501182937945)
              ·
                refine ⟨52014819242690625887203459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69353092323587501182937945 52014819242690625887203459)
                ·
                  refine ⟨78022228864035938830805189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52014819242690625887203459 78022228864035938830805189)
                  ·
                    refine ⟨14629167912006738530775973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78022228864035938830805189 14629167912006738530775973)
                    ·
                      refine ⟨2742968983501263474520495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14629167912006738530775973 2742968983501263474520495)
                      ·
                        rfl

theorem cell23_5341913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_5341913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341913 prefixEnd_5341913 := by exact prefixLift 5341913
  have htrace : WordTrace (prefixWord ++ tailWord_5341913) baseStart_5341913 baseEnd_5341913 := by
    simpa [prefixWord, tailWord_5341913, baseEnd_5341913] using wordTrace_append hprefix tailTrace_5341913
  have hstable : (prefixWord ++ tailWord_5341913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341913).length < 2 ^ (prefixWord ++ tailWord_5341913).sum := by decide
  have hdescent : baseEnd_5341913 < baseStart_5341913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341921 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_5341921 : Nat := 118140960795 + 5341921 * 2 ^ 59
def prefixEnd_5341921 : Nat := 4983230072969 + 3 ^ 40 * 5341921 * 2
def baseEnd_5341921 : Nat := 2742973091346499443220459

theorem tailTrace_5341921 : CollatzResearch.WordTrace tailWord_5341921 prefixEnd_5341921 2742973091346499443220459 := by
  unfold tailWord_5341921
  simp only [CollatzResearch.WordTrace]
  refine ⟨194835865280140019317809617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129890576853426679545206411 194835865280140019317809617)
  ·
    refine ⟨146126898960105014488357213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194835865280140019317809617 146126898960105014488357213)
    ·
      refine ⟨54797587110039380433133955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146126898960105014488357213 54797587110039380433133955)
      ·
        refine ⟨82196380665059070649700933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54797587110039380433133955 82196380665059070649700933)
        ·
          refine ⟨15411821374698575746818925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82196380665059070649700933 15411821374698575746818925)
          ·
            refine ⟨5779433015511965905057097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15411821374698575746818925 5779433015511965905057097)
            ·
              refine ⟨4334574761633974428792823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5779433015511965905057097 4334574761633974428792823)
              ·
                refine ⟨6501862142450961643189235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334574761633974428792823 6501862142450961643189235)
                ·
                  refine ⟨9752793213676442464783853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6501862142450961643189235 9752793213676442464783853)
                  ·
                    refine ⟨3657297455128665924293945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9752793213676442464783853 3657297455128665924293945)
                    ·
                      refine ⟨2742973091346499443220459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657297455128665924293945 2742973091346499443220459)
                      ·
                        rfl

theorem cell23_5341921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_5341921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341921 prefixEnd_5341921 := by exact prefixLift 5341921
  have htrace : WordTrace (prefixWord ++ tailWord_5341921) baseStart_5341921 baseEnd_5341921 := by
    simpa [prefixWord, tailWord_5341921, baseEnd_5341921] using wordTrace_append hprefix tailTrace_5341921
  have hstable : (prefixWord ++ tailWord_5341921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341921).length < 2 ^ (prefixWord ++ tailWord_5341921).sum := by decide
  have hdescent : baseEnd_5341921 < baseStart_5341921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341934 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_5341934 : Nat := 118140960795 + 5341934 * 2 ^ 59
def prefixEnd_5341934 : Nat := 4983230072969 + 3 ^ 40 * 5341934 * 2
def baseEnd_5341934 : Nat := 2742979766595007892357899

theorem tailTrace_5341934 : CollatzResearch.WordTrace tailWord_5341934 prefixEnd_5341934 2742979766595007892357899 := by
  unfold tailWord_5341934
  simp only [CollatzResearch.WordTrace]
  refine ⟨24354542428636615317254107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129890892952728615025355237 24354542428636615317254107)
  ·
    refine ⟨36531813642954922975881161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24354542428636615317254107 36531813642954922975881161)
    ·
      refine ⟨27398860232216192231910871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36531813642954922975881161 27398860232216192231910871)
      ·
        refine ⟨41098290348324288347866307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27398860232216192231910871 41098290348324288347866307)
        ·
          refine ⟨61647435522486432521799461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41098290348324288347866307 61647435522486432521799461)
          ·
            refine ⟨11558894160466206097837399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61647435522486432521799461 11558894160466206097837399)
            ·
              refine ⟨17338341240699309146756099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11558894160466206097837399 17338341240699309146756099)
              ·
                refine ⟨26007511861048963720134149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17338341240699309146756099 26007511861048963720134149)
                ·
                  refine ⟨4876408473946680697525153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26007511861048963720134149 4876408473946680697525153)
                  ·
                    refine ⟨3657306355460010523143865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4876408473946680697525153 3657306355460010523143865)
                    ·
                      refine ⟨2742979766595007892357899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657306355460010523143865 2742979766595007892357899)
                      ·
                        rfl

theorem cell23_5341934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_5341934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341934 prefixEnd_5341934 := by exact prefixLift 5341934
  have htrace : WordTrace (prefixWord ++ tailWord_5341934) baseStart_5341934 baseEnd_5341934 := by
    simpa [prefixWord, tailWord_5341934, baseEnd_5341934] using wordTrace_append hprefix tailTrace_5341934
  have hstable : (prefixWord ++ tailWord_5341934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341934).length < 2 ^ (prefixWord ++ tailWord_5341934).sum := by decide
  have hdescent : baseEnd_5341934 < baseStart_5341934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341963 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_5341963 : Nat := 118140960795 + 5341963 * 2 ^ 59
def prefixEnd_5341963 : Nat := 4983230072969 + 3 ^ 40 * 5341963 * 2
def baseEnd_5341963 : Nat := 2742994657533988278895265

theorem tailTrace_5341963 : CollatzResearch.WordTrace tailWord_5341963 prefixEnd_5341963 2742994657533988278895265 := by
  unfold tailWord_5341963
  simp only [CollatzResearch.WordTrace]
  refine ⟨194837397145987860490838543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129891598097325240327225695 194837397145987860490838543)
  ·
    refine ⟨292256095718981790736257815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194837397145987860490838543 292256095718981790736257815)
    ·
      refine ⟨438384143578472686104386723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292256095718981790736257815 438384143578472686104386723)
      ·
        refine ⟨657576215367709029156580085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438384143578472686104386723 657576215367709029156580085)
        ·
          refine ⟨61647770190722721483429383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 657576215367709029156580085 61647770190722721483429383)
          ·
            refine ⟨92471655286084082225144075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61647770190722721483429383 92471655286084082225144075)
            ·
              refine ⟨138707482929126123337716113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92471655286084082225144075 138707482929126123337716113)
              ·
                refine ⟨104030612196844592503287085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138707482929126123337716113 104030612196844592503287085)
                ·
                  refine ⟨39011479573816722188732657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104030612196844592503287085 39011479573816722188732657)
                  ·
                    refine ⟨29258609680362541641549493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39011479573816722188732657 29258609680362541641549493)
                    ·
                      refine ⟨2742994657533988278895265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29258609680362541641549493 2742994657533988278895265)
                      ·
                        rfl

theorem cell23_5341963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_5341963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341963 prefixEnd_5341963 := by exact prefixLift 5341963
  have htrace : WordTrace (prefixWord ++ tailWord_5341963) baseStart_5341963 baseEnd_5341963 := by
    simpa [prefixWord, tailWord_5341963, baseEnd_5341963] using wordTrace_append hprefix tailTrace_5341963
  have hstable : (prefixWord ++ tailWord_5341963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341963).length < 2 ^ (prefixWord ++ tailWord_5341963).sum := by decide
  have hdescent : baseEnd_5341963 < baseStart_5341963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5341993 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_5341993 : Nat := 118140960795 + 5341993 * 2 ^ 59
def prefixEnd_5341993 : Nat := 4983230072969 + 3 ^ 40 * 5341993 * 2
def baseEnd_5341993 : Nat := 2743010061953623161520127

theorem tailTrace_5341993 : CollatzResearch.WordTrace tailWord_5341993 prefixEnd_5341993 2743010061953623161520127 := by
  unfold tailWord_5341993
  simp only [CollatzResearch.WordTrace]
  refine ⟨194838491335879175614430633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129892327557252783742953755 194838491335879175614430633)
  ·
    refine ⟨146128868501909381710822975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194838491335879175614430633 146128868501909381710822975)
    ·
      refine ⟨219193302752864072566234463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146128868501909381710822975 219193302752864072566234463)
      ·
        refine ⟨328789954129296108849351695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219193302752864072566234463 328789954129296108849351695)
        ·
          refine ⟨493184931193944163274027543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328789954129296108849351695 493184931193944163274027543)
          ·
            refine ⟨739777396790916244911041315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493184931193944163274027543 739777396790916244911041315)
            ·
              refine ⟨1109666095186374367366561973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739777396790916244911041315 1109666095186374367366561973)
              ·
                refine ⟨104031196423722596940615185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1109666095186374367366561973 104031196423722596940615185)
                ·
                  refine ⟨78023397317791947705461389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104031196423722596940615185 78023397317791947705461389)
                  ·
                    refine ⟨29258773994171980389548021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78023397317791947705461389 29258773994171980389548021)
                    ·
                      refine ⟨2743010061953623161520127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29258773994171980389548021 2743010061953623161520127)
                      ·
                        rfl

theorem cell23_5341993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_5341993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5341993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5341993 prefixEnd_5341993 := by exact prefixLift 5341993
  have htrace : WordTrace (prefixWord ++ tailWord_5341993) baseStart_5341993 baseEnd_5341993 := by
    simpa [prefixWord, tailWord_5341993, baseEnd_5341993] using wordTrace_append hprefix tailTrace_5341993
  have hstable : (prefixWord ++ tailWord_5341993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5341993).length < 2 ^ (prefixWord ++ tailWord_5341993).sum := by decide
  have hdescent : baseEnd_5341993 < baseStart_5341993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5341993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342034 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_5342034 : Nat := 118140960795 + 5342034 * 2 ^ 59
def prefixEnd_5342034 : Nat := 4983230072969 + 3 ^ 40 * 5342034 * 2
def baseEnd_5342034 : Nat := 914343704886819167035813

theorem tailTrace_5342034 : CollatzResearch.WordTrace tailWord_5342034 prefixEnd_5342034 914343704886819167035813 := by
  unfold tailWord_5342034
  simp only [CollatzResearch.WordTrace]
  refine ⟨48709996682182659904168289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129893324485820426411115437 48709996682182659904168289)
  ·
    refine ⟨36532497511636994928126217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48709996682182659904168289 36532497511636994928126217)
    ·
      refine ⟨27399373133727746196094663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36532497511636994928126217 27399373133727746196094663)
      ·
        refine ⟨41099059700591619294141995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27399373133727746196094663 41099059700591619294141995)
        ·
          refine ⟨61648589550887428941212993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41099059700591619294141995 61648589550887428941212993)
          ·
            refine ⟨46236442163165571705909745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61648589550887428941212993 46236442163165571705909745)
            ·
              refine ⟨34677331622374178779432309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46236442163165571705909745 34677331622374178779432309)
              ·
                refine ⟨3250999839597579260571779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34677331622374178779432309 3250999839597579260571779)
                ·
                  refine ⟨4876499759396368890857669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250999839597579260571779 4876499759396368890857669)
                  ·
                    refine ⟨914343704886819167035813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4876499759396368890857669 914343704886819167035813)
                    ·
                      rfl

theorem cell23_5342034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_5342034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342034 prefixEnd_5342034 := by exact prefixLift 5342034
  have htrace : WordTrace (prefixWord ++ tailWord_5342034) baseStart_5342034 baseEnd_5342034 := by
    simpa [prefixWord, tailWord_5342034, baseEnd_5342034] using wordTrace_append hprefix tailTrace_5342034
  have hstable : (prefixWord ++ tailWord_5342034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342034).length < 2 ^ (prefixWord ++ tailWord_5342034).sum := by decide
  have hdescent : baseEnd_5342034 < baseStart_5342034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 9]
def baseStart_5342043 : Nat := 118140960795 + 5342043 * 2 ^ 59
def prefixEnd_5342043 : Nat := 4983230072969 + 3 ^ 40 * 5342043 * 2
def baseEnd_5342043 : Nat := 914345245328782655298299

theorem tailTrace_5342043 : CollatzResearch.WordTrace tailWord_5342043 prefixEnd_5342043 914345245328782655298299 := by
  unfold tailWord_5342043
  simp only [CollatzResearch.WordTrace]
  refine ⟨194840314985698034153750783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129893543323798689435833855 194840314985698034153750783)
  ·
    refine ⟨292260472478547051230626175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194840314985698034153750783 292260472478547051230626175)
    ·
      refine ⟨438390708717820576845939263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292260472478547051230626175 438390708717820576845939263)
      ·
        refine ⟨657586063076730865268908895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438390708717820576845939263 657586063076730865268908895)
        ·
          refine ⟨986379094615096297903363343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657586063076730865268908895 986379094615096297903363343)
          ·
            refine ⟨1479568641922644446855045015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986379094615096297903363343 1479568641922644446855045015)
            ·
              refine ⟨2219352962883966670282567523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479568641922644446855045015 2219352962883966670282567523)
              ·
                refine ⟨3329029444325950005423851285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219352962883966670282567523 3329029444325950005423851285)
                ·
                  refine ⟨156048255202778906504243029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3329029444325950005423851285 156048255202778906504243029)
                  ·
                    refine ⟨914345245328782655298299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156048255202778906504243029 914345245328782655298299)
                    ·
                      rfl

theorem cell23_5342043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_5342043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342043 prefixEnd_5342043 := by exact prefixLift 5342043
  have htrace : WordTrace (prefixWord ++ tailWord_5342043) baseStart_5342043 baseEnd_5342043 := by
    simpa [prefixWord, tailWord_5342043, baseEnd_5342043] using wordTrace_append hprefix tailTrace_5342043
  have hstable : (prefixWord ++ tailWord_5342043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342043).length < 2 ^ (prefixWord ++ tailWord_5342043).sum := by decide
  have hdescent : baseEnd_5342043 < baseStart_5342043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342044 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5342044 : Nat := 118140960795 + 5342044 * 2 ^ 59
def prefixEnd_5342044 : Nat := 4983230072969 + 3 ^ 40 * 5342044 * 2
def baseEnd_5342044 : Nat := 2743036249467002461982393

theorem tailTrace_5342044 : CollatzResearch.WordTrace tailWord_5342044 prefixEnd_5342044 2743036249467002461982393 := by
  unfold tailWord_5342044
  simp only [CollatzResearch.WordTrace]
  refine ⟨97420175729347205662268593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129893567639129607549691457 97420175729347205662268593)
  ·
    refine ⟨73065131797010404246701445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97420175729347205662268593 73065131797010404246701445)
    ·
      refine ⟨13699712211939450796256521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73065131797010404246701445 13699712211939450796256521)
      ·
        refine ⟨10274784158954588097192391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13699712211939450796256521 10274784158954588097192391)
        ·
          refine ⟨15412176238431882145788587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10274784158954588097192391 15412176238431882145788587)
          ·
            refine ⟨23118264357647823218682881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15412176238431882145788587 23118264357647823218682881)
            ·
              refine ⟨17338698268235867414012161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23118264357647823218682881 17338698268235867414012161)
              ·
                refine ⟨13004023701176900560509121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17338698268235867414012161 13004023701176900560509121)
                ·
                  refine ⟨9753017775882675420381841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13004023701176900560509121 9753017775882675420381841)
                  ·
                    refine ⟨7314763331912006565286381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9753017775882675420381841 7314763331912006565286381)
                    ·
                      refine ⟨2743036249467002461982393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7314763331912006565286381 2743036249467002461982393)
                      ·
                        rfl

theorem cell23_5342044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5342044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342044 prefixEnd_5342044 := by exact prefixLift 5342044
  have htrace : WordTrace (prefixWord ++ tailWord_5342044) baseStart_5342044 baseEnd_5342044 := by
    simpa [prefixWord, tailWord_5342044, baseEnd_5342044] using wordTrace_append hprefix tailTrace_5342044
  have hstable : (prefixWord ++ tailWord_5342044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342044).length < 2 ^ (prefixWord ++ tailWord_5342044).sum := by decide
  have hdescent : baseEnd_5342044 < baseStart_5342044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342051 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 1, 4]
def baseStart_5342051 : Nat := 118140960795 + 5342051 * 2 ^ 59
def prefixEnd_5342051 : Nat := 4983230072969 + 3 ^ 40 * 5342051 * 2
def baseEnd_5342051 : Nat := 914346614610527978198287

theorem tailTrace_5342051 : CollatzResearch.WordTrace tailWord_5342051 prefixEnd_5342051 914346614610527978198287 := by
  unfold tailWord_5342051
  simp only [CollatzResearch.WordTrace]
  refine ⟨194840606769669051520042007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129893737846446034346694671 194840606769669051520042007)
  ·
    refine ⟨292260910154503577280063011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194840606769669051520042007 292260910154503577280063011)
    ·
      refine ⟨438391365231755365920094517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292260910154503577280063011 438391365231755365920094517)
      ·
        refine ⟨41099190490477065555008861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 438391365231755365920094517 41099190490477065555008861)
        ·
          refine ⟨15412196433928899583128323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41099190490477065555008861 15412196433928899583128323)
          ·
            refine ⟨23118294650893349374692485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15412196433928899583128323 23118294650893349374692485)
            ·
              refine ⟨4334680247042503007754841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23118294650893349374692485 4334680247042503007754841)
              ·
                refine ⟨3251010185281877255816131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4334680247042503007754841 3251010185281877255816131)
                ·
                  refine ⟨4876515277922815883724197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251010185281877255816131 4876515277922815883724197)
                  ·
                    refine ⟨914346614610527978198287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4876515277922815883724197 914346614610527978198287)
                    ·
                      rfl

theorem cell23_5342051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 4].length) (baseStart_5342051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342051 prefixEnd_5342051 := by exact prefixLift 5342051
  have htrace : WordTrace (prefixWord ++ tailWord_5342051) baseStart_5342051 baseEnd_5342051 := by
    simpa [prefixWord, tailWord_5342051, baseEnd_5342051] using wordTrace_append hprefix tailTrace_5342051
  have hstable : (prefixWord ++ tailWord_5342051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342051).length < 2 ^ (prefixWord ++ tailWord_5342051).sum := by decide
  have hdescent : baseEnd_5342051 < baseStart_5342051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342060 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_5342060 : Nat := 118140960795 + 5342060 * 2 ^ 59
def prefixEnd_5342060 : Nat := 4983230072969 + 3 ^ 40 * 5342060 * 2
def baseEnd_5342060 : Nat := 914348155052491466460773

theorem tailTrace_5342060 : CollatzResearch.WordTrace tailWord_5342060 prefixEnd_5342060 914348155052491466460773 := by
  unfold tailWord_5342060
  simp only [CollatzResearch.WordTrace]
  refine ⟨97420467513318223028559817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129893956684424297371413089 97420467513318223028559817)
  ·
    refine ⟨73065350634988667271419863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97420467513318223028559817 73065350634988667271419863)
    ·
      refine ⟨109598025952483000907129795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73065350634988667271419863 109598025952483000907129795)
      ·
        refine ⟨164397038928724501360694693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109598025952483000907129795 164397038928724501360694693)
        ·
          refine ⟨30824444799135844005130255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164397038928724501360694693 30824444799135844005130255)
          ·
            refine ⟨46236667198703766007695383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30824444799135844005130255 46236667198703766007695383)
            ·
              refine ⟨69355000798055649011543075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46236667198703766007695383 69355000798055649011543075)
              ·
                refine ⟨104032501197083473517314613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69355000798055649011543075 104032501197083473517314613)
                ·
                  refine ⟨9753046987226575642248245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104032501197083473517314613 9753046987226575642248245)
                  ·
                    refine ⟨914348155052491466460773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9753046987226575642248245 914348155052491466460773)
                    ·
                      rfl

theorem cell23_5342060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_5342060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342060 prefixEnd_5342060 := by exact prefixLift 5342060
  have htrace : WordTrace (prefixWord ++ tailWord_5342060) baseStart_5342060 baseEnd_5342060 := by
    simpa [prefixWord, tailWord_5342060, baseEnd_5342060] using wordTrace_append hprefix tailTrace_5342060
  have hstable : (prefixWord ++ tailWord_5342060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342060).length < 2 ^ (prefixWord ++ tailWord_5342060).sum := by decide
  have hdescent : baseEnd_5342060 < baseStart_5342060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342067 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 4, 3, 2]
def baseStart_5342067 : Nat := 118140960795 + 5342067 * 2 ^ 59
def prefixEnd_5342067 : Nat := 4983230072969 + 3 ^ 40 * 5342067 * 2
def baseEnd_5342067 : Nat := 2743048059522055871994787

theorem tailTrace_5342067 : CollatzResearch.WordTrace tailWord_5342067 prefixEnd_5342067 2743048059522055871994787 := by
  unfold tailWord_5342067
  simp only [CollatzResearch.WordTrace]
  refine ⟨194841190337611086252624455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129894126891740724168416303 194841190337611086252624455)
  ·
    refine ⟨292261785506416629378936683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194841190337611086252624455 292261785506416629378936683)
    ·
      refine ⟨438392678259624944068405025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292261785506416629378936683 438392678259624944068405025)
      ·
        refine ⟨328794508694718708051303769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438392678259624944068405025 328794508694718708051303769)
        ·
          refine ⟨246595881521039031038477827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328794508694718708051303769 246595881521039031038477827)
          ·
            refine ⟨369893822281558546557716741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246595881521039031038477827 369893822281558546557716741)
            ·
              refine ⟨69355091677792227479571889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369893822281558546557716741 69355091677792227479571889)
              ·
                refine ⟨52016318758344170609678917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69355091677792227479571889 52016318758344170609678917)
                ·
                  refine ⟨9753059767189531989314797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52016318758344170609678917 9753059767189531989314797)
                  ·
                    refine ⟨3657397412696074495993049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9753059767189531989314797 3657397412696074495993049)
                    ·
                      refine ⟨2743048059522055871994787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657397412696074495993049 2743048059522055871994787)
                      ·
                        rfl

theorem cell23_5342067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3, 2].length) (baseStart_5342067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342067 prefixEnd_5342067 := by exact prefixLift 5342067
  have htrace : WordTrace (prefixWord ++ tailWord_5342067) baseStart_5342067 baseEnd_5342067 := by
    simpa [prefixWord, tailWord_5342067, baseEnd_5342067] using wordTrace_append hprefix tailTrace_5342067
  have hstable : (prefixWord ++ tailWord_5342067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342067).length < 2 ^ (prefixWord ++ tailWord_5342067).sum := by decide
  have hdescent : baseEnd_5342067 < baseStart_5342067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342078 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5342078 : Nat := 118140960795 + 5342078 * 2 ^ 59
def prefixEnd_5342078 : Nat := 4983230072969 + 3 ^ 40 * 5342078 * 2
def baseEnd_5342078 : Nat := 2743053707809255328957237

theorem tailTrace_5342078 : CollatzResearch.WordTrace tailWord_5342078 prefixEnd_5342078 2743053707809255328957237 := by
  unfold tailWord_5342078
  simp only [CollatzResearch.WordTrace]
  refine ⟨24355198942571404391409361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129894394360380823420849925 24355198942571404391409361)
  ·
    refine ⟨18266399206928553293557021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24355198942571404391409361 18266399206928553293557021)
    ·
      refine ⟨6849899702598207485083883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18266399206928553293557021 6849899702598207485083883)
      ·
        refine ⟨10274849553897311227625825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6849899702598207485083883 10274849553897311227625825)
        ·
          refine ⟨7706137165422983420719369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10274849553897311227625825 7706137165422983420719369)
          ·
            refine ⟨5779602874067237565539527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7706137165422983420719369 5779602874067237565539527)
            ·
              refine ⟨8669404311100856348309291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779602874067237565539527 8669404311100856348309291)
              ·
                refine ⟨13004106466651284522463937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8669404311100856348309291 13004106466651284522463937)
                ·
                  refine ⟨9753079849988463391847953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13004106466651284522463937 9753079849988463391847953)
                  ·
                    refine ⟨7314809887491347543885965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9753079849988463391847953 7314809887491347543885965)
                    ·
                      refine ⟨2743053707809255328957237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7314809887491347543885965 2743053707809255328957237)
                      ·
                        rfl

theorem cell23_5342078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5342078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342078 prefixEnd_5342078 := by exact prefixLift 5342078
  have htrace : WordTrace (prefixWord ++ tailWord_5342078) baseStart_5342078 baseEnd_5342078 := by
    simpa [prefixWord, tailWord_5342078, baseEnd_5342078] using wordTrace_append hprefix tailTrace_5342078
  have hstable : (prefixWord ++ tailWord_5342078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342078).length < 2 ^ (prefixWord ++ tailWord_5342078).sum := by decide
  have hdescent : baseEnd_5342078 < baseStart_5342078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342137 : List Nat := [1, 2, 1, 4, 2, 2, 4, 7]
def baseStart_5342137 : Nat := 118140960795 + 5342137 * 2 ^ 59
def prefixEnd_5342137 : Nat := 4983230072969 + 3 ^ 40 * 5342137 * 2
def baseEnd_5342137 : Nat := 101595703821032244374795

theorem tailTrace_5342137 : CollatzResearch.WordTrace tailWord_5342137 prefixEnd_5342137 101595703821032244374795 := by
  unfold tailWord_5342137
  simp only [CollatzResearch.WordTrace]
  refine ⟨194843743447357488207672665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129895828964904992138448443 194843743447357488207672665)
  ·
    refine ⟨146132807585518116155754499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194843743447357488207672665 146132807585518116155754499)
    ·
      refine ⟨219199211378277174233631749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146132807585518116155754499 219199211378277174233631749)
      ·
        refine ⟨41099852133426970168805953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219199211378277174233631749 41099852133426970168805953)
        ·
          refine ⟨30824889100070227626604465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41099852133426970168805953 30824889100070227626604465)
          ·
            refine ⟨23118666825052670719953349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30824889100070227626604465 23118666825052670719953349)
            ·
              refine ⟨4334750029697375759991253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23118666825052670719953349 4334750029697375759991253)
              ·
                refine ⟨101595703821032244374795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4334750029697375759991253 101595703821032244374795)
                ·
                  rfl

theorem cell23_5342137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 7].length) (baseStart_5342137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342137 prefixEnd_5342137 := by exact prefixLift 5342137
  have htrace : WordTrace (prefixWord ++ tailWord_5342137) baseStart_5342137 baseEnd_5342137 := by
    simpa [prefixWord, tailWord_5342137, baseEnd_5342137] using wordTrace_append hprefix tailTrace_5342137
  have hstable : (prefixWord ++ tailWord_5342137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342137).length < 2 ^ (prefixWord ++ tailWord_5342137).sum := by decide
  have hdescent : baseEnd_5342137 < baseStart_5342137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342160 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_5342160 : Nat := 118140960795 + 5342160 * 2 ^ 59
def prefixEnd_5342160 : Nat := 4983230072969 + 3 ^ 40 * 5342160 * 2
def baseEnd_5342160 : Nat := 2743095813222924008131859

theorem tailTrace_5342160 : CollatzResearch.WordTrace tailWord_5342160 prefixEnd_5342160 2743095813222924008131859 := by
  unfold tailWord_5342160
  simp only [CollatzResearch.WordTrace]
  refine ⟨97422291163137081567879967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129896388217516108757173289 97422291163137081567879967)
  ·
    refine ⟨146133436744705622351819951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97422291163137081567879967 146133436744705622351819951)
    ·
      refine ⟨219200155117058433527729927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146133436744705622351819951 219200155117058433527729927)
      ·
        refine ⟨328800232675587650291594891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219200155117058433527729927 328800232675587650291594891)
        ·
          refine ⟨493200349013381475437392337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328800232675587650291594891 493200349013381475437392337)
          ·
            refine ⟨369900261760036106578044253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493200349013381475437392337 369900261760036106578044253)
            ·
              refine ⟨138712598160013539966766595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369900261760036106578044253 138712598160013539966766595)
              ·
                refine ⟨208068897240020309950149893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138712598160013539966766595 208068897240020309950149893)
                ·
                  refine ⟨39012918232503808115653105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208068897240020309950149893 39012918232503808115653105)
                  ·
                    refine ⟨29259688674377856086739829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39012918232503808115653105 29259688674377856086739829)
                    ·
                      refine ⟨2743095813222924008131859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29259688674377856086739829 2743095813222924008131859)
                      ·
                        rfl

theorem cell23_5342160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_5342160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342160 prefixEnd_5342160 := by exact prefixLift 5342160
  have htrace : WordTrace (prefixWord ++ tailWord_5342160) baseStart_5342160 baseEnd_5342160 := by
    simpa [prefixWord, tailWord_5342160, baseEnd_5342160] using wordTrace_append hprefix tailTrace_5342160
  have hstable : (prefixWord ++ tailWord_5342160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342160).length < 2 ^ (prefixWord ++ tailWord_5342160).sum := by decide
  have hdescent : baseEnd_5342160 < baseStart_5342160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342165 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5342165 : Nat := 118140960795 + 5342165 * 2 ^ 59
def prefixEnd_5342165 : Nat := 4983230072969 + 3 ^ 40 * 5342165 * 2
def baseEnd_5342165 : Nat := 2743098380626196488569337

theorem tailTrace_5342165 : CollatzResearch.WordTrace tailWord_5342165 prefixEnd_5342165 2743098380626196488569337 := by
  unfold tailWord_5342165
  simp only [CollatzResearch.WordTrace]
  refine ⟨194844764691256048989691949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129896509794170699326461299 194844764691256048989691949)
  ·
    refine ⟨73066786759221018371134481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194844764691256048989691949 73066786759221018371134481)
    ·
      refine ⟨54800090069415763778350861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73066786759221018371134481 54800090069415763778350861)
      ·
        refine ⟨20550033776030911416881573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54800090069415763778350861 20550033776030911416881573)
        ·
          refine ⟨3853131333005795890665295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20550033776030911416881573 3853131333005795890665295)
          ·
            refine ⟨5779696999508693835997943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853131333005795890665295 5779696999508693835997943)
            ·
              refine ⟨8669545499263040753996915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779696999508693835997943 8669545499263040753996915)
              ·
                refine ⟨13004318248894561130995373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8669545499263040753996915 13004318248894561130995373)
                ·
                  refine ⟨4876619343335460424123265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13004318248894561130995373 4876619343335460424123265)
                  ·
                    refine ⟨3657464507501595318092449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4876619343335460424123265 3657464507501595318092449)
                    ·
                      refine ⟨2743098380626196488569337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657464507501595318092449 2743098380626196488569337)
                      ·
                        rfl

theorem cell23_5342165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5342165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342165 prefixEnd_5342165 := by exact prefixLift 5342165
  have htrace : WordTrace (prefixWord ++ tailWord_5342165) baseStart_5342165 baseEnd_5342165 := by
    simpa [prefixWord, tailWord_5342165, baseEnd_5342165] using wordTrace_append hprefix tailTrace_5342165
  have hstable : (prefixWord ++ tailWord_5342165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342165).length < 2 ^ (prefixWord ++ tailWord_5342165).sum := by decide
  have hdescent : baseEnd_5342165 < baseStart_5342165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342191 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 1, 3, 2]
def baseStart_5342191 : Nat := 118140960795 + 5342191 * 2 ^ 59
def prefixEnd_5342191 : Nat := 4983230072969 + 3 ^ 40 * 5342191 * 2
def baseEnd_5342191 : Nat := 2743111731123213386844217

theorem tailTrace_5342191 : CollatzResearch.WordTrace tailWord_5342191 prefixEnd_5342191 2743111731123213386844217 := by
  unfold tailWord_5342191
  simp only [CollatzResearch.WordTrace]
  refine ⟨194845712989161855430138427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129897141992774570286758951 194845712989161855430138427)
  ·
    refine ⟨292268569483742783145207641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194845712989161855430138427 292268569483742783145207641)
    ·
      refine ⟨219201427112807087358905731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292268569483742783145207641 219201427112807087358905731)
      ·
        refine ⟨328802140669210631038358597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219201427112807087358905731 328802140669210631038358597)
        ·
          refine ⟨61650401375476993319692237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328802140669210631038358597 61650401375476993319692237)
          ·
            refine ⟨23118900515803872494884589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61650401375476993319692237 23118900515803872494884589)
            ·
              refine ⟨8669587693426452185581721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23118900515803872494884589 8669587693426452185581721)
              ·
                refine ⟨6502190770069839139186291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8669587693426452185581721 6502190770069839139186291)
                ·
                  refine ⟨9753286155104758708779437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6502190770069839139186291 9753286155104758708779437)
                  ·
                    refine ⟨3657482308164284515792289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9753286155104758708779437 3657482308164284515792289)
                    ·
                      refine ⟨2743111731123213386844217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657482308164284515792289 2743111731123213386844217)
                      ·
                        rfl

theorem cell23_5342191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 3, 2].length) (baseStart_5342191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342191 prefixEnd_5342191 := by exact prefixLift 5342191
  have htrace : WordTrace (prefixWord ++ tailWord_5342191) baseStart_5342191 baseEnd_5342191 := by
    simpa [prefixWord, tailWord_5342191, baseEnd_5342191] using wordTrace_append hprefix tailTrace_5342191
  have hstable : (prefixWord ++ tailWord_5342191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342191).length < 2 ^ (prefixWord ++ tailWord_5342191).sum := by decide
  have hdescent : baseEnd_5342191 < baseStart_5342191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342204 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_5342204 : Nat := 118140960795 + 5342204 * 2 ^ 59
def prefixEnd_5342204 : Nat := 4983230072969 + 3 ^ 40 * 5342204 * 2
def baseEnd_5342204 : Nat := 2743118406371721835981657

theorem tailTrace_5342204 : CollatzResearch.WordTrace tailWord_5342204 prefixEnd_5342204 2743118406371721835981657 := by
  unfold tailWord_5342204
  simp only [CollatzResearch.WordTrace]
  refine ⟨97423093569057379325180833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129897458092076505766907777 97423093569057379325180833)
  ·
    refine ⟨73067320176793034493885625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97423093569057379325180833 73067320176793034493885625)
    ·
      refine ⟨54800490132594775870414219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73067320176793034493885625 54800490132594775870414219)
      ·
        refine ⟨82200735198892163805621329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54800490132594775870414219 82200735198892163805621329)
        ·
          refine ⟨61650551399169122854215997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82200735198892163805621329 61650551399169122854215997)
          ·
            refine ⟨23118956774688421070330999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61650551399169122854215997 23118956774688421070330999)
            ·
              refine ⟨34678435162032631605496499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23118956774688421070330999 34678435162032631605496499)
              ·
                refine ⟨52017652743048947408244749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34678435162032631605496499 52017652743048947408244749)
                ·
                  refine ⟨19506619778643355278091781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52017652743048947408244749 19506619778643355278091781)
                  ·
                    refine ⟨3657491208495629114642209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19506619778643355278091781 3657491208495629114642209)
                    ·
                      refine ⟨2743118406371721835981657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657491208495629114642209 2743118406371721835981657)
                      ·
                        rfl

theorem cell23_5342204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_5342204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342204 prefixEnd_5342204 := by exact prefixLift 5342204
  have htrace : WordTrace (prefixWord ++ tailWord_5342204) baseStart_5342204 baseEnd_5342204 := by
    simpa [prefixWord, tailWord_5342204, baseEnd_5342204] using wordTrace_append hprefix tailTrace_5342204
  have hstable : (prefixWord ++ tailWord_5342204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342204).length < 2 ^ (prefixWord ++ tailWord_5342204).sum := by decide
  have hdescent : baseEnd_5342204 < baseStart_5342204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342244 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 7]
def baseStart_5342244 : Nat := 118140960795 + 5342244 * 2 ^ 59
def prefixEnd_5342244 : Nat := 4983230072969 + 3 ^ 40 * 5342244 * 2
def baseEnd_5342244 : Nat := 304793216177544631053497

theorem tailTrace_5342244 : CollatzResearch.WordTrace tailWord_5342244 prefixEnd_5342244 304793216177544631053497 := by
  unfold tailWord_5342244
  simp only [CollatzResearch.WordTrace]
  refine ⟨97423823028984922740908893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129898430705313230321211857 97423823028984922740908893)
  ·
    refine ⟨36533933635869346027840835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97423823028984922740908893 36533933635869346027840835)
    ·
      refine ⟨54800900453804019041761253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36533933635869346027840835 54800900453804019041761253)
      ·
        refine ⟨10275168835088253570330235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54800900453804019041761253 10275168835088253570330235)
        ·
          refine ⟨15412753252632380355495353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10275168835088253570330235 15412753252632380355495353)
          ·
            refine ⟨11559564939474285266621515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15412753252632380355495353 11559564939474285266621515)
            ·
              refine ⟨17339347409211427899932273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11559564939474285266621515 17339347409211427899932273)
              ·
                refine ⟨13004510556908570924949205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17339347409211427899932273 13004510556908570924949205)
                ·
                  refine ⟨304793216177544631053497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13004510556908570924949205 304793216177544631053497)
                  ·
                    rfl

theorem cell23_5342244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_5342244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342244 prefixEnd_5342244 := by exact prefixLift 5342244
  have htrace : WordTrace (prefixWord ++ tailWord_5342244) baseStart_5342244 baseEnd_5342244 := by
    simpa [prefixWord, tailWord_5342244, baseEnd_5342244] using wordTrace_append hprefix tailTrace_5342244
  have hstable : (prefixWord ++ tailWord_5342244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342244).length < 2 ^ (prefixWord ++ tailWord_5342244).sum := by decide
  have hdescent : baseEnd_5342244 < baseStart_5342244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342254 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_5342254 : Nat := 118140960795 + 5342254 * 2 ^ 59
def prefixEnd_5342254 : Nat := 4983230072969 + 3 ^ 40 * 5342254 * 2
def baseEnd_5342254 : Nat := 2743144080404446640356427

theorem tailTrace_5342254 : CollatzResearch.WordTrace tailWord_5342254 prefixEnd_5342254 2743144080404446640356427 := by
  unfold tailWord_5342254
  simp only [CollatzResearch.WordTrace]
  refine ⟨24356001348491702148710227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129898673858622411459787877 24356001348491702148710227)
  ·
    refine ⟨36534002022737553223065341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24356001348491702148710227 36534002022737553223065341)
    ·
      refine ⟨13700250758526582458649503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36534002022737553223065341 13700250758526582458649503)
      ·
        refine ⟨20550376137789873687974255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13700250758526582458649503 20550376137789873687974255)
        ·
          refine ⟨30825564206684810531961383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20550376137789873687974255 30825564206684810531961383)
          ·
            refine ⟨46238346310027215797942075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30825564206684810531961383 46238346310027215797942075)
            ·
              refine ⟨69357519465040823696913113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46238346310027215797942075 69357519465040823696913113)
              ·
                refine ⟨52018139598780617772684835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69357519465040823696913113 52018139598780617772684835)
                ·
                  refine ⟨78027209398170926659027253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52018139598780617772684835 78027209398170926659027253)
                  ·
                    refine ⟨7315050881078524374283805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78027209398170926659027253 7315050881078524374283805)
                    ·
                      refine ⟨2743144080404446640356427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7315050881078524374283805 2743144080404446640356427)
                      ·
                        rfl

theorem cell23_5342254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_5342254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342254 prefixEnd_5342254 := by exact prefixLift 5342254
  have htrace : WordTrace (prefixWord ++ tailWord_5342254) baseStart_5342254 baseEnd_5342254 := by
    simpa [prefixWord, tailWord_5342254, baseEnd_5342254] using wordTrace_append hprefix tailTrace_5342254
  have hstable : (prefixWord ++ tailWord_5342254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342254).length < 2 ^ (prefixWord ++ tailWord_5342254).sum := by decide
  have hdescent : baseEnd_5342254 < baseStart_5342254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342257 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_5342257 : Nat := 118140960795 + 5342257 * 2 ^ 59
def prefixEnd_5342257 : Nat := 4983230072969 + 3 ^ 40 * 5342257 * 2
def baseEnd_5342257 : Nat := 914381873615470042872971

theorem tailTrace_5342257 : CollatzResearch.WordTrace tailWord_5342257 prefixEnd_5342257 914381873615470042872971 := by
  unfold tailWord_5342257
  simp only [CollatzResearch.WordTrace]
  refine ⟨194848120206922748702041025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129898746804615165801360683 194848120206922748702041025)
  ·
    refine ⟨146136090155192061526530769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194848120206922748702041025 146136090155192061526530769)
    ·
      refine ⟨109602067616394046144898077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146136090155192061526530769 109602067616394046144898077)
      ·
        refine ⟨41100775356147767304336779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109602067616394046144898077 41100775356147767304336779)
        ·
          refine ⟨61651163034221650956505169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41100775356147767304336779 61651163034221650956505169)
          ·
            refine ⟨46238372275666238217378877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61651163034221650956505169 46238372275666238217378877)
            ·
              refine ⟨17339389603374839331517079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46238372275666238217378877 17339389603374839331517079)
              ·
                refine ⟨26009084405062258997275619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17339389603374839331517079 26009084405062258997275619)
                ·
                  refine ⟨39013626607593388495913429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26009084405062258997275619 39013626607593388495913429)
                  ·
                    refine ⟨914381873615470042872971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39013626607593388495913429 914381873615470042872971)
                    ·
                      rfl

theorem cell23_5342257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_5342257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342257 prefixEnd_5342257 := by exact prefixLift 5342257
  have htrace : WordTrace (prefixWord ++ tailWord_5342257) baseStart_5342257 baseEnd_5342257 := by
    simpa [prefixWord, tailWord_5342257, baseEnd_5342257] using wordTrace_append hprefix tailTrace_5342257
  have hstable : (prefixWord ++ tailWord_5342257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342257).length < 2 ^ (prefixWord ++ tailWord_5342257).sum := by decide
  have hdescent : baseEnd_5342257 < baseStart_5342257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342278 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5342278 : Nat := 118140960795 + 5342278 * 2 ^ 59
def prefixEnd_5342278 : Nat := 4983230072969 + 3 ^ 40 * 5342278 * 2
def baseEnd_5342278 : Nat := 304795155993350505161813

theorem tailTrace_5342278 : CollatzResearch.WordTrace tailWord_5342278 prefixEnd_5342278 304795155993350505161813 := by
  unfold tailWord_5342278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089027691870208415267359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129899257426564446192370325 6089027691870208415267359)
  ·
    refine ⟨9133541537805312622901039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089027691870208415267359 9133541537805312622901039)
    ·
      refine ⟨13700312306707968934351559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9133541537805312622901039 13700312306707968934351559)
      ·
        refine ⟨20550468460061953401527339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13700312306707968934351559 20550468460061953401527339)
        ·
          refine ⟨30825702690092930102291009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20550468460061953401527339 30825702690092930102291009)
          ·
            refine ⟨23119277017569697576718257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30825702690092930102291009 23119277017569697576718257)
            ·
              refine ⟨17339457763177273182538693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23119277017569697576718257 17339457763177273182538693)
              ·
                refine ⟨3251148330595738721726005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17339457763177273182538693 3251148330595738721726005)
                ·
                  refine ⟨304795155993350505161813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251148330595738721726005 304795155993350505161813)
                  ·
                    rfl

theorem cell23_5342278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5342278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342278 prefixEnd_5342278 := by exact prefixLift 5342278
  have htrace : WordTrace (prefixWord ++ tailWord_5342278) baseStart_5342278 baseEnd_5342278 := by
    simpa [prefixWord, tailWord_5342278, baseEnd_5342278] using wordTrace_append hprefix tailTrace_5342278
  have hstable : (prefixWord ++ tailWord_5342278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342278).length < 2 ^ (prefixWord ++ tailWord_5342278).sum := by decide
  have hdescent : baseEnd_5342278 < baseStart_5342278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342304 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 3, 4]
def baseStart_5342304 : Nat := 118140960795 + 5342304 * 2 ^ 59
def prefixEnd_5342304 : Nat := 4983230072969 + 3 ^ 40 * 5342304 * 2
def baseEnd_5342304 : Nat := 914389918145723814910399

theorem tailTrace_5342304 : CollatzResearch.WordTrace tailWord_5342304 prefixEnd_5342304 914389918145723814910399 := by
  unfold tailWord_5342304
  simp only [CollatzResearch.WordTrace]
  refine ⟨97424917218876237864500983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129899889625168317152667977 97424917218876237864500983)
  ·
    refine ⟨146137375828314356796751475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97424917218876237864500983 146137375828314356796751475)
    ·
      refine ⟨219206063742471535195127213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146137375828314356796751475 219206063742471535195127213)
      ·
        refine ⟨82202273903426825698172705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219206063742471535195127213 82202273903426825698172705)
        ·
          refine ⟨61651705427570119273629529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82202273903426825698172705 61651705427570119273629529)
          ·
            refine ⟨46238779070677589455222147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61651705427570119273629529 46238779070677589455222147)
            ·
              refine ⟨69358168606016384182833221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46238779070677589455222147 69358168606016384182833221)
              ·
                refine ⟨13004656613628072034281229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69358168606016384182833221 13004656613628072034281229)
                ·
                  refine ⟨4876746230110527012855461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13004656613628072034281229 4876746230110527012855461)
                  ·
                    refine ⟨914389918145723814910399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4876746230110527012855461 914389918145723814910399)
                    ·
                      rfl

theorem cell23_5342304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_5342304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342304 prefixEnd_5342304 := by exact prefixLift 5342304
  have htrace : WordTrace (prefixWord ++ tailWord_5342304) baseStart_5342304 baseEnd_5342304 := by
    simpa [prefixWord, tailWord_5342304, baseEnd_5342304] using wordTrace_append hprefix tailTrace_5342304
  have hstable : (prefixWord ++ tailWord_5342304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342304).length < 2 ^ (prefixWord ++ tailWord_5342304).sum := by decide
  have hdescent : baseEnd_5342304 < baseStart_5342304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342307 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4]
def baseStart_5342307 : Nat := 118140960795 + 5342307 * 2 ^ 59
def prefixEnd_5342307 : Nat := 4983230072969 + 3 ^ 40 * 5342307 * 2
def baseEnd_5342307 : Nat := 2743171294879134932993683

theorem tailTrace_5342307 : CollatzResearch.WordTrace tailWord_5342307 prefixEnd_5342307 2743171294879134932993683 := by
  unfold tailWord_5342307
  simp only [CollatzResearch.WordTrace]
  refine ⟨194849943856741607241361175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129899962571161071494240783 194849943856741607241361175)
  ·
    refine ⟨292274915785112410862041763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194849943856741607241361175 292274915785112410862041763)
    ·
      refine ⟨438412373677668616293062645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292274915785112410862041763 438412373677668616293062645)
      ·
        refine ⟨41101160032281432777474623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 438412373677668616293062645 41101160032281432777474623)
        ·
          refine ⟨61651740048422149166211935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41101160032281432777474623 61651740048422149166211935)
          ·
            refine ⟨92477610072633223749317903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61651740048422149166211935 92477610072633223749317903)
            ·
              refine ⟨138716415108949835623976855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92477610072633223749317903 138716415108949835623976855)
              ·
                refine ⟨208074622663424753435965283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138716415108949835623976855 208074622663424753435965283)
                ·
                  refine ⟨312111933995137130153947925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208074622663424753435965283 312111933995137130153947925)
                  ·
                    refine ⟨14630246906022052975966309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 312111933995137130153947925 14630246906022052975966309)
                    ·
                      refine ⟨2743171294879134932993683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14630246906022052975966309 2743171294879134932993683)
                      ·
                        rfl

theorem cell23_5342307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_5342307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342307 prefixEnd_5342307 := by exact prefixLift 5342307
  have htrace : WordTrace (prefixWord ++ tailWord_5342307) baseStart_5342307 baseEnd_5342307 := by
    simpa [prefixWord, tailWord_5342307, baseEnd_5342307] using wordTrace_append hprefix tailTrace_5342307
  have hstable : (prefixWord ++ tailWord_5342307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342307).length < 2 ^ (prefixWord ++ tailWord_5342307).sum := by decide
  have hdescent : baseEnd_5342307 < baseStart_5342307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342321 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 1, 4]
def baseStart_5342321 : Nat := 118140960795 + 5342321 * 2 ^ 59
def prefixEnd_5342321 : Nat := 4983230072969 + 3 ^ 40 * 5342321 * 2
def baseEnd_5342321 : Nat := 914392827869432626072873

theorem tailTrace_5342321 : CollatzResearch.WordTrace tailWord_5342321 prefixEnd_5342321 914392827869432626072873 := by
  unfold tailWord_5342321
  simp only [CollatzResearch.WordTrace]
  refine ⟨194850454478690887632370817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129900302985793925088247211 194850454478690887632370817)
  ·
    refine ⟨146137840859018165724278113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194850454478690887632370817 146137840859018165724278113)
    ·
      refine ⟨109603380644263624293208585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146137840859018165724278113 109603380644263624293208585)
      ·
        refine ⟨82202535483197718219906439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109603380644263624293208585 82202535483197718219906439)
        ·
          refine ⟨123303803224796577329859659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82202535483197718219906439 123303803224796577329859659)
          ·
            refine ⟨184955704837194865994789489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123303803224796577329859659 184955704837194865994789489)
            ·
              refine ⟨138716778627896149496092117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184955704837194865994789489 138716778627896149496092117)
              ·
                refine ⟨3251174499091316003814659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138716778627896149496092117 3251174499091316003814659)
                ·
                  refine ⟨4876761748636974005721989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251174499091316003814659 4876761748636974005721989)
                  ·
                    refine ⟨914392827869432626072873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4876761748636974005721989 914392827869432626072873)
                    ·
                      rfl

theorem cell23_5342321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_5342321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342321 prefixEnd_5342321 := by exact prefixLift 5342321
  have htrace : WordTrace (prefixWord ++ tailWord_5342321) baseStart_5342321 baseEnd_5342321 := by
    simpa [prefixWord, tailWord_5342321, baseEnd_5342321] using wordTrace_append hprefix tailTrace_5342321
  have hstable : (prefixWord ++ tailWord_5342321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342321).length < 2 ^ (prefixWord ++ tailWord_5342321).sum := by decide
  have hdescent : baseEnd_5342321 < baseStart_5342321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342357 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_5342357 : Nat := 118140960795 + 5342357 * 2 ^ 59
def prefixEnd_5342357 : Nat := 4983230072969 + 3 ^ 40 * 5342357 * 2
def baseEnd_5342357 : Nat := 2743196968911859737368453

theorem tailTrace_5342357 : CollatzResearch.WordTrace tailWord_5342357 prefixEnd_5342357 2743196968911859737368453 := by
  unfold tailWord_5342357
  simp only [CollatzResearch.WordTrace]
  refine ⟨194851767506560465780681325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129901178337706977187120883 194851767506560465780681325)
  ·
    refine ⟨73069412814960174667755497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194851767506560465780681325 73069412814960174667755497)
    ·
      refine ⟨54802059611220131000816623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73069412814960174667755497 54802059611220131000816623)
      ·
        refine ⟨82203089416830196501224935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54802059611220131000816623 82203089416830196501224935)
        ·
          refine ⟨123304634125245294751837403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82203089416830196501224935 123304634125245294751837403)
          ·
            refine ⟨184956951187867942127756105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123304634125245294751837403 184956951187867942127756105)
            ·
              refine ⟨138717713390900956595817079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184956951187867942127756105 138717713390900956595817079)
              ·
                refine ⟨208076570086351434893725619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138717713390900956595817079 208076570086351434893725619)
                ·
                  refine ⟨312114855129527152340588429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208076570086351434893725619 312114855129527152340588429)
                  ·
                    refine ⟨117043070673572682127720661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312114855129527152340588429 117043070673572682127720661)
                    ·
                      refine ⟨2743196968911859737368453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117043070673572682127720661 2743196968911859737368453)
                      ·
                        rfl

theorem cell23_5342357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_5342357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342357 prefixEnd_5342357 := by exact prefixLift 5342357
  have htrace : WordTrace (prefixWord ++ tailWord_5342357) baseStart_5342357 baseEnd_5342357 := by
    simpa [prefixWord, tailWord_5342357, baseEnd_5342357] using wordTrace_append hprefix tailTrace_5342357
  have hstable : (prefixWord ++ tailWord_5342357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342357).length < 2 ^ (prefixWord ++ tailWord_5342357).sum := by decide
  have hdescent : baseEnd_5342357 < baseStart_5342357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342445 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_5342445 : Nat := 118140960795 + 5342445 * 2 ^ 59
def prefixEnd_5342445 : Nat := 4983230072969 + 3 ^ 40 * 5342445 * 2
def baseEnd_5342445 : Nat := 914414051736485131022683

theorem tailTrace_5342445 : CollatzResearch.WordTrace tailWord_5342445 prefixEnd_5342445 914414051736485131022683 := by
  unfold tailWord_5342445
  simp only [CollatzResearch.WordTrace]
  refine ⟨194854977130241656809884789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129903318086827771206589859 194854977130241656809884789)
  ·
    refine ⟨18267654105960155325926699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194854977130241656809884789 18267654105960155325926699)
    ·
      refine ⟨27401481158940232988890049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18267654105960155325926699 27401481158940232988890049)
      ·
        refine ⟨20551110869205174741667537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27401481158940232988890049 20551110869205174741667537)
        ·
          refine ⟨15413333151903881056250653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20551110869205174741667537 15413333151903881056250653)
          ·
            refine ⟨5779999931963955396093995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15413333151903881056250653 5779999931963955396093995)
            ·
              refine ⟨8669999897945933094140993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779999931963955396093995 8669999897945933094140993)
              ·
                refine ⟨6502499923459449820605745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8669999897945933094140993 6502499923459449820605745)
                ·
                  refine ⟨4876874942594587365454309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6502499923459449820605745 4876874942594587365454309)
                  ·
                    refine ⟨914414051736485131022683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4876874942594587365454309 914414051736485131022683)
                    ·
                      rfl

theorem cell23_5342445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_5342445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342445 prefixEnd_5342445 := by exact prefixLift 5342445
  have htrace : WordTrace (prefixWord ++ tailWord_5342445) baseStart_5342445 baseEnd_5342445 := by
    simpa [prefixWord, tailWord_5342445, baseEnd_5342445] using wordTrace_append hprefix tailTrace_5342445
  have hstable : (prefixWord ++ tailWord_5342445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342445).length < 2 ^ (prefixWord ++ tailWord_5342445).sum := by decide
  have hdescent : baseEnd_5342445 < baseStart_5342445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342468 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_5342468 : Nat := 118140960795 + 5342468 * 2 ^ 59
def prefixEnd_5342468 : Nat := 4983230072969 + 3 ^ 40 * 5342468 * 2
def baseEnd_5342468 : Nat := 2743253965264508803080443

theorem tailTrace_5342468 : CollatzResearch.WordTrace tailWord_5342468 prefixEnd_5342468 2743253965264508803080443 := by
  unfold tailWord_5342468
  simp only [CollatzResearch.WordTrace]
  refine ⟨97427908004579165868986029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129903877339438887825314705 97427908004579165868986029)
  ·
    refine ⟨36535465501717187200869761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97427908004579165868986029 36535465501717187200869761)
    ·
      refine ⟨27401599126287890400652321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36535465501717187200869761 27401599126287890400652321)
      ·
        refine ⟨20551199344715917800489241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27401599126287890400652321 20551199344715917800489241)
        ·
          refine ⟨15413399508536938350366931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20551199344715917800489241 15413399508536938350366931)
          ·
            refine ⟨23120099262805407525550397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15413399508536938350366931 23120099262805407525550397)
            ·
              refine ⟨8670037223552027822081399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23120099262805407525550397 8670037223552027822081399)
              ·
                refine ⟨13005055835328041733122099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670037223552027822081399 13005055835328041733122099)
                ·
                  refine ⟨19507583752992062599683149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13005055835328041733122099 19507583752992062599683149)
                  ·
                    refine ⟨7315343907372023474881181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19507583752992062599683149 7315343907372023474881181)
                    ·
                      refine ⟨2743253965264508803080443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7315343907372023474881181 2743253965264508803080443)
                      ·
                        rfl

theorem cell23_5342468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_5342468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342468 prefixEnd_5342468 := by exact prefixLift 5342468
  have htrace : WordTrace (prefixWord ++ tailWord_5342468) baseStart_5342468 baseEnd_5342468 := by
    simpa [prefixWord, tailWord_5342468, baseEnd_5342468] using wordTrace_append hprefix tailTrace_5342468
  have hstable : (prefixWord ++ tailWord_5342468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342468).length < 2 ^ (prefixWord ++ tailWord_5342468).sum := by decide
  have hdescent : baseEnd_5342468 < baseStart_5342468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342491 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 3, 4, 2]
def baseStart_5342491 : Nat := 118140960795 + 5342491 * 2 ^ 59
def prefixEnd_5342491 : Nat := 4983230072969 + 3 ^ 40 * 5342491 * 2
def baseEnd_5342491 : Nat := 2743265775319562213092837

theorem tailTrace_5342491 : CollatzResearch.WordTrace tailWord_5342491 prefixEnd_5342491 2743265775319562213092837 := by
  unfold tailWord_5342491
  simp only [CollatzResearch.WordTrace]
  refine ⟨194856654888075006666059327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129904436592050004444039551 194856654888075006666059327)
  ·
    refine ⟨292284982332112509999088991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194856654888075006666059327 292284982332112509999088991)
    ·
      refine ⟨438427473498168764998633487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292284982332112509999088991 438427473498168764998633487)
      ·
        refine ⟨657641210247253147497950231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438427473498168764998633487 657641210247253147497950231)
        ·
          refine ⟨986461815370879721246925347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657641210247253147497950231 986461815370879721246925347)
          ·
            refine ⟨1479692723056319581870388021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986461815370879721246925347 1479692723056319581870388021)
            ·
              refine ⟨138721192786529960800348877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1479692723056319581870388021 138721192786529960800348877)
              ·
                refine ⟨52020447294948735300130829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138721192786529960800348877 52020447294948735300130829)
                ·
                  refine ⟨19507667735605775737549061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52020447294948735300130829 19507667735605775737549061)
                  ·
                    refine ⟨3657687700426082950790449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19507667735605775737549061 3657687700426082950790449)
                    ·
                      refine ⟨2743265775319562213092837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657687700426082950790449 2743265775319562213092837)
                      ·
                        rfl

theorem cell23_5342491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4, 2].length) (baseStart_5342491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342491 prefixEnd_5342491 := by exact prefixLift 5342491
  have htrace : WordTrace (prefixWord ++ tailWord_5342491) baseStart_5342491 baseEnd_5342491 := by
    simpa [prefixWord, tailWord_5342491, baseEnd_5342491] using wordTrace_append hprefix tailTrace_5342491
  have hstable : (prefixWord ++ tailWord_5342491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342491).length < 2 ^ (prefixWord ++ tailWord_5342491).sum := by decide
  have hdescent : baseEnd_5342491 < baseStart_5342491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342548 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 5]
def baseStart_5342548 : Nat := 118140960795 + 5342548 * 2 ^ 59
def prefixEnd_5342548 : Nat := 4983230072969 + 3 ^ 40 * 5342548 * 2
def baseEnd_5342548 : Nat := 304810560412985387786675

theorem tailTrace_5342548 : CollatzResearch.WordTrace tailWord_5342548 prefixEnd_5342548 304810560412985387786675 := by
  unfold tailWord_5342548
  simp only [CollatzResearch.WordTrace]
  refine ⟨97429366924434252700442149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129905822565912336933922865 97429366924434252700442149)
  ·
    refine ⟨18268006298331422381332903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97429366924434252700442149 18268006298331422381332903)
    ·
      refine ⟨27402009447497133571999355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18268006298331422381332903 27402009447497133571999355)
      ·
        refine ⟨41103014171245700357999033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27402009447497133571999355 41103014171245700357999033)
        ·
          refine ⟨30827260628434275268499275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41103014171245700357999033 30827260628434275268499275)
          ·
            refine ⟨46240890942651412902748913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30827260628434275268499275 46240890942651412902748913)
            ·
              refine ⟨34680668206988559677061685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46240890942651412902748913 34680668206988559677061685)
              ·
                refine ⟨3251312644405177469724533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34680668206988559677061685 3251312644405177469724533)
                ·
                  refine ⟨304810560412985387786675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251312644405177469724533 304810560412985387786675)
                  ·
                    rfl

theorem cell23_5342548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_5342548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342548 prefixEnd_5342548 := by exact prefixLift 5342548
  have htrace : WordTrace (prefixWord ++ tailWord_5342548) baseStart_5342548 baseEnd_5342548 := by
    simpa [prefixWord, tailWord_5342548, baseEnd_5342548] using wordTrace_append hprefix tailTrace_5342548
  have hstable : (prefixWord ++ tailWord_5342548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342548).length < 2 ^ (prefixWord ++ tailWord_5342548).sum := by decide
  have hdescent : baseEnd_5342548 < baseStart_5342548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342618 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_5342618 : Nat := 118140960795 + 5342618 * 2 ^ 59
def prefixEnd_5342618 : Nat := 4983230072969 + 3 ^ 40 * 5342618 * 2
def baseEnd_5342618 : Nat := 2743330987362683216204753

theorem tailTrace_5342618 : CollatzResearch.WordTrace tailWord_5342618 prefixEnd_5342618 2743330987362683216204753 := by
  unfold tailWord_5342618
  simp only [CollatzResearch.WordTrace]
  refine ⟨48715321739653726838983127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129907524639076604903955005 48715321739653726838983127)
  ·
    refine ⟨73072982609480590258474691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48715321739653726838983127 73072982609480590258474691)
    ·
      refine ⟨109609473914220885387712037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73072982609480590258474691 109609473914220885387712037)
      ·
        refine ⟨20551776358916416010196007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109609473914220885387712037 20551776358916416010196007)
        ·
          refine ⟨30827664538374624015294011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20551776358916416010196007 30827664538374624015294011)
          ·
            refine ⟨46241496807561936022941017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30827664538374624015294011 46241496807561936022941017)
            ·
              refine ⟨34681122605671452017205763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46241496807561936022941017 34681122605671452017205763)
              ·
                refine ⟨52021683908507178025808645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34681122605671452017205763 52021683908507178025808645)
                ·
                  refine ⟨9754065732845095879839121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52021683908507178025808645 9754065732845095879839121)
                  ·
                    refine ⟨7315549299633821909879341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9754065732845095879839121 7315549299633821909879341)
                    ·
                      refine ⟨2743330987362683216204753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7315549299633821909879341 2743330987362683216204753)
                      ·
                        rfl

theorem cell23_5342618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_5342618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342618 prefixEnd_5342618 := by exact prefixLift 5342618
  have htrace : WordTrace (prefixWord ++ tailWord_5342618) baseStart_5342618 baseEnd_5342618 := by
    simpa [prefixWord, tailWord_5342618, baseEnd_5342618] using wordTrace_append hprefix tailTrace_5342618
  have hstable : (prefixWord ++ tailWord_5342618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342618).length < 2 ^ (prefixWord ++ tailWord_5342618).sum := by decide
  have hdescent : baseEnd_5342618 < baseStart_5342618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342641 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5342641 : Nat := 118140960795 + 5342641 * 2 ^ 59
def prefixEnd_5342641 : Nat := 4983230072969 + 3 ^ 40 * 5342641 * 2
def baseEnd_5342641 : Nat := 2743342797417736626217147

theorem tailTrace_5342641 : CollatzResearch.WordTrace tailWord_5342641 prefixEnd_5342641 2743342797417736626217147 := by
  unfold tailWord_5342641
  simp only [CollatzResearch.WordTrace]
  refine ⟨194862125837531582284019777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129908083891687721522679851 194862125837531582284019777)
  ·
    refine ⟨146146594378148686713014833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194862125837531582284019777 146146594378148686713014833)
    ·
      refine ⟨109609945783611515034761125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146146594378148686713014833 109609945783611515034761125)
      ·
        refine ⟨20551864834427159069017711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109609945783611515034761125 20551864834427159069017711)
        ·
          refine ⟨30827797251640738603526567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20551864834427159069017711 30827797251640738603526567)
          ·
            refine ⟨46241695877461107905289851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30827797251640738603526567 46241695877461107905289851)
            ·
              refine ⟨69362543816191661857934777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46241695877461107905289851 69362543816191661857934777)
              ·
                refine ⟨52021907862143746393451083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69362543816191661857934777 52021907862143746393451083)
                ·
                  refine ⟨78032861793215619590176625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52021907862143746393451083 78032861793215619590176625)
                  ·
                    refine ⟨58524646344911714692632469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78032861793215619590176625 58524646344911714692632469)
                    ·
                      refine ⟨2743342797417736626217147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58524646344911714692632469 2743342797417736626217147)
                      ·
                        rfl

theorem cell23_5342641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5342641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342641 prefixEnd_5342641 := by exact prefixLift 5342641
  have htrace : WordTrace (prefixWord ++ tailWord_5342641) baseStart_5342641 baseEnd_5342641 := by
    simpa [prefixWord, tailWord_5342641, baseEnd_5342641] using wordTrace_append hprefix tailTrace_5342641
  have hstable : (prefixWord ++ tailWord_5342641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342641).length < 2 ^ (prefixWord ++ tailWord_5342641).sum := by decide
  have hdescent : baseEnd_5342641 < baseStart_5342641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342682 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_5342682 : Nat := 118140960795 + 5342682 * 2 ^ 59
def prefixEnd_5342682 : Nat := 4983230072969 + 3 ^ 40 * 5342682 * 2
def baseEnd_5342682 : Nat := 2743363850124570965804459

theorem tailTrace_5342682 : CollatzResearch.WordTrace tailWord_5342682 prefixEnd_5342682 2743363850124570965804459 := by
  unfold tailWord_5342682
  simp only [CollatzResearch.WordTrace]
  refine ⟨48715905307595761571565575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129909080820255364190841533 48715905307595761571565575)
  ·
    refine ⟨73073857961393642357348363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48715905307595761571565575 73073857961393642357348363)
    ·
      refine ⟨109610786942090463536022545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73073857961393642357348363 109610786942090463536022545)
      ·
        refine ⟨82208090206567847652016909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109610786942090463536022545 82208090206567847652016909)
        ·
          refine ⟨30828033827462942869506341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82208090206567847652016909 30828033827462942869506341)
          ·
            refine ⟨5780256342649301788032439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30828033827462942869506341 5780256342649301788032439)
            ·
              refine ⟨8670384513973952682048659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5780256342649301788032439 8670384513973952682048659)
              ·
                refine ⟨13005576770960929023072989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670384513973952682048659 13005576770960929023072989)
                ·
                  refine ⟨4877091289110348383652371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13005576770960929023072989 4877091289110348383652371)
                  ·
                    refine ⟨7315636933665522575478557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4877091289110348383652371 7315636933665522575478557)
                    ·
                      refine ⟨2743363850124570965804459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7315636933665522575478557 2743363850124570965804459)
                      ·
                        rfl

theorem cell23_5342682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_5342682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342682 prefixEnd_5342682 := by exact prefixLift 5342682
  have htrace : WordTrace (prefixWord ++ tailWord_5342682) baseStart_5342682 baseEnd_5342682 := by
    simpa [prefixWord, tailWord_5342682, baseEnd_5342682] using wordTrace_append hprefix tailTrace_5342682
  have hstable : (prefixWord ++ tailWord_5342682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342682).length < 2 ^ (prefixWord ++ tailWord_5342682).sum := by decide
  have hdescent : baseEnd_5342682 < baseStart_5342682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342688 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 6, 2]
def baseStart_5342688 : Nat := 118140960795 + 5342688 * 2 ^ 59
def prefixEnd_5342688 : Nat := 4983230072969 + 3 ^ 40 * 5342688 * 2
def baseEnd_5342688 : Nat := 2743366931008497942329431

theorem tailTrace_5342688 : CollatzResearch.WordTrace tailWord_5342688 prefixEnd_5342688 2743366931008497942329431 := by
  unfold tailWord_5342688
  simp only [CollatzResearch.WordTrace]
  refine ⟨97431920034180654655490359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129909226712240872873987145 97431920034180654655490359)
  ·
    refine ⟨146147880051270981983235539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97431920034180654655490359 146147880051270981983235539)
    ·
      refine ⟨219221820076906472974853309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146147880051270981983235539 219221820076906472974853309)
      ·
        refine ⟨82208182528839927365569991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219221820076906472974853309 82208182528839927365569991)
        ·
          refine ⟨123312273793259891048354987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82208182528839927365569991 123312273793259891048354987)
          ·
            refine ⟨184968410689889836572532481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123312273793259891048354987 184968410689889836572532481)
            ·
              refine ⟨138726308017417377429399361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184968410689889836572532481 138726308017417377429399361)
              ·
                refine ⟨104044731013063033072049521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138726308017417377429399361 104044731013063033072049521)
                ·
                  refine ⟨78033548259797274804037141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104044731013063033072049521 78033548259797274804037141)
                  ·
                    refine ⟨3657822574677997256439241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78033548259797274804037141 3657822574677997256439241)
                    ·
                      refine ⟨2743366931008497942329431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657822574677997256439241 2743366931008497942329431)
                      ·
                        rfl

theorem cell23_5342688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_5342688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342688 prefixEnd_5342688 := by exact prefixLift 5342688
  have htrace : WordTrace (prefixWord ++ tailWord_5342688) baseStart_5342688 baseEnd_5342688 := by
    simpa [prefixWord, tailWord_5342688, baseEnd_5342688] using wordTrace_append hprefix tailTrace_5342688
  have hstable : (prefixWord ++ tailWord_5342688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342688).length < 2 ^ (prefixWord ++ tailWord_5342688).sum := by decide
  have hdescent : baseEnd_5342688 < baseStart_5342688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342705 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_5342705 : Nat := 118140960795 + 5342705 * 2 ^ 59
def prefixEnd_5342705 : Nat := 4983230072969 + 3 ^ 40 * 5342705 * 2
def baseEnd_5342705 : Nat := 2743375660179624375816853

theorem tailTrace_5342705 : CollatzResearch.WordTrace tailWord_5342705 prefixEnd_5342705 2743375660179624375816853 := by
  unfold tailWord_5342705
  simp only [CollatzResearch.WordTrace]
  refine ⟨194864460109299721214349569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129909640072866480809566379 194864460109299721214349569)
  ·
    refine ⟨146148345081974790910762177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194864460109299721214349569 146148345081974790910762177)
    ·
      refine ⟨109611258811481093183071633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146148345081974790910762177 109611258811481093183071633)
      ·
        refine ⟨82208444108610819887303725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109611258811481093183071633 82208444108610819887303725)
        ·
          refine ⟨30828166540729057457738897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82208444108610819887303725 30828166540729057457738897)
          ·
            refine ⟨23121124905546793093304173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30828166540729057457738897 23121124905546793093304173)
            ·
              refine ⟨8670421839580047409989065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23121124905546793093304173 8670421839580047409989065)
              ·
                refine ⟨6502816379685035557491799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8670421839580047409989065 6502816379685035557491799)
                ·
                  refine ⟨9754224569527553336237699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6502816379685035557491799 9754224569527553336237699)
                  ·
                    refine ⟨14631336854291330004356549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9754224569527553336237699 14631336854291330004356549)
                    ·
                      refine ⟨2743375660179624375816853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14631336854291330004356549 2743375660179624375816853)
                      ·
                        rfl

theorem cell23_5342705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_5342705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342705 prefixEnd_5342705 := by exact prefixLift 5342705
  have htrace : WordTrace (prefixWord ++ tailWord_5342705) baseStart_5342705 baseEnd_5342705 := by
    simpa [prefixWord, tailWord_5342705, baseEnd_5342705] using wordTrace_append hprefix tailTrace_5342705
  have hstable : (prefixWord ++ tailWord_5342705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342705).length < 2 ^ (prefixWord ++ tailWord_5342705).sum := by decide
  have hdescent : baseEnd_5342705 < baseStart_5342705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342709 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5342709 : Nat := 118140960795 + 5342709 * 2 ^ 59
def prefixEnd_5342709 : Nat := 4983230072969 + 3 ^ 40 * 5342709 * 2
def baseEnd_5342709 : Nat := 2743377714102242360166835

theorem tailTrace_5342709 : CollatzResearch.WordTrace tailWord_5342709 prefixEnd_5342709 2743377714102242360166835 := by
  unfold tailWord_5342709
  simp only [CollatzResearch.WordTrace]
  refine ⟨194864606001285229897495181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129909737334190153264996787 194864606001285229897495181)
  ·
    refine ⟨73074227250481961211560693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194864606001285229897495181 73074227250481961211560693)
    ·
      refine ⟨6850708804732683863583815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73074227250481961211560693 6850708804732683863583815)
      ·
        refine ⟨10276063207099025795375723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850708804732683863583815 10276063207099025795375723)
        ·
          refine ⟨15414094810648538693063585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10276063207099025795375723 15414094810648538693063585)
          ·
            refine ⟨11560571107986404019797689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15414094810648538693063585 11560571107986404019797689)
            ·
              refine ⟨8670428330989803014848267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11560571107986404019797689 8670428330989803014848267)
              ·
                refine ⟨13005642496484704522272401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670428330989803014848267 13005642496484704522272401)
                ·
                  refine ⟨9754231872363528391704301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13005642496484704522272401 9754231872363528391704301)
                  ·
                    refine ⟨3657836952136323146889113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9754231872363528391704301 3657836952136323146889113)
                    ·
                      refine ⟨2743377714102242360166835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657836952136323146889113 2743377714102242360166835)
                      ·
                        rfl

theorem cell23_5342709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5342709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342709 prefixEnd_5342709 := by exact prefixLift 5342709
  have htrace : WordTrace (prefixWord ++ tailWord_5342709) baseStart_5342709 baseEnd_5342709 := by
    simpa [prefixWord, tailWord_5342709, baseEnd_5342709] using wordTrace_append hprefix tailTrace_5342709
  have hstable : (prefixWord ++ tailWord_5342709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342709).length < 2 ^ (prefixWord ++ tailWord_5342709).sum := by decide
  have hdescent : baseEnd_5342709 < baseStart_5342709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342732 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_5342732 : Nat := 118140960795 + 5342732 * 2 ^ 59
def prefixEnd_5342732 : Nat := 4983230072969 + 3 ^ 40 * 5342732 * 2
def baseEnd_5342732 : Nat := 914463174719098590059743

theorem tailTrace_5342732 : CollatzResearch.WordTrace tailWord_5342732 prefixEnd_5342732 914463174719098590059743 := by
  unfold tailWord_5342732
  simp only [CollatzResearch.WordTrace]
  refine ⟨97432722440100952412791225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129910296586801269883721633 97432722440100952412791225)
  ·
    refine ⟨73074541830075714309593419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97432722440100952412791225 73074541830075714309593419)
    ·
      refine ⟨109611812745113571464390129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73074541830075714309593419 109611812745113571464390129)
      ·
        refine ⟨82208859558835178598292597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109611812745113571464390129 82208859558835178598292597)
        ·
          refine ⟨7707080583640797993589931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82208859558835178598292597 7707080583640797993589931)
          ·
            refine ⟨11560620875461196990384897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707080583640797993589931 11560620875461196990384897)
            ·
              refine ⟨8670465656595897742788673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11560620875461196990384897 8670465656595897742788673)
              ·
                refine ⟨6502849242446923307091505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8670465656595897742788673 6502849242446923307091505)
                ·
                  refine ⟨4877136931835192480318629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6502849242446923307091505 4877136931835192480318629)
                  ·
                    refine ⟨914463174719098590059743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4877136931835192480318629 914463174719098590059743)
                    ·
                      rfl

theorem cell23_5342732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_5342732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342732 prefixEnd_5342732 := by exact prefixLift 5342732
  have htrace : WordTrace (prefixWord ++ tailWord_5342732) baseStart_5342732 baseEnd_5342732 := by
    simpa [prefixWord, tailWord_5342732, baseEnd_5342732] using wordTrace_append hprefix tailTrace_5342732
  have hstable : (prefixWord ++ tailWord_5342732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342732).length < 2 ^ (prefixWord ++ tailWord_5342732).sum := by decide
  have hdescent : baseEnd_5342732 < baseStart_5342732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342733 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5342733 : Nat := 118140960795 + 5342733 * 2 ^ 59
def prefixEnd_5342733 : Nat := 4983230072969 + 3 ^ 40 * 5342733 * 2
def baseEnd_5342733 : Nat := 2743390037637950266266725

theorem tailTrace_5342733 : CollatzResearch.WordTrace tailWord_5342733 prefixEnd_5342733 2743390037637950266266725 := by
  unfold tailWord_5342733
  simp only [CollatzResearch.WordTrace]
  refine ⟨194865481353198281996368853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129910320902132187997579235 194865481353198281996368853)
  ·
    refine ⟨4567159719215584734289895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 194865481353198281996368853 4567159719215584734289895)
    ·
      refine ⟨6850739578823377101434843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4567159719215584734289895 6850739578823377101434843)
      ·
        refine ⟨10276109368235065652152265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850739578823377101434843 10276109368235065652152265)
        ·
          refine ⟨7707082026176299239114199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10276109368235065652152265 7707082026176299239114199)
          ·
            refine ⟨11560623039264448858671299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707082026176299239114199 11560623039264448858671299)
            ·
              refine ⟨17340934558896673288006949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11560623039264448858671299 17340934558896673288006949)
              ·
                refine ⟨3251425229793126241501303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17340934558896673288006949 3251425229793126241501303)
                ·
                  refine ⟨4877137844689689362251955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251425229793126241501303 4877137844689689362251955)
                  ·
                    refine ⟨7315706767034534043377933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4877137844689689362251955 7315706767034534043377933)
                    ·
                      refine ⟨2743390037637950266266725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7315706767034534043377933 2743390037637950266266725)
                      ·
                        rfl

theorem cell23_5342733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5342733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342733 prefixEnd_5342733 := by exact prefixLift 5342733
  have htrace : WordTrace (prefixWord ++ tailWord_5342733) baseStart_5342733 baseEnd_5342733 := by
    simpa [prefixWord, tailWord_5342733, baseEnd_5342733] using wordTrace_append hprefix tailTrace_5342733
  have hstable : (prefixWord ++ tailWord_5342733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342733).length < 2 ^ (prefixWord ++ tailWord_5342733).sum := by decide
  have hdescent : baseEnd_5342733 < baseStart_5342733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342739 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 1, 2, 2]
def baseStart_5342739 : Nat := 118140960795 + 5342739 * 2 ^ 59
def prefixEnd_5342739 : Nat := 4983230072969 + 3 ^ 40 * 5342739 * 2
def baseEnd_5342739 : Nat := 2743393118521877242791697

theorem tailTrace_5342739 : CollatzResearch.WordTrace tailWord_5342739 prefixEnd_5342739 2743393118521877242791697 := by
  unfold tailWord_5342739
  simp only [CollatzResearch.WordTrace]
  refine ⟨194865700191176545021087271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129910466794117696680724847 194865700191176545021087271)
  ·
    refine ⟨292298550286764817531630907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194865700191176545021087271 292298550286764817531630907)
    ·
      refine ⟨438447825430147226297446361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292298550286764817531630907 438447825430147226297446361)
      ·
        refine ⟨328835869072610419723084771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438447825430147226297446361 328835869072610419723084771)
        ·
          refine ⟨493253803608915629584627157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328835869072610419723084771 493253803608915629584627157)
          ·
            refine ⟨11560636022083960068389699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 493253803608915629584627157 11560636022083960068389699)
            ·
              refine ⟨17340954033125940102584549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11560636022083960068389699 17340954033125940102584549)
              ·
                refine ⟨3251428881211113769234603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17340954033125940102584549 3251428881211113769234603)
                ·
                  refine ⟨4877143321816670653851905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251428881211113769234603 4877143321816670653851905)
                  ·
                    refine ⟨3657857491362502990388929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4877143321816670653851905 3657857491362502990388929)
                    ·
                      refine ⟨2743393118521877242791697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3657857491362502990388929 2743393118521877242791697)
                      ·
                        rfl

theorem cell23_5342739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 2, 2].length) (baseStart_5342739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342739 prefixEnd_5342739 := by exact prefixLift 5342739
  have htrace : WordTrace (prefixWord ++ tailWord_5342739) baseStart_5342739 baseEnd_5342739 := by
    simpa [prefixWord, tailWord_5342739, baseEnd_5342739] using wordTrace_append hprefix tailTrace_5342739
  have hstable : (prefixWord ++ tailWord_5342739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342739).length < 2 ^ (prefixWord ++ tailWord_5342739).sum := by decide
  have hdescent : baseEnd_5342739 < baseStart_5342739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342798 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_5342798 : Nat := 118140960795 + 5342798 * 2 ^ 59
def prefixEnd_5342798 : Nat := 4983230072969 + 3 ^ 40 * 5342798 * 2
def baseEnd_5342798 : Nat := 2743423413880492511953925

theorem tailTrace_5342798 : CollatzResearch.WordTrace tailWord_5342798 prefixEnd_5342798 2743423413880492511953925 := by
  unfold tailWord_5342798
  simp only [CollatzResearch.WordTrace]
  refine ⟨24358481512245349762185631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129911901398641865398323365 24358481512245349762185631)
  ·
    refine ⟨36537722268368024643278447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24358481512245349762185631 36537722268368024643278447)
    ·
      refine ⟨54806583402552036964917671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36537722268368024643278447 54806583402552036964917671)
      ·
        refine ⟨82209875103828055447376507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54806583402552036964917671 82209875103828055447376507)
        ·
          refine ⟨123314812655742083171064761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82209875103828055447376507 123314812655742083171064761)
          ·
            refine ⟨92486109491806562378298571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123314812655742083171064761 92486109491806562378298571)
            ·
              refine ⟨138729164237709843567447857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92486109491806562378298571 138729164237709843567447857)
              ·
                refine ⟨104046873178282382675585893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138729164237709843567447857 104046873178282382675585893)
                ·
                  refine ⟨19508788720927946751672355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104046873178282382675585893 19508788720927946751672355)
                  ·
                    refine ⟨29263183081391920127508533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19508788720927946751672355 29263183081391920127508533)
                    ·
                      refine ⟨2743423413880492511953925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29263183081391920127508533 2743423413880492511953925)
                      ·
                        rfl

theorem cell23_5342798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_5342798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342798 prefixEnd_5342798 := by exact prefixLift 5342798
  have htrace : WordTrace (prefixWord ++ tailWord_5342798) baseStart_5342798 baseEnd_5342798 := by
    simpa [prefixWord, tailWord_5342798, baseEnd_5342798] using wordTrace_append hprefix tailTrace_5342798
  have hstable : (prefixWord ++ tailWord_5342798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342798).length < 2 ^ (prefixWord ++ tailWord_5342798).sum := by decide
  have hdescent : baseEnd_5342798 < baseStart_5342798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342852 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 7]
def baseStart_5342852 : Nat := 118140960795 + 5342852 * 2 ^ 59
def prefixEnd_5342852 : Nat := 4983230072969 + 3 ^ 40 * 5342852 * 2
def baseEnd_5342852 : Nat := 304827904648426144519853

theorem tailTrace_5342852 : CollatzResearch.WordTrace tailWord_5342852 prefixEnd_5342852 304827904648426144519853 := by
  unfold tailWord_5342852
  simp only [CollatzResearch.WordTrace]
  refine ⟨97434910819883582659975405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129913214426511443546633873 97434910819883582659975405)
  ·
    refine ⟨36538091557456343497490777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97434910819883582659975405 36538091557456343497490777)
    ·
      refine ⟨27403568668092257623118083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36538091557456343497490777 27403568668092257623118083)
      ·
        refine ⟨41105353002138386434677125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27403568668092257623118083 41105353002138386434677125)
        ·
          refine ⟨7707253687900947456501961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41105353002138386434677125 7707253687900947456501961)
          ·
            refine ⟨5780440265925710592376471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7707253687900947456501961 5780440265925710592376471)
            ·
              refine ⟨8670660398888565888564707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5780440265925710592376471 8670660398888565888564707)
              ·
                refine ⟨13005990598332848832847061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670660398888565888564707 13005990598332848832847061)
                ·
                  refine ⟨304827904648426144519853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13005990598332848832847061 304827904648426144519853)
                  ·
                    rfl

theorem cell23_5342852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_5342852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342852 prefixEnd_5342852 := by exact prefixLift 5342852
  have htrace : WordTrace (prefixWord ++ tailWord_5342852) baseStart_5342852 baseEnd_5342852 := by
    simpa [prefixWord, tailWord_5342852, baseEnd_5342852] using wordTrace_append hprefix tailTrace_5342852
  have hstable : (prefixWord ++ tailWord_5342852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342852).length < 2 ^ (prefixWord ++ tailWord_5342852).sum := by decide
  have hdescent : baseEnd_5342852 < baseStart_5342852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342885 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_5342885 : Nat := 118140960795 + 5342885 * 2 ^ 59
def prefixEnd_5342885 : Nat := 4983230072969 + 3 ^ 40 * 5342885 * 2
def baseEnd_5342885 : Nat := 2743468086697433671566025

theorem tailTrace_5342885 : CollatzResearch.WordTrace tailWord_5342885 prefixEnd_5342885 2743468086697433671566025 := by
  unfold tailWord_5342885
  simp only [CollatzResearch.WordTrace]
  refine ⟨194871025248647611955902109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129914016832431741303934739 194871025248647611955902109)
  ·
    refine ⟨73076634468242854483463291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194871025248647611955902109 73076634468242854483463291)
    ·
      refine ⟨109614951702364281725194937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73076634468242854483463291 109614951702364281725194937)
      ·
        refine ⟨82211213776773211293896203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109614951702364281725194937 82211213776773211293896203)
        ·
          refine ⟨123316820665159816940844305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82211213776773211293896203 123316820665159816940844305)
          ·
            refine ⟨92487615498869862705633229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123316820665159816940844305 92487615498869862705633229)
            ·
              refine ⟨34682855812076198514612461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92487615498869862705633229 34682855812076198514612461)
              ·
                refine ⟨13006070929528574442979673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34682855812076198514612461 13006070929528574442979673)
                ·
                  refine ⟨9754553197146430832234755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13006070929528574442979673 9754553197146430832234755)
                  ·
                    refine ⟨14631829795719646248352133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9754553197146430832234755 14631829795719646248352133)
                    ·
                      refine ⟨2743468086697433671566025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14631829795719646248352133 2743468086697433671566025)
                      ·
                        rfl

theorem cell23_5342885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_5342885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342885 prefixEnd_5342885 := by exact prefixLift 5342885
  have htrace : WordTrace (prefixWord ++ tailWord_5342885) baseStart_5342885 baseEnd_5342885 := by
    simpa [prefixWord, tailWord_5342885, baseEnd_5342885] using wordTrace_append hprefix tailTrace_5342885
  have hstable : (prefixWord ++ tailWord_5342885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342885).length < 2 ^ (prefixWord ++ tailWord_5342885).sum := by decide
  have hdescent : baseEnd_5342885 < baseStart_5342885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342928 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_5342928 : Nat := 118140960795 + 5342928 * 2 ^ 59
def prefixEnd_5342928 : Nat := 4983230072969 + 3 ^ 40 * 5342928 * 2
def baseEnd_5342928 : Nat := 2743490166365577003328327

theorem tailTrace_5342928 : CollatzResearch.WordTrace tailWord_5342928 prefixEnd_5342928 2743490166365577003328327 := by
  unfold tailWord_5342928
  simp only [CollatzResearch.WordTrace]
  refine ⟨97436296793745915149858719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129915062391661220199811625 97436296793745915149858719)
  ·
    refine ⟨146154445190618872724788079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97436296793745915149858719 146154445190618872724788079)
    ·
      refine ⟨219231667785928309087182119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146154445190618872724788079 219231667785928309087182119)
      ·
        refine ⟨328847501678892463630773179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219231667785928309087182119 328847501678892463630773179)
        ·
          refine ⟨493271252518338695446159769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328847501678892463630773179 493271252518338695446159769)
          ·
            refine ⟨369953439388754021584619827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493271252518338695446159769 369953439388754021584619827)
            ·
              refine ⟨554930159083131032376929741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369953439388754021584619827 554930159083131032376929741)
              ·
                refine ⟨208098809656174137141348653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554930159083131032376929741 208098809656174137141348653)
                ·
                  refine ⟨78037053621065301428005745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208098809656174137141348653 78037053621065301428005745)
                  ·
                    refine ⟨58527790215798976071004309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78037053621065301428005745 58527790215798976071004309)
                    ·
                      refine ⟨2743490166365577003328327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58527790215798976071004309 2743490166365577003328327)
                      ·
                        rfl

theorem cell23_5342928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_5342928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342928 prefixEnd_5342928 := by exact prefixLift 5342928
  have htrace : WordTrace (prefixWord ++ tailWord_5342928) baseStart_5342928 baseEnd_5342928 := by
    simpa [prefixWord, tailWord_5342928, baseEnd_5342928] using wordTrace_append hprefix tailTrace_5342928
  have hstable : (prefixWord ++ tailWord_5342928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342928).length < 2 ^ (prefixWord ++ tailWord_5342928).sum := by decide
  have hdescent : baseEnd_5342928 < baseStart_5342928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5342975 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_5342975 : Nat := 118140960795 + 5342975 * 2 ^ 59
def prefixEnd_5342975 : Nat := 4983230072969 + 3 ^ 40 * 5342975 * 2
def baseEnd_5342975 : Nat := 2743514299956338319440611

theorem tailTrace_5342975 : CollatzResearch.WordTrace tailWord_5342975 prefixEnd_5342975 2743514299956338319440611 := by
  unfold tailWord_5342975
  simp only [CollatzResearch.WordTrace]
  refine ⟨194874307818321557326678379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129916205212214371551118919 194874307818321557326678379)
  ·
    refine ⟨292311461727482335990017569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194874307818321557326678379 292311461727482335990017569)
    ·
      refine ⟨219233596295611751992513177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292311461727482335990017569 219233596295611751992513177)
      ·
        refine ⟨164425197221708813994384883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219233596295611751992513177 164425197221708813994384883)
        ·
          refine ⟨246637795832563220991577325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164425197221708813994384883 246637795832563220991577325)
          ·
            refine ⟨92489173437211207871841497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246637795832563220991577325 92489173437211207871841497)
            ·
              refine ⟨69366880077908405903881123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92489173437211207871841497 69366880077908405903881123)
              ·
                refine ⟨104050320116862608855821685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69366880077908405903881123 104050320116862608855821685)
                ·
                  refine ⟨9754717510955869580233283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104050320116862608855821685 9754717510955869580233283)
                  ·
                    refine ⟨14632076266433804370349925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9754717510955869580233283 14632076266433804370349925)
                    ·
                      refine ⟨2743514299956338319440611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14632076266433804370349925 2743514299956338319440611)
                      ·
                        rfl

theorem cell23_5342975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_5342975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5342975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5342975 prefixEnd_5342975 := by exact prefixLift 5342975
  have htrace : WordTrace (prefixWord ++ tailWord_5342975) baseStart_5342975 baseEnd_5342975 := by
    simpa [prefixWord, tailWord_5342975, baseEnd_5342975] using wordTrace_append hprefix tailTrace_5342975
  have hstable : (prefixWord ++ tailWord_5342975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5342975).length < 2 ^ (prefixWord ++ tailWord_5342975).sum := by decide
  have hdescent : baseEnd_5342975 < baseStart_5342975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5342975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343002 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_5343002 : Nat := 118140960795 + 5343002 * 2 ^ 59
def prefixEnd_5343002 : Nat := 4983230072969 + 3 ^ 40 * 5343002 * 2
def baseEnd_5343002 : Nat := 914509387978003237934329

theorem tailTrace_5343002 : CollatzResearch.WordTrace tailWord_5343002 prefixEnd_5343002 914509387978003237934329 := by
  unfold tailWord_5343002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48718823147305935234477815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129916861726149160625274173 48718823147305935234477815)
  ·
    refine ⟨73078234720958902851716723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48718823147305935234477815 73078234720958902851716723)
    ·
      refine ⟨109617352081438354277575085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73078234720958902851716723 109617352081438354277575085)
      ·
        refine ⟨41106507030539382854090657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109617352081438354277575085 41106507030539382854090657)
        ·
          refine ⟨30829880272904537140567993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41106507030539382854090657 30829880272904537140567993)
          ·
            refine ⟨23122410204678402855425995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30829880272904537140567993 23122410204678402855425995)
            ·
              refine ⟨34683615307017604283138993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23122410204678402855425995 34683615307017604283138993)
              ·
                refine ⟨26012711480263203212354245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34683615307017604283138993 26012711480263203212354245)
                ·
                  refine ⟨4877383402549350602316421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26012711480263203212354245 4877383402549350602316421)
                  ·
                    refine ⟨914509387978003237934329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4877383402549350602316421 914509387978003237934329)
                    ·
                      rfl

theorem cell23_5343002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_5343002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343002 prefixEnd_5343002 := by exact prefixLift 5343002
  have htrace : WordTrace (prefixWord ++ tailWord_5343002) baseStart_5343002 baseEnd_5343002 := by
    simpa [prefixWord, tailWord_5343002, baseEnd_5343002] using wordTrace_append hprefix tailTrace_5343002
  have hstable : (prefixWord ++ tailWord_5343002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343002).length < 2 ^ (prefixWord ++ tailWord_5343002).sum := by decide
  have hdescent : baseEnd_5343002 < baseStart_5343002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343012 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_5343012 : Nat := 118140960795 + 5343012 * 2 ^ 59
def prefixEnd_5343012 : Nat := 4983230072969 + 3 ^ 40 * 5343012 * 2
def baseEnd_5343012 : Nat := 2743533298740554674677941

theorem tailTrace_5343012 : CollatzResearch.WordTrace tailWord_5343012 prefixEnd_5343012 2743533298740554674677941 := by
  unfold tailWord_5343012
  simp only [CollatzResearch.WordTrace]
  refine ⟨97437828659593756322887645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129917104879458341763850193 97437828659593756322887645)
  ·
    refine ⟨36539185747347658621082867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97437828659593756322887645 36539185747347658621082867)
    ·
      refine ⟨54808778621021487931624301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36539185747347658621082867 54808778621021487931624301)
      ·
        refine ⟨20553291982883057974359113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54808778621021487931624301 20553291982883057974359113)
        ·
          refine ⟨15414968987162293480769335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20553291982883057974359113 15414968987162293480769335)
          ·
            refine ⟨23122453480743440221154003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15414968987162293480769335 23122453480743440221154003)
            ·
              refine ⟨34683680221115160331731005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23122453480743440221154003 34683680221115160331731005)
              ·
                refine ⟨13006380082918185124399127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34683680221115160331731005 13006380082918185124399127)
                ·
                  refine ⟨19509570124377277686598691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13006380082918185124399127 19509570124377277686598691)
                  ·
                    refine ⟨29264355186565916529898037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19509570124377277686598691 29264355186565916529898037)
                    ·
                      refine ⟨2743533298740554674677941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29264355186565916529898037 2743533298740554674677941)
                      ·
                        rfl

theorem cell23_5343012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_5343012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343012 prefixEnd_5343012 := by exact prefixLift 5343012
  have htrace : WordTrace (prefixWord ++ tailWord_5343012) baseStart_5343012 baseEnd_5343012 := by
    simpa [prefixWord, tailWord_5343012, baseEnd_5343012] using wordTrace_append hprefix tailTrace_5343012
  have hstable : (prefixWord ++ tailWord_5343012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343012).length < 2 ^ (prefixWord ++ tailWord_5343012).sum := by decide
  have hdescent : baseEnd_5343012 < baseStart_5343012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343026 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_5343026 : Nat := 118140960795 + 5343026 * 2 ^ 59
def prefixEnd_5343026 : Nat := 4983230072969 + 3 ^ 40 * 5343026 * 2
def baseEnd_5343026 : Nat := 2743540487469717619902877

theorem tailTrace_5343026 : CollatzResearch.WordTrace tailWord_5343026 prefixEnd_5343026 2743540487469717619902877 := by
  unfold tailWord_5343026
  simp only [CollatzResearch.WordTrace]
  refine ⟨48719041985284198259196233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129917445294091195357856621 48719041985284198259196233)
  ·
    refine ⟨36539281488963148694397175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48719041985284198259196233 36539281488963148694397175)
    ·
      refine ⟨54808922233444723041595763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36539281488963148694397175 54808922233444723041595763)
      ·
        refine ⟨82213383350167084562393645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54808922233444723041595763 82213383350167084562393645)
        ·
          refine ⟨30830018756312656710897617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82213383350167084562393645 30830018756312656710897617)
          ·
            refine ⟨23122514067234492533173213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30830018756312656710897617 23122514067234492533173213)
            ·
              refine ⟨8670942775212934699939955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23122514067234492533173213 8670942775212934699939955)
              ·
                refine ⟨13006414162819402049909933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670942775212934699939955 13006414162819402049909933)
                ·
                  refine ⟨4877405311057275768716225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13006414162819402049909933 4877405311057275768716225)
                  ·
                    refine ⟨3658053983292956826537169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4877405311057275768716225 3658053983292956826537169)
                    ·
                      refine ⟨2743540487469717619902877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658053983292956826537169 2743540487469717619902877)
                      ·
                        rfl

theorem cell23_5343026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_5343026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343026 prefixEnd_5343026 := by exact prefixLift 5343026
  have htrace : WordTrace (prefixWord ++ tailWord_5343026) baseStart_5343026 baseEnd_5343026 := by
    simpa [prefixWord, tailWord_5343026, baseEnd_5343026] using wordTrace_append hprefix tailTrace_5343026
  have hstable : (prefixWord ++ tailWord_5343026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343026).length < 2 ^ (prefixWord ++ tailWord_5343026).sum := by decide
  have hdescent : baseEnd_5343026 < baseStart_5343026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343086 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_5343086 : Nat := 118140960795 + 5343086 * 2 ^ 59
def prefixEnd_5343086 : Nat := 4983230072969 + 3 ^ 40 * 5343086 * 2
def baseEnd_5343086 : Nat := 2743571296308987385152601

theorem tailTrace_5343086 : CollatzResearch.WordTrace tailWord_5343086 prefixEnd_5343086 2743571296308987385152601 := by
  unfold tailWord_5343086
  simp only [CollatzResearch.WordTrace]
  refine ⟨24359794540114927910496139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129918904213946282189312741 24359794540114927910496139)
  ·
    refine ⟨36539691810172391865744209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24359794540114927910496139 36539691810172391865744209)
    ·
      refine ⟨27404768857629293899308157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36539691810172391865744209 27404768857629293899308157)
      ·
        refine ⟨10276788321610985212240559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27404768857629293899308157 10276788321610985212240559)
        ·
          refine ⟨15415182482416477818360839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10276788321610985212240559 15415182482416477818360839)
          ·
            refine ⟨23122773723624716727541259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15415182482416477818360839 23122773723624716727541259)
            ·
              refine ⟨34684160585437075091311889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23122773723624716727541259 34684160585437075091311889)
              ·
                refine ⟨26013120439077806318483917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34684160585437075091311889 26013120439077806318483917)
                ·
                  refine ⟨9754920164654177369431469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26013120439077806318483917 9754920164654177369431469)
                  ·
                    refine ⟨3658095061745316513536801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9754920164654177369431469 3658095061745316513536801)
                    ·
                      refine ⟨2743571296308987385152601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658095061745316513536801 2743571296308987385152601)
                      ·
                        rfl

theorem cell23_5343086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_5343086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343086 prefixEnd_5343086 := by exact prefixLift 5343086
  have htrace : WordTrace (prefixWord ++ tailWord_5343086) baseStart_5343086 baseEnd_5343086 := by
    simpa [prefixWord, tailWord_5343086, baseEnd_5343086] using wordTrace_append hprefix tailTrace_5343086
  have hstable : (prefixWord ++ tailWord_5343086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343086).length < 2 ^ (prefixWord ++ tailWord_5343086).sum := by decide
  have hdescent : baseEnd_5343086 < baseStart_5343086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343099 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 6, 2, 2]
def baseStart_5343099 : Nat := 118140960795 + 5343099 * 2 ^ 59
def prefixEnd_5343099 : Nat := 4983230072969 + 3 ^ 40 * 5343099 * 2
def baseEnd_5343099 : Nat := 2743577971557495834290041

theorem tailTrace_5343099 : CollatzResearch.WordTrace tailWord_5343099 prefixEnd_5343099 2743577971557495834290041 := by
  unfold tailWord_5343099
  simp only [CollatzResearch.WordTrace]
  refine ⟨194878830469872326504192351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129919220313248217669461567 194878830469872326504192351)
  ·
    refine ⟨292318245704808489756288527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194878830469872326504192351 292318245704808489756288527)
    ·
      refine ⟨438477368557212734634432791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292318245704808489756288527 438477368557212734634432791)
      ·
        refine ⟨657716052835819101951649187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438477368557212734634432791 657716052835819101951649187)
        ·
          refine ⟨986574079253728652927473781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657716052835819101951649187 986574079253728652927473781)
          ·
            refine ⟨92491319930037061211950667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 986574079253728652927473781 92491319930037061211950667)
            ·
              refine ⟨138736979895055591817926001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92491319930037061211950667 138736979895055591817926001)
              ·
                refine ⟨104052734921291693863444501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138736979895055591817926001 104052734921291693863444501)
                ·
                  refine ⟨4877471949435548149848961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104052734921291693863444501 4877471949435548149848961)
                  ·
                    refine ⟨3658103962076661112386721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4877471949435548149848961 3658103962076661112386721)
                    ·
                      refine ⟨2743577971557495834290041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658103962076661112386721 2743577971557495834290041)
                      ·
                        rfl

theorem cell23_5343099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 2, 2].length) (baseStart_5343099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343099 prefixEnd_5343099 := by exact prefixLift 5343099
  have htrace : WordTrace (prefixWord ++ tailWord_5343099) baseStart_5343099 baseEnd_5343099 := by
    simpa [prefixWord, tailWord_5343099, baseEnd_5343099] using wordTrace_append hprefix tailTrace_5343099
  have hstable : (prefixWord ++ tailWord_5343099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343099).length < 2 ^ (prefixWord ++ tailWord_5343099).sum := by decide
  have hdescent : baseEnd_5343099 < baseStart_5343099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343115 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_5343115 : Nat := 118140960795 + 5343115 * 2 ^ 59
def prefixEnd_5343115 : Nat := 4983230072969 + 3 ^ 40 * 5343115 * 2
def baseEnd_5343115 : Nat := 2743586187247967771689967

theorem tailTrace_5343115 : CollatzResearch.WordTrace tailWord_5343115 prefixEnd_5343115 2743586187247967771689967 := by
  unfold tailWord_5343115
  simp only [CollatzResearch.WordTrace]
  refine ⟨194879414037814361236774799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129919609358542907491183199 194879414037814361236774799)
  ·
    refine ⟨292319121056721541855162199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194879414037814361236774799 292319121056721541855162199)
    ·
      refine ⟨438478681585082312782743299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292319121056721541855162199 438478681585082312782743299)
      ·
        refine ⟨657718022377623469174114949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438478681585082312782743299 657718022377623469174114949)
        ·
          refine ⟨123322129195804400470146553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 657718022377623469174114949 123322129195804400470146553)
          ·
            refine ⟨92491596896853300352609915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123322129195804400470146553 92491596896853300352609915)
            ·
              refine ⟨138737395345279950528914873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92491596896853300352609915 138737395345279950528914873)
              ·
                refine ⟨104053046508959962896686155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138737395345279950528914873 104053046508959962896686155)
                ·
                  refine ⟨156079569763439944345029233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104053046508959962896686155 156079569763439944345029233)
                  ·
                    refine ⟨117059677322579958258771925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156079569763439944345029233 117059677322579958258771925)
                    ·
                      refine ⟨2743586187247967771689967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117059677322579958258771925 2743586187247967771689967)
                      ·
                        rfl

theorem cell23_5343115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_5343115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343115 prefixEnd_5343115 := by exact prefixLift 5343115
  have htrace : WordTrace (prefixWord ++ tailWord_5343115) baseStart_5343115 baseEnd_5343115 := by
    simpa [prefixWord, tailWord_5343115, baseEnd_5343115] using wordTrace_append hprefix tailTrace_5343115
  have hstable : (prefixWord ++ tailWord_5343115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343115).length < 2 ^ (prefixWord ++ tailWord_5343115).sum := by decide
  have hdescent : baseEnd_5343115 < baseStart_5343115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343133 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_5343133 : Nat := 118140960795 + 5343133 * 2 ^ 59
def prefixEnd_5343133 : Nat := 4983230072969 + 3 ^ 40 * 5343133 * 2
def baseEnd_5343133 : Nat := 2743595429899748701264885

theorem tailTrace_5343133 : CollatzResearch.WordTrace tailWord_5343133 prefixEnd_5343133 2743595429899748701264885 := by
  unfold tailWord_5343133
  simp only [CollatzResearch.WordTrace]
  refine ⟨194880070551749150310930053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129920047034499433540620035 194880070551749150310930053)
  ·
    refine ⟨36540013228452965683299385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194880070551749150310930053 36540013228452965683299385)
    ·
      refine ⟨27405009921339724262474539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36540013228452965683299385 27405009921339724262474539)
      ·
        refine ⟨41107514882009586393711809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27405009921339724262474539 41107514882009586393711809)
        ·
          refine ⟨30830636161507189795283857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41107514882009586393711809 30830636161507189795283857)
          ·
            refine ⟨23122977121130392346462893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30830636161507189795283857 23122977121130392346462893)
            ·
              refine ⟨8671116420423897129923585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23122977121130392346462893 8671116420423897129923585)
              ·
                refine ⟨6503337315317922847442689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8671116420423897129923585 6503337315317922847442689)
                ·
                  refine ⟨4877502986488442135582017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6503337315317922847442689 4877502986488442135582017)
                  ·
                    refine ⟨3658127239866331601686513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4877502986488442135582017 3658127239866331601686513)
                    ·
                      refine ⟨2743595429899748701264885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658127239866331601686513 2743595429899748701264885)
                      ·
                        rfl

theorem cell23_5343133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_5343133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343133 prefixEnd_5343133 := by exact prefixLift 5343133
  have htrace : WordTrace (prefixWord ++ tailWord_5343133) baseStart_5343133 baseEnd_5343133 := by
    simpa [prefixWord, tailWord_5343133, baseEnd_5343133] using wordTrace_append hprefix tailTrace_5343133
  have hstable : (prefixWord ++ tailWord_5343133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343133).length < 2 ^ (prefixWord ++ tailWord_5343133).sum := by decide
  have hdescent : baseEnd_5343133 < baseStart_5343133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343186 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_5343186 : Nat := 118140960795 + 5343186 * 2 ^ 59
def prefixEnd_5343186 : Nat := 4983230072969 + 3 ^ 40 * 5343186 * 2
def baseEnd_5343186 : Nat := 914540881458145664634047

theorem tailTrace_5343186 : CollatzResearch.WordTrace tailWord_5343186 prefixEnd_5343186 914540881458145664634047 := by
  unfold tailWord_5343186
  simp only [CollatzResearch.WordTrace]
  refine ⟨48720500905139285090652353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129921335747038093575072941 48720500905139285090652353)
  ·
    refine ⟨36540375678854463817989265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48720500905139285090652353 36540375678854463817989265)
    ·
      refine ⟨27405281759140847863491949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36540375678854463817989265 27405281759140847863491949)
      ·
        refine ⟨10276980659677817948809481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27405281759140847863491949 10276980659677817948809481)
        ·
          refine ⟨7707735494758363461607111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10276980659677817948809481 7707735494758363461607111)
          ·
            refine ⟨11561603242137545192410667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707735494758363461607111 11561603242137545192410667)
            ·
              refine ⟨17342404863206317788616001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11561603242137545192410667 17342404863206317788616001)
              ·
                refine ⟨13006803647404738341462001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17342404863206317788616001 13006803647404738341462001)
                ·
                  refine ⟨9755102735553553756096501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13006803647404738341462001 9755102735553553756096501)
                  ·
                    refine ⟨914540881458145664634047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9755102735553553756096501 914540881458145664634047)
                    ·
                      rfl

theorem cell23_5343186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_5343186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343186 prefixEnd_5343186 := by exact prefixLift 5343186
  have htrace : WordTrace (prefixWord ++ tailWord_5343186) baseStart_5343186 baseEnd_5343186 := by
    simpa [prefixWord, tailWord_5343186, baseEnd_5343186] using wordTrace_append hprefix tailTrace_5343186
  have hstable : (prefixWord ++ tailWord_5343186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343186).length < 2 ^ (prefixWord ++ tailWord_5343186).sum := by decide
  have hdescent : baseEnd_5343186 < baseStart_5343186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343189 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5343189 : Nat := 118140960795 + 5343189 * 2 ^ 59
def prefixEnd_5343189 : Nat := 4983230072969 + 3 ^ 40 * 5343189 * 2
def baseEnd_5343189 : Nat := 2743624184816400482164627

theorem tailTrace_5343189 : CollatzResearch.WordTrace tailWord_5343189 prefixEnd_5343189 2743624184816400482164627 := by
  unfold tailWord_5343189
  simp only [CollatzResearch.WordTrace]
  refine ⟨194882113039546271874968621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129921408693030847916645747 194882113039546271874968621)
  ·
    refine ⟨73080792389829851953113233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194882113039546271874968621 73080792389829851953113233)
    ·
      refine ⟨54810594292372388964834925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73080792389829851953113233 54810594292372388964834925)
      ·
        refine ⟨20553972859639645861813097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54810594292372388964834925 20553972859639645861813097)
        ·
          refine ⟨15415479644729734396359823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20553972859639645861813097 15415479644729734396359823)
          ·
            refine ⟨23123219467094601594539735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15415479644729734396359823 23123219467094601594539735)
            ·
              refine ⟨34684829200641902391809603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23123219467094601594539735 34684829200641902391809603)
              ·
                refine ⟨52027243800962853587714405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34684829200641902391809603 52027243800962853587714405)
                ·
                  refine ⟨9755108212680535047696451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52027243800962853587714405 9755108212680535047696451)
                  ·
                    refine ⟨14632662319020802571544677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9755108212680535047696451 14632662319020802571544677)
                    ·
                      refine ⟨2743624184816400482164627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14632662319020802571544677 2743624184816400482164627)
                      ·
                        rfl

theorem cell23_5343189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5343189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343189 prefixEnd_5343189 := by exact prefixLift 5343189
  have htrace : WordTrace (prefixWord ++ tailWord_5343189) baseStart_5343189 baseEnd_5343189 := by
    simpa [prefixWord, tailWord_5343189, baseEnd_5343189] using wordTrace_append hprefix tailTrace_5343189
  have hstable : (prefixWord ++ tailWord_5343189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343189).length < 2 ^ (prefixWord ++ tailWord_5343189).sum := by decide
  have hdescent : baseEnd_5343189 < baseStart_5343189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343190 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_5343190 : Nat := 118140960795 + 5343190 * 2 ^ 59
def prefixEnd_5343190 : Nat := 4983230072969 + 3 ^ 40 * 5343190 * 2
def baseEnd_5343190 : Nat := 304847188699672775361347

theorem tailTrace_5343190 : CollatzResearch.WordTrace tailWord_5343190 prefixEnd_5343190 304847188699672775361347 := by
  unfold tailWord_5343190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12180134344533915565359689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129921433008361766030503349 12180134344533915565359689)
  ·
    refine ⟨9135100758400436674019767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12180134344533915565359689 9135100758400436674019767)
    ·
      refine ⟨13702651137600655011029651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9135100758400436674019767 13702651137600655011029651)
      ·
        refine ⟨20553976706400982516544477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13702651137600655011029651 20553976706400982516544477)
        ·
          refine ⟨7707741264900368443704179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20553976706400982516544477 7707741264900368443704179)
          ·
            refine ⟨11561611897350552665556269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707741264900368443704179 11561611897350552665556269)
            ·
              refine ⟨4335604461506457249583601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11561611897350552665556269 4335604461506457249583601)
              ·
                refine ⟨3251703346129842937187701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4335604461506457249583601 3251703346129842937187701)
                ·
                  refine ⟨304847188699672775361347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251703346129842937187701 304847188699672775361347)
                  ·
                    rfl

theorem cell23_5343190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_5343190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343190 prefixEnd_5343190 := by exact prefixLift 5343190
  have htrace : WordTrace (prefixWord ++ tailWord_5343190) baseStart_5343190 baseEnd_5343190 := by
    simpa [prefixWord, tailWord_5343190, baseEnd_5343190] using wordTrace_append hprefix tailTrace_5343190
  have hstable : (prefixWord ++ tailWord_5343190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343190).length < 2 ^ (prefixWord ++ tailWord_5343190).sum := by decide
  have hdescent : baseEnd_5343190 < baseStart_5343190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343249 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 5, 5, 2]
def baseStart_5343249 : Nat := 118140960795 + 5343249 * 2 ^ 59
def prefixEnd_5343249 : Nat := 4983230072969 + 3 ^ 40 * 5343249 * 2
def baseEnd_5343249 : Nat := 2743654993655670247414351

theorem tailTrace_5343249 : CollatzResearch.WordTrace tailWord_5343249 prefixEnd_5343249 2743654993655670247414351 := by
  unfold tailWord_5343249
  simp only [CollatzResearch.WordTrace]
  refine ⟨194884301419328902122152801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129922867612885934748101867 194884301419328902122152801)
  ·
    refine ⟨146163226064496676591614601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194884301419328902122152801 146163226064496676591614601)
    ·
      refine ⟨109622419548372507443710951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146163226064496676591614601 109622419548372507443710951)
      ·
        refine ⟨164433629322558761165566427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109622419548372507443710951 164433629322558761165566427)
        ·
          refine ⟨246650443983838141748349641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164433629322558761165566427 246650443983838141748349641)
          ·
            refine ⟨184987832987878606311262231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246650443983838141748349641 184987832987878606311262231)
            ·
              refine ⟨277481749481817909466893347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184987832987878606311262231 277481749481817909466893347)
              ·
                refine ⟨416222624222726864200340021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277481749481817909466893347 416222624222726864200340021)
                ·
                  refine ⟨39020871020880643518781877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416222624222726864200340021 39020871020880643518781877)
                  ·
                    refine ⟨3658206658207560329885801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39020871020880643518781877 3658206658207560329885801)
                    ·
                      refine ⟨2743654993655670247414351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658206658207560329885801 2743654993655670247414351)
                      ·
                        rfl

theorem cell23_5343249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_5343249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343249 prefixEnd_5343249 := by exact prefixLift 5343249
  have htrace : WordTrace (prefixWord ++ tailWord_5343249) baseStart_5343249 baseEnd_5343249 := by
    simpa [prefixWord, tailWord_5343249, baseEnd_5343249] using wordTrace_append hprefix tailTrace_5343249
  have hstable : (prefixWord ++ tailWord_5343249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343249).length < 2 ^ (prefixWord ++ tailWord_5343249).sum := by decide
  have hdescent : baseEnd_5343249 < baseStart_5343249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343256 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_5343256 : Nat := 118140960795 + 5343256 * 2 ^ 59
def prefixEnd_5343256 : Nat := 4983230072969 + 3 ^ 40 * 5343256 * 2
def baseEnd_5343256 : Nat := 2743658588020251720026819

theorem tailTrace_5343256 : CollatzResearch.WordTrace tailWord_5343256 prefixEnd_5343256 2743658588020251720026819 := by
  unfold tailWord_5343256
  simp only [CollatzResearch.WordTrace]
  refine ⟨97442278365151771158828811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129923037820202361545105081 97442278365151771158828811)
  ·
    refine ⟨146163417547727656738243217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97442278365151771158828811 146163417547727656738243217)
    ·
      refine ⟨109622563160795742553682413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146163417547727656738243217 109622563160795742553682413)
      ·
        refine ⟨41108461185298403457630905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109622563160795742553682413 41108461185298403457630905)
        ·
          refine ⟨30831345888973802593223179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41108461185298403457630905 30831345888973802593223179)
          ·
            refine ⟨46247018833460703889834769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30831345888973802593223179 46247018833460703889834769)
            ·
              refine ⟨34685264125095527917376077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46247018833460703889834769 34685264125095527917376077)
              ·
                refine ⟨13006974046910822969016029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34685264125095527917376077 13006974046910822969016029)
                ·
                  refine ⟨4877615267591558613381011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13006974046910822969016029 4877615267591558613381011)
                  ·
                    refine ⟨7316422901387337920071517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4877615267591558613381011 7316422901387337920071517)
                    ·
                      refine ⟨2743658588020251720026819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7316422901387337920071517 2743658588020251720026819)
                      ·
                        rfl

theorem cell23_5343256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_5343256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343256 prefixEnd_5343256 := by exact prefixLift 5343256
  have htrace : WordTrace (prefixWord ++ tailWord_5343256) baseStart_5343256 baseEnd_5343256 := by
    simpa [prefixWord, tailWord_5343256, baseEnd_5343256] using wordTrace_append hprefix tailTrace_5343256
  have hstable : (prefixWord ++ tailWord_5343256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343256).length < 2 ^ (prefixWord ++ tailWord_5343256).sum := by decide
  have hdescent : baseEnd_5343256 < baseStart_5343256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343266 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_5343266 : Nat := 118140960795 + 5343266 * 2 ^ 59
def prefixEnd_5343266 : Nat := 4983230072969 + 3 ^ 40 * 5343266 * 2
def baseEnd_5343266 : Nat := 2743663722826796680901773

theorem tailTrace_5343266 : CollatzResearch.WordTrace tailWord_5343266 prefixEnd_5343266 2743663722826796680901773 := by
  unfold tailWord_5343266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48721230365066828506380413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129923280973511542683681101 48721230365066828506380413)
  ·
    refine ⟨18270461386900060689892655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48721230365066828506380413 18270461386900060689892655)
    ·
      refine ⟨27405692080350091034838983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18270461386900060689892655 27405692080350091034838983)
      ·
        refine ⟨41108538120525136552258475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27405692080350091034838983 41108538120525136552258475)
        ·
          refine ⟨61662807180787704828387713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41108538120525136552258475 61662807180787704828387713)
          ·
            refine ⟨46247105385590778621290785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61662807180787704828387713 46247105385590778621290785)
            ·
              refine ⟨34685329039193083965968089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46247105385590778621290785 34685329039193083965968089)
              ·
                refine ⟨26013996779394812974476067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34685329039193083965968089 26013996779394812974476067)
                ·
                  refine ⟨39020995169092219461714101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26013996779394812974476067 39020995169092219461714101)
                  ·
                    refine ⟨3658218297102395574535697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39020995169092219461714101 3658218297102395574535697)
                    ·
                      refine ⟨2743663722826796680901773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658218297102395574535697 2743663722826796680901773)
                      ·
                        rfl

theorem cell23_5343266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_5343266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343266 prefixEnd_5343266 := by exact prefixLift 5343266
  have htrace : WordTrace (prefixWord ++ tailWord_5343266) baseStart_5343266 baseEnd_5343266 := by
    simpa [prefixWord, tailWord_5343266, baseEnd_5343266] using wordTrace_append hprefix tailTrace_5343266
  have hstable : (prefixWord ++ tailWord_5343266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343266).length < 2 ^ (prefixWord ++ tailWord_5343266).sum := by decide
  have hdescent : baseEnd_5343266 < baseStart_5343266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343279 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 8, 2]
def baseStart_5343279 : Nat := 118140960795 + 5343279 * 2 ^ 59
def prefixEnd_5343279 : Nat := 4983230072969 + 3 ^ 40 * 5343279 * 2
def baseEnd_5343279 : Nat := 2743670398075305130039213

theorem tailTrace_5343279 : CollatzResearch.WordTrace tailWord_5343279 prefixEnd_5343279 2743670398075305130039213 := by
  unfold tailWord_5343279
  simp only [CollatzResearch.WordTrace]
  refine ⟨194885395609220217245744891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129923597072813478163829927 194885395609220217245744891)
  ·
    refine ⟨292328093413830325868617337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194885395609220217245744891 292328093413830325868617337)
    ·
      refine ⟨219246070060372744401463003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292328093413830325868617337 219246070060372744401463003)
      ·
        refine ⟨328869105090559116602194505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219246070060372744401463003 328869105090559116602194505)
        ·
          refine ⟨246651828817919337451645879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328869105090559116602194505 246651828817919337451645879)
          ·
            refine ⟨369977743226879006177468819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246651828817919337451645879 369977743226879006177468819)
            ·
              refine ⟨554966614840318509266203229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369977743226879006177468819 554966614840318509266203229)
              ·
                refine ⟨208112480565119440974826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554966614840318509266203229 208112480565119440974826211)
                ·
                  refine ⟨312168720847679161462239317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208112480565119440974826211 312168720847679161462239317)
                  ·
                    refine ⟨3658227197433740173385617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 312168720847679161462239317 3658227197433740173385617)
                    ·
                      refine ⟨2743670398075305130039213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658227197433740173385617 2743670398075305130039213)
                      ·
                        rfl

theorem cell23_5343279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8, 2].length) (baseStart_5343279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343279 prefixEnd_5343279 := by exact prefixLift 5343279
  have htrace : WordTrace (prefixWord ++ tailWord_5343279) baseStart_5343279 baseEnd_5343279 := by
    simpa [prefixWord, tailWord_5343279, baseEnd_5343279] using wordTrace_append hprefix tailTrace_5343279
  have hstable : (prefixWord ++ tailWord_5343279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343279).length < 2 ^ (prefixWord ++ tailWord_5343279).sum := by decide
  have hdescent : baseEnd_5343279 < baseStart_5343279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343296 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4]
def baseStart_5343296 : Nat := 118140960795 + 5343296 * 2 ^ 59
def prefixEnd_5343296 : Nat := 4983230072969 + 3 ^ 40 * 5343296 * 2
def baseEnd_5343296 : Nat := 2743679127246431563526635

theorem tailTrace_5343296 : CollatzResearch.WordTrace tailWord_5343296 prefixEnd_5343296 2743679127246431563526635 := by
  unfold tailWord_5343296
  simp only [CollatzResearch.WordTrace]
  refine ⟨97443007825079314574556871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129924010433439086099409161 97443007825079314574556871)
  ·
    refine ⟨146164511737618971861835307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97443007825079314574556871 146164511737618971861835307)
    ·
      refine ⟨219246767606428457792752961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146164511737618971861835307 219246767606428457792752961)
      ·
        refine ⟨164435075704821343344564721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219246767606428457792752961 164435075704821343344564721)
        ·
          refine ⟨123326306778616007508423541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164435075704821343344564721 123326306778616007508423541)
          ·
            refine ⟨11561841260495250703914707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123326306778616007508423541 11561841260495250703914707)
            ·
              refine ⟨17342761890742876055872061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11561841260495250703914707 17342761890742876055872061)
              ·
                refine ⟨6503535709028578520952023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17342761890742876055872061 6503535709028578520952023)
                ·
                  refine ⟨9755303563542867781428035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503535709028578520952023 9755303563542867781428035)
                  ·
                    refine ⟨14632955345314301672142053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9755303563542867781428035 14632955345314301672142053)
                    ·
                      refine ⟨2743679127246431563526635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14632955345314301672142053 2743679127246431563526635)
                      ·
                        rfl

theorem cell23_5343296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_5343296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343296 prefixEnd_5343296 := by exact prefixLift 5343296
  have htrace : WordTrace (prefixWord ++ tailWord_5343296) baseStart_5343296 baseEnd_5343296 := by
    simpa [prefixWord, tailWord_5343296, baseEnd_5343296] using wordTrace_append hprefix tailTrace_5343296
  have hstable : (prefixWord ++ tailWord_5343296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343296).length < 2 ^ (prefixWord ++ tailWord_5343296).sum := by decide
  have hdescent : baseEnd_5343296 < baseStart_5343296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343299 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 3]
def baseStart_5343299 : Nat := 118140960795 + 5343299 * 2 ^ 59
def prefixEnd_5343299 : Nat := 4983230072969 + 3 ^ 40 * 5343299 * 2
def baseEnd_5343299 : Nat := 2743680667688395051789121

theorem tailTrace_5343299 : CollatzResearch.WordTrace tailWord_5343299 prefixEnd_5343299 2743680667688395051789121 := by
  unfold tailWord_5343299
  simp only [CollatzResearch.WordTrace]
  refine ⟨194886125069147760661472951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129924083379431840440981967 194886125069147760661472951)
  ·
    refine ⟨292329187603721640992209427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194886125069147760661472951 292329187603721640992209427)
    ·
      refine ⟨438493781405582461488314141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292329187603721640992209427 438493781405582461488314141)
      ·
        refine ⟨164435168027093423058117803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438493781405582461488314141 164435168027093423058117803)
        ·
          refine ⟨246652752040640134587176705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164435168027093423058117803 246652752040640134587176705)
          ·
            refine ⟨184989564030480100940382529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246652752040640134587176705 184989564030480100940382529)
            ·
              refine ⟨138742173022860075705286897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184989564030480100940382529 138742173022860075705286897)
              ·
                refine ⟨104056629767145056778965173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138742173022860075705286897 104056629767145056778965173)
                ·
                  refine ⟨9755309040669849073027985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104056629767145056778965173 9755309040669849073027985)
                  ·
                    refine ⟨7316481780502386804770989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9755309040669849073027985 7316481780502386804770989)
                    ·
                      refine ⟨2743680667688395051789121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7316481780502386804770989 2743680667688395051789121)
                      ·
                        rfl

theorem cell23_5343299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_5343299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343299 prefixEnd_5343299 := by exact prefixLift 5343299
  have htrace : WordTrace (prefixWord ++ tailWord_5343299) baseStart_5343299 baseEnd_5343299 := by
    simpa [prefixWord, tailWord_5343299, baseEnd_5343299] using wordTrace_append hprefix tailTrace_5343299
  have hstable : (prefixWord ++ tailWord_5343299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343299).length < 2 ^ (prefixWord ++ tailWord_5343299).sum := by decide
  have hdescent : baseEnd_5343299 < baseStart_5343299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343312 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_5343312 : Nat := 118140960795 + 5343312 * 2 ^ 59
def prefixEnd_5343312 : Nat := 4983230072969 + 3 ^ 40 * 5343312 * 2
def baseEnd_5343312 : Nat := 2743687342936903500926561

theorem tailTrace_5343312 : CollatzResearch.WordTrace tailWord_5343312 prefixEnd_5343312 2743687342936903500926561 := by
  unfold tailWord_5343312
  simp only [CollatzResearch.WordTrace]
  refine ⟨97443299609050331940848095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129924399478733775921130793 97443299609050331940848095)
  ·
    refine ⟨146164949413575497911272143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97443299609050331940848095 146164949413575497911272143)
    ·
      refine ⟨219247424120363246866908215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146164949413575497911272143 219247424120363246866908215)
      ·
        refine ⟨328871136180544870300362323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219247424120363246866908215 328871136180544870300362323)
        ·
          refine ⟨493306704270817305450543485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328871136180544870300362323 493306704270817305450543485)
          ·
            refine ⟨184990014101556489543953807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493306704270817305450543485 184990014101556489543953807)
            ·
              refine ⟨277485021152334734315930711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184990014101556489543953807 277485021152334734315930711)
              ·
                refine ⟨416227531728502101473896067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277485021152334734315930711 416227531728502101473896067)
                ·
                  refine ⟨624341297592753152210844101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416227531728502101473896067 624341297592753152210844101)
                  ·
                    refine ⟨117063993298641216039533269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624341297592753152210844101 117063993298641216039533269)
                    ·
                      refine ⟨2743687342936903500926561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117063993298641216039533269 2743687342936903500926561)
                      ·
                        rfl

theorem cell23_5343312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_5343312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343312 prefixEnd_5343312 := by exact prefixLift 5343312
  have htrace : WordTrace (prefixWord ++ tailWord_5343312) baseStart_5343312 baseEnd_5343312 := by
    simpa [prefixWord, tailWord_5343312, baseEnd_5343312] using wordTrace_append hprefix tailTrace_5343312
  have hstable : (prefixWord ++ tailWord_5343312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343312).length < 2 ^ (prefixWord ++ tailWord_5343312).sum := by decide
  have hdescent : baseEnd_5343312 < baseStart_5343312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343330 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5343330 : Nat := 118140960795 + 5343330 * 2 ^ 59
def prefixEnd_5343330 : Nat := 4983230072969 + 3 ^ 40 * 5343330 * 2
def baseEnd_5343330 : Nat := 2743696585588684430501479

theorem tailTrace_5343330 : CollatzResearch.WordTrace tailWord_5343330 prefixEnd_5343330 2743696585588684430501479 := by
  unfold tailWord_5343330
  simp only [CollatzResearch.WordTrace]
  refine ⟨48721813933008863238962861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129924837154690301970567629 48721813933008863238962861)
  ·
    refine ⟨18270680224878323714611073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48721813933008863238962861 18270680224878323714611073)
    ·
      refine ⟨13703010168658742785958305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18270680224878323714611073 13703010168658742785958305)
      ·
        refine ⟨10277257626494057089468729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13703010168658742785958305 10277257626494057089468729)
        ·
          refine ⟨7707943219870542817101547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10277257626494057089468729 7707943219870542817101547)
          ·
            refine ⟨11561914829805814225652321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707943219870542817101547 11561914829805814225652321)
            ·
              refine ⟨8671436122354360669239241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11561914829805814225652321 8671436122354360669239241)
              ·
                refine ⟨6503577091765770501929431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8671436122354360669239241 6503577091765770501929431)
                ·
                  refine ⟨9755365637648655752894147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503577091765770501929431 9755365637648655752894147)
                  ·
                    refine ⟨14633048456472983629341221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9755365637648655752894147 14633048456472983629341221)
                    ·
                      refine ⟨2743696585588684430501479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14633048456472983629341221 2743696585588684430501479)
                      ·
                        rfl

theorem cell23_5343330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5343330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343330 prefixEnd_5343330 := by exact prefixLift 5343330
  have htrace : WordTrace (prefixWord ++ tailWord_5343330) baseStart_5343330 baseEnd_5343330 := by
    simpa [prefixWord, tailWord_5343330, baseEnd_5343330] using wordTrace_append hprefix tailTrace_5343330
  have hstable : (prefixWord ++ tailWord_5343330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343330).length < 2 ^ (prefixWord ++ tailWord_5343330).sum := by decide
  have hdescent : baseEnd_5343330 < baseStart_5343330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343333 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_5343333 : Nat := 118140960795 + 5343333 * 2 ^ 59
def prefixEnd_5343333 : Nat := 4983230072969 + 3 ^ 40 * 5343333 * 2
def baseEnd_5343333 : Nat := 2743698126030647918763965

theorem tailTrace_5343333 : CollatzResearch.WordTrace tailWord_5343333 prefixEnd_5343333 2743698126030647918763965 := by
  unfold tailWord_5343333
  simp only [CollatzResearch.WordTrace]
  refine ⟨194887365151024584468210653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129924910100683056312140435 194887365151024584468210653)
  ·
    refine ⟨73082761931634219175578995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194887365151024584468210653 73082761931634219175578995)
    ·
      refine ⟨109624142897451328763368493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73082761931634219175578995 109624142897451328763368493)
      ·
        refine ⟨41109053586544248286263185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109624142897451328763368493 41109053586544248286263185)
        ·
          refine ⟨30831790189908186214697389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41109053586544248286263185 30831790189908186214697389)
          ·
            refine ⟨11561921321215569830511521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30831790189908186214697389 11561921321215569830511521)
            ·
              refine ⟨8671440990911677372883641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11561921321215569830511521 8671440990911677372883641)
              ·
                refine ⟨6503580743183758029662731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8671440990911677372883641 6503580743183758029662731)
                ·
                  refine ⟨9755371114775637044494097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503580743183758029662731 9755371114775637044494097)
                  ·
                    refine ⟨7316528336081727783370573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9755371114775637044494097 7316528336081727783370573)
                    ·
                      refine ⟨2743698126030647918763965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7316528336081727783370573 2743698126030647918763965)
                      ·
                        rfl

theorem cell23_5343333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_5343333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343333 prefixEnd_5343333 := by exact prefixLift 5343333
  have htrace : WordTrace (prefixWord ++ tailWord_5343333) baseStart_5343333 baseEnd_5343333 := by
    simpa [prefixWord, tailWord_5343333, baseEnd_5343333] using wordTrace_append hprefix tailTrace_5343333
  have hstable : (prefixWord ++ tailWord_5343333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343333).length < 2 ^ (prefixWord ++ tailWord_5343333).sum := by decide
  have hdescent : baseEnd_5343333 < baseStart_5343333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343369 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_5343369 : Nat := 118140960795 + 5343369 * 2 ^ 59
def prefixEnd_5343369 : Nat := 4983230072969 + 3 ^ 40 * 5343369 * 2
def baseEnd_5343369 : Nat := 2743716611334209777913799

theorem tailTrace_5343369 : CollatzResearch.WordTrace tailWord_5343369 prefixEnd_5343369 2743716611334209777913799 := by
  unfold tailWord_5343369
  simp only [CollatzResearch.WordTrace]
  refine ⟨194888678178894162616521161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129925785452596108411014107 194888678178894162616521161)
  ·
    refine ⟨146166508634170621962390871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194888678178894162616521161 146166508634170621962390871)
    ·
      refine ⟨219249762951255932943586307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146166508634170621962390871 219249762951255932943586307)
      ·
        refine ⟨328874644426883899415379461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219249762951255932943586307 328874644426883899415379461)
        ·
          refine ⟨61663995830040731140383649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328874644426883899415379461 61663995830040731140383649)
          ·
            refine ⟨46247996872530548355287737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61663995830040731140383649 46247996872530548355287737)
            ·
              refine ⟨34685997654397911266465803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46247996872530548355287737 34685997654397911266465803)
              ·
                refine ⟨52028996481596866899698705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34685997654397911266465803 52028996481596866899698705)
                ·
                  refine ⟨39021747361197650174774029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52028996481596866899698705 39021747361197650174774029)
                  ·
                    refine ⟨14633155260449118815540261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39021747361197650174774029 14633155260449118815540261)
                    ·
                      refine ⟨2743716611334209777913799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14633155260449118815540261 2743716611334209777913799)
                      ·
                        rfl

theorem cell23_5343369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_5343369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343369 prefixEnd_5343369 := by exact prefixLift 5343369
  have htrace : WordTrace (prefixWord ++ tailWord_5343369) baseStart_5343369 baseEnd_5343369 := by
    simpa [prefixWord, tailWord_5343369, baseEnd_5343369] using wordTrace_append hprefix tailTrace_5343369
  have hstable : (prefixWord ++ tailWord_5343369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343369).length < 2 ^ (prefixWord ++ tailWord_5343369).sum := by decide
  have hdescent : baseEnd_5343369 < baseStart_5343369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343439 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 1, 7]
def baseStart_5343439 : Nat := 118140960795 + 5343439 * 2 ^ 59
def prefixEnd_5343439 : Nat := 4983230072969 + 3 ^ 40 * 5343439 * 2
def baseEnd_5343439 : Nat := 914584184993341501346159

theorem tailTrace_5343439 : CollatzResearch.WordTrace tailWord_5343439 prefixEnd_5343439 914584184993341501346159 := by
  unfold tailWord_5343439
  simp only [CollatzResearch.WordTrace]
  refine ⟨194891231288640564571569371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129927487525760376381046247 194891231288640564571569371)
  ·
    refine ⟨292336846932960846857354057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194891231288640564571569371 292336846932960846857354057)
    ·
      refine ⟨219252635199720635143015543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292336846932960846857354057 219252635199720635143015543)
      ·
        refine ⟨328878952799580952714523315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219252635199720635143015543 328878952799580952714523315)
        ·
          refine ⟨493318429199371429071784973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328878952799580952714523315 493318429199371429071784973)
          ·
            refine ⟨184994410949764285901919365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493318429199371429071784973 184994410949764285901919365)
            ·
              refine ⟨34686452053080803606609881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184994410949764285901919365 34686452053080803606609881)
              ·
                refine ⟨26014839039810602704957411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34686452053080803606609881 26014839039810602704957411)
                ·
                  refine ⟨39022258559715904057436117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26014839039810602704957411 39022258559715904057436117)
                  ·
                    refine ⟨914584184993341501346159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39022258559715904057436117 914584184993341501346159)
                    ·
                      rfl

theorem cell23_5343439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_5343439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343439 prefixEnd_5343439 := by exact prefixLift 5343439
  have htrace : WordTrace (prefixWord ++ tailWord_5343439) baseStart_5343439 baseEnd_5343439 := by
    simpa [prefixWord, tailWord_5343439, baseEnd_5343439] using wordTrace_append hprefix tailTrace_5343439
  have hstable : (prefixWord ++ tailWord_5343439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343439).length < 2 ^ (prefixWord ++ tailWord_5343439).sum := by decide
  have hdescent : baseEnd_5343439 < baseStart_5343439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343449 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_5343449 : Nat := 118140960795 + 5343449 * 2 ^ 59
def prefixEnd_5343449 : Nat := 4983230072969 + 3 ^ 40 * 5343449 * 2
def baseEnd_5343449 : Nat := 2743757689786569464913431

theorem tailTrace_5343449 : CollatzResearch.WordTrace tailWord_5343449 prefixEnd_5343449 2743757689786569464913431 := by
  unfold tailWord_5343449
  simp only [CollatzResearch.WordTrace]
  refine ⟨194891596018604336279433401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129927730679069557519622267 194891596018604336279433401)
  ·
    refine ⟨146168697013953252209575051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194891596018604336279433401 146168697013953252209575051)
    ·
      refine ⟨219253045520929878314362577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146168697013953252209575051 219253045520929878314362577)
      ·
        refine ⟨164439784140697408735771933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219253045520929878314362577 164439784140697408735771933)
        ·
          refine ⟨61664919052761528275914475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164439784140697408735771933 61664919052761528275914475)
          ·
            refine ⟨92497378579142292413871713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61664919052761528275914475 92497378579142292413871713)
            ·
              refine ⟨69373033934356719310403785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92497378579142292413871713 69373033934356719310403785)
              ·
                refine ⟨52029775450767539482802839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69373033934356719310403785 52029775450767539482802839)
                ·
                  refine ⟨78044663176151309224204259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52029775450767539482802839 78044663176151309224204259)
                  ·
                    refine ⟨117066994764226963836306389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78044663176151309224204259 117066994764226963836306389)
                    ·
                      refine ⟨2743757689786569464913431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117066994764226963836306389 2743757689786569464913431)
                      ·
                        rfl

theorem cell23_5343449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_5343449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343449 prefixEnd_5343449 := by exact prefixLift 5343449
  have htrace : WordTrace (prefixWord ++ tailWord_5343449) baseStart_5343449 baseEnd_5343449 := by
    simpa [prefixWord, tailWord_5343449, baseEnd_5343449] using wordTrace_append hprefix tailTrace_5343449
  have hstable : (prefixWord ++ tailWord_5343449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343449).length < 2 ^ (prefixWord ++ tailWord_5343449).sum := by decide
  have hdescent : baseEnd_5343449 < baseStart_5343449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343458 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5343458 : Nat := 118140960795 + 5343458 * 2 ^ 59
def prefixEnd_5343458 : Nat := 4983230072969 + 3 ^ 40 * 5343458 * 2
def baseEnd_5343458 : Nat := 2743762311112459929700891

theorem tailTrace_5343458 : CollatzResearch.WordTrace tailWord_5343458 prefixEnd_5343458 2743762311112459929700891 := by
  unfold tailWord_5343458
  simp only [CollatzResearch.WordTrace]
  refine ⟨48722981068892932704127757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129927949517047820544340685 48722981068892932704127757)
  ·
    refine ⟨18271117900834849764047909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48722981068892932704127757 18271117900834849764047909)
    ·
      refine ⟨3425834606406534330758983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18271117900834849764047909 3425834606406534330758983)
      ·
        refine ⟨5138751909609801496138475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425834606406534330758983 5138751909609801496138475)
        ·
          refine ⟨7708127864414702244207713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5138751909609801496138475 7708127864414702244207713)
          ·
            refine ⟨5781095898311026683155785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7708127864414702244207713 5781095898311026683155785)
            ·
              refine ⟨4335821923733270012366839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5781095898311026683155785 4335821923733270012366839)
              ·
                refine ⟨6503732885599905018550259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335821923733270012366839 6503732885599905018550259)
                ·
                  refine ⟨9755599328399857527825389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503732885599905018550259 9755599328399857527825389)
                  ·
                    refine ⟨3658349748149946572934521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9755599328399857527825389 3658349748149946572934521)
                    ·
                      refine ⟨2743762311112459929700891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658349748149946572934521 2743762311112459929700891)
                      ·
                        rfl

theorem cell23_5343458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5343458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343458 prefixEnd_5343458 := by exact prefixLift 5343458
  have htrace : WordTrace (prefixWord ++ tailWord_5343458) baseStart_5343458 baseEnd_5343458 := by
    simpa [prefixWord, tailWord_5343458, baseEnd_5343458] using wordTrace_append hprefix tailTrace_5343458
  have hstable : (prefixWord ++ tailWord_5343458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343458).length < 2 ^ (prefixWord ++ tailWord_5343458).sum := by decide
  have hdescent : baseEnd_5343458 < baseStart_5343458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343537 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 3, 4]
def baseStart_5343537 : Nat := 118140960795 + 5343537 * 2 ^ 59
def prefixEnd_5343537 : Nat := 4983230072969 + 3 ^ 40 * 5343537 * 2
def baseEnd_5343537 : Nat := 914600958694721706871009

theorem tailTrace_5343537 : CollatzResearch.WordTrace tailWord_5343537 prefixEnd_5343537 914600958694721706871009 := by
  unfold tailWord_5343537
  simp only [CollatzResearch.WordTrace]
  refine ⟨194894805642285527308636865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129929870428190351539091243 194894805642285527308636865)
  ·
    refine ⟨146171104231714145481477649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194894805642285527308636865 146171104231714145481477649)
    ·
      refine ⟨109628328173785609111108237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146171104231714145481477649 109628328173785609111108237)
      ·
        refine ⟨41110623065169603416665589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109628328173785609111108237 41110623065169603416665589)
        ·
          refine ⟨3854120912359650320312399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41110623065169603416665589 3854120912359650320312399)
          ·
            refine ⟨5781181368539475480468599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854120912359650320312399 5781181368539475480468599)
            ·
              refine ⟨8671772052809213220702899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781181368539475480468599 8671772052809213220702899)
              ·
                refine ⟨13007658079213819831054349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671772052809213220702899 13007658079213819831054349)
                ·
                  refine ⟨4877871779705182436645381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13007658079213819831054349 4877871779705182436645381)
                  ·
                    refine ⟨914600958694721706871009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4877871779705182436645381 914600958694721706871009)
                    ·
                      rfl

theorem cell23_5343537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_5343537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343537 prefixEnd_5343537 := by exact prefixLift 5343537
  have htrace : WordTrace (prefixWord ++ tailWord_5343537) baseStart_5343537 baseEnd_5343537 := by
    simpa [prefixWord, tailWord_5343537, baseEnd_5343537] using wordTrace_append hprefix tailTrace_5343537
  have hstable : (prefixWord ++ tailWord_5343537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343537).length < 2 ^ (prefixWord ++ tailWord_5343537).sum := by decide
  have hdescent : baseEnd_5343537 < baseStart_5343537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343550 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_5343550 : Nat := 118140960795 + 5343550 * 2 ^ 59
def prefixEnd_5343550 : Nat := 4983230072969 + 3 ^ 40 * 5343550 * 2
def baseEnd_5343550 : Nat := 304867727925852618861163

theorem tailTrace_5343550 : CollatzResearch.WordTrace tailWord_5343550 prefixEnd_5343550 304867727925852618861163 := by
  unfold tailWord_5343550
  simp only [CollatzResearch.WordTrace]
  refine ⟨24361909973904803816107513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129930186527492287019240069 24361909973904803816107513)
  ·
    refine ⟨18271432480428602862080635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24361909973904803816107513 18271432480428602862080635)
    ·
      refine ⟨27407148720642904293120953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18271432480428602862080635 27407148720642904293120953)
      ·
        refine ⟨20555361540482178219840715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27407148720642904293120953 20555361540482178219840715)
        ·
          refine ⟨30833042310723267329761073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20555361540482178219840715 30833042310723267329761073)
          ·
            refine ⟨23124781733042450497320805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30833042310723267329761073 23124781733042450497320805)
            ·
              refine ⟨4335896574945459468247651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23124781733042450497320805 4335896574945459468247651)
              ·
                refine ⟨6503844862418189202371477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335896574945459468247651 6503844862418189202371477)
                ·
                  refine ⟨304867727925852618861163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6503844862418189202371477 304867727925852618861163)
                  ·
                    rfl

theorem cell23_5343550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_5343550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343550 prefixEnd_5343550 := by exact prefixLift 5343550
  have htrace : WordTrace (prefixWord ++ tailWord_5343550) baseStart_5343550 baseEnd_5343550 := by
    simpa [prefixWord, tailWord_5343550, baseEnd_5343550] using wordTrace_append hprefix tailTrace_5343550
  have hstable : (prefixWord ++ tailWord_5343550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343550).length < 2 ^ (prefixWord ++ tailWord_5343550).sum := by decide
  have hdescent : baseEnd_5343550 < baseStart_5343550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343570 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_5343570 : Nat := 118140960795 + 5343570 * 2 ^ 59
def prefixEnd_5343570 : Nat := 4983230072969 + 3 ^ 40 * 5343570 * 2
def baseEnd_5343570 : Nat := 2743819820945763491500375

theorem tailTrace_5343570 : CollatzResearch.WordTrace tailWord_5343570 prefixEnd_5343570 2743819820945763491500375 := by
  unfold tailWord_5343570
  simp only [CollatzResearch.WordTrace]
  refine ⟨48724002312791493486147041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129930672834110649296392109 48724002312791493486147041)
  ·
    refine ⟨36543001734593620114610281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48724002312791493486147041 36543001734593620114610281)
    ·
      refine ⟨27407251300945215085957711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36543001734593620114610281 27407251300945215085957711)
      ·
        refine ⟨41110876951417822628936567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27407251300945215085957711 41110876951417822628936567)
        ·
          refine ⟨61666315427126733943404851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41110876951417822628936567 61666315427126733943404851)
          ·
            refine ⟨92499473140690100915107277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61666315427126733943404851 92499473140690100915107277)
            ·
              refine ⟨34687302427758787843165229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92499473140690100915107277 34687302427758787843165229)
              ·
                refine ⟨13007738410409545441186961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34687302427758787843165229 13007738410409545441186961)
                ·
                  refine ⟨9755803807807159080890221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13007738410409545441186961 9755803807807159080890221)
                  ·
                    refine ⟨3658426427927684655333833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9755803807807159080890221 3658426427927684655333833)
                    ·
                      refine ⟨2743819820945763491500375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658426427927684655333833 2743819820945763491500375)
                      ·
                        rfl

theorem cell23_5343570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_5343570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343570 prefixEnd_5343570 := by exact prefixLift 5343570
  have htrace : WordTrace (prefixWord ++ tailWord_5343570) baseStart_5343570 baseEnd_5343570 := by
    simpa [prefixWord, tailWord_5343570, baseEnd_5343570] using wordTrace_append hprefix tailTrace_5343570
  have hstable : (prefixWord ++ tailWord_5343570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343570).length < 2 ^ (prefixWord ++ tailWord_5343570).sum := by decide
  have hdescent : baseEnd_5343570 < baseStart_5343570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343583 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 4]
def baseStart_5343583 : Nat := 118140960795 + 5343583 * 2 ^ 59
def prefixEnd_5343583 : Nat := 4983230072969 + 3 ^ 40 * 5343583 * 2
def baseEnd_5343583 : Nat := 2743826496194271940637815

theorem tailTrace_5343583 : CollatzResearch.WordTrace tailWord_5343583 prefixEnd_5343583 2743826496194271940637815 := by
  unfold tailWord_5343583
  simp only [CollatzResearch.WordTrace]
  refine ⟨194896483400118877164811403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129930988933412584776540935 194896483400118877164811403)
  ·
    refine ⟨292344725100178315747217105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194896483400118877164811403 292344725100178315747217105)
    ·
      refine ⟨219258543825133736810412829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292344725100178315747217105 219258543825133736810412829)
      ·
        refine ⟨82221953934425151303904811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219258543825133736810412829 82221953934425151303904811)
        ·
          refine ⟨123332930901637726955857217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82221953934425151303904811 123332930901637726955857217)
          ·
            refine ⟨92499698176228295216892913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123332930901637726955857217 92499698176228295216892913)
            ·
              refine ⟨69374773632171221412669685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92499698176228295216892913 69374773632171221412669685)
              ·
                refine ⟨6503885028016052007437783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69374773632171221412669685 6503885028016052007437783)
                ·
                  refine ⟨9755827542024078011156675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503885028016052007437783 9755827542024078011156675)
                  ·
                    refine ⟨14633741313036117016735013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9755827542024078011156675 14633741313036117016735013)
                    ·
                      refine ⟨2743826496194271940637815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14633741313036117016735013 2743826496194271940637815)
                      ·
                        rfl

theorem cell23_5343583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_5343583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343583 prefixEnd_5343583 := by exact prefixLift 5343583
  have htrace : WordTrace (prefixWord ++ tailWord_5343583) baseStart_5343583 baseEnd_5343583 := by
    simpa [prefixWord, tailWord_5343583, baseEnd_5343583] using wordTrace_append hprefix tailTrace_5343583
  have hstable : (prefixWord ++ tailWord_5343583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343583).length < 2 ^ (prefixWord ++ tailWord_5343583).sum := by decide
  have hdescent : baseEnd_5343583 < baseStart_5343583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343594 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5343594 : Nat := 118140960795 + 5343594 * 2 ^ 59
def prefixEnd_5343594 : Nat := 4983230072969 + 3 ^ 40 * 5343594 * 2
def baseEnd_5343594 : Nat := 2743832144481471397600265

theorem tailTrace_5343594 : CollatzResearch.WordTrace tailWord_5343594 prefixEnd_5343594 2743832144481471397600265 := by
  unfold tailWord_5343594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48724221150769756510865459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129931256402052684028974557 48724221150769756510865459)
  ·
    refine ⟨73086331726154634766298189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48724221150769756510865459 73086331726154634766298189)
    ·
      refine ⟨27407374397307988037361821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73086331726154634766298189 27407374397307988037361821)
      ·
        refine ⟨10277765398990495514010683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27407374397307988037361821 10277765398990495514010683)
        ·
          refine ⟨15416648098485743271016025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10277765398990495514010683 15416648098485743271016025)
          ·
            refine ⟨11562486073864307453262019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15416648098485743271016025 11562486073864307453262019)
            ·
              refine ⟨17343729110796461179893029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11562486073864307453262019 17343729110796461179893029)
              ·
                refine ⟨3251949208274336471229943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17343729110796461179893029 3251949208274336471229943)
                ·
                  refine ⟨4877923812411504706844915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251949208274336471229943 4877923812411504706844915)
                  ·
                    refine ⟨7316885718617257060267373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4877923812411504706844915 7316885718617257060267373)
                    ·
                      refine ⟨2743832144481471397600265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7316885718617257060267373 2743832144481471397600265)
                      ·
                        rfl

theorem cell23_5343594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5343594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343594 prefixEnd_5343594 := by exact prefixLift 5343594
  have htrace : WordTrace (prefixWord ++ tailWord_5343594) baseStart_5343594 baseEnd_5343594 := by
    simpa [prefixWord, tailWord_5343594, baseEnd_5343594] using wordTrace_append hprefix tailTrace_5343594
  have hstable : (prefixWord ++ tailWord_5343594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343594).length < 2 ^ (prefixWord ++ tailWord_5343594).sum := by decide
  have hdescent : baseEnd_5343594 < baseStart_5343594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343613 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_5343613 : Nat := 118140960795 + 5343613 * 2 ^ 59
def prefixEnd_5343613 : Nat := 4983230072969 + 3 ^ 40 * 5343613 * 2
def baseEnd_5343613 : Nat := 2743841900613906823262677

theorem tailTrace_5343613 : CollatzResearch.WordTrace tailWord_5343613 prefixEnd_5343613 2743841900613906823262677 := by
  unfold tailWord_5343613
  simp only [CollatzResearch.WordTrace]
  refine ⟨194897577590010192288403493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129931718393340128192268995 194897577590010192288403493)
  ·
    refine ⟨36543295798126911054075655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194897577590010192288403493 36543295798126911054075655)
    ·
      refine ⟨54814943697190366581113483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36543295798126911054075655 54814943697190366581113483)
      ·
        refine ⟨82222415545785549871670225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54814943697190366581113483 82222415545785549871670225)
        ·
          refine ⟨61666811659339162403752669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82222415545785549871670225 61666811659339162403752669)
          ·
            refine ⟨23125054372252185901407251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61666811659339162403752669 23125054372252185901407251)
            ·
              refine ⟨34687581558378278852110877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23125054372252185901407251 34687581558378278852110877)
              ·
                refine ⟨13007843084391854569541579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34687581558378278852110877 13007843084391854569541579)
                ·
                  refine ⟨19511764626587781854312369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13007843084391854569541579 19511764626587781854312369)
                  ·
                    refine ⟨14633823469940836390734277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19511764626587781854312369 14633823469940836390734277)
                    ·
                      refine ⟨2743841900613906823262677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14633823469940836390734277 2743841900613906823262677)
                      ·
                        rfl

theorem cell23_5343613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_5343613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343613 prefixEnd_5343613 := by exact prefixLift 5343613
  have htrace : WordTrace (prefixWord ++ tailWord_5343613) baseStart_5343613 baseEnd_5343613 := by
    simpa [prefixWord, tailWord_5343613, baseEnd_5343613] using wordTrace_append hprefix tailTrace_5343613
  have hstable : (prefixWord ++ tailWord_5343613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343613).length < 2 ^ (prefixWord ++ tailWord_5343613).sum := by decide
  have hdescent : baseEnd_5343613 < baseStart_5343613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343617 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5343617 : Nat := 118140960795 + 5343617 * 2 ^ 59
def prefixEnd_5343617 : Nat := 4983230072969 + 3 ^ 40 * 5343617 * 2
def baseEnd_5343617 : Nat := 2743843954536524807612659

theorem tailTrace_5343617 : CollatzResearch.WordTrace tailWord_5343617 prefixEnd_5343617 2743843954536524807612659 := by
  unfold tailWord_5343617
  simp only [CollatzResearch.WordTrace]
  refine ⟨194897723481995700971549105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129931815654663800647699403 194897723481995700971549105)
  ·
    refine ⟨146173292611496775728661829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194897723481995700971549105 146173292611496775728661829)
    ·
      refine ⟨27407492364655645449124093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146173292611496775728661829 27407492364655645449124093)
      ·
        refine ⟨10277809636745867043421535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27407492364655645449124093 10277809636745867043421535)
        ·
          refine ⟨15416714455118800565132303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10277809636745867043421535 15416714455118800565132303)
          ·
            refine ⟨23125071682678200847698455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15416714455118800565132303 23125071682678200847698455)
            ·
              refine ⟨34687607524017301271547683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23125071682678200847698455 34687607524017301271547683)
              ·
                refine ⟨52031411286025951907321525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34687607524017301271547683 52031411286025951907321525)
                ·
                  refine ⟨4877944808064932991311393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52031411286025951907321525 4877944808064932991311393)
                  ·
                    refine ⟨3658458606048699743483545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4877944808064932991311393 3658458606048699743483545)
                    ·
                      refine ⟨2743843954536524807612659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658458606048699743483545 2743843954536524807612659)
                      ·
                        rfl

theorem cell23_5343617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5343617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343617 prefixEnd_5343617 := by exact prefixLift 5343617
  have htrace : WordTrace (prefixWord ++ tailWord_5343617) baseStart_5343617 baseEnd_5343617 := by
    simpa [prefixWord, tailWord_5343617, baseEnd_5343617] using wordTrace_append hprefix tailTrace_5343617
  have hstable : (prefixWord ++ tailWord_5343617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343617).length < 2 ^ (prefixWord ++ tailWord_5343617).sum := by decide
  have hdescent : baseEnd_5343617 < baseStart_5343617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343620 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_5343620 : Nat := 118140960795 + 5343620 * 2 ^ 59
def prefixEnd_5343620 : Nat := 4983230072969 + 3 ^ 40 * 5343620 * 2
def baseEnd_5343620 : Nat := 2743845494978488295875145

theorem tailTrace_5343620 : CollatzResearch.WordTrace tailWord_5343620 prefixEnd_5343620 2743845494978488295875145 := by
  unfold tailWord_5343620
  simp only [CollatzResearch.WordTrace]
  refine ⟨97448916450492416241954157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129931888600656554989272209 97448916450492416241954157)
  ·
    refine ⟨36543343668934656090732809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97448916450492416241954157 36543343668934656090732809)
    ·
      refine ⟨27407507751700992068049607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36543343668934656090732809 27407507751700992068049607)
      ·
        refine ⟨41111261627551488102074411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27407507751700992068049607 41111261627551488102074411)
        ·
          refine ⟨61666892441327232153111617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41111261627551488102074411 61666892441327232153111617)
          ·
            refine ⟨46250169330995424114833713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61666892441327232153111617 46250169330995424114833713)
            ·
              refine ⟨34687626998246568086125285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46250169330995424114833713 34687626998246568086125285)
              ·
                refine ⟨6503930062171231516148491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34687626998246568086125285 6503930062171231516148491)
                ·
                  refine ⟨9755895093256847274222737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503930062171231516148491 9755895093256847274222737)
                  ·
                    refine ⟨7316921319942635455667053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9755895093256847274222737 7316921319942635455667053)
                    ·
                      refine ⟨2743845494978488295875145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7316921319942635455667053 2743845494978488295875145)
                      ·
                        rfl

theorem cell23_5343620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_5343620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343620 prefixEnd_5343620 := by exact prefixLift 5343620
  have htrace : WordTrace (prefixWord ++ tailWord_5343620) baseStart_5343620 baseEnd_5343620 := by
    simpa [prefixWord, tailWord_5343620, baseEnd_5343620] using wordTrace_append hprefix tailTrace_5343620
  have hstable : (prefixWord ++ tailWord_5343620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343620).length < 2 ^ (prefixWord ++ tailWord_5343620).sum := by decide
  have hdescent : baseEnd_5343620 < baseStart_5343620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343623 : List Nat := [1, 1, 4, 2, 2, 1, 5, 7]
def baseStart_5343623 : Nat := 118140960795 + 5343623 * 2 ^ 59
def prefixEnd_5343623 : Nat := 4983230072969 + 3 ^ 40 * 5343623 * 2
def baseEnd_5343623 : Nat := 101623964274831547560653

theorem tailTrace_5343623 : CollatzResearch.WordTrace tailWord_5343623 prefixEnd_5343623 101623964274831547560653 := by
  unfold tailWord_5343623
  simp only [CollatzResearch.WordTrace]
  refine ⟨194897942319973963996267523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129931961546649309330845015 194897942319973963996267523)
  ·
    refine ⟨292346913479960945994401285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194897942319973963996267523 292346913479960945994401285)
    ·
      refine ⟨54815046277492677373950241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292346913479960945994401285 54815046277492677373950241)
      ·
        refine ⟨41111284708119508030462681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54815046277492677373950241 41111284708119508030462681)
        ·
          refine ⟨30833463531089631022847011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41111284708119508030462681 30833463531089631022847011)
          ·
            refine ⟨46250195296634446534270517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30833463531089631022847011 46250195296634446534270517)
            ·
              refine ⟨4335955809059479362587861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46250195296634446534270517 4335955809059479362587861)
              ·
                refine ⟨101623964274831547560653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4335955809059479362587861 101623964274831547560653)
                ·
                  rfl

theorem cell23_5343623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 7].length) (baseStart_5343623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343623 prefixEnd_5343623 := by exact prefixLift 5343623
  have htrace : WordTrace (prefixWord ++ tailWord_5343623) baseStart_5343623 baseEnd_5343623 := by
    simpa [prefixWord, tailWord_5343623, baseEnd_5343623] using wordTrace_append hprefix tailTrace_5343623
  have hstable : (prefixWord ++ tailWord_5343623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343623).length < 2 ^ (prefixWord ++ tailWord_5343623).sum := by decide
  have hdescent : baseEnd_5343623 < baseStart_5343623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343630 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5343630 : Nat := 118140960795 + 5343630 * 2 ^ 59
def prefixEnd_5343630 : Nat := 4983230072969 + 3 ^ 40 * 5343630 * 2
def baseEnd_5343630 : Nat := 2743850629785033256750099

theorem tailTrace_5343630 : CollatzResearch.WordTrace tailWord_5343630 prefixEnd_5343630 2743850629785033256750099 := by
  unfold tailWord_5343630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24362274703868575523971543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129932131753965736127848229 24362274703868575523971543)
  ·
    refine ⟨36543412055802863285957315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24362274703868575523971543 36543412055802863285957315)
    ·
      refine ⟨54815118083704294928935973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36543412055802863285957315 54815118083704294928935973)
      ·
        refine ⟨10277834640694555299175495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54815118083704294928935973 10277834640694555299175495)
        ·
          refine ⟨15416751961041832948763243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10277834640694555299175495 15416751961041832948763243)
          ·
            refine ⟨23125127941562749423144865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15416751961041832948763243 23125127941562749423144865)
            ·
              refine ⟨17343845956172062067358649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23125127941562749423144865 17343845956172062067358649)
              ·
                refine ⟨13007884467129046550518987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17343845956172062067358649 13007884467129046550518987)
                ·
                  refine ⟨19511826700693569825778481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13007884467129046550518987 19511826700693569825778481)
                  ·
                    refine ⟨14633870025520177369333861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19511826700693569825778481 14633870025520177369333861)
                    ·
                      refine ⟨2743850629785033256750099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14633870025520177369333861 2743850629785033256750099)
                      ·
                        rfl

theorem cell23_5343630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5343630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343630 prefixEnd_5343630 := by exact prefixLift 5343630
  have htrace : WordTrace (prefixWord ++ tailWord_5343630) baseStart_5343630 baseEnd_5343630 := by
    simpa [prefixWord, tailWord_5343630, baseEnd_5343630] using wordTrace_append hprefix tailTrace_5343630
  have hstable : (prefixWord ++ tailWord_5343630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343630).length < 2 ^ (prefixWord ++ tailWord_5343630).sum := by decide
  have hdescent : baseEnd_5343630 < baseStart_5343630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343677 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_5343677 : Nat := 118140960795 + 5343677 * 2 ^ 59
def prefixEnd_5343677 : Nat := 4983230072969 + 3 ^ 40 * 5343677 * 2
def baseEnd_5343677 : Nat := 2743874763375794572862383

theorem tailTrace_5343677 : CollatzResearch.WordTrace tailWord_5343677 prefixEnd_5343677 2743874763375794572862383 := by
  unfold tailWord_5343677
  simp only [CollatzResearch.WordTrace]
  refine ⟨194899911861778331218733285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129933274574518887479155523 194899911861778331218733285)
  ·
    refine ⟨36543733474083437103512491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194899911861778331218733285 36543733474083437103512491)
    ·
      refine ⟨54815600211125155655268737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36543733474083437103512491 54815600211125155655268737)
      ·
        refine ⟨41111700158343866741451553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54815600211125155655268737 41111700158343866741451553)
        ·
          refine ⟨30833775118757900056088665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41111700158343866741451553 30833775118757900056088665)
          ·
            refine ⟨23125331339068425042066499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30833775118757900056088665 23125331339068425042066499)
            ·
              refine ⟨34687997008602637563099749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23125331339068425042066499 34687997008602637563099749)
              ·
                refine ⟨6503999439112994543081203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34687997008602637563099749 6503999439112994543081203)
                ·
                  refine ⟨9755999158669491814621805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503999439112994543081203 9755999158669491814621805)
                  ·
                    refine ⟨3658499684501059430483177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9755999158669491814621805 3658499684501059430483177)
                    ·
                      refine ⟨2743874763375794572862383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658499684501059430483177 2743874763375794572862383)
                      ·
                        rfl

theorem cell23_5343677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_5343677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343677 prefixEnd_5343677 := by exact prefixLift 5343677
  have htrace : WordTrace (prefixWord ++ tailWord_5343677) baseStart_5343677 baseEnd_5343677 := by
    simpa [prefixWord, tailWord_5343677, baseEnd_5343677] using wordTrace_append hprefix tailTrace_5343677
  have hstable : (prefixWord ++ tailWord_5343677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343677).length < 2 ^ (prefixWord ++ tailWord_5343677).sum := by decide
  have hdescent : baseEnd_5343677 < baseStart_5343677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343690 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_5343690 : Nat := 118140960795 + 5343690 * 2 ^ 59
def prefixEnd_5343690 : Nat := 4983230072969 + 3 ^ 40 * 5343690 * 2
def baseEnd_5343690 : Nat := 2743881438624303021999823

theorem tailTrace_5343690 : CollatzResearch.WordTrace tailWord_5343690 prefixEnd_5343690 2743881438624303021999823 := by
  unfold tailWord_5343690
  simp only [CollatzResearch.WordTrace]
  refine ⟨48725096502682808609739131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129933590673820822959304349 48725096502682808609739131)
  ·
    refine ⟨73087644754024212914608697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48725096502682808609739131 73087644754024212914608697)
    ·
      refine ⟨54815733565518159685956523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73087644754024212914608697 54815733565518159685956523)
      ·
        refine ⟨82223600348277239528934785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54815733565518159685956523 82223600348277239528934785)
        ·
          refine ⟨61667700261207929646701089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82223600348277239528934785 61667700261207929646701089)
          ·
            refine ⟨46250775195905947235025817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61667700261207929646701089 46250775195905947235025817)
            ·
              refine ⟨34688081396929460426269363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46250775195905947235025817 34688081396929460426269363)
              ·
                refine ⟨52032122095394190639404045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34688081396929460426269363 52032122095394190639404045)
                ·
                  refine ⟨19512045785772821489776517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52032122095394190639404045 19512045785772821489776517)
                  ·
                    refine ⟨3658508584832404029333097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19512045785772821489776517 3658508584832404029333097)
                    ·
                      refine ⟨2743881438624303021999823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658508584832404029333097 2743881438624303021999823)
                      ·
                        rfl

theorem cell23_5343690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_5343690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343690 prefixEnd_5343690 := by exact prefixLift 5343690
  have htrace : WordTrace (prefixWord ++ tailWord_5343690) baseStart_5343690 baseEnd_5343690 := by
    simpa [prefixWord, tailWord_5343690, baseEnd_5343690] using wordTrace_append hprefix tailTrace_5343690
  have hstable : (prefixWord ++ tailWord_5343690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343690).length < 2 ^ (prefixWord ++ tailWord_5343690).sum := by decide
  have hdescent : baseEnd_5343690 < baseStart_5343690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343723 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 3]
def baseStart_5343723 : Nat := 118140960795 + 5343723 * 2 ^ 59
def prefixEnd_5343723 : Nat := 4983230072969 + 3 ^ 40 * 5343723 * 2
def baseEnd_5343723 : Nat := 2743898383485901392887171

theorem tailTrace_5343723 : CollatzResearch.WordTrace tailWord_5343723 prefixEnd_5343723 2743898383485901392887171 := by
  unfold tailWord_5343723
  simp only [CollatzResearch.WordTrace]
  refine ⟨194901589619611681074907823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129934393079741120716605215 194901589619611681074907823)
  ·
    refine ⟨292352384429417521612361735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194901589619611681074907823 292352384429417521612361735)
    ·
      refine ⟨438528576644126282418542603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292352384429417521612361735 438528576644126282418542603)
      ·
        refine ⟨657792864966189423627813905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438528576644126282418542603 657792864966189423627813905)
        ·
          refine ⟨493344648724642067720860429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657792864966189423627813905 493344648724642067720860429)
          ·
            refine ⟨185004243271740775395322661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493344648724642067720860429 185004243271740775395322661)
            ·
              refine ⟨34688295613451395386622999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185004243271740775395322661 34688295613451395386622999)
              ·
                refine ⟨52032443420177093079934499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34688295613451395386622999 52032443420177093079934499)
                ·
                  refine ⟨78048665130265639619901749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52032443420177093079934499 78048665130265639619901749)
                  ·
                    refine ⟨7317062355962403714365789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78048665130265639619901749 7317062355962403714365789)
                    ·
                      refine ⟨2743898383485901392887171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7317062355962403714365789 2743898383485901392887171)
                      ·
                        rfl

theorem cell23_5343723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 3].length) (baseStart_5343723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343723 prefixEnd_5343723 := by exact prefixLift 5343723
  have htrace : WordTrace (prefixWord ++ tailWord_5343723) baseStart_5343723 baseEnd_5343723 := by
    simpa [prefixWord, tailWord_5343723, baseEnd_5343723] using wordTrace_append hprefix tailTrace_5343723
  have hstable : (prefixWord ++ tailWord_5343723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343723).length < 2 ^ (prefixWord ++ tailWord_5343723).sum := by decide
  have hdescent : baseEnd_5343723 < baseStart_5343723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343764 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 5]
def baseStart_5343764 : Nat := 118140960795 + 5343764 * 2 ^ 59
def prefixEnd_5343764 : Nat := 4983230072969 + 3 ^ 40 * 5343764 * 2
def baseEnd_5343764 : Nat := 304879937354748414719387

theorem tailTrace_5343764 : CollatzResearch.WordTrace tailWord_5343764 prefixEnd_5343764 304879937354748414719387 := by
  unfold tailWord_5343764
  simp only [CollatzResearch.WordTrace]
  refine ⟨97451542506231572538575173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129935390008308763384766897 97451542506231572538575173)
  ·
    refine ⟨18272164219918419850982845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97451542506231572538575173 18272164219918419850982845)
    ·
      refine ⟨6852061582469407444118567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18272164219918419850982845 6852061582469407444118567)
      ·
        refine ⟨10278092373704111166177851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6852061582469407444118567 10278092373704111166177851)
        ·
          refine ⟨15417138560556166749266777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10278092373704111166177851 15417138560556166749266777)
          ·
            refine ⟨11562853920417125061950083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15417138560556166749266777 11562853920417125061950083)
            ·
              refine ⟨17344280880625687592925125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11562853920417125061950083 17344280880625687592925125)
              ·
                refine ⟨3252052665117316423673461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17344280880625687592925125 3252052665117316423673461)
                ·
                  refine ⟨304879937354748414719387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3252052665117316423673461 304879937354748414719387)
                  ·
                    rfl

theorem cell23_5343764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_5343764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343764 prefixEnd_5343764 := by exact prefixLift 5343764
  have htrace : WordTrace (prefixWord ++ tailWord_5343764) baseStart_5343764 baseEnd_5343764 := by
    simpa [prefixWord, tailWord_5343764, baseEnd_5343764] using wordTrace_append hprefix tailTrace_5343764
  have hstable : (prefixWord ++ tailWord_5343764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343764).length < 2 ^ (prefixWord ++ tailWord_5343764).sum := by decide
  have hdescent : baseEnd_5343764 < baseStart_5343764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343800 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_5343800 : Nat := 118140960795 + 5343800 * 2 ^ 59
def prefixEnd_5343800 : Nat := 4983230072969 + 3 ^ 40 * 5343800 * 2
def baseEnd_5343800 : Nat := 2743937921496297591624317

theorem tailTrace_5343800 : CollatzResearch.WordTrace tailWord_5343800 prefixEnd_5343800 2743937921496297591624317 := by
  unfold tailWord_5343800
  simp only [CollatzResearch.WordTrace]
  refine ⟨97452199020166361612730427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129936265360221815483640569 97452199020166361612730427)
  ·
    refine ⟨146178298530249542419095641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97452199020166361612730427 146178298530249542419095641)
    ·
      refine ⟨109633723897687156814321731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146178298530249542419095641 109633723897687156814321731)
      ·
        refine ⟨164450585846530735221482597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109633723897687156814321731 164450585846530735221482597)
        ·
          refine ⟨30834484846224512854027987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164450585846530735221482597 30834484846224512854027987)
          ·
            refine ⟨46251727269336769281041981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30834484846224512854027987 46251727269336769281041981)
            ·
              refine ⟨17344397726001288480390743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46251727269336769281041981 17344397726001288480390743)
              ·
                refine ⟨26016596589001932720586115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17344397726001288480390743 26016596589001932720586115)
                ·
                  refine ⟨39024894883502899080879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26016596589001932720586115 39024894883502899080879173)
                  ·
                    refine ⟨7317167790656793577664845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39024894883502899080879173 7317167790656793577664845)
                    ·
                      refine ⟨2743937921496297591624317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7317167790656793577664845 2743937921496297591624317)
                      ·
                        rfl

theorem cell23_5343800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_5343800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343800 prefixEnd_5343800 := by exact prefixLift 5343800
  have htrace : WordTrace (prefixWord ++ tailWord_5343800) baseStart_5343800 baseEnd_5343800 := by
    simpa [prefixWord, tailWord_5343800, baseEnd_5343800] using wordTrace_append hprefix tailTrace_5343800
  have hstable : (prefixWord ++ tailWord_5343800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343800).length < 2 ^ (prefixWord ++ tailWord_5343800).sum := by decide
  have hdescent : baseEnd_5343800 < baseStart_5343800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343823 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_5343823 : Nat := 118140960795 + 5343823 * 2 ^ 59
def prefixEnd_5343823 : Nat := 4983230072969 + 3 ^ 40 * 5343823 * 2
def baseEnd_5343823 : Nat := 2743949731551351001636711

theorem tailTrace_5343823 : CollatzResearch.WordTrace tailWord_5343823 prefixEnd_5343823 2743949731551351001636711 := by
  unfold tailWord_5343823
  simp only [CollatzResearch.WordTrace]
  refine ⟨194905236919249398153548123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129936824612832932102365415 194905236919249398153548123)
  ·
    refine ⟨292357855378874097230322185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194905236919249398153548123 292357855378874097230322185)
    ·
      refine ⟨219268391534155572922741639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292357855378874097230322185 219268391534155572922741639)
      ·
        refine ⟨328902587301233359384112459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219268391534155572922741639 328902587301233359384112459)
        ·
          refine ⟨493353880951850039076168689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328902587301233359384112459 493353880951850039076168689)
          ·
            refine ⟨370015410713887529307126517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493353880951850039076168689 370015410713887529307126517)
            ·
              refine ⟨34688944754426955872543111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370015410713887529307126517 34688944754426955872543111)
              ·
                refine ⟨52033417131640433808814667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34688944754426955872543111 52033417131640433808814667)
                ·
                  refine ⟨78050125697460650713222001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52033417131640433808814667 78050125697460650713222001)
                  ·
                    refine ⟨58537594273095488034916501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78050125697460650713222001 58537594273095488034916501)
                    ·
                      refine ⟨2743949731551351001636711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58537594273095488034916501 2743949731551351001636711)
                      ·
                        rfl

theorem cell23_5343823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_5343823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343823 prefixEnd_5343823 := by exact prefixLift 5343823
  have htrace : WordTrace (prefixWord ++ tailWord_5343823) baseStart_5343823 baseEnd_5343823 := by
    simpa [prefixWord, tailWord_5343823, baseEnd_5343823] using wordTrace_append hprefix tailTrace_5343823
  have hstable : (prefixWord ++ tailWord_5343823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343823).length < 2 ^ (prefixWord ++ tailWord_5343823).sum := by decide
  have hdescent : baseEnd_5343823 < baseStart_5343823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343858 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_5343858 : Nat := 118140960795 + 5343858 * 2 ^ 59
def prefixEnd_5343858 : Nat := 4983230072969 + 3 ^ 40 * 5343858 * 2
def baseEnd_5343858 : Nat := 914655901124752788233017

theorem tailTrace_5343858 : CollatzResearch.WordTrace tailWord_5343858 prefixEnd_5343858 914655901124752788233017 := by
  unfold tailWord_5343858
  simp only [CollatzResearch.WordTrace]
  refine ⟨48726628368530649782768057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129937675649415066087381485 48726628368530649782768057)
  ·
    refine ⟨36544971276397987337076043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48726628368530649782768057 36544971276397987337076043)
    ·
      refine ⟨54817456914596981005614065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36544971276397987337076043 54817456914596981005614065)
      ·
        refine ⟨41113092685947735754210549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54817456914596981005614065 41113092685947735754210549)
        ·
          refine ⟨3854352439307600226957239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41113092685947735754210549 3854352439307600226957239)
          ·
            refine ⟨5781528658961400340435859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854352439307600226957239 5781528658961400340435859)
            ·
              refine ⟨8672292988442100510653789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781528658961400340435859 8672292988442100510653789)
              ·
                refine ⟨3252109870665787691495171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8672292988442100510653789 3252109870665787691495171)
                ·
                  refine ⟨4878164805998681537242757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252109870665787691495171 4878164805998681537242757)
                  ·
                    refine ⟨914655901124752788233017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878164805998681537242757 914655901124752788233017)
                    ·
                      rfl

theorem cell23_5343858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_5343858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343858 prefixEnd_5343858 := by exact prefixLift 5343858
  have htrace : WordTrace (prefixWord ++ tailWord_5343858) baseStart_5343858 baseEnd_5343858 := by
    simpa [prefixWord, tailWord_5343858, baseEnd_5343858] using wordTrace_append hprefix tailTrace_5343858
  have hstable : (prefixWord ++ tailWord_5343858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343858).length < 2 ^ (prefixWord ++ tailWord_5343858).sum := by decide
  have hdescent : baseEnd_5343858 < baseStart_5343858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343897 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 2, 4]
def baseStart_5343897 : Nat := 118140960795 + 5343897 * 2 ^ 59
def prefixEnd_5343897 : Nat := 4983230072969 + 3 ^ 40 * 5343897 * 2
def baseEnd_5343897 : Nat := 914662576373261237370457

theorem tailTrace_5343897 : CollatzResearch.WordTrace tailWord_5343897 prefixEnd_5343897 914662576373261237370457 := by
  unfold tailWord_5343897
  simp only [CollatzResearch.WordTrace]
  refine ⟨194907935920981308791741945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129938623947320872527827963 194907935920981308791741945)
  ·
    refine ⟨146180951940735981593806459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194907935920981308791741945 146180951940735981593806459)
    ·
      refine ⟨219271427911103972390709689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146180951940735981593806459 219271427911103972390709689)
      ·
        refine ⟨164453570933327979293032267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219271427911103972390709689 164453570933327979293032267)
        ·
          refine ⟨246680356399991968939548401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164453570933327979293032267 246680356399991968939548401)
          ·
            refine ⟨185010267299993976704661301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246680356399991968939548401 185010267299993976704661301)
            ·
              refine ⟨17344712559374435316061997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185010267299993976704661301 17344712559374435316061997)
              ·
                refine ⟨6504267209765413243523249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17344712559374435316061997 6504267209765413243523249)
                ·
                  refine ⟨4878200407324059932642437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6504267209765413243523249 4878200407324059932642437)
                  ·
                    refine ⟨914662576373261237370457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878200407324059932642437 914662576373261237370457)
                    ·
                      rfl

theorem cell23_5343897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_5343897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343897 prefixEnd_5343897 := by exact prefixLift 5343897
  have htrace : WordTrace (prefixWord ++ tailWord_5343897) baseStart_5343897 baseEnd_5343897 := by
    simpa [prefixWord, tailWord_5343897, baseEnd_5343897] using wordTrace_append hprefix tailTrace_5343897
  have hstable : (prefixWord ++ tailWord_5343897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343897).length < 2 ^ (prefixWord ++ tailWord_5343897).sum := by decide
  have hdescent : baseEnd_5343897 < baseStart_5343897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343907 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 3]
def baseStart_5343907 : Nat := 118140960795 + 5343907 * 2 ^ 59
def prefixEnd_5343907 : Nat := 4983230072969 + 3 ^ 40 * 5343907 * 2
def baseEnd_5343907 : Nat := 2743992863926328672986325

theorem tailTrace_5343907 : CollatzResearch.WordTrace tailWord_5343907 prefixEnd_5343907 2743992863926328672986325 := by
  unfold tailWord_5343907
  simp only [CollatzResearch.WordTrace]
  refine ⟨194908300650945080499605975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129938867100630053666403983 194908300650945080499605975)
  ·
    refine ⟨292362450976417620749408963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194908300650945080499605975 292362450976417620749408963)
    ·
      refine ⟨438543676464626431124113445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292362450976417620749408963 438543676464626431124113445)
      ·
        refine ⟨82226939337117455835771271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 438543676464626431124113445 82226939337117455835771271)
        ·
          refine ⟨123340409005676183753656907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82226939337117455835771271 123340409005676183753656907)
          ·
            refine ⟨185010613508514275630485361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123340409005676183753656907 185010613508514275630485361)
            ·
              refine ⟨138757960131385706722864021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185010613508514275630485361 138757960131385706722864021)
              ·
                refine ⟨6504279381158705002634251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138757960131385706722864021 6504279381158705002634251)
                ·
                  refine ⟨9756419071738057503951377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6504279381158705002634251 9756419071738057503951377)
                  ·
                    refine ⟨7317314303803543127963533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9756419071738057503951377 7317314303803543127963533)
                    ·
                      refine ⟨2743992863926328672986325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7317314303803543127963533 2743992863926328672986325)
                      ·
                        rfl

theorem cell23_5343907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_5343907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343907 prefixEnd_5343907 := by exact prefixLift 5343907
  have htrace : WordTrace (prefixWord ++ tailWord_5343907) baseStart_5343907 baseEnd_5343907 := by
    simpa [prefixWord, tailWord_5343907, baseEnd_5343907] using wordTrace_append hprefix tailTrace_5343907
  have hstable : (prefixWord ++ tailWord_5343907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343907).length < 2 ^ (prefixWord ++ tailWord_5343907).sum := by decide
  have hdescent : baseEnd_5343907 < baseStart_5343907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343917 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5343917 : Nat := 118140960795 + 5343917 * 2 ^ 59
def prefixEnd_5343917 : Nat := 4983230072969 + 3 ^ 40 * 5343917 * 2
def baseEnd_5343917 : Nat := 2743997998732873633861279

theorem tailTrace_5343917 : CollatzResearch.WordTrace tailWord_5343917 prefixEnd_5343917 2743997998732873633861279 := by
  unfold tailWord_5343917
  simp only [CollatzResearch.WordTrace]
  refine ⟨194908665380908852207470005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129939110253939234804980003 194908665380908852207470005)
  ·
    refine ⟨18272687379460204894450313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194908665380908852207470005 18272687379460204894450313)
    ·
      refine ⟨13704515534595153670837735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18272687379460204894450313 13704515534595153670837735)
      ·
        refine ⟨20556773301892730506256603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13704515534595153670837735 20556773301892730506256603)
        ·
          refine ⟨30835159952839095759384905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20556773301892730506256603 30835159952839095759384905)
          ·
            refine ⟨23126369964629321819538679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30835159952839095759384905 23126369964629321819538679)
            ·
              refine ⟨34689554946943982729308019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23126369964629321819538679 34689554946943982729308019)
              ·
                refine ⟨52034332420415974093962029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34689554946943982729308019 52034332420415974093962029)
                ·
                  refine ⟨19512874657655990285235761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52034332420415974093962029 19512874657655990285235761)
                  ·
                    refine ⟨14634655993241992713926821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19512874657655990285235761 14634655993241992713926821)
                    ·
                      refine ⟨2743997998732873633861279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14634655993241992713926821 2743997998732873633861279)
                      ·
                        rfl

theorem cell23_5343917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5343917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343917 prefixEnd_5343917 := by exact prefixLift 5343917
  have htrace : WordTrace (prefixWord ++ tailWord_5343917) baseStart_5343917 baseEnd_5343917 := by
    simpa [prefixWord, tailWord_5343917, baseEnd_5343917] using wordTrace_append hprefix tailTrace_5343917
  have hstable : (prefixWord ++ tailWord_5343917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343917).length < 2 ^ (prefixWord ++ tailWord_5343917).sum := by decide
  have hdescent : baseEnd_5343917 < baseStart_5343917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343980 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_5343980 : Nat := 118140960795 + 5343980 * 2 ^ 59
def prefixEnd_5343980 : Nat := 4983230072969 + 3 ^ 40 * 5343980 * 2
def baseEnd_5343980 : Nat := 2744030348014106887373489

theorem tailTrace_5343980 : CollatzResearch.WordTrace tailWord_5343980 prefixEnd_5343980 2744030348014106887373489 := by
  unfold tailWord_5343980
  simp only [CollatzResearch.WordTrace]
  refine ⟨97455481589840306983506697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129940642119787075978008929 97455481589840306983506697)
  ·
    refine ⟨73091611192380230237630023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97455481589840306983506697 73091611192380230237630023)
    ·
      refine ⟨109637416788570345356445035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73091611192380230237630023 109637416788570345356445035)
      ·
        refine ⟨164456125182855518034667553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109637416788570345356445035 164456125182855518034667553)
        ·
          refine ⟨123342093887141638526000665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164456125182855518034667553 123342093887141638526000665)
          ·
            refine ⟨92506570415356228894500499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123342093887141638526000665 92506570415356228894500499)
            ·
              refine ⟨138759855623034343341750749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92506570415356228894500499 138759855623034343341750749)
              ·
                refine ⟨52034945858637878753156531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138759855623034343341750749 52034945858637878753156531)
                ·
                  refine ⟨78052418787956818129734797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52034945858637878753156531 78052418787956818129734797)
                  ·
                    refine ⟨29269657045483806798650549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78052418787956818129734797 29269657045483806798650549)
                    ·
                      refine ⟨2744030348014106887373489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29269657045483806798650549 2744030348014106887373489)
                      ·
                        rfl

theorem cell23_5343980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_5343980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343980 prefixEnd_5343980 := by exact prefixLift 5343980
  have htrace : WordTrace (prefixWord ++ tailWord_5343980) baseStart_5343980 baseEnd_5343980 := by
    simpa [prefixWord, tailWord_5343980, baseEnd_5343980] using wordTrace_append hprefix tailTrace_5343980
  have hstable : (prefixWord ++ tailWord_5343980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343980).length < 2 ^ (prefixWord ++ tailWord_5343980).sum := by decide
  have hdescent : baseEnd_5343980 < baseStart_5343980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5343981 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5343981 : Nat := 118140960795 + 5343981 * 2 ^ 59
def prefixEnd_5343981 : Nat := 4983230072969 + 3 ^ 40 * 5343981 * 2
def baseEnd_5343981 : Nat := 2744030861494761383460985

theorem tailTrace_5343981 : CollatzResearch.WordTrace tailWord_5343981 prefixEnd_5343981 2744030861494761383460985 := by
  unfold tailWord_5343981
  simp only [CollatzResearch.WordTrace]
  refine ⟨194910999652676991137799797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129940666435117994091866531 194910999652676991137799797)
  ·
    refine ⟨18272906217438467919168731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194910999652676991137799797 18272906217438467919168731)
    ·
      refine ⟨27409359326157701878753097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18272906217438467919168731 27409359326157701878753097)
      ·
        refine ⟨20557019494618276409064823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27409359326157701878753097 20557019494618276409064823)
        ·
          refine ⟨30835529241927414613597235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20557019494618276409064823 30835529241927414613597235)
          ·
            refine ⟨46253293862891121920395853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30835529241927414613597235 46253293862891121920395853)
            ·
              refine ⟨17344985198584170720148445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46253293862891121920395853 17344985198584170720148445)
              ·
                refine ⟨6504369449469064020055667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17344985198584170720148445 6504369449469064020055667)
                ·
                  refine ⟨9756554174203596030083501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6504369449469064020055667 9756554174203596030083501)
                  ·
                    refine ⟨3658707815326348511281313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9756554174203596030083501 3658707815326348511281313)
                    ·
                      refine ⟨2744030861494761383460985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658707815326348511281313 2744030861494761383460985)
                      ·
                        rfl

theorem cell23_5343981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5343981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5343981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5343981 prefixEnd_5343981 := by exact prefixLift 5343981
  have htrace : WordTrace (prefixWord ++ tailWord_5343981) baseStart_5343981 baseEnd_5343981 := by
    simpa [prefixWord, tailWord_5343981, baseEnd_5343981] using wordTrace_append hprefix tailTrace_5343981
  have hstable : (prefixWord ++ tailWord_5343981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5343981).length < 2 ^ (prefixWord ++ tailWord_5343981).sum := by decide
  have hdescent : baseEnd_5343981 < baseStart_5343981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5343981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344051 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 5]
def baseStart_5344051 : Nat := 118140960795 + 5344051 * 2 ^ 59
def prefixEnd_5344051 : Nat := 4983230072969 + 3 ^ 40 * 5344051 * 2
def baseEnd_5344051 : Nat := 304896311682286234398407

theorem tailTrace_5344051 : CollatzResearch.WordTrace tailWord_5344051 prefixEnd_5344051 304896311682286234398407 := by
  unfold tailWord_5344051
  simp only [CollatzResearch.WordTrace]
  refine ⟨194913552762423393092848007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129942368508282262061898671 194913552762423393092848007)
  ·
    refine ⟨292370329143635089639272011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194913552762423393092848007 292370329143635089639272011)
    ·
      refine ⟨438555493715452634458908017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292370329143635089639272011 438555493715452634458908017)
      ·
        refine ⟨328916620286589475844181013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438555493715452634458908017 328916620286589475844181013)
        ·
          refine ⟨15417966575933881680195985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 328916620286589475844181013 15417966575933881680195985)
          ·
            refine ⟨11563474931950411260146989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15417966575933881680195985 11563474931950411260146989)
            ·
              refine ⟨4336303099481404222555121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11563474931950411260146989 4336303099481404222555121)
              ·
                refine ⟨3252227324611053166916341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4336303099481404222555121 3252227324611053166916341)
                ·
                  refine ⟨304896311682286234398407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3252227324611053166916341 304896311682286234398407)
                  ·
                    rfl

theorem cell23_5344051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 5].length) (baseStart_5344051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344051 prefixEnd_5344051 := by exact prefixLift 5344051
  have htrace : WordTrace (prefixWord ++ tailWord_5344051) baseStart_5344051 baseEnd_5344051 := by
    simpa [prefixWord, tailWord_5344051, baseEnd_5344051] using wordTrace_append hprefix tailTrace_5344051
  have hstable : (prefixWord ++ tailWord_5344051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344051).length < 2 ^ (prefixWord ++ tailWord_5344051).sum := by decide
  have hdescent : baseEnd_5344051 < baseStart_5344051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344062 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_5344062 : Nat := 118140960795 + 5344062 * 2 ^ 59
def prefixEnd_5344062 : Nat := 4983230072969 + 3 ^ 40 * 5344062 * 2
def baseEnd_5344062 : Nat := 2744072453427775566548113

theorem tailTrace_5344062 : CollatzResearch.WordTrace tailWord_5344062 prefixEnd_5344062 2744072453427775566548113 := by
  unfold tailWord_5344062
  simp only [CollatzResearch.WordTrace]
  refine ⟨24364244245672942746437305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129942635976922361314332293 24364244245672942746437305)
  ·
    refine ⟨18273183184254707059827979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24364244245672942746437305 18273183184254707059827979)
    ·
      refine ⟨27409774776382060589741969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18273183184254707059827979 27409774776382060589741969)
      ·
        refine ⟨20557331082286545442306477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27409774776382060589741969 20557331082286545442306477)
        ·
          refine ⟨7708999155857454540864929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20557331082286545442306477 7708999155857454540864929)
          ·
            refine ⟨5781749366893090905648697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7708999155857454540864929 5781749366893090905648697)
            ·
              refine ⟨4336312025169818179236523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5781749366893090905648697 4336312025169818179236523)
              ·
                refine ⟨6504468037754727268854785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4336312025169818179236523 6504468037754727268854785)
                ·
                  refine ⟨4878351028316045451641089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6504468037754727268854785 4878351028316045451641089)
                  ·
                    refine ⟨3658763271237034088730817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4878351028316045451641089 3658763271237034088730817)
                    ·
                      refine ⟨2744072453427775566548113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658763271237034088730817 2744072453427775566548113)
                      ·
                        rfl

theorem cell23_5344062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_5344062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344062 prefixEnd_5344062 := by exact prefixLift 5344062
  have htrace : WordTrace (prefixWord ++ tailWord_5344062) baseStart_5344062 baseEnd_5344062 := by
    simpa [prefixWord, tailWord_5344062, baseEnd_5344062] using wordTrace_append hprefix tailTrace_5344062
  have hstable : (prefixWord ++ tailWord_5344062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344062).length < 2 ^ (prefixWord ++ tailWord_5344062).sum := by decide
  have hdescent : baseEnd_5344062 < baseStart_5344062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344067 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 4]
def baseStart_5344067 : Nat := 118140960795 + 5344067 * 2 ^ 59
def prefixEnd_5344067 : Nat := 4983230072969 + 3 ^ 40 * 5344067 * 2
def baseEnd_5344067 : Nat := 2744075020831048046985589

theorem tailTrace_5344067 : CollatzResearch.WordTrace tailWord_5344067 prefixEnd_5344067 2744075020831048046985589 := by
  unfold tailWord_5344067
  simp only [CollatzResearch.WordTrace]
  refine ⟨194914136330365427825430455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129942757553576951883620303 194914136330365427825430455)
  ·
    refine ⟨292371204495548141738145683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194914136330365427825430455 292371204495548141738145683)
    ·
      refine ⟨438556806743322212607218525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292371204495548141738145683 438556806743322212607218525)
      ·
        refine ⟨164458802528745829727706947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438556806743322212607218525 164458802528745829727706947)
        ·
          refine ⟨246688203793118744591560421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164458802528745829727706947 246688203793118744591560421)
          ·
            refine ⟨46254038211209764610917579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246688203793118744591560421 46254038211209764610917579)
            ·
              refine ⟨69381057316814646916376369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46254038211209764610917579 69381057316814646916376369)
              ·
                refine ⟨52035792987610985187282277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69381057316814646916376369 52035792987610985187282277)
                ·
                  refine ⟨9756711185177059722615427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52035792987610985187282277 9756711185177059722615427)
                  ·
                    refine ⟨14635066777765589583923141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9756711185177059722615427 14635066777765589583923141)
                    ·
                      refine ⟨2744075020831048046985589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14635066777765589583923141 2744075020831048046985589)
                      ·
                        rfl

theorem cell23_5344067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_5344067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344067 prefixEnd_5344067 := by exact prefixLift 5344067
  have htrace : WordTrace (prefixWord ++ tailWord_5344067) baseStart_5344067 baseEnd_5344067 := by
    simpa [prefixWord, tailWord_5344067, baseEnd_5344067] using wordTrace_append hprefix tailTrace_5344067
  have hstable : (prefixWord ++ tailWord_5344067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344067).length < 2 ^ (prefixWord ++ tailWord_5344067).sum := by decide
  have hdescent : baseEnd_5344067 < baseStart_5344067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344107 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 6]
def baseStart_5344107 : Nat := 118140960795 + 5344107 * 2 ^ 59
def prefixEnd_5344107 : Nat := 4983230072969 + 3 ^ 40 * 5344107 * 2
def baseEnd_5344107 : Nat := 304899506673025321165045

theorem tailTrace_5344107 : CollatzResearch.WordTrace tailWord_5344107 prefixEnd_5344107 304899506673025321165045 := by
  unfold tailWord_5344107
  simp only [CollatzResearch.WordTrace]
  refine ⟨194915595250220514656886575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129943730166813676437924383 194915595250220514656886575)
  ·
    refine ⟨292373392875330771985329863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194915595250220514656886575 292373392875330771985329863)
    ·
      refine ⟨438560089312996157977994795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292373392875330771985329863 438560089312996157977994795)
      ·
        refine ⟨657840133969494236966992193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438560089312996157977994795 657840133969494236966992193)
        ·
          refine ⟨493380100477120677725244145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657840133969494236966992193 493380100477120677725244145)
          ·
            refine ⟨370035075357840508293933109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493380100477120677725244145 370035075357840508293933109)
            ·
              refine ⟨34690788314797547652556229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370035075357840508293933109 34690788314797547652556229)
              ·
                refine ⟨6504522809024540184854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34690788314797547652556229 6504522809024540184854293)
                ·
                  refine ⟨304899506673025321165045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6504522809024540184854293 304899506673025321165045)
                  ·
                    rfl

theorem cell23_5344107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 6].length) (baseStart_5344107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344107 prefixEnd_5344107 := by exact prefixLift 5344107
  have htrace : WordTrace (prefixWord ++ tailWord_5344107) baseStart_5344107 baseEnd_5344107 := by
    simpa [prefixWord, tailWord_5344107, baseEnd_5344107] using wordTrace_append hprefix tailTrace_5344107
  have hstable : (prefixWord ++ tailWord_5344107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344107).length < 2 ^ (prefixWord ++ tailWord_5344107).sum := by decide
  have hdescent : baseEnd_5344107 < baseStart_5344107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344118 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5344118 : Nat := 118140960795 + 5344118 * 2 ^ 59
def prefixEnd_5344118 : Nat := 4983230072969 + 3 ^ 40 * 5344118 * 2
def baseEnd_5344118 : Nat := 2744101208344427347447855

theorem tailTrace_5344118 : CollatzResearch.WordTrace tailWord_5344118 prefixEnd_5344118 2744101208344427347447855 := by
  unfold tailWord_5344118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182249778323791470971063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129943997635453775690358005 12182249778323791470971063)
  ·
    refine ⟨18273374667485687206456595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12182249778323791470971063 18273374667485687206456595)
    ·
      refine ⟨27410062001228530809684893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18273374667485687206456595 27410062001228530809684893)
      ·
        refine ⟨10278773250460699053631835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27410062001228530809684893 10278773250460699053631835)
        ·
          refine ⟨15418159875691048580447753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10278773250460699053631835 15418159875691048580447753)
          ·
            refine ⟨11563619906768286435335815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15418159875691048580447753 11563619906768286435335815)
            ·
              refine ⟨17345429860152429653003723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11563619906768286435335815 17345429860152429653003723)
              ·
                refine ⟨26018144790228644479505585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17345429860152429653003723 26018144790228644479505585)
                ·
                  refine ⟨19513608592671483359629189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26018144790228644479505585 19513608592671483359629189)
                  ·
                    refine ⟨3658801611125903129930473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19513608592671483359629189 3658801611125903129930473)
                    ·
                      refine ⟨2744101208344427347447855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658801611125903129930473 2744101208344427347447855)
                      ·
                        rfl

theorem cell23_5344118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5344118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344118 prefixEnd_5344118 := by exact prefixLift 5344118
  have htrace : WordTrace (prefixWord ++ tailWord_5344118) baseStart_5344118 baseEnd_5344118 := by
    simpa [prefixWord, tailWord_5344118, baseEnd_5344118] using wordTrace_append hprefix tailTrace_5344118
  have hstable : (prefixWord ++ tailWord_5344118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344118).length < 2 ^ (prefixWord ++ tailWord_5344118).sum := by decide
  have hdescent : baseEnd_5344118 < baseStart_5344118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344138 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5344138 : Nat := 118140960795 + 5344138 * 2 ^ 59
def prefixEnd_5344138 : Nat := 4983230072969 + 3 ^ 40 * 5344138 * 2
def baseEnd_5344138 : Nat := 2744111477957517269197763

theorem tailTrace_5344138 : CollatzResearch.WordTrace tailWord_5344138 prefixEnd_5344138 2744111477957517269197763 := by
  unfold tailWord_5344138
  simp only [CollatzResearch.WordTrace]
  refine ⟨48729181478277051737816267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129944483942072137967510045 48729181478277051737816267)
  ·
    refine ⟨73093772217415577606724401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48729181478277051737816267 73093772217415577606724401)
    ·
      refine ⟨54820329163061683205043301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73093772217415577606724401 54820329163061683205043301)
      ·
        refine ⟨10278811718074065600945619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54820329163061683205043301 10278811718074065600945619)
        ·
          refine ⟨15418217577111098401418429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10278811718074065600945619 15418217577111098401418429)
          ·
            refine ⟨5781831591416661900531911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15418217577111098401418429 5781831591416661900531911)
            ·
              refine ⟨8672747387124992850797867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781831591416661900531911 8672747387124992850797867)
              ·
                refine ⟨13009121080687489276196801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8672747387124992850797867 13009121080687489276196801)
                ·
                  refine ⟨9756840810515616957147601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13009121080687489276196801 9756840810515616957147601)
                  ·
                    refine ⟨7317630607886712717860701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9756840810515616957147601 7317630607886712717860701)
                    ·
                      refine ⟨2744111477957517269197763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7317630607886712717860701 2744111477957517269197763)
                      ·
                        rfl

theorem cell23_5344138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5344138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344138 prefixEnd_5344138 := by exact prefixLift 5344138
  have htrace : WordTrace (prefixWord ++ tailWord_5344138) baseStart_5344138 baseEnd_5344138 := by
    simpa [prefixWord, tailWord_5344138, baseEnd_5344138] using wordTrace_append hprefix tailTrace_5344138
  have hstable : (prefixWord ++ tailWord_5344138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344138).length < 2 ^ (prefixWord ++ tailWord_5344138).sum := by decide
  have hdescent : baseEnd_5344138 < baseStart_5344138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344184 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 1, 6]
def baseStart_5344184 : Nat := 118140960795 + 5344184 * 2 ^ 59
def prefixEnd_5344184 : Nat := 4983230072969 + 3 ^ 40 * 5344184 * 2
def baseEnd_5344184 : Nat := 914711699355874696407517

theorem tailTrace_5344184 : CollatzResearch.WordTrace tailWord_5344184 prefixEnd_5344184 914711699355874696407517 := by
  unfold tailWord_5344184
  simp only [CollatzResearch.WordTrace]
  refine ⟨97459201835470778403719803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129945602447294371204959737 97459201835470778403719803)
  ·
    refine ⟨146188802753206167605579705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97459201835470778403719803 146188802753206167605579705)
    ·
      refine ⟨109641602064904625704184779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146188802753206167605579705 109641602064904625704184779)
      ·
        refine ⟨164462403097356938556277169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109641602064904625704184779 164462403097356938556277169)
        ·
          refine ⟨123346802323017703917207877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164462403097356938556277169 123346802323017703917207877)
          ·
            refine ⟨23127525435565819484476477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123346802323017703917207877 23127525435565819484476477)
            ·
              refine ⟨8672822038337182306678679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23127525435565819484476477 8672822038337182306678679)
              ·
                refine ⟨13009233057505773460018019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8672822038337182306678679 13009233057505773460018019)
                ·
                  refine ⟨19513849586258660190027029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13009233057505773460018019 19513849586258660190027029)
                  ·
                    refine ⟨914711699355874696407517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19513849586258660190027029 914711699355874696407517)
                    ·
                      rfl

theorem cell23_5344184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_5344184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344184 prefixEnd_5344184 := by exact prefixLift 5344184
  have htrace : WordTrace (prefixWord ++ tailWord_5344184) baseStart_5344184 baseEnd_5344184 := by
    simpa [prefixWord, tailWord_5344184, baseEnd_5344184] using wordTrace_append hprefix tailTrace_5344184
  have hstable : (prefixWord ++ tailWord_5344184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344184).length < 2 ^ (prefixWord ++ tailWord_5344184).sum := by decide
  have hdescent : baseEnd_5344184 < baseStart_5344184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344191 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 5, 2, 2]
def baseStart_5344191 : Nat := 118140960795 + 5344191 * 2 ^ 59
def prefixEnd_5344191 : Nat := 4983230072969 + 3 ^ 40 * 5344191 * 2
def baseEnd_5344191 : Nat := 2744138692432205561835019

theorem tailTrace_5344191 : CollatzResearch.WordTrace tailWord_5344191 prefixEnd_5344191 2744138692432205561835019 := by
  unfold tailWord_5344191
  simp only [CollatzResearch.WordTrace]
  refine ⟨194918658981916197002944427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129945772654610798001962951 194918658981916197002944427)
  ·
    refine ⟨292377988472874295504416641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194918658981916197002944427 292377988472874295504416641)
    ·
      refine ⟨219283491354655721628312481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292377988472874295504416641 219283491354655721628312481)
      ·
        refine ⟨164462618515991791221234361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219283491354655721628312481 164462618515991791221234361)
        ·
          refine ⟨123346963886993843415925771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164462618515991791221234361 123346963886993843415925771)
          ·
            refine ⟨185020445830490765123888657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123346963886993843415925771 185020445830490765123888657)
            ·
              refine ⟨138765334372868073842916493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185020445830490765123888657 138765334372868073842916493)
              ·
                refine ⟨52037000389825527691093685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138765334372868073842916493 52037000389825527691093685)
                ·
                  refine ⟨4878468786546143221040033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52037000389825527691093685 4878468786546143221040033)
                  ·
                    refine ⟨3658851589909607415780025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4878468786546143221040033 3658851589909607415780025)
                    ·
                      refine ⟨2744138692432205561835019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658851589909607415780025 2744138692432205561835019)
                      ·
                        rfl

theorem cell23_5344191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_5344191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344191 prefixEnd_5344191 := by exact prefixLift 5344191
  have htrace : WordTrace (prefixWord ++ tailWord_5344191) baseStart_5344191 baseEnd_5344191 := by
    simpa [prefixWord, tailWord_5344191, baseEnd_5344191] using wordTrace_append hprefix tailTrace_5344191
  have hstable : (prefixWord ++ tailWord_5344191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344191).length < 2 ^ (prefixWord ++ tailWord_5344191).sum := by decide
  have hdescent : baseEnd_5344191 < baseStart_5344191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344204 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5344204 : Nat := 118140960795 + 5344204 * 2 ^ 59
def prefixEnd_5344204 : Nat := 4983230072969 + 3 ^ 40 * 5344204 * 2
def baseEnd_5344204 : Nat := 2744145367680714010972459

theorem tailTrace_5344204 : CollatzResearch.WordTrace tailWord_5344204 prefixEnd_5344204 2744145367680714010972459 := by
  unfold tailWord_5344204
  simp only [CollatzResearch.WordTrace]
  refine ⟨97459566565434550111583833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129946088753912733482111777 97459566565434550111583833)
  ·
    refine ⟨73094674924075912583687875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97459566565434550111583833 73094674924075912583687875)
    ·
      refine ⟨109642012386113868875531813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73094674924075912583687875 109642012386113868875531813)
      ·
        refine ⟨20557877322396350414162215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109642012386113868875531813 20557877322396350414162215)
        ·
          refine ⟨30836815983594525621243323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20557877322396350414162215 30836815983594525621243323)
          ·
            refine ⟨46255223975391788431864985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30836815983594525621243323 46255223975391788431864985)
            ·
              refine ⟨34691417981543841323898739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46255223975391788431864985 34691417981543841323898739)
              ·
                refine ⟨52037126972315761985848109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34691417981543841323898739 52037126972315761985848109)
                ·
                  refine ⟨19513922614618410744693041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52037126972315761985848109 19513922614618410744693041)
                  ·
                    refine ⟨14635441960963808058519781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19513922614618410744693041 14635441960963808058519781)
                    ·
                      refine ⟨2744145367680714010972459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14635441960963808058519781 2744145367680714010972459)
                      ·
                        rfl

theorem cell23_5344204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5344204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344204 prefixEnd_5344204 := by exact prefixLift 5344204
  have htrace : WordTrace (prefixWord ++ tailWord_5344204) baseStart_5344204 baseEnd_5344204 := by
    simpa [prefixWord, tailWord_5344204, baseEnd_5344204] using wordTrace_append hprefix tailTrace_5344204
  have hstable : (prefixWord ++ tailWord_5344204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344204).length < 2 ^ (prefixWord ++ tailWord_5344204).sum := by decide
  have hdescent : baseEnd_5344204 < baseStart_5344204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344242 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5344242 : Nat := 118140960795 + 5344242 * 2 ^ 59
def prefixEnd_5344242 : Nat := 4983230072969 + 3 ^ 40 * 5344242 * 2
def baseEnd_5344242 : Nat := 2744164879945584862297285

theorem tailTrace_5344242 : CollatzResearch.WordTrace tailWord_5344242 prefixEnd_5344242 2744164879945584862297285 := by
  unfold tailWord_5344242
  simp only [CollatzResearch.WordTrace]
  refine ⟨48730129776182858178262745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129947012736487621808700653 48730129776182858178262745)
  ·
    refine ⟨36547597332137143633697059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48730129776182858178262745 36547597332137143633697059)
    ·
      refine ⟨54821395998205715450545589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36547597332137143633697059 54821395998205715450545589)
      ·
        refine ⟨5139505874831785823488649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54821395998205715450545589 5139505874831785823488649)
        ·
          refine ⟨3854629406123839367616487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5139505874831785823488649 3854629406123839367616487)
          ·
            refine ⟨5781944109185759051424731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854629406123839367616487 5781944109185759051424731)
            ·
              refine ⟨8672916163778638577137097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781944109185759051424731 8672916163778638577137097)
              ·
                refine ⟨6504687122833978932852823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8672916163778638577137097 6504687122833978932852823)
                ·
                  refine ⟨9757030684250968399279235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6504687122833978932852823 9757030684250968399279235)
                  ·
                    refine ⟨14635546026376452598918853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9757030684250968399279235 14635546026376452598918853)
                    ·
                      refine ⟨2744164879945584862297285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14635546026376452598918853 2744164879945584862297285)
                      ·
                        rfl

theorem cell23_5344242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5344242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344242 prefixEnd_5344242 := by exact prefixLift 5344242
  have htrace : WordTrace (prefixWord ++ tailWord_5344242) baseStart_5344242 baseEnd_5344242 := by
    simpa [prefixWord, tailWord_5344242, baseEnd_5344242] using wordTrace_append hprefix tailTrace_5344242
  have hstable : (prefixWord ++ tailWord_5344242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344242).length < 2 ^ (prefixWord ++ tailWord_5344242).sum := by decide
  have hdescent : baseEnd_5344242 < baseStart_5344242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344245 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5344245 : Nat := 118140960795 + 5344245 * 2 ^ 59
def prefixEnd_5344245 : Nat := 4983230072969 + 3 ^ 40 * 5344245 * 2
def baseEnd_5344245 : Nat := 2744166420387548350559771

theorem tailTrace_5344245 : CollatzResearch.WordTrace tailWord_5344245 prefixEnd_5344245 2744166420387548350559771 := by
  unfold tailWord_5344245
  simp only [CollatzResearch.WordTrace]
  refine ⟨194920628523720564225410189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129947085682480376150273459 194920628523720564225410189)
  ·
    refine ⟨73095235696395211584528821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194920628523720564225410189 73095235696395211584528821)
    ·
      refine ⟨6852678346537051086049577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73095235696395211584528821 6852678346537051086049577)
      ·
        refine ⟨5139508759902788314537183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6852678346537051086049577 5139508759902788314537183)
        ·
          refine ⟨7709263139854182471805775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139508759902788314537183 7709263139854182471805775)
          ·
            refine ⟨11563894709781273707708663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7709263139854182471805775 11563894709781273707708663)
            ·
              refine ⟨17345842064671910561562995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11563894709781273707708663 17345842064671910561562995)
              ·
                refine ⟨26018763097007865842344493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17345842064671910561562995 26018763097007865842344493)
                ·
                  refine ⟨9757036161377949690879185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26018763097007865842344493 9757036161377949690879185)
                  ·
                    refine ⟨7317777121033462268159389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9757036161377949690879185 7317777121033462268159389)
                    ·
                      refine ⟨2744166420387548350559771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7317777121033462268159389 2744166420387548350559771)
                      ·
                        rfl

theorem cell23_5344245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5344245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344245 prefixEnd_5344245 := by exact prefixLift 5344245
  have htrace : WordTrace (prefixWord ++ tailWord_5344245) baseStart_5344245 baseEnd_5344245 := by
    simpa [prefixWord, tailWord_5344245, baseEnd_5344245] using wordTrace_append hprefix tailTrace_5344245
  have hstable : (prefixWord ++ tailWord_5344245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344245).length < 2 ^ (prefixWord ++ tailWord_5344245).sum := by decide
  have hdescent : baseEnd_5344245 < baseStart_5344245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344304 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 7]
def baseStart_5344304 : Nat := 118140960795 + 5344304 * 2 ^ 59
def prefixEnd_5344304 : Nat := 4983230072969 + 3 ^ 40 * 5344304 * 2
def baseEnd_5344304 : Nat := 304910746194018179969111

theorem tailTrace_5344304 : CollatzResearch.WordTrace tailWord_5344304 prefixEnd_5344304 304910746194018179969111 := by
  unfold tailWord_5344304
  simp only [CollatzResearch.WordTrace]
  refine ⟨97461390215253408650903983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129948520287004544867871977 97461390215253408650903983)
  ·
    refine ⟨146192085322880112976355975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97461390215253408650903983 146192085322880112976355975)
    ·
      refine ⟨219288127984320169464533963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146192085322880112976355975 219288127984320169464533963)
      ·
        refine ⟨328932191976480254196800945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219288127984320169464533963 328932191976480254196800945)
        ·
          refine ⟨246699143982360190647600709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328932191976480254196800945 246699143982360190647600709)
          ·
            refine ⟨46256089496692535746425133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246699143982360190647600709 46256089496692535746425133)
            ·
              refine ⟨17346033561259700904909425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46256089496692535746425133 17346033561259700904909425)
              ·
                refine ⟨13009525170944775678682069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17346033561259700904909425 13009525170944775678682069)
                ·
                  refine ⟨304910746194018179969111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13009525170944775678682069 304910746194018179969111)
                  ·
                    rfl

theorem cell23_5344304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_5344304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344304 prefixEnd_5344304 := by exact prefixLift 5344304
  have htrace : WordTrace (prefixWord ++ tailWord_5344304) baseStart_5344304 baseEnd_5344304 := by
    simpa [prefixWord, tailWord_5344304, baseEnd_5344304] using wordTrace_append hprefix tailTrace_5344304
  have hstable : (prefixWord ++ tailWord_5344304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344304).length < 2 ^ (prefixWord ++ tailWord_5344304).sum := by decide
  have hdescent : baseEnd_5344304 < baseStart_5344304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344338 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_5344338 : Nat := 118140960795 + 5344338 * 2 ^ 59
def prefixEnd_5344338 : Nat := 4983230072969 + 3 ^ 40 * 5344338 * 2
def baseEnd_5344338 : Nat := 304912686009824054077427

theorem tailTrace_5344338 : CollatzResearch.WordTrace tailWord_5344338 prefixEnd_5344338 304912686009824054077427 := by
  unfold tailWord_5344338
  simp only [CollatzResearch.WordTrace]
  refine ⟨48731005128095910277136417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129949347008255760739030445 48731005128095910277136417)
  ·
    refine ⟨36548253846071932707852313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48731005128095910277136417 36548253846071932707852313)
    ·
      refine ⟨27411190384553949530889235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36548253846071932707852313 27411190384553949530889235)
      ·
        refine ⟨41116785576830924296333853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27411190384553949530889235 41116785576830924296333853)
        ·
          refine ⟨15418794591311596611125195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41116785576830924296333853 15418794591311596611125195)
          ·
            refine ⟨23128191886967394916687793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15418794591311596611125195 23128191886967394916687793)
            ·
              refine ⟨17346143915225546187515845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23128191886967394916687793 17346143915225546187515845)
              ·
                refine ⟨3252401984104789910159221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17346143915225546187515845 3252401984104789910159221)
                ·
                  refine ⟨304912686009824054077427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3252401984104789910159221 304912686009824054077427)
                  ·
                    rfl

theorem cell23_5344338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_5344338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344338 prefixEnd_5344338 := by exact prefixLift 5344338
  have htrace : WordTrace (prefixWord ++ tailWord_5344338) baseStart_5344338 baseEnd_5344338 := by
    simpa [prefixWord, tailWord_5344338, baseEnd_5344338] using wordTrace_append hprefix tailTrace_5344338
  have hstable : (prefixWord ++ tailWord_5344338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344338).length < 2 ^ (prefixWord ++ tailWord_5344338).sum := by decide
  have hdescent : baseEnd_5344338 < baseStart_5344338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344344 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5344344 : Nat := 118140960795 + 5344344 * 2 ^ 59
def prefixEnd_5344344 : Nat := 4983230072969 + 3 ^ 40 * 5344344 * 2
def baseEnd_5344344 : Nat := 2744217254972343463221815

theorem tailTrace_5344344 : CollatzResearch.WordTrace tailWord_5344344 prefixEnd_5344344 2744217254972343463221815 := by
  unfold tailWord_5344344
  simp only [CollatzResearch.WordTrace]
  refine ⟨97462119675180952066632043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129949492900241269422176057 97462119675180952066632043)
  ·
    refine ⟨146193179512771428099948065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97462119675180952066632043 146193179512771428099948065)
    ·
      refine ⟨109644884634578571074961049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146193179512771428099948065 109644884634578571074961049)
      ·
        refine ⟨82233663475933928306220787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109644884634578571074961049 82233663475933928306220787)
        ·
          refine ⟨123350495213900892459331181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82233663475933928306220787 123350495213900892459331181)
          ·
            refine ⟨46256435705212834672249193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123350495213900892459331181 46256435705212834672249193)
            ·
              refine ⟨34692326778909626004186895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46256435705212834672249193 34692326778909626004186895)
              ·
                refine ⟨52038490168364439006280343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34692326778909626004186895 52038490168364439006280343)
                ·
                  refine ⟨78057735252546658509420515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52038490168364439006280343 78057735252546658509420515)
                  ·
                    refine ⟨117086602878819987764130773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78057735252546658509420515 117086602878819987764130773)
                    ·
                      refine ⟨2744217254972343463221815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117086602878819987764130773 2744217254972343463221815)
                      ·
                        rfl

theorem cell23_5344344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5344344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344344 prefixEnd_5344344 := by exact prefixLift 5344344
  have htrace : WordTrace (prefixWord ++ tailWord_5344344) baseStart_5344344 baseEnd_5344344 := by
    simpa [prefixWord, tailWord_5344344, baseEnd_5344344] using wordTrace_append hprefix tailTrace_5344344
  have hstable : (prefixWord ++ tailWord_5344344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344344).length < 2 ^ (prefixWord ++ tailWord_5344344).sum := by decide
  have hdescent : baseEnd_5344344 < baseStart_5344344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344349 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5344349 : Nat := 118140960795 + 5344349 * 2 ^ 59
def prefixEnd_5344349 : Nat := 4983230072969 + 3 ^ 40 * 5344349 * 2
def baseEnd_5344349 : Nat := 2744219822375615943659293

theorem tailTrace_5344349 : CollatzResearch.WordTrace tailWord_5344349 prefixEnd_5344349 2744219822375615943659293 := by
  unfold tailWord_5344349
  simp only [CollatzResearch.WordTrace]
  refine ⟨194924421715343789987196101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129949614476895859991464067 194924421715343789987196101)
  ·
    refine ⟨36548329071626960622599269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194924421715343789987196101 36548329071626960622599269)
    ·
      refine ⟨6852811700930055116737363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36548329071626960622599269 6852811700930055116737363)
      ·
        refine ⟨10279217551395082675106045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6852811700930055116737363 10279217551395082675106045)
        ·
          refine ⟨3854706581773156003164767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10279217551395082675106045 3854706581773156003164767)
          ·
            refine ⟨5782059872659734004747151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854706581773156003164767 5782059872659734004747151)
            ·
              refine ⟨8673089808989601007120727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5782059872659734004747151 8673089808989601007120727)
              ·
                refine ⟨13009634713484401510681091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8673089808989601007120727 13009634713484401510681091)
                ·
                  refine ⟨19514452070226602266021637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13009634713484401510681091 19514452070226602266021637)
                  ·
                    refine ⟨3658959763167487924879057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19514452070226602266021637 3658959763167487924879057)
                    ·
                      refine ⟨2744219822375615943659293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3658959763167487924879057 2744219822375615943659293)
                      ·
                        rfl

theorem cell23_5344349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5344349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344349 prefixEnd_5344349 := by exact prefixLift 5344349
  have htrace : WordTrace (prefixWord ++ tailWord_5344349) baseStart_5344349 baseEnd_5344349 := by
    simpa [prefixWord, tailWord_5344349, baseEnd_5344349] using wordTrace_append hprefix tailTrace_5344349
  have hstable : (prefixWord ++ tailWord_5344349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344349).length < 2 ^ (prefixWord ++ tailWord_5344349).sum := by decide
  have hdescent : baseEnd_5344349 < baseStart_5344349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344364 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_5344364 : Nat := 118140960795 + 5344364 * 2 ^ 59
def prefixEnd_5344364 : Nat := 4983230072969 + 3 ^ 40 * 5344364 * 2
def baseEnd_5344364 : Nat := 914742508195144461657241

theorem tailTrace_5344364 : CollatzResearch.WordTrace tailWord_5344364 prefixEnd_5344364 914742508195144461657241 := by
  unfold tailWord_5344364
  simp only [CollatzResearch.WordTrace]
  refine ⟨97462484405144723774496073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129949979206859631699328097 97462484405144723774496073)
  ·
    refine ⟨73096863303858542830872055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97462484405144723774496073 73096863303858542830872055)
    ·
      refine ⟨109645294955787814246308083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73096863303858542830872055 109645294955787814246308083)
      ·
        refine ⟨164467942433681721369462125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109645294955787814246308083 164467942433681721369462125)
        ·
          refine ⟨61675478412630645513548297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164467942433681721369462125 61675478412630645513548297)
          ·
            refine ⟨46256608809472984135161223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61675478412630645513548297 46256608809472984135161223)
            ·
              refine ⟨69384913214209476202741835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46256608809472984135161223 69384913214209476202741835)
              ·
                refine ⟨104077369821314214304112753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69384913214209476202741835 104077369821314214304112753)
                ·
                  refine ⟨78058027365985660728084565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104077369821314214304112753 78058027365985660728084565)
                  ·
                    refine ⟨914742508195144461657241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78058027365985660728084565 914742508195144461657241)
                    ·
                      rfl

theorem cell23_5344364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_5344364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344364 prefixEnd_5344364 := by exact prefixLift 5344364
  have htrace : WordTrace (prefixWord ++ tailWord_5344364) baseStart_5344364 baseEnd_5344364 := by
    simpa [prefixWord, tailWord_5344364, baseEnd_5344364] using wordTrace_append hprefix tailTrace_5344364
  have hstable : (prefixWord ++ tailWord_5344364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344364).length < 2 ^ (prefixWord ++ tailWord_5344364).sum := by decide
  have hdescent : baseEnd_5344364 < baseStart_5344364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344384 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_5344384 : Nat := 118140960795 + 5344384 * 2 ^ 59
def prefixEnd_5344384 : Nat := 4983230072969 + 3 ^ 40 * 5344384 * 2
def baseEnd_5344384 : Nat := 2744237794198523306721631

theorem tailTrace_5344384 : CollatzResearch.WordTrace tailWord_5344384 prefixEnd_5344384 2744237794198523306721631 := by
  unfold tailWord_5344384
  simp only [CollatzResearch.WordTrace]
  refine ⟨97462849135108495482360103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129950465513477993976480137 97462849135108495482360103)
  ·
    refine ⟨146194273702662743223540155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97462849135108495482360103 146194273702662743223540155)
    ·
      refine ⟨219291410553994114835310233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146194273702662743223540155 219291410553994114835310233)
      ·
        refine ⟨164468557915495586126482675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219291410553994114835310233 164468557915495586126482675)
        ·
          refine ⟨246702836873243379189724013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164468557915495586126482675 246702836873243379189724013)
          ·
            refine ⟨92513563827466267196146505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246702836873243379189724013 92513563827466267196146505)
            ·
              refine ⟨69385172870599700397109879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92513563827466267196146505 69385172870599700397109879)
              ·
                refine ⟨104077759305899550595664819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69385172870599700397109879 104077759305899550595664819)
                ·
                  refine ⟨156116638958849325893497229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104077759305899550595664819 156116638958849325893497229)
                  ·
                    refine ⟨58543739609568497210061461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156116638958849325893497229 58543739609568497210061461)
                    ·
                      refine ⟨2744237794198523306721631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58543739609568497210061461 2744237794198523306721631)
                      ·
                        rfl

theorem cell23_5344384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_5344384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344384 prefixEnd_5344384 := by exact prefixLift 5344384
  have htrace : WordTrace (prefixWord ++ tailWord_5344384) baseStart_5344384 baseEnd_5344384 := by
    simpa [prefixWord, tailWord_5344384, baseEnd_5344384] using wordTrace_append hprefix tailTrace_5344384
  have hstable : (prefixWord ++ tailWord_5344384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344384).length < 2 ^ (prefixWord ++ tailWord_5344384).sum := by decide
  have hdescent : baseEnd_5344384 < baseStart_5344384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344388 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_5344388 : Nat := 118140960795 + 5344388 * 2 ^ 59
def prefixEnd_5344388 : Nat := 4983230072969 + 3 ^ 40 * 5344388 * 2
def baseEnd_5344388 : Nat := 2744239848121141291071613

theorem tailTrace_5344388 : CollatzResearch.WordTrace tailWord_5344388 prefixEnd_5344388 2744239848121141291071613 := by
  unfold tailWord_5344388
  simp only [CollatzResearch.WordTrace]
  refine ⟨97462922081101249823932909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129950562774801666431910545 97462922081101249823932909)
  ·
    refine ⟨36548595780412968683974841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97462922081101249823932909 36548595780412968683974841)
    ·
      refine ⟨27411446835309726512981131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36548595780412968683974841 27411446835309726512981131)
      ·
        refine ⟨41117170252964589769471697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27411446835309726512981131 41117170252964589769471697)
        ·
          refine ⟨30837877689723442327103773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41117170252964589769471697 30837877689723442327103773)
          ·
            refine ⟨11564204133646290872663915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30837877689723442327103773 11564204133646290872663915)
            ·
              refine ⟨17346306200469436308995873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11564204133646290872663915 17346306200469436308995873)
              ·
                refine ⟨13009729650352077231746905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17346306200469436308995873 13009729650352077231746905)
                ·
                  refine ⟨9757297237764057923810179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13009729650352077231746905 9757297237764057923810179)
                  ·
                    refine ⟨14635945856646086885715269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9757297237764057923810179 14635945856646086885715269)
                    ·
                      refine ⟨2744239848121141291071613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14635945856646086885715269 2744239848121141291071613)
                      ·
                        rfl

theorem cell23_5344388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_5344388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344388 prefixEnd_5344388 := by exact prefixLift 5344388
  have htrace : WordTrace (prefixWord ++ tailWord_5344388) baseStart_5344388 baseEnd_5344388 := by
    simpa [prefixWord, tailWord_5344388, baseEnd_5344388] using wordTrace_append hprefix tailTrace_5344388
  have hstable : (prefixWord ++ tailWord_5344388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344388).length < 2 ^ (prefixWord ++ tailWord_5344388).sum := by decide
  have hdescent : baseEnd_5344388 < baseStart_5344388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344449 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5344449 : Nat := 118140960795 + 5344449 * 2 ^ 59
def prefixEnd_5344449 : Nat := 4983230072969 + 3 ^ 40 * 5344449 * 2
def baseEnd_5344449 : Nat := 914757056813688517469611

theorem tailTrace_5344449 : CollatzResearch.WordTrace tailWord_5344449 prefixEnd_5344449 914757056813688517469611 := by
  unfold tailWord_5344449
  simp only [CollatzResearch.WordTrace]
  refine ⟨194928069014981507065836401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129952046009987671377224267 194928069014981507065836401)
  ·
    refine ⟨146196051761236130299377301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194928069014981507065836401 146196051761236130299377301)
    ·
      refine ⟨6852939926307943607783311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146196051761236130299377301 6852939926307943607783311)
      ·
        refine ⟨10279409889461915411674967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6852939926307943607783311 10279409889461915411674967)
        ·
          refine ⟨15419114834192873117512451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10279409889461915411674967 15419114834192873117512451)
          ·
            refine ⟨23128672251289309676268677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15419114834192873117512451 23128672251289309676268677)
            ·
              refine ⟨4336626047116745564300377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23128672251289309676268677 4336626047116745564300377)
              ·
                refine ⟨3252469535337559173225283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4336626047116745564300377 3252469535337559173225283)
                ·
                  refine ⟨4878704303006338759837925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252469535337559173225283 4878704303006338759837925)
                  ·
                    refine ⟨914757056813688517469611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878704303006338759837925 914757056813688517469611)
                    ·
                      rfl

theorem cell23_5344449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5344449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344449 prefixEnd_5344449 := by exact prefixLift 5344449
  have htrace : WordTrace (prefixWord ++ tailWord_5344449) baseStart_5344449 baseEnd_5344449 := by
    simpa [prefixWord, tailWord_5344449, baseEnd_5344449] using wordTrace_append hprefix tailTrace_5344449
  have hstable : (prefixWord ++ tailWord_5344449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344449).length < 2 ^ (prefixWord ++ tailWord_5344449).sum := by decide
  have hdescent : baseEnd_5344449 < baseStart_5344449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344471 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 1, 6]
def baseStart_5344471 : Nat := 118140960795 + 5344471 * 2 ^ 59
def prefixEnd_5344471 : Nat := 4983230072969 + 3 ^ 40 * 5344471 * 2
def baseEnd_5344471 : Nat := 914760822338488155444577

theorem tailTrace_5344471 : CollatzResearch.WordTrace tailWord_5344471 prefixEnd_5344471 914760822338488155444577 := by
  unfold tailWord_5344471
  simp only [CollatzResearch.WordTrace]
  refine ⟨194928871420901804823137267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129952580947267869882091511 194928871420901804823137267)
  ·
    refine ⟨292393307131352707234705901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194928871420901804823137267 292393307131352707234705901)
    ·
      refine ⟨109647490174257265213014713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292393307131352707234705901 109647490174257265213014713)
      ·
        refine ⟨82235617630692948909761035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109647490174257265213014713 82235617630692948909761035)
        ·
          refine ⟨123353426446039423364641553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82235617630692948909761035 123353426446039423364641553)
          ·
            refine ⟨92515069834529567523481165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123353426446039423364641553 92515069834529567523481165)
            ·
              refine ⟨34693151187948587821305437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92515069834529567523481165 34693151187948587821305437)
              ·
                refine ⟨13009931695480720432989539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34693151187948587821305437 13009931695480720432989539)
                ·
                  refine ⟨19514897543221080649484309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13009931695480720432989539 19514897543221080649484309)
                  ·
                    refine ⟨914760822338488155444577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19514897543221080649484309 914760822338488155444577)
                    ·
                      rfl

theorem cell23_5344471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_5344471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344471 prefixEnd_5344471 := by exact prefixLift 5344471
  have htrace : WordTrace (prefixWord ++ tailWord_5344471) baseStart_5344471 baseEnd_5344471 := by
    simpa [prefixWord, tailWord_5344471, baseEnd_5344471] using wordTrace_append hprefix tailTrace_5344471
  have hstable : (prefixWord ++ tailWord_5344471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344471).length < 2 ^ (prefixWord ++ tailWord_5344471).sum := by decide
  have hdescent : baseEnd_5344471 < baseStart_5344471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344488 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 4, 4]
def baseStart_5344488 : Nat := 118140960795 + 5344488 * 2 ^ 59
def prefixEnd_5344488 : Nat := 4983230072969 + 3 ^ 40 * 5344488 * 2
def baseEnd_5344488 : Nat := 914763732062196966607051

theorem tailTrace_5344488 : CollatzResearch.WordTrace tailWord_5344488 prefixEnd_5344488 914763732062196966607051 := by
  unfold tailWord_5344488
  simp only [CollatzResearch.WordTrace]
  refine ⟨97464745730920108363253059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129952994307893477817670745 97464745730920108363253059)
  ·
    refine ⟨146197118596380162544879589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97464745730920108363253059 146197118596380162544879589)
    ·
      refine ⟨27411959736821280477164923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146197118596380162544879589 27411959736821280477164923)
      ·
        refine ⟨41117939605231920715747385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27411959736821280477164923 41117939605231920715747385)
        ·
          refine ⟨30838454703923940536810539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41117939605231920715747385 30838454703923940536810539)
          ·
            refine ⟨46257682055885910805215809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30838454703923940536810539 46257682055885910805215809)
            ·
              refine ⟨34693261541914433103911857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46257682055885910805215809 34693261541914433103911857)
              ·
                refine ⟨26019946156435824827933893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34693261541914433103911857 26019946156435824827933893)
                ·
                  refine ⟨4878739904331717155237605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26019946156435824827933893 4878739904331717155237605)
                  ·
                    refine ⟨914763732062196966607051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4878739904331717155237605 914763732062196966607051)
                    ·
                      rfl

theorem cell23_5344488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_5344488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344488 prefixEnd_5344488 := by exact prefixLift 5344488
  have htrace : WordTrace (prefixWord ++ tailWord_5344488) baseStart_5344488 baseEnd_5344488 := by
    simpa [prefixWord, tailWord_5344488, baseEnd_5344488] using wordTrace_append hprefix tailTrace_5344488
  have hstable : (prefixWord ++ tailWord_5344488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344488).length < 2 ^ (prefixWord ++ tailWord_5344488).sum := by decide
  have hdescent : baseEnd_5344488 < baseStart_5344488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344495 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 4]
def baseStart_5344495 : Nat := 118140960795 + 5344495 * 2 ^ 59
def prefixEnd_5344495 : Nat := 4983230072969 + 3 ^ 40 * 5344495 * 2
def baseEnd_5344495 : Nat := 2744294790551172372433621

theorem tailTrace_5344495 : CollatzResearch.WordTrace tailWord_5344495 prefixEnd_5344495 2744294790551172372433621 := by
  unfold tailWord_5344495
  simp only [CollatzResearch.WordTrace]
  refine ⟨194929746772814856922010939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129953164515209904614673959 194929746772814856922010939)
  ·
    refine ⟨292394620159222285383016409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194929746772814856922010939 292394620159222285383016409)
    ·
      refine ⟨219295965119416714037262307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292394620159222285383016409 219295965119416714037262307)
      ·
        refine ⟨328943947679125071055893461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219295965119416714037262307 328943947679125071055893461)
        ·
          refine ⟨7709623773729493852872503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 328943947679125071055893461 7709623773729493852872503)
          ·
            refine ⟨11564435660594240779308755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7709623773729493852872503 11564435660594240779308755)
            ·
              refine ⟨17346653490891361168963133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11564435660594240779308755 17346653490891361168963133)
              ·
                refine ⟨6504995059084260438361175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17346653490891361168963133 6504995059084260438361175)
                ·
                  refine ⟨9757492588626390657541763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6504995059084260438361175 9757492588626390657541763)
                  ·
                    refine ⟨14636238882939585986312645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9757492588626390657541763 14636238882939585986312645)
                    ·
                      refine ⟨2744294790551172372433621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14636238882939585986312645 2744294790551172372433621)
                      ·
                        rfl

theorem cell23_5344495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_5344495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344495 prefixEnd_5344495 := by exact prefixLift 5344495
  have htrace : WordTrace (prefixWord ++ tailWord_5344495) baseStart_5344495 baseEnd_5344495 := by
    simpa [prefixWord, tailWord_5344495, baseEnd_5344495] using wordTrace_append hprefix tailTrace_5344495
  have hstable : (prefixWord ++ tailWord_5344495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344495).length < 2 ^ (prefixWord ++ tailWord_5344495).sum := by decide
  have hdescent : baseEnd_5344495 < baseStart_5344495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344581 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_5344581 : Nat := 118140960795 + 5344581 * 2 ^ 59
def prefixEnd_5344581 : Nat := 4983230072969 + 3 ^ 40 * 5344581 * 2
def baseEnd_5344581 : Nat := 2744338949887459035958225

theorem tailTrace_5344581 : CollatzResearch.WordTrace tailWord_5344581 prefixEnd_5344581 2744338949887459035958225 := by
  unfold tailWord_5344581
  simp only [CollatzResearch.WordTrace]
  refine ⟨194932883450503293609641597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129955255633668862406427731 194932883450503293609641597)
  ·
    refine ⟨73099831293938735103615599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194932883450503293609641597 73099831293938735103615599)
    ·
      refine ⟨109649746940908102655423399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73099831293938735103615599 109649746940908102655423399)
      ·
        refine ⟨164474620411362153983135099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109649746940908102655423399 164474620411362153983135099)
        ·
          refine ⟨246711930617043230974702649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164474620411362153983135099 246711930617043230974702649)
          ·
            refine ⟨185033947962782423231026987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246711930617043230974702649 185033947962782423231026987)
            ·
              refine ⟨277550921944173634846540481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185033947962782423231026987 277550921944173634846540481)
              ·
                refine ⟨208163191458130226134905361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277550921944173634846540481 208163191458130226134905361)
                ·
                  refine ⟨156122393593597669601179021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208163191458130226134905361 156122393593597669601179021)
                  ·
                    refine ⟨58545897597599126100442133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156122393593597669601179021 58545897597599126100442133)
                    ·
                      refine ⟨2744338949887459035958225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58545897597599126100442133 2744338949887459035958225)
                      ·
                        rfl

theorem cell23_5344581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_5344581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344581 prefixEnd_5344581 := by exact prefixLift 5344581
  have htrace : WordTrace (prefixWord ++ tailWord_5344581) baseStart_5344581 baseEnd_5344581 := by
    simpa [prefixWord, tailWord_5344581, baseEnd_5344581] using wordTrace_append hprefix tailTrace_5344581
  have hstable : (prefixWord ++ tailWord_5344581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344581).length < 2 ^ (prefixWord ++ tailWord_5344581).sum := by decide
  have hdescent : baseEnd_5344581 < baseStart_5344581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344588 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5344588 : Nat := 118140960795 + 5344588 * 2 ^ 59
def prefixEnd_5344588 : Nat := 4983230072969 + 3 ^ 40 * 5344588 * 2
def baseEnd_5344588 : Nat := 2744342544252040508570693

theorem tailTrace_5344588 : CollatzResearch.WordTrace tailWord_5344588 prefixEnd_5344588 2744342544252040508570693 := by
  unfold tailWord_5344588
  simp only [CollatzResearch.WordTrace]
  refine ⟨97466569380738966902573209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129955425840985289203430945 97466569380738966902573209)
  ·
    refine ⟨73099927035554225176929907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97466569380738966902573209 73099927035554225176929907)
    ·
      refine ⟨109649890553331337765394861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73099927035554225176929907 109649890553331337765394861)
      ·
        refine ⟨41118708957499251662023073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109649890553331337765394861 41118708957499251662023073)
        ·
          refine ⟨30839031718124438746517305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41118708957499251662023073 30839031718124438746517305)
          ·
            refine ⟨23129273788593329059887979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30839031718124438746517305 23129273788593329059887979)
            ·
              refine ⟨34693910682889993589831969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23129273788593329059887979 34693910682889993589831969)
              ·
                refine ⟨26020433012167495192373977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34693910682889993589831969 26020433012167495192373977)
                ·
                  refine ⟨19515324759125621394280483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26020433012167495192373977 19515324759125621394280483)
                  ·
                    refine ⟨29272987138688432091420725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19515324759125621394280483 29272987138688432091420725)
                    ·
                      refine ⟨2744342544252040508570693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29272987138688432091420725 2744342544252040508570693)
                      ·
                        rfl

theorem cell23_5344588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5344588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344588 prefixEnd_5344588 := by exact prefixLift 5344588
  have htrace : WordTrace (prefixWord ++ tailWord_5344588) baseStart_5344588 baseEnd_5344588 := by
    simpa [prefixWord, tailWord_5344588, baseEnd_5344588] using wordTrace_append hprefix tailTrace_5344588
  have hstable : (prefixWord ++ tailWord_5344588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344588).length < 2 ^ (prefixWord ++ tailWord_5344588).sum := by decide
  have hdescent : baseEnd_5344588 < baseStart_5344588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
