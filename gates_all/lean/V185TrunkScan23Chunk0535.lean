import V185TrunkScan23Chunk0534

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3163395 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5]
def baseStart_3163395 : Nat := 118140960795 + 3163395 * 2 ^ 59
def prefixEnd_3163395 : Nat := 4983230072969 + 3 ^ 40 * 3163395 * 2
def baseEnd_3163395 : Nat := 1624342135029755936214317

theorem tailTrace_3163395 : CollatzResearch.WordTrace tailWord_3163395 prefixEnd_3163395 1624342135029755936214317 := by
  unfold tailWord_3163395
  simp only [CollatzResearch.WordTrace]
  refine ⟨115378494374567654698427639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76918996249711769798951759 115378494374567654698427639)
  ·
    refine ⟨173067741561851482047641459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115378494374567654698427639 173067741561851482047641459)
    ·
      refine ⟨259601612342777223071462189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173067741561851482047641459 259601612342777223071462189)
      ·
        refine ⟨97350604628541458651798321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259601612342777223071462189 97350604628541458651798321)
        ·
          refine ⟨73012953471406093988848741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97350604628541458651798321 73012953471406093988848741)
          ·
            refine ⟨13689928775888642622909139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73012953471406093988848741 13689928775888642622909139)
            ·
              refine ⟨20534893163832963934363709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13689928775888642622909139 20534893163832963934363709)
              ·
                refine ⟨7700584936437361475386391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20534893163832963934363709 7700584936437361475386391)
                ·
                  refine ⟨11550877404656042213079587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7700584936437361475386391 11550877404656042213079587)
                  ·
                    refine ⟨17326316106984063319619381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11550877404656042213079587 17326316106984063319619381)
                    ·
                      refine ⟨1624342135029755936214317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17326316106984063319619381 1624342135029755936214317)
                      ·
                        rfl

theorem cell23_3163395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_3163395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163395 prefixEnd_3163395 := by exact prefixLift 3163395
  have htrace : WordTrace (prefixWord ++ tailWord_3163395) baseStart_3163395 baseEnd_3163395 := by
    simpa [prefixWord, tailWord_3163395, baseEnd_3163395] using wordTrace_append hprefix tailTrace_3163395
  have hstable : (prefixWord ++ tailWord_3163395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163395).length < 2 ^ (prefixWord ++ tailWord_3163395).sum := by decide
  have hdescent : baseEnd_3163395 < baseStart_3163395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163402 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3163402 : Nat := 118140960795 + 3163402 * 2 ^ 59
def prefixEnd_3163402 : Nat := 4983230072969 + 3 ^ 40 * 3163402 * 2
def baseEnd_3163402 : Nat := 541448576464779136275595

theorem tailTrace_3163402 : CollatzResearch.WordTrace tailWord_3163402 prefixEnd_3163402 541448576464779136275595 := by
  unfold tailWord_3163402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28844687421385573723483115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76919166457028196595954973 28844687421385573723483115)
  ·
    refine ⟨43267031132078360585224673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28844687421385573723483115 43267031132078360585224673)
    ·
      refine ⟨32450273349058770438918505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43267031132078360585224673 32450273349058770438918505)
      ·
        refine ⟨24337705011794077829188879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32450273349058770438918505 24337705011794077829188879)
        ·
          refine ⟨36506557517691116743783319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24337705011794077829188879 36506557517691116743783319)
          ·
            refine ⟨54759836276536675115674979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36506557517691116743783319 54759836276536675115674979)
            ·
              refine ⟨82139754414805012673512469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54759836276536675115674979 82139754414805012673512469)
              ·
                refine ⟨3850300988193984969070897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82139754414805012673512469 3850300988193984969070897)
                ·
                  refine ⟨2887725741145488726803173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3850300988193984969070897 2887725741145488726803173)
                  ·
                    refine ⟨541448576464779136275595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887725741145488726803173 541448576464779136275595)
                    ·
                      rfl

theorem cell23_3163402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3163402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163402 prefixEnd_3163402 := by exact prefixLift 3163402
  have htrace : WordTrace (prefixWord ++ tailWord_3163402) baseStart_3163402 baseEnd_3163402 := by
    simpa [prefixWord, tailWord_3163402, baseEnd_3163402] using wordTrace_append hprefix tailTrace_3163402
  have hstable : (prefixWord ++ tailWord_3163402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163402).length < 2 ^ (prefixWord ++ tailWord_3163402).sum := by decide
  have hdescent : baseEnd_3163402 < baseStart_3163402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163415 : List Nat := [1, 1, 3, 4, 1, 1, 4, 8]
def baseStart_3163415 : Nat := 118140960795 + 3163415 * 2 ^ 59
def prefixEnd_3163415 : Nat := 4983230072969 + 3 ^ 40 * 3163415 * 2
def baseEnd_3163415 : Nat := 60161200171957253998675

theorem tailTrace_3163415 : CollatzResearch.WordTrace tailWord_3163415 prefixEnd_3163415 60161200171957253998675 := by
  unfold tailWord_3163415
  simp only [CollatzResearch.WordTrace]
  refine ⟨115379223834495198114155699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76919482556330132076103799 115379223834495198114155699)
  ·
    refine ⟨173068835751742797171233549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115379223834495198114155699 173068835751742797171233549)
    ·
      refine ⟨64900813406903548939212581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173068835751742797171233549 64900813406903548939212581)
      ·
        refine ⟨12168902513794415426102359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64900813406903548939212581 12168902513794415426102359)
        ·
          refine ⟨18253353770691623139153539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168902513794415426102359 18253353770691623139153539)
          ·
            refine ⟨27380030656037434708730309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18253353770691623139153539 27380030656037434708730309)
            ·
              refine ⟨5133755748007019007886933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27380030656037434708730309 5133755748007019007886933)
              ·
                refine ⟨60161200171957253998675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5133755748007019007886933 60161200171957253998675)
                ·
                  rfl

theorem cell23_3163415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 8].length) (baseStart_3163415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163415 prefixEnd_3163415 := by exact prefixLift 3163415
  have htrace : WordTrace (prefixWord ++ tailWord_3163415) baseStart_3163415 baseEnd_3163415 := by
    simpa [prefixWord, tailWord_3163415, baseEnd_3163415] using wordTrace_append hprefix tailTrace_3163415
  have hstable : (prefixWord ++ tailWord_3163415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163415).length < 2 ^ (prefixWord ++ tailWord_3163415).sum := by decide
  have hdescent : baseEnd_3163415 < baseStart_3163415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163426 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3163426 : Nat := 118140960795 + 3163426 * 2 ^ 59
def prefixEnd_3163426 : Nat := 4983230072969 + 3 ^ 40 * 3163426 * 2
def baseEnd_3163426 : Nat := 1624358052930045314926675

theorem tailTrace_3163426 : CollatzResearch.WordTrace tailWord_3163426 prefixEnd_3163426 1624358052930045314926675 := by
  unfold tailWord_3163426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28844906259363836748201533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76919750024970231328537421 28844906259363836748201533)
  ·
    refine ⟨10816839847261438780575575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28844906259363836748201533 10816839847261438780575575)
    ·
      refine ⟨16225259770892158170863363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10816839847261438780575575 16225259770892158170863363)
      ·
        refine ⟨24337889656338237256295045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16225259770892158170863363 24337889656338237256295045)
        ·
          refine ⟨4563354310563419485555321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24337889656338237256295045 4563354310563419485555321)
          ·
            refine ⟨3422515732922564614166491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4563354310563419485555321 3422515732922564614166491)
            ·
              refine ⟨5133773599383846921249737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422515732922564614166491 5133773599383846921249737)
              ·
                refine ⟨3850330199537885190937303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133773599383846921249737 3850330199537885190937303)
                ·
                  refine ⟨5775495299306827786405955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850330199537885190937303 5775495299306827786405955)
                  ·
                    refine ⟨8663242948960241679608933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5775495299306827786405955 8663242948960241679608933)
                    ·
                      refine ⟨1624358052930045314926675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8663242948960241679608933 1624358052930045314926675)
                      ·
                        rfl

theorem cell23_3163426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3163426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163426 prefixEnd_3163426 := by exact prefixLift 3163426
  have htrace : WordTrace (prefixWord ++ tailWord_3163426) baseStart_3163426 baseEnd_3163426 := by
    simpa [prefixWord, tailWord_3163426, baseEnd_3163426] using wordTrace_append hprefix tailTrace_3163426
  have hstable : (prefixWord ++ tailWord_3163426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163426).length < 2 ^ (prefixWord ++ tailWord_3163426).sum := by decide
  have hdescent : baseEnd_3163426 < baseStart_3163426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163429 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_3163429 : Nat := 118140960795 + 3163429 * 2 ^ 59
def prefixEnd_3163429 : Nat := 4983230072969 + 3 ^ 40 * 3163429 * 2
def baseEnd_3163429 : Nat := 1624359593372008803189161

theorem tailTrace_3163429 : CollatzResearch.WordTrace tailWord_3163429 prefixEnd_3163429 1624359593372008803189161 := by
  unfold tailWord_3163429
  simp only [CollatzResearch.WordTrace]
  refine ⟨115379734456444478505165341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76919822970962985670110227 115379734456444478505165341)
  ·
    refine ⟨43267400421166679439437003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115379734456444478505165341 43267400421166679439437003)
    ·
      refine ⟨64901100631750019159155505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43267400421166679439437003 64901100631750019159155505)
      ·
        refine ⟨48675825473812514369366629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64901100631750019159155505 48675825473812514369366629)
        ·
          refine ⟨9126717276339846444256243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48675825473812514369366629 9126717276339846444256243)
          ·
            refine ⟨13690075914509769666384365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126717276339846444256243 13690075914509769666384365)
            ·
              refine ⟨5133778467941163624894137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13690075914509769666384365 5133778467941163624894137)
              ·
                refine ⟨3850333850955872718670603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133778467941163624894137 3850333850955872718670603)
                ·
                  refine ⟨5775500776433809078005905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850333850955872718670603 5775500776433809078005905)
                  ·
                    refine ⟨4331625582325356808504429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5775500776433809078005905 4331625582325356808504429)
                    ·
                      refine ⟨1624359593372008803189161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331625582325356808504429 1624359593372008803189161)
                      ·
                        rfl

theorem cell23_3163429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_3163429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163429 prefixEnd_3163429 := by exact prefixLift 3163429
  have htrace : WordTrace (prefixWord ++ tailWord_3163429) baseStart_3163429 baseEnd_3163429 := by
    simpa [prefixWord, tailWord_3163429, baseEnd_3163429] using wordTrace_append hprefix tailTrace_3163429
  have hstable : (prefixWord ++ tailWord_3163429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163429).length < 2 ^ (prefixWord ++ tailWord_3163429).sum := by decide
  have hdescent : baseEnd_3163429 < baseStart_3163429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163442 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3163442 : Nat := 118140960795 + 3163442 * 2 ^ 59
def prefixEnd_3163442 : Nat := 4983230072969 + 3 ^ 40 * 3163442 * 2
def baseEnd_3163442 : Nat := 1624366268620517252326601

theorem tailTrace_3163442 : CollatzResearch.WordTrace tailWord_3163442 prefixEnd_3163442 1624366268620517252326601 := by
  unfold tailWord_3163442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28845052151349345431347145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76920139070264921150259053 28845052151349345431347145)
  ·
    refine ⟨21633789113512009073510359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28845052151349345431347145 21633789113512009073510359)
    ·
      refine ⟨32450683670268013610265539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21633789113512009073510359 32450683670268013610265539)
      ·
        refine ⟨48676025505402020415398309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32450683670268013610265539 48676025505402020415398309)
        ·
          refine ⟨9126754782262878827887183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48676025505402020415398309 9126754782262878827887183)
          ·
            refine ⟨13690132173394318241830775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126754782262878827887183 13690132173394318241830775)
            ·
              refine ⟨20535198260091477362746163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690132173394318241830775 20535198260091477362746163)
              ·
                refine ⟨30802797390137216044119245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20535198260091477362746163 30802797390137216044119245)
                ·
                  refine ⟨11551049021301456016544717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30802797390137216044119245 11551049021301456016544717)
                  ·
                    refine ⟨4331643382988046006204269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11551049021301456016544717 4331643382988046006204269)
                    ·
                      refine ⟨1624366268620517252326601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331643382988046006204269 1624366268620517252326601)
                      ·
                        rfl

theorem cell23_3163442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3163442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163442 prefixEnd_3163442 := by exact prefixLift 3163442
  have htrace : WordTrace (prefixWord ++ tailWord_3163442) baseStart_3163442 baseEnd_3163442 := by
    simpa [prefixWord, tailWord_3163442, baseEnd_3163442] using wordTrace_append hprefix tailTrace_3163442
  have hstable : (prefixWord ++ tailWord_3163442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163442).length < 2 ^ (prefixWord ++ tailWord_3163442).sum := by decide
  have hdescent : baseEnd_3163442 < baseStart_3163442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163460 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3163460 : Nat := 118140960795 + 3163460 * 2 ^ 59
def prefixEnd_3163460 : Nat := 4983230072969 + 3 ^ 40 * 3163460 * 2
def baseEnd_3163460 : Nat := 1624375511272298181901519

theorem tailTrace_3163460 : CollatzResearch.WordTrace tailWord_3163460 prefixEnd_3163460 1624375511272298181901519 := by
  unfold tailWord_3163460
  simp only [CollatzResearch.WordTrace]
  refine ⟨57690432559666085399771917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76920576746221447199695889 57690432559666085399771917)
  ·
    refine ⟨21633912209874782024914469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57690432559666085399771917 21633912209874782024914469)
    ·
      refine ⟨4056358539351521629671463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21633912209874782024914469 4056358539351521629671463)
      ·
        refine ⟨6084537809027282444507195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056358539351521629671463 6084537809027282444507195)
        ·
          refine ⟨9126806713540923666760793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6084537809027282444507195 9126806713540923666760793)
          ·
            refine ⟨6845105035155692750070595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9126806713540923666760793 6845105035155692750070595)
            ·
              refine ⟨10267657552733539125105893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845105035155692750070595 10267657552733539125105893)
              ·
                refine ⟨1925185791137538585957355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10267657552733539125105893 1925185791137538585957355)
                ·
                  refine ⟨2887778686706307878936033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925185791137538585957355 2887778686706307878936033)
                  ·
                    refine ⟨2165834015029730909202025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2887778686706307878936033 2165834015029730909202025)
                    ·
                      refine ⟨1624375511272298181901519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165834015029730909202025 1624375511272298181901519)
                      ·
                        rfl

theorem cell23_3163460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3163460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163460 prefixEnd_3163460 := by exact prefixLift 3163460
  have htrace : WordTrace (prefixWord ++ tailWord_3163460) baseStart_3163460 baseEnd_3163460 := by
    simpa [prefixWord, tailWord_3163460, baseEnd_3163460] using wordTrace_append hprefix tailTrace_3163460
  have hstable : (prefixWord ++ tailWord_3163460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163460).length < 2 ^ (prefixWord ++ tailWord_3163460).sum := by decide
  have hdescent : baseEnd_3163460 < baseStart_3163460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163465 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_3163465 : Nat := 118140960795 + 3163465 * 2 ^ 59
def prefixEnd_3163465 : Nat := 4983230072969 + 3 ^ 40 * 3163465 * 2
def baseEnd_3163465 : Nat := 1624378078675570662338995

theorem tailTrace_3163465 : CollatzResearch.WordTrace tailWord_3163465 prefixEnd_3163465 1624378078675570662338995 := by
  unfold tailWord_3163465
  simp only [CollatzResearch.WordTrace]
  refine ⟨115381047484314056653475849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76920698322876037768983899 115381047484314056653475849)
  ·
    refine ⟨86535785613235542490106887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115381047484314056653475849 86535785613235542490106887)
    ·
      refine ⟨129803678419853313735160331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86535785613235542490106887 129803678419853313735160331)
      ·
        refine ⟨194705517629779970602740497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129803678419853313735160331 194705517629779970602740497)
        ·
          refine ⟨146029138222334977952055373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194705517629779970602740497 146029138222334977952055373)
          ·
            refine ⟨54760926833375616732020765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146029138222334977952055373 54760926833375616732020765)
            ·
              refine ⟨20535347562515856274507787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54760926833375616732020765 20535347562515856274507787)
              ·
                refine ⟨30803021343773784411761681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20535347562515856274507787 30803021343773784411761681)
                ·
                  refine ⟨23102266007830338308821261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30803021343773784411761681 23102266007830338308821261)
                  ·
                    refine ⟨8663349752936376865807973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23102266007830338308821261 8663349752936376865807973)
                    ·
                      refine ⟨1624378078675570662338995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8663349752936376865807973 1624378078675570662338995)
                      ·
                        rfl

theorem cell23_3163465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_3163465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163465 prefixEnd_3163465 := by exact prefixLift 3163465
  have htrace : WordTrace (prefixWord ++ tailWord_3163465) baseStart_3163465 baseEnd_3163465 := by
    simpa [prefixWord, tailWord_3163465, baseEnd_3163465] using wordTrace_append hprefix tailTrace_3163465
  have hstable : (prefixWord ++ tailWord_3163465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163465).length < 2 ^ (prefixWord ++ tailWord_3163465).sum := by decide
  have hdescent : baseEnd_3163465 < baseStart_3163465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163475 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 2, 6]
def baseStart_3163475 : Nat := 118140960795 + 3163475 * 2 ^ 59
def prefixEnd_3163475 : Nat := 4983230072969 + 3 ^ 40 * 3163475 * 2
def baseEnd_3163475 : Nat := 541461071160705207737983

theorem tailTrace_3163475 : CollatzResearch.WordTrace tailWord_3163475 prefixEnd_3163475 541461071160705207737983 := by
  unfold tailWord_3163475
  simp only [CollatzResearch.WordTrace]
  refine ⟨115381412214277828361339879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76920941476185218907559919 115381412214277828361339879)
  ·
    refine ⟨173072118321416742542009819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115381412214277828361339879 173072118321416742542009819)
    ·
      refine ⟨259608177482125113813014729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173072118321416742542009819 259608177482125113813014729)
      ·
        refine ⟨194706133111593835359761047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259608177482125113813014729 194706133111593835359761047)
        ·
          refine ⟨292059199667390753039641571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194706133111593835359761047 292059199667390753039641571)
          ·
            refine ⟨438088799501086129559462357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292059199667390753039641571 438088799501086129559462357)
            ·
              refine ⟨10267706238306706161549899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 438088799501086129559462357 10267706238306706161549899)
              ·
                refine ⟨15401559357460059242324849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10267706238306706161549899 15401559357460059242324849)
                ·
                  refine ⟨11551169518095044431743637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15401559357460059242324849 11551169518095044431743637)
                  ·
                    refine ⟨541461071160705207737983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11551169518095044431743637 541461071160705207737983)
                    ·
                      rfl

theorem cell23_3163475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 6].length) (baseStart_3163475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163475 prefixEnd_3163475 := by exact prefixLift 3163475
  have htrace : WordTrace (prefixWord ++ tailWord_3163475) baseStart_3163475 baseEnd_3163475 := by
    simpa [prefixWord, tailWord_3163475, baseEnd_3163475] using wordTrace_append hprefix tailTrace_3163475
  have hstable : (prefixWord ++ tailWord_3163475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163475).length < 2 ^ (prefixWord ++ tailWord_3163475).sum := by decide
  have hdescent : baseEnd_3163475 < baseStart_3163475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163532 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3163532 : Nat := 118140960795 + 3163532 * 2 ^ 59
def prefixEnd_3163532 : Nat := 4983230072969 + 3 ^ 40 * 3163532 * 2
def baseEnd_3163532 : Nat := 1624412481879421900201187

theorem tailTrace_3163532 : CollatzResearch.WordTrace tailWord_3163532 prefixEnd_3163532 1624412481879421900201187 := by
  unfold tailWord_3163532
  simp only [CollatzResearch.WordTrace]
  refine ⟨57691745587535663548082425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76922327450047551397443233 57691745587535663548082425)
  ·
    refine ⟨43268809190651747661061819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57691745587535663548082425 43268809190651747661061819)
    ·
      refine ⟨64903213785977621491592729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43268809190651747661061819 64903213785977621491592729)
      ·
        refine ⟨48677410339483216118694547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64903213785977621491592729 48677410339483216118694547)
        ·
          refine ⟨73016115509224824178041821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48677410339483216118694547 73016115509224824178041821)
          ·
            refine ⟨27381043315959309066765683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73016115509224824178041821 27381043315959309066765683)
            ·
              refine ⟨41071564973938963600148525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27381043315959309066765683 41071564973938963600148525)
              ·
                refine ⟨15401836865227111350055697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41071564973938963600148525 15401836865227111350055697)
                ·
                  refine ⟨11551377648920333512541773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15401836865227111350055697 11551377648920333512541773)
                  ·
                    refine ⟨4331766618345125067203165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11551377648920333512541773 4331766618345125067203165)
                    ·
                      refine ⟨1624412481879421900201187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331766618345125067203165 1624412481879421900201187)
                      ·
                        rfl

theorem cell23_3163532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3163532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163532 prefixEnd_3163532 := by exact prefixLift 3163532
  have htrace : WordTrace (prefixWord ++ tailWord_3163532) baseStart_3163532 baseEnd_3163532 := by
    simpa [prefixWord, tailWord_3163532, baseEnd_3163532] using wordTrace_append hprefix tailTrace_3163532
  have hstable : (prefixWord ++ tailWord_3163532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163532).length < 2 ^ (prefixWord ++ tailWord_3163532).sum := by decide
  have hdescent : baseEnd_3163532 < baseStart_3163532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163552 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_3163552 : Nat := 118140960795 + 3163552 * 2 ^ 59
def prefixEnd_3163552 : Nat := 4983230072969 + 3 ^ 40 * 3163552 * 2
def baseEnd_3163552 : Nat := 541474250497503940650365

theorem tailTrace_3163552 : CollatzResearch.WordTrace tailWord_3163552 prefixEnd_3163552 541474250497503940650365 := by
  unfold tailWord_3163552
  simp only [CollatzResearch.WordTrace]
  refine ⟨57692110317499435255946455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76922813756665913674595273 57692110317499435255946455)
  ·
    refine ⟨86538165476249152883919683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57692110317499435255946455 86538165476249152883919683)
    ·
      refine ⟨129807248214373729325879525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86538165476249152883919683 129807248214373729325879525)
      ·
        refine ⟨24338859040195074248602411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129807248214373729325879525 24338859040195074248602411)
        ·
          refine ⟨36508288560292611372903617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24338859040195074248602411 36508288560292611372903617)
          ·
            refine ⟨27381216420219458529677713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36508288560292611372903617 27381216420219458529677713)
            ·
              refine ⟨20535912315164593897258285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27381216420219458529677713 20535912315164593897258285)
              ·
                refine ⟨7700967118186722711471857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20535912315164593897258285 7700967118186722711471857)
                ·
                  refine ⟨5775725338640042033603893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7700967118186722711471857 5775725338640042033603893)
                  ·
                    refine ⟨541474250497503940650365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5775725338640042033603893 541474250497503940650365)
                    ·
                      rfl

theorem cell23_3163552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_3163552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163552 prefixEnd_3163552 := by exact prefixLift 3163552
  have htrace : WordTrace (prefixWord ++ tailWord_3163552) baseStart_3163552 baseEnd_3163552 := by
    simpa [prefixWord, tailWord_3163552, baseEnd_3163552] using wordTrace_append hprefix tailTrace_3163552
  have hstable : (prefixWord ++ tailWord_3163552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163552).length < 2 ^ (prefixWord ++ tailWord_3163552).sum := by decide
  have hdescent : baseEnd_3163552 < baseStart_3163552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163606 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3163606 : Nat := 118140960795 + 3163606 * 2 ^ 59
def prefixEnd_3163606 : Nat := 4983230072969 + 3 ^ 40 * 3163606 * 2
def baseEnd_3163606 : Nat := 1624450479447854610675847

theorem tailTrace_3163606 : CollatzResearch.WordTrace tailWord_3163606 prefixEnd_3163606 1624450479447854610675847 := by
  unfold tailWord_3163606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211636886050202358397417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76924126784535491822905781 7211636886050202358397417)
  ·
    refine ⟨5408727664537651768798063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7211636886050202358397417 5408727664537651768798063)
    ·
      refine ⟨8113091496806477653197095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408727664537651768798063 8113091496806477653197095)
      ·
        refine ⟨12169637245209716479795643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8113091496806477653197095 12169637245209716479795643)
        ·
          refine ⟨18254455867814574719693465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12169637245209716479795643 18254455867814574719693465)
          ·
            refine ⟨13690841900860931039770099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18254455867814574719693465 13690841900860931039770099)
            ·
              refine ⟨20536262851291396559655149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690841900860931039770099 20536262851291396559655149)
              ·
                refine ⟨7701098569234273709870681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20536262851291396559655149 7701098569234273709870681)
                ·
                  refine ⟨5775823926925705282403011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7701098569234273709870681 5775823926925705282403011)
                  ·
                    refine ⟨8663735890388557923604517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5775823926925705282403011 8663735890388557923604517)
                    ·
                      refine ⟨1624450479447854610675847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8663735890388557923604517 1624450479447854610675847)
                      ·
                        rfl

theorem cell23_3163606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3163606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163606 prefixEnd_3163606 := by exact prefixLift 3163606
  have htrace : WordTrace (prefixWord ++ tailWord_3163606) baseStart_3163606 baseEnd_3163606 := by
    simpa [prefixWord, tailWord_3163606, baseEnd_3163606] using wordTrace_append hprefix tailTrace_3163606
  have hstable : (prefixWord ++ tailWord_3163606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163606).length < 2 ^ (prefixWord ++ tailWord_3163606).sum := by decide
  have hdescent : baseEnd_3163606 < baseStart_3163606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163609 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_3163609 : Nat := 118140960795 + 3163609 * 2 ^ 59
def prefixEnd_3163609 : Nat := 4983230072969 + 3 ^ 40 * 3163609 * 2
def baseEnd_3163609 : Nat := 1624452019889818098938333

theorem tailTrace_3163609 : CollatzResearch.WordTrace tailWord_3163609 prefixEnd_3163609 1624452019889818098938333 := by
  unfold tailWord_3163609
  simp only [CollatzResearch.WordTrace]
  refine ⟨115386299595792369246717881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76924199730528246164478587 115386299595792369246717881)
  ·
    refine ⟨86539724696844276935038411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115386299595792369246717881 86539724696844276935038411)
    ·
      refine ⟨129809587045266415402557617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86539724696844276935038411 129809587045266415402557617)
      ·
        refine ⟨97357190283949811551918213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129809587045266415402557617 97357190283949811551918213)
        ·
          refine ⟨18254473178240589665984665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97357190283949811551918213 18254473178240589665984665)
          ·
            refine ⟨13690854883680442249488499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18254473178240589665984665 13690854883680442249488499)
            ·
              refine ⟨20536282325520663374232749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690854883680442249488499 20536282325520663374232749)
              ·
                refine ⟨7701105872070248765337281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20536282325520663374232749 7701105872070248765337281)
                ·
                  refine ⟨5775829404052686574002961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7701105872070248765337281 5775829404052686574002961)
                  ·
                    refine ⟨4331872053039514930502221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5775829404052686574002961 4331872053039514930502221)
                    ·
                      refine ⟨1624452019889818098938333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331872053039514930502221 1624452019889818098938333)
                      ·
                        rfl

theorem cell23_3163609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_3163609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163609 prefixEnd_3163609 := by exact prefixLift 3163609
  have htrace : WordTrace (prefixWord ++ tailWord_3163609) baseStart_3163609 baseEnd_3163609 := by
    simpa [prefixWord, tailWord_3163609, baseEnd_3163609] using wordTrace_append hprefix tailTrace_3163609
  have hstable : (prefixWord ++ tailWord_3163609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163609).length < 2 ^ (prefixWord ++ tailWord_3163609).sum := by decide
  have hdescent : baseEnd_3163609 < baseStart_3163609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163633 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 1, 4]
def baseStart_3163633 : Nat := 118140960795 + 3163633 * 2 ^ 59
def prefixEnd_3163633 : Nat := 4983230072969 + 3 ^ 40 * 3163633 * 2
def baseEnd_3163633 : Nat := 541488114475175335012741

theorem tailTrace_3163633 : CollatzResearch.WordTrace tailWord_3163633 prefixEnd_3163633 541488114475175335012741 := by
  unfold tailWord_3163633
  simp only [CollatzResearch.WordTrace]
  refine ⟨115387174947705421345591553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76924783298470280897061035 115387174947705421345591553)
  ·
    refine ⟨86540381210779066009193665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115387174947705421345591553 86540381210779066009193665)
    ·
      refine ⟨64905285908084299506895249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86540381210779066009193665 64905285908084299506895249)
      ·
        refine ⟨48678964431063224630171437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64905285908084299506895249 48678964431063224630171437)
        ·
          refine ⟨18254611661648709236314289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48678964431063224630171437 18254611661648709236314289)
          ·
            refine ⟨13690958746236531927235717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18254611661648709236314289 13690958746236531927235717)
            ·
              refine ⟨2567054764919349736356697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13690958746236531927235717 2567054764919349736356697)
              ·
                refine ⟨1925291073689512302267523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567054764919349736356697 1925291073689512302267523)
                ·
                  refine ⟨2887936610534268453401285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925291073689512302267523 2887936610534268453401285)
                  ·
                    refine ⟨541488114475175335012741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887936610534268453401285 541488114475175335012741)
                    ·
                      rfl

theorem cell23_3163633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_3163633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163633 prefixEnd_3163633 := by exact prefixLift 3163633
  have htrace : WordTrace (prefixWord ++ tailWord_3163633) baseStart_3163633 baseEnd_3163633 := by
    simpa [prefixWord, tailWord_3163633, baseEnd_3163633] using wordTrace_append hprefix tailTrace_3163633
  have hstable : (prefixWord ++ tailWord_3163633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163633).length < 2 ^ (prefixWord ++ tailWord_3163633).sum := by decide
  have hdescent : baseEnd_3163633 < baseStart_3163633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163642 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_3163642 : Nat := 118140960795 + 3163642 * 2 ^ 59
def prefixEnd_3163642 : Nat := 4983230072969 + 3 ^ 40 * 3163642 * 2
def baseEnd_3163642 : Nat := 541489654917138823275227

theorem tailTrace_3163642 : CollatzResearch.WordTrace tailWord_3163642 prefixEnd_3163642 541489654917138823275227 := by
  unfold tailWord_3163642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28846875801168203970667295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76925002136448543921779453 28846875801168203970667295)
  ·
    refine ⟨43270313701752305956000943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28846875801168203970667295 43270313701752305956000943)
    ·
      refine ⟨64905470552628458934001415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43270313701752305956000943 64905470552628458934001415)
      ·
        refine ⟨97358205828942688401002123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64905470552628458934001415 97358205828942688401002123)
        ·
          refine ⟨146037308743414032601503185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97358205828942688401002123 146037308743414032601503185)
          ·
            refine ⟨109527981557560524451127389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146037308743414032601503185 109527981557560524451127389)
            ·
              refine ⟨41072993084085196669172771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109527981557560524451127389 41072993084085196669172771)
              ·
                refine ⟨61609489626127795003759157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41072993084085196669172771 61609489626127795003759157)
                ·
                  refine ⟨5775889652449480781602421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61609489626127795003759157 5775889652449480781602421)
                  ·
                    refine ⟨541489654917138823275227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5775889652449480781602421 541489654917138823275227)
                    ·
                      rfl

theorem cell23_3163642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_3163642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163642 prefixEnd_3163642 := by exact prefixLift 3163642
  have htrace : WordTrace (prefixWord ++ tailWord_3163642) baseStart_3163642 baseEnd_3163642 := by
    simpa [prefixWord, tailWord_3163642, baseEnd_3163642] using wordTrace_append hprefix tailTrace_3163642
  have hstable : (prefixWord ++ tailWord_3163642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163642).length < 2 ^ (prefixWord ++ tailWord_3163642).sum := by decide
  have hdescent : baseEnd_3163642 < baseStart_3163642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163692 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3163692 : Nat := 118140960795 + 3163692 * 2 ^ 59
def prefixEnd_3163692 : Nat := 4983230072969 + 3 ^ 40 * 3163692 * 2
def baseEnd_3163692 : Nat := 1624494638784141274200451

theorem tailTrace_3163692 : CollatzResearch.WordTrace tailWord_3163692 prefixEnd_3163692 1624494638784141274200451 := by
  unfold tailWord_3163692
  simp only [CollatzResearch.WordTrace]
  refine ⟨57694663427245837210994665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76926217902994449614659553 57694663427245837210994665)
  ·
    refine ⟨43270997570434377908245999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57694663427245837210994665 43270997570434377908245999)
    ·
      refine ⟨64906496355651566862368999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43270997570434377908245999 64906496355651566862368999)
      ·
        refine ⟨97359744533477350293553499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64906496355651566862368999 97359744533477350293553499)
        ·
          refine ⟨146039616800216025440330249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97359744533477350293553499 146039616800216025440330249)
          ·
            refine ⟨109529712600162019080247687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146039616800216025440330249 109529712600162019080247687)
            ·
              refine ⟨164294568900243028620371531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109529712600162019080247687 164294568900243028620371531)
              ·
                refine ⟨246441853350364542930557297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164294568900243028620371531 246441853350364542930557297)
                ·
                  refine ⟨184831390012773407197917973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246441853350364542930557297 184831390012773407197917973)
                  ·
                    refine ⟨8663971406848753462402405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184831390012773407197917973 8663971406848753462402405)
                    ·
                      refine ⟨1624494638784141274200451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8663971406848753462402405 1624494638784141274200451)
                      ·
                        rfl

theorem cell23_3163692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3163692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163692 prefixEnd_3163692 := by exact prefixLift 3163692
  have htrace : WordTrace (prefixWord ++ tailWord_3163692) baseStart_3163692 baseEnd_3163692 := by
    simpa [prefixWord, tailWord_3163692, baseEnd_3163692] using wordTrace_append hprefix tailTrace_3163692
  have hstable : (prefixWord ++ tailWord_3163692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163692).length < 2 ^ (prefixWord ++ tailWord_3163692).sum := by decide
  have hdescent : baseEnd_3163692 < baseStart_3163692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163699 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5]
def baseStart_3163699 : Nat := 118140960795 + 3163699 * 2 ^ 59
def prefixEnd_3163699 : Nat := 4983230072969 + 3 ^ 40 * 3163699 * 2
def baseEnd_3163699 : Nat := 1624498233148722746812919

theorem tailTrace_3163699 : CollatzResearch.WordTrace tailWord_3163699 prefixEnd_3163699 1624498233148722746812919 := by
  unfold tailWord_3163699
  simp only [CollatzResearch.WordTrace]
  refine ⟨115389582165466314617494151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76926388110310876411662767 115389582165466314617494151)
  ·
    refine ⟨173084373248199471926241227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115389582165466314617494151 173084373248199471926241227)
    ·
      refine ⟨259626559872299207889361841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173084373248199471926241227 259626559872299207889361841)
      ·
        refine ⟨194719919904224405917021381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259626559872299207889361841 194719919904224405917021381)
        ·
          refine ⟨36509984982042076109441509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194719919904224405917021381 36509984982042076109441509)
          ·
            refine ⟨6845622184132889270520283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36509984982042076109441509 6845622184132889270520283)
            ·
              refine ⟨10268433276199333905780425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845622184132889270520283 10268433276199333905780425)
              ·
                refine ⟨7701324957149500429335319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10268433276199333905780425 7701324957149500429335319)
                ·
                  refine ⟨11551987435724250644002979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7701324957149500429335319 11551987435724250644002979)
                  ·
                    refine ⟨17327981153586375966004469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11551987435724250644002979 17327981153586375966004469)
                    ·
                      refine ⟨1624498233148722746812919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17327981153586375966004469 1624498233148722746812919)
                      ·
                        rfl

theorem cell23_3163699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_3163699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163699 prefixEnd_3163699 := by exact prefixLift 3163699
  have htrace : WordTrace (prefixWord ++ tailWord_3163699) baseStart_3163699 baseEnd_3163699 := by
    simpa [prefixWord, tailWord_3163699, baseEnd_3163699] using wordTrace_append hprefix tailTrace_3163699
  have hstable : (prefixWord ++ tailWord_3163699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163699).length < 2 ^ (prefixWord ++ tailWord_3163699).sum := by decide
  have hdescent : baseEnd_3163699 < baseStart_3163699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163713 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3163713 : Nat := 118140960795 + 3163713 * 2 ^ 59
def prefixEnd_3163713 : Nat := 4983230072969 + 3 ^ 40 * 3163713 * 2
def baseEnd_3163713 : Nat := 1624505421877885692037855

theorem tailTrace_3163713 : CollatzResearch.WordTrace tailWord_3163713 prefixEnd_3163713 1624505421877885692037855 := by
  unfold tailWord_3163713
  simp only [CollatzResearch.WordTrace]
  refine ⟨115390092787415595008503793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76926728524943730005669195 115390092787415595008503793)
  ·
    refine ⟨86542569590561696256377845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115390092787415595008503793 86542569590561696256377845)
    ·
      refine ⟨8113365899115159024035423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86542569590561696256377845 8113365899115159024035423)
      ·
        refine ⟨12170048848672738536053135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8113365899115159024035423 12170048848672738536053135)
        ·
          refine ⟨18255073273009107804079703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12170048848672738536053135 18255073273009107804079703)
          ·
            refine ⟨27382609909513661706119555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18255073273009107804079703 27382609909513661706119555)
            ·
              refine ⟨41073914864270492559179333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27382609909513661706119555 41073914864270492559179333)
              ·
                refine ⟨7701359037050717354846125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41073914864270492559179333 7701359037050717354846125)
                ·
                  refine ⟨2888009638894019008067297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7701359037050717354846125 2888009638894019008067297)
                  ·
                    refine ⟨2166007229170514256050473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2888009638894019008067297 2166007229170514256050473)
                    ·
                      refine ⟨1624505421877885692037855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166007229170514256050473 1624505421877885692037855)
                      ·
                        rfl

theorem cell23_3163713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3163713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163713 prefixEnd_3163713 := by exact prefixLift 3163713
  have htrace : WordTrace (prefixWord ++ tailWord_3163713) baseStart_3163713 baseEnd_3163713 := by
    simpa [prefixWord, tailWord_3163713, baseEnd_3163713] using wordTrace_append hprefix tailTrace_3163713
  have hstable : (prefixWord ++ tailWord_3163713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163713).length < 2 ^ (prefixWord ++ tailWord_3163713).sum := by decide
  have hdescent : baseEnd_3163713 < baseStart_3163713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163719 : List Nat := [1, 1, 4, 1, 5, 1, 1, 9]
def baseStart_3163719 : Nat := 118140960795 + 3163719 * 2 ^ 59
def prefixEnd_3163719 : Nat := 4983230072969 + 3 ^ 40 * 3163719 * 2
def baseEnd_3163719 : Nat := 60166981583770839576401

theorem tailTrace_3163719 : CollatzResearch.WordTrace tailWord_3163719 prefixEnd_3163719 60166981583770839576401 := by
  unfold tailWord_3163719
  simp only [CollatzResearch.WordTrace]
  refine ⟨115390311625393858033222211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76926874416929238688814807 115390311625393858033222211)
  ·
    refine ⟨173085467438090787049833317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115390311625393858033222211 173085467438090787049833317)
    ·
      refine ⟨32453525144642022571843747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173085467438090787049833317 32453525144642022571843747)
      ·
        refine ⟨48680287716963033857765621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32453525144642022571843747 48680287716963033857765621)
        ·
          refine ⟨4563776973465284424165527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48680287716963033857765621 4563776973465284424165527)
          ·
            refine ⟨6845665460197926636248291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563776973465284424165527 6845665460197926636248291)
            ·
              refine ⟨10268498190296889954372437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845665460197926636248291 10268498190296889954372437)
              ·
                refine ⟨60166981583770839576401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10268498190296889954372437 60166981583770839576401)
                ·
                  rfl

theorem cell23_3163719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 9].length) (baseStart_3163719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163719 prefixEnd_3163719 := by exact prefixLift 3163719
  have htrace : WordTrace (prefixWord ++ tailWord_3163719) baseStart_3163719 baseEnd_3163719 := by
    simpa [prefixWord, tailWord_3163719, baseEnd_3163719] using wordTrace_append hprefix tailTrace_3163719
  have hstable : (prefixWord ++ tailWord_3163719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163719).length < 2 ^ (prefixWord ++ tailWord_3163719).sum := by decide
  have hdescent : baseEnd_3163719 < baseStart_3163719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163729 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_3163729 : Nat := 118140960795 + 3163729 * 2 ^ 59
def prefixEnd_3163729 : Nat := 4983230072969 + 3 ^ 40 * 3163729 * 2
def baseEnd_3163729 : Nat := 1624513637568357629437781

theorem tailTrace_3163729 : CollatzResearch.WordTrace tailWord_3163729 prefixEnd_3163729 1624513637568357629437781 := by
  unfold tailWord_3163729
  simp only [CollatzResearch.WordTrace]
  refine ⟨115390676355357629741086241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76927117570238419827390827 115390676355357629741086241)
  ·
    refine ⟨86543007266518222305814681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115390676355357629741086241 86543007266518222305814681)
    ·
      refine ⟨64907255449888666729361011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86543007266518222305814681 64907255449888666729361011)
      ·
        refine ⟨97360883174833000094041517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64907255449888666729361011 97360883174833000094041517)
        ·
          refine ⟨36510331190562375035265569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97360883174833000094041517 36510331190562375035265569)
          ·
            refine ⟨27382748392921781276449177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36510331190562375035265569 27382748392921781276449177)
            ·
              refine ⟨20537061294691335957336883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27382748392921781276449177 20537061294691335957336883)
              ·
                refine ⟨30805591942037003936005325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20537061294691335957336883 30805591942037003936005325)
                ·
                  refine ⟨11552096978263876476001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30805591942037003936005325 11552096978263876476001997)
                  ·
                    refine ⟨4332036366848953678500749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11552096978263876476001997 4332036366848953678500749)
                    ·
                      refine ⟨1624513637568357629437781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4332036366848953678500749 1624513637568357629437781)
                      ·
                        rfl

theorem cell23_3163729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_3163729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163729 prefixEnd_3163729 := by exact prefixLift 3163729
  have htrace : WordTrace (prefixWord ++ tailWord_3163729) baseStart_3163729 baseEnd_3163729 := by
    simpa [prefixWord, tailWord_3163729, baseEnd_3163729] using wordTrace_append hprefix tailTrace_3163729
  have hstable : (prefixWord ++ tailWord_3163729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163729).length < 2 ^ (prefixWord ++ tailWord_3163729).sum := by decide
  have hdescent : baseEnd_3163729 < baseStart_3163729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163747 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 1, 2, 2]
def baseStart_3163747 : Nat := 118140960795 + 3163747 * 2 ^ 59
def prefixEnd_3163747 : Nat := 4983230072969 + 3 ^ 40 * 3163747 * 2
def baseEnd_3163747 : Nat := 1624522880220138559012699

theorem tailTrace_3163747 : CollatzResearch.WordTrace tailWord_3163747 prefixEnd_3163747 1624522880220138559012699 := by
  unfold tailWord_3163747
  simp only [CollatzResearch.WordTrace]
  refine ⟨115391332869292418815241495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76927555246194945876827663 115391332869292418815241495)
  ·
    refine ⟨173086999303938628222862243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115391332869292418815241495 173086999303938628222862243)
    ·
      refine ⟨259630498955907942334293365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173086999303938628222862243 259630498955907942334293365)
      ·
        refine ⟨24340359277116369593840003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259630498955907942334293365 24340359277116369593840003)
        ·
          refine ⟨36510538915674554390760005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24340359277116369593840003 36510538915674554390760005)
          ·
            refine ⟨6845726046688978948267501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36510538915674554390760005 6845726046688978948267501)
            ·
              refine ⟨2567147267508367105600313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6845726046688978948267501 2567147267508367105600313)
              ·
                refine ⟨1925360450631275329200235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567147267508367105600313 1925360450631275329200235)
                ·
                  refine ⟨2888040675946912993800353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925360450631275329200235 2888040675946912993800353)
                  ·
                    refine ⟨2166030506960184745350265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2888040675946912993800353 2166030506960184745350265)
                    ·
                      refine ⟨1624522880220138559012699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166030506960184745350265 1624522880220138559012699)
                      ·
                        rfl

theorem cell23_3163747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_3163747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163747 prefixEnd_3163747 := by exact prefixLift 3163747
  have htrace : WordTrace (prefixWord ++ tailWord_3163747) baseStart_3163747 baseEnd_3163747 := by
    simpa [prefixWord, tailWord_3163747, baseEnd_3163747] using wordTrace_append hprefix tailTrace_3163747
  have hstable : (prefixWord ++ tailWord_3163747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163747).length < 2 ^ (prefixWord ++ tailWord_3163747).sum := by decide
  have hdescent : baseEnd_3163747 < baseStart_3163747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163756 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 3, 3, 2]
def baseStart_3163756 : Nat := 118140960795 + 3163756 * 2 ^ 59
def prefixEnd_3163756 : Nat := 4983230072969 + 3 ^ 40 * 3163756 * 2
def baseEnd_3163756 : Nat := 1624527501546029023800157

theorem tailTrace_3163756 : CollatzResearch.WordTrace tailWord_3163756 prefixEnd_3163756 1624527501546029023800157 := by
  unfold tailWord_3163756
  simp only [CollatzResearch.WordTrace]
  refine ⟨57695830563129906676159561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76927774084173208901546081 57695830563129906676159561)
  ·
    refine ⟨43271872922347430007119671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57695830563129906676159561 43271872922347430007119671)
    ·
      refine ⟨64907809383521145010679507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43271872922347430007119671 64907809383521145010679507)
      ·
        refine ⟨97361714075281717516019261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64907809383521145010679507 97361714075281717516019261)
        ·
          refine ⟨36510642778230644068507223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97361714075281717516019261 36510642778230644068507223)
          ·
            refine ⟨54765964167345966102760835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36510642778230644068507223 54765964167345966102760835)
            ·
              refine ⟨82148946251018949154141253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54765964167345966102760835 82148946251018949154141253)
              ·
                refine ⟨15402927422066052966401485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82148946251018949154141253 15402927422066052966401485)
                ·
                  refine ⟨5776097783274769862400557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15402927422066052966401485 5776097783274769862400557)
                  ·
                    refine ⟨2166036668728038698400209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5776097783274769862400557 2166036668728038698400209)
                    ·
                      refine ⟨1624527501546029023800157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166036668728038698400209 1624527501546029023800157)
                      ·
                        rfl

theorem cell23_3163756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_3163756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163756 prefixEnd_3163756 := by exact prefixLift 3163756
  have htrace : WordTrace (prefixWord ++ tailWord_3163756) baseStart_3163756 baseEnd_3163756 := by
    simpa [prefixWord, tailWord_3163756, baseEnd_3163756] using wordTrace_append hprefix tailTrace_3163756
  have hstable : (prefixWord ++ tailWord_3163756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163756).length < 2 ^ (prefixWord ++ tailWord_3163756).sum := by decide
  have hdescent : baseEnd_3163756 < baseStart_3163756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163757 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_3163757 : Nat := 118140960795 + 3163757 * 2 ^ 59
def prefixEnd_3163757 : Nat := 4983230072969 + 3 ^ 40 * 3163757 * 2
def baseEnd_3163757 : Nat := 541509338342227839962551

theorem tailTrace_3163757 : CollatzResearch.WordTrace tailWord_3163757 prefixEnd_3163757 541509338342227839962551 := by
  unfold tailWord_3163757
  simp only [CollatzResearch.WordTrace]
  refine ⟨115391697599256190523105525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76927798399504127015403683 115391697599256190523105525)
  ·
    refine ⟨10817971649930267861541143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115391697599256190523105525 10817971649930267861541143)
    ·
      refine ⟨16226957474895401792311715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817971649930267861541143 16226957474895401792311715)
      ·
        refine ⟨24340436212343102688467573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16226957474895401792311715 24340436212343102688467573)
        ·
          refine ⟨2281915894907165877043835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24340436212343102688467573 2281915894907165877043835)
          ·
            refine ⟨3422873842360748815565753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281915894907165877043835 3422873842360748815565753)
            ·
              refine ⟨2567155381770561611674315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422873842360748815565753 2567155381770561611674315)
              ·
                refine ⟨3850733072655842417511473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567155381770561611674315 3850733072655842417511473)
                ·
                  refine ⟨2888049804491881813133605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3850733072655842417511473 2888049804491881813133605)
                  ·
                    refine ⟨541509338342227839962551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2888049804491881813133605 541509338342227839962551)
                    ·
                      rfl

theorem cell23_3163757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_3163757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163757 prefixEnd_3163757 := by exact prefixLift 3163757
  have htrace : WordTrace (prefixWord ++ tailWord_3163757) baseStart_3163757 baseEnd_3163757 := by
    simpa [prefixWord, tailWord_3163757, baseEnd_3163757] using wordTrace_append hprefix tailTrace_3163757
  have hstable : (prefixWord ++ tailWord_3163757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163757).length < 2 ^ (prefixWord ++ tailWord_3163757).sum := by decide
  have hdescent : baseEnd_3163757 < baseStart_3163757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163773 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_3163773 : Nat := 118140960795 + 3163773 * 2 ^ 59
def prefixEnd_3163773 : Nat := 4983230072969 + 3 ^ 40 * 3163773 * 2
def baseEnd_3163773 : Nat := 1624536230717155457287579

theorem tailTrace_3163773 : CollatzResearch.WordTrace tailWord_3163773 prefixEnd_3163773 1624536230717155457287579 := by
  unfold tailWord_3163773
  simp only [CollatzResearch.WordTrace]
  refine ⟨115392281167198225255687973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76928187444798816837125315 115392281167198225255687973)
  ·
    refine ⟨21636052718849667235441495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115392281167198225255687973 21636052718849667235441495)
    ·
      refine ⟨32454079078274500853162243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21636052718849667235441495 32454079078274500853162243)
      ·
        refine ⟨48681118617411751279743365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32454079078274500853162243 48681118617411751279743365)
        ·
          refine ⟨9127709740764703364951881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48681118617411751279743365 9127709740764703364951881)
          ·
            refine ⟨6845782305573527523713911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9127709740764703364951881 6845782305573527523713911)
            ·
              refine ⟨10268673458360291285570867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845782305573527523713911 10268673458360291285570867)
              ·
                refine ⟨15403010187540436928356301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10268673458360291285570867 15403010187540436928356301)
                ·
                  refine ⟨5776128820327663848133613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15403010187540436928356301 5776128820327663848133613)
                  ·
                    refine ⟨2166048307622873943050105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5776128820327663848133613 2166048307622873943050105)
                    ·
                      refine ⟨1624536230717155457287579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166048307622873943050105 1624536230717155457287579)
                      ·
                        rfl

theorem cell23_3163773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_3163773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163773 prefixEnd_3163773 := by exact prefixLift 3163773
  have htrace : WordTrace (prefixWord ++ tailWord_3163773) baseStart_3163773 baseEnd_3163773 := by
    simpa [prefixWord, tailWord_3163773, baseEnd_3163773] using wordTrace_append hprefix tailTrace_3163773
  have hstable : (prefixWord ++ tailWord_3163773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163773).length < 2 ^ (prefixWord ++ tailWord_3163773).sum := by decide
  have hdescent : baseEnd_3163773 < baseStart_3163773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163839 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 1, 7]
def baseStart_3163839 : Nat := 118140960795 + 3163839 * 2 ^ 59
def prefixEnd_3163839 : Nat := 4983230072969 + 3 ^ 40 * 3163839 * 2
def baseEnd_3163839 : Nat := 541523373480117399687425

theorem tailTrace_3163839 : CollatzResearch.WordTrace tailWord_3163839 prefixEnd_3163839 541523373480117399687425 := by
  unfold tailWord_3163839
  simp only [CollatzResearch.WordTrace]
  refine ⟨115394688384959118527590571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76929792256639412351727047 115394688384959118527590571)
  ·
    refine ⟨173092032577438677791385857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115394688384959118527590571 173092032577438677791385857)
    ·
      refine ⟨129819024433079008343539393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173092032577438677791385857 129819024433079008343539393)
      ·
        refine ⟨97364268324809256257654545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129819024433079008343539393 97364268324809256257654545)
        ·
          refine ⟨73023201243606942193240909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97364268324809256257654545 73023201243606942193240909)
          ·
            refine ⟨27383700466352603322465341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73023201243606942193240909 27383700466352603322465341)
            ·
              refine ⟨10268887674882226245924503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27383700466352603322465341 10268887674882226245924503)
              ·
                refine ⟨15403331512323339368886755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10268887674882226245924503 15403331512323339368886755)
                ·
                  refine ⟨23104997268485009053330133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15403331512323339368886755 23104997268485009053330133)
                  ·
                    refine ⟨541523373480117399687425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23104997268485009053330133 541523373480117399687425)
                    ·
                      rfl

theorem cell23_3163839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_3163839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163839 prefixEnd_3163839 := by exact prefixLift 3163839
  have htrace : WordTrace (prefixWord ++ tailWord_3163839) baseStart_3163839 baseEnd_3163839 := by
    simpa [prefixWord, tailWord_3163839, baseEnd_3163839] using wordTrace_append hprefix tailTrace_3163839
  have hstable : (prefixWord ++ tailWord_3163839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163839).length < 2 ^ (prefixWord ++ tailWord_3163839).sum := by decide
  have hdescent : baseEnd_3163839 < baseStart_3163839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163919 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_3163919 : Nat := 118140960795 + 3163919 * 2 ^ 59
def prefixEnd_3163919 : Nat := 4983230072969 + 3 ^ 40 * 3163919 * 2
def baseEnd_3163919 : Nat := 1624611198892711886061907

theorem tailTrace_3163919 : CollatzResearch.WordTrace tailWord_3163919 prefixEnd_3163919 1624611198892711886061907 := by
  unfold tailWord_3163919
  simp only [CollatzResearch.WordTrace]
  refine ⟨115397606224669292190502811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76931737483112861460335207 115397606224669292190502811)
  ·
    refine ⟨173096409337003938285754217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115397606224669292190502811 173096409337003938285754217)
    ·
      refine ⟨129822307002752953714315663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173096409337003938285754217 129822307002752953714315663)
      ·
        refine ⟨194733460504129430571473495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129822307002752953714315663 194733460504129430571473495)
        ·
          refine ⟨292100190756194145857210243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194733460504129430571473495 292100190756194145857210243)
          ·
            refine ⟨438150286134291218785815365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292100190756194145857210243 438150286134291218785815365)
            ·
              refine ⟨82153178650179603522340381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438150286134291218785815365 82153178650179603522340381)
              ·
                refine ⟨30807441993817351320877643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82153178650179603522340381 30807441993817351320877643)
                ·
                  refine ⟨46211162990726026981316465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30807441993817351320877643 46211162990726026981316465)
                  ·
                    refine ⟨34658372243044520235987349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46211162990726026981316465 34658372243044520235987349)
                    ·
                      refine ⟨1624611198892711886061907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34658372243044520235987349 1624611198892711886061907)
                      ·
                        rfl

theorem cell23_3163919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_3163919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163919 prefixEnd_3163919 := by exact prefixLift 3163919
  have htrace : WordTrace (prefixWord ++ tailWord_3163919) baseStart_3163919 baseEnd_3163919 := by
    simpa [prefixWord, tailWord_3163919, baseEnd_3163919] using wordTrace_append hprefix tailTrace_3163919
  have hstable : (prefixWord ++ tailWord_3163919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163919).length < 2 ^ (prefixWord ++ tailWord_3163919).sum := by decide
  have hdescent : baseEnd_3163919 < baseStart_3163919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163993 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 2, 4]
def baseStart_3163993 : Nat := 118140960795 + 3163993 * 2 ^ 59
def prefixEnd_3163993 : Nat := 4983230072969 + 3 ^ 40 * 3163993 * 2
def baseEnd_3163993 : Nat := 541549732153714865512189

theorem tailTrace_3163993 : CollatzResearch.WordTrace tailWord_3163993 prefixEnd_3163993 541549732153714865512189 := by
  unfold tailWord_3163993
  simp only [CollatzResearch.WordTrace]
  refine ⟨115400305226401202828696633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76933536817600801885797755 115400305226401202828696633)
  ·
    refine ⟨86550228919800902121522475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115400305226401202828696633 86550228919800902121522475)
    ·
      refine ⟨129825343379701353182283713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86550228919800902121522475 129825343379701353182283713)
      ·
        refine ⟨97369007534776014886712785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129825343379701353182283713 97369007534776014886712785)
        ·
          refine ⟨73026755651082011165034589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97369007534776014886712785 73026755651082011165034589)
          ·
            refine ⟨27385033369155754186887971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73026755651082011165034589 27385033369155754186887971)
            ·
              refine ⟨41077550053733631280331957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27385033369155754186887971 41077550053733631280331957)
              ·
                refine ⟨3851020317537527932531121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41077550053733631280331957 3851020317537527932531121)
                ·
                  refine ⟨2888265238153145949398341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3851020317537527932531121 2888265238153145949398341)
                  ·
                    refine ⟨541549732153714865512189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2888265238153145949398341 541549732153714865512189)
                    ·
                      rfl

theorem cell23_3163993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_3163993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163993 prefixEnd_3163993 := by exact prefixLift 3163993
  have htrace : WordTrace (prefixWord ++ tailWord_3163993) baseStart_3163993 baseEnd_3163993 := by
    simpa [prefixWord, tailWord_3163993, baseEnd_3163993] using wordTrace_append hprefix tailTrace_3163993
  have hstable : (prefixWord ++ tailWord_3163993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163993).length < 2 ^ (prefixWord ++ tailWord_3163993).sum := by decide
  have hdescent : baseEnd_3163993 < baseStart_3163993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164000 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 5, 2, 2]
def baseStart_3164000 : Nat := 118140960795 + 3164000 * 2 ^ 59
def prefixEnd_3164000 : Nat := 4983230072969 + 3 ^ 40 * 3164000 * 2
def baseEnd_3164000 : Nat := 1624652790825726069149035

theorem tailTrace_3164000 : CollatzResearch.WordTrace tailWord_3164000 prefixEnd_3164000 1624652790825726069149035 := by
  unfold tailWord_3164000
  simp only [CollatzResearch.WordTrace]
  refine ⟨57700280268687921512100727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76933707024917228682800969 57700280268687921512100727)
  ·
    refine ⟨86550420403031882268151091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57700280268687921512100727 86550420403031882268151091)
    ·
      refine ⟨129825630604547823402226637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86550420403031882268151091 129825630604547823402226637)
      ·
        refine ⟨48684611476705433775834989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129825630604547823402226637 48684611476705433775834989)
        ·
          refine ⟨18256729303764537665938121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48684611476705433775834989 18256729303764537665938121)
          ·
            refine ⟨13692546977823403249453591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18256729303764537665938121 13692546977823403249453591)
            ·
              refine ⟨20538820466735104874180387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13692546977823403249453591 20538820466735104874180387)
              ·
                refine ⟨30808230700102657311270581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20538820466735104874180387 30808230700102657311270581)
                ·
                  refine ⟨2888271628134624122931617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30808230700102657311270581 2888271628134624122931617)
                  ·
                    refine ⟨2166203721100968092198713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2888271628134624122931617 2166203721100968092198713)
                    ·
                      refine ⟨1624652790825726069149035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166203721100968092198713 1624652790825726069149035)
                      ·
                        rfl

theorem cell23_3164000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_3164000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164000 prefixEnd_3164000 := by exact prefixLift 3164000
  have htrace : WordTrace (prefixWord ++ tailWord_3164000) baseStart_3164000 baseEnd_3164000 := by
    simpa [prefixWord, tailWord_3164000, baseEnd_3164000] using wordTrace_append hprefix tailTrace_3164000
  have hstable : (prefixWord ++ tailWord_3164000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164000).length < 2 ^ (prefixWord ++ tailWord_3164000).sum := by decide
  have hdescent : baseEnd_3164000 < baseStart_3164000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164004 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_3164004 : Nat := 118140960795 + 3164004 * 2 ^ 59
def prefixEnd_3164004 : Nat := 4983230072969 + 3 ^ 40 * 3164004 * 2
def baseEnd_3164004 : Nat := 1624654844748344053499017

theorem tailTrace_3164004 : CollatzResearch.WordTrace tailWord_3164004 prefixEnd_3164004 1624654844748344053499017 := by
  unfold tailWord_3164004
  simp only [CollatzResearch.WordTrace]
  refine ⟨57700353214680675853673533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76933804286240901138231377 57700353214680675853673533)
  ·
    refine ⟨21637632455505253445127575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57700353214680675853673533 21637632455505253445127575)
    ·
      refine ⟨32456448683257880167691363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21637632455505253445127575 32456448683257880167691363)
      ·
        refine ⟨48684673024886820251537045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32456448683257880167691363 48684673024886820251537045)
        ·
          refine ⟨2282094048041569699290799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48684673024886820251537045 2282094048041569699290799)
          ·
            refine ⟨3423141072062354548936199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282094048041569699290799 3423141072062354548936199)
            ·
              refine ⟨5134711608093531823404299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423141072062354548936199 5134711608093531823404299)
              ·
                refine ⟨7702067412140297735106449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134711608093531823404299 7702067412140297735106449)
                ·
                  refine ⟨5776550559105223301329837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702067412140297735106449 5776550559105223301329837)
                  ·
                    refine ⟨2166206459664458737998689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5776550559105223301329837 2166206459664458737998689)
                    ·
                      refine ⟨1624654844748344053499017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166206459664458737998689 1624654844748344053499017)
                      ·
                        rfl

theorem cell23_3164004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_3164004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164004 prefixEnd_3164004 := by exact prefixLift 3164004
  have htrace : WordTrace (prefixWord ++ tailWord_3164004) baseStart_3164004 baseEnd_3164004 := by
    simpa [prefixWord, tailWord_3164004, baseEnd_3164004] using wordTrace_append hprefix tailTrace_3164004
  have hstable : (prefixWord ++ tailWord_3164004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164004).length < 2 ^ (prefixWord ++ tailWord_3164004).sum := by decide
  have hdescent : baseEnd_3164004 < baseStart_3164004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164013 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3164013 : Nat := 118140960795 + 3164013 * 2 ^ 59
def prefixEnd_3164013 : Nat := 4983230072969 + 3 ^ 40 * 3164013 * 2
def baseEnd_3164013 : Nat := 1624659466074234518286475

theorem tailTrace_3164013 : CollatzResearch.WordTrace tailWord_3164013 prefixEnd_3164013 1624659466074234518286475 := by
  unfold tailWord_3164013
  simp only [CollatzResearch.WordTrace]
  refine ⟨115401034686328746244424693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76934023124219164162949795 115401034686328746244424693)
  ·
    refine ⟨10818847001843319960414815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115401034686328746244424693 10818847001843319960414815)
    ·
      refine ⟨16228270502764979940622223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10818847001843319960414815 16228270502764979940622223)
      ·
        refine ⟨24342405754147469910933335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16228270502764979940622223 24342405754147469910933335)
        ·
          refine ⟨36513608631221204866400003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24342405754147469910933335 36513608631221204866400003)
          ·
            refine ⟨54770412946831807299600005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36513608631221204866400003 54770412946831807299600005)
            ·
              refine ⟨10269452427530963868675001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54770412946831807299600005 10269452427530963868675001)
              ·
                refine ⟨7702089320648222901506251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10269452427530963868675001 7702089320648222901506251)
                ·
                  refine ⟨11553133980972334352259377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7702089320648222901506251 11553133980972334352259377)
                  ·
                    refine ⟨8664850485729250764194533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11553133980972334352259377 8664850485729250764194533)
                    ·
                      refine ⟨1624659466074234518286475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8664850485729250764194533 1624659466074234518286475)
                      ·
                        rfl

theorem cell23_3164013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3164013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164013 prefixEnd_3164013 := by exact prefixLift 3164013
  have htrace : WordTrace (prefixWord ++ tailWord_3164013) baseStart_3164013 baseEnd_3164013 := by
    simpa [prefixWord, tailWord_3164013, baseEnd_3164013] using wordTrace_append hprefix tailTrace_3164013
  have hstable : (prefixWord ++ tailWord_3164013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164013).length < 2 ^ (prefixWord ++ tailWord_3164013).sum := by decide
  have hdescent : baseEnd_3164013 < baseStart_3164013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164036 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_3164036 : Nat := 118140960795 + 3164036 * 2 ^ 59
def prefixEnd_3164036 : Nat := 4983230072969 + 3 ^ 40 * 3164036 * 2
def baseEnd_3164036 : Nat := 541557092043095976099623

theorem tailTrace_3164036 : CollatzResearch.WordTrace tailWord_3164036 prefixEnd_3164036 541557092043095976099623 := by
  unfold tailWord_3164036
  simp only [CollatzResearch.WordTrace]
  refine ⟨57700936782622710586255981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76934582376830280781674641 57700936782622710586255981)
  ·
    refine ⟨21637851293483516469845993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57700936782622710586255981 21637851293483516469845993)
    ·
      refine ⟨16228388470112637352384495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21637851293483516469845993 16228388470112637352384495)
      ·
        refine ⟨24342582705168956028576743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16228388470112637352384495 24342582705168956028576743)
        ·
          refine ⟨36513874057753434042865115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24342582705168956028576743 36513874057753434042865115)
          ·
            refine ⟨54770811086630151064297673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36513874057753434042865115 54770811086630151064297673)
            ·
              refine ⟨41078108314972613298223255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54770811086630151064297673 41078108314972613298223255)
              ·
                refine ⟨61617162472458919947334883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41078108314972613298223255 61617162472458919947334883)
                ·
                  refine ⟨92425743708688379921002325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61617162472458919947334883 92425743708688379921002325)
                  ·
                    refine ⟨541557092043095976099623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92425743708688379921002325 541557092043095976099623)
                    ·
                      rfl

theorem cell23_3164036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_3164036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164036 prefixEnd_3164036 := by exact prefixLift 3164036
  have htrace : WordTrace (prefixWord ++ tailWord_3164036) baseStart_3164036 baseEnd_3164036 := by
    simpa [prefixWord, tailWord_3164036, baseEnd_3164036] using wordTrace_append hprefix tailTrace_3164036
  have hstable : (prefixWord ++ tailWord_3164036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164036).length < 2 ^ (prefixWord ++ tailWord_3164036).sum := by decide
  have hdescent : baseEnd_3164036 < baseStart_3164036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164107 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 2, 2, 2]
def baseStart_3164107 : Nat := 118140960795 + 3164107 * 2 ^ 59
def prefixEnd_3164107 : Nat := 4983230072969 + 3 ^ 40 * 3164107 * 2
def baseEnd_3164107 : Nat := 1624707733255757150511043

theorem tailTrace_3164107 : CollatzResearch.WordTrace tailWord_3164107 prefixEnd_3164107 1624707733255757150511043 := by
  unfold tailWord_3164107
  simp only [CollatzResearch.WordTrace]
  refine ⟨115404463147988200298346575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76936308765325466865564383 115404463147988200298346575)
  ·
    refine ⟨173106694721982300447519863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115404463147988200298346575 173106694721982300447519863)
    ·
      refine ⟨259660042082973450671279795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173106694721982300447519863 259660042082973450671279795)
      ·
        refine ⟨389490063124460176006919693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259660042082973450671279795 389490063124460176006919693)
        ·
          refine ⟨146058773671672566002594885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389490063124460176006919693 146058773671672566002594885)
          ·
            refine ⟨27386020063438606125486541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146058773671672566002594885 27386020063438606125486541)
            ·
              refine ⟨10269757523789477297057453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27386020063438606125486541 10269757523789477297057453)
              ·
                refine ⟨3851159071421053986396545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10269757523789477297057453 3851159071421053986396545)
                ·
                  refine ⟨2888369303565790489797409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3851159071421053986396545 2888369303565790489797409)
                  ·
                    refine ⟨2166276977674342867348057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2888369303565790489797409 2166276977674342867348057)
                    ·
                      refine ⟨1624707733255757150511043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166276977674342867348057 1624707733255757150511043)
                      ·
                        rfl

theorem cell23_3164107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 2, 2].length) (baseStart_3164107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164107 prefixEnd_3164107 := by exact prefixLift 3164107
  have htrace : WordTrace (prefixWord ++ tailWord_3164107) baseStart_3164107 baseEnd_3164107 := by
    simpa [prefixWord, tailWord_3164107, baseEnd_3164107] using wordTrace_append hprefix tailTrace_3164107
  have hstable : (prefixWord ++ tailWord_3164107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164107).length < 2 ^ (prefixWord ++ tailWord_3164107).sum := by decide
  have hdescent : baseEnd_3164107 < baseStart_3164107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164143 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 2, 5]
def baseStart_3164143 : Nat := 118140960795 + 3164143 * 2 ^ 59
def prefixEnd_3164143 : Nat := 4983230072969 + 3 ^ 40 * 3164143 * 2
def baseEnd_3164143 : Nat := 541575406186439669886959

theorem tailTrace_3164143 : CollatzResearch.WordTrace tailWord_3164143 prefixEnd_3164143 541575406186439669886959 := by
  unfold tailWord_3164143
  simp only [CollatzResearch.WordTrace]
  refine ⟨115405776175857778446657083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76937184117238518964438055 115405776175857778446657083)
  ·
    refine ⟨173108664263786667669985625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115405776175857778446657083 173108664263786667669985625)
    ·
      refine ⟨129831498197840000752489219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173108664263786667669985625 129831498197840000752489219)
      ·
        refine ⟨194747247296760001128733829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129831498197840000752489219 194747247296760001128733829)
        ·
          refine ⟨36515108868142500211637593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194747247296760001128733829 36515108868142500211637593)
          ·
            refine ⟨27386331651106875158728195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36515108868142500211637593 27386331651106875158728195)
            ·
              refine ⟨41079497476660312738092293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27386331651106875158728195 41079497476660312738092293)
              ·
                refine ⟨7702405776873808638392305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41079497476660312738092293 7702405776873808638392305)
                ·
                  refine ⟨5776804332655356478794229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7702405776873808638392305 5776804332655356478794229)
                  ·
                    refine ⟨541575406186439669886959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5776804332655356478794229 541575406186439669886959)
                    ·
                      rfl

theorem cell23_3164143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_3164143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164143 prefixEnd_3164143 := by exact prefixLift 3164143
  have htrace : WordTrace (prefixWord ++ tailWord_3164143) baseStart_3164143 baseEnd_3164143 := by
    simpa [prefixWord, tailWord_3164143, baseEnd_3164143] using wordTrace_append hprefix tailTrace_3164143
  have hstable : (prefixWord ++ tailWord_3164143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164143).length < 2 ^ (prefixWord ++ tailWord_3164143).sum := by decide
  have hdescent : baseEnd_3164143 < baseStart_3164143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164153 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3164153 : Nat := 118140960795 + 3164153 * 2 ^ 59
def prefixEnd_3164153 : Nat := 4983230072969 + 3 ^ 40 * 3164153 * 2
def baseEnd_3164153 : Nat := 1624731353365863970535831

theorem tailTrace_3164153 : CollatzResearch.WordTrace tailWord_3164153 prefixEnd_3164153 1624731353365863970535831 := by
  unfold tailWord_3164153
  simp only [CollatzResearch.WordTrace]
  refine ⟨115406140905821550154521113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76937427270547700103014075 115406140905821550154521113)
  ·
    refine ⟨86554605679366162615890835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115406140905821550154521113 86554605679366162615890835)
    ·
      refine ⟨129831908519049243923836253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86554605679366162615890835 129831908519049243923836253)
      ·
        refine ⟨48686965694643466471438595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129831908519049243923836253 48686965694643466471438595)
        ·
          refine ⟨73030448541965199707157893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48686965694643466471438595 73030448541965199707157893)
          ·
            refine ⟨13693209101618474945092105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73030448541965199707157893 13693209101618474945092105)
            ·
              refine ⟨10269906826213856208819079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13693209101618474945092105 10269906826213856208819079)
              ·
                refine ⟨15404860239320784313228619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10269906826213856208819079 15404860239320784313228619)
                ·
                  refine ⟨23107290358981176469842929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15404860239320784313228619 23107290358981176469842929)
                  ·
                    refine ⟨17330467769235882352382197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23107290358981176469842929 17330467769235882352382197)
                    ·
                      refine ⟨1624731353365863970535831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17330467769235882352382197 1624731353365863970535831)
                      ·
                        rfl

theorem cell23_3164153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3164153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164153 prefixEnd_3164153 := by exact prefixLift 3164153
  have htrace : WordTrace (prefixWord ++ tailWord_3164153) baseStart_3164153 baseEnd_3164153 := by
    simpa [prefixWord, tailWord_3164153, baseEnd_3164153] using wordTrace_append hprefix tailTrace_3164153
  have hstable : (prefixWord ++ tailWord_3164153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164153).length < 2 ^ (prefixWord ++ tailWord_3164153).sum := by decide
  have hdescent : baseEnd_3164153 < baseStart_3164153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164163 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 4]
def baseStart_3164163 : Nat := 118140960795 + 3164163 * 2 ^ 59
def prefixEnd_3164163 : Nat := 4983230072969 + 3 ^ 40 * 3164163 * 2
def baseEnd_3164163 : Nat := 1624736488172408931410785

theorem tailTrace_3164163 : CollatzResearch.WordTrace tailWord_3164163 prefixEnd_3164163 1624736488172408931410785 := by
  unfold tailWord_3164163
  simp only [CollatzResearch.WordTrace]
  refine ⟨115406505635785321862385143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76937670423856881241590095 115406505635785321862385143)
  ·
    refine ⟨173109758453677982793577715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115406505635785321862385143 173109758453677982793577715)
    ·
      refine ⟨259664637680516974190366573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173109758453677982793577715 259664637680516974190366573)
      ·
        refine ⟨97374239130193865321387465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259664637680516974190366573 97374239130193865321387465)
        ·
          refine ⟨73030679347645398991040599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97374239130193865321387465 73030679347645398991040599)
          ·
            refine ⟨109546019021468098486560899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73030679347645398991040599 109546019021468098486560899)
            ·
              refine ⟨164319028532202147729841349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109546019021468098486560899 164319028532202147729841349)
              ·
                refine ⟨30809817849787902699345253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164319028532202147729841349 30809817849787902699345253)
                ·
                  refine ⟨5776840846835231756127235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30809817849787902699345253 5776840846835231756127235)
                  ·
                    refine ⟨8665261270252847634190853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776840846835231756127235 8665261270252847634190853)
                    ·
                      refine ⟨1624736488172408931410785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8665261270252847634190853 1624736488172408931410785)
                      ·
                        rfl

theorem cell23_3164163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_3164163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164163 prefixEnd_3164163 := by exact prefixLift 3164163
  have htrace : WordTrace (prefixWord ++ tailWord_3164163) baseStart_3164163 baseEnd_3164163 := by
    simpa [prefixWord, tailWord_3164163, baseEnd_3164163] using wordTrace_append hprefix tailTrace_3164163
  have hstable : (prefixWord ++ tailWord_3164163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164163).length < 2 ^ (prefixWord ++ tailWord_3164163).sum := by decide
  have hdescent : baseEnd_3164163 < baseStart_3164163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164203 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 6]
def baseStart_3164203 : Nat := 118140960795 + 3164203 * 2 ^ 59
def prefixEnd_3164203 : Nat := 4983230072969 + 3 ^ 40 * 3164203 * 2
def baseEnd_3164203 : Nat := 180528558599843197212289

theorem tailTrace_3164203 : CollatzResearch.WordTrace tailWord_3164203 prefixEnd_3164203 180528558599843197212289 := by
  unfold tailWord_3164203
  simp only [CollatzResearch.WordTrace]
  refine ⟨115407964555640408693841263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76938643037093605795894175 115407964555640408693841263)
  ·
    refine ⟨173111946833460613040761895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115407964555640408693841263 173111946833460613040761895)
    ·
      refine ⟨259667920250190919561142843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173111946833460613040761895 259667920250190919561142843)
      ·
        refine ⟨389501880375286379341714265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259667920250190919561142843 389501880375286379341714265)
        ·
          refine ⟨292126410281464784506285699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389501880375286379341714265 292126410281464784506285699)
          ·
            refine ⟨438189615422197176759428549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292126410281464784506285699 438189615422197176759428549)
            ·
              refine ⟨82160552891661970642392853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438189615422197176759428549 82160552891661970642392853)
              ·
                refine ⟨3851275916796654873862165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82160552891661970642392853 3851275916796654873862165)
                ·
                  refine ⟨180528558599843197212289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3851275916796654873862165 180528558599843197212289)
                  ·
                    rfl

theorem cell23_3164203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 6].length) (baseStart_3164203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164203 prefixEnd_3164203 := by exact prefixLift 3164203
  have htrace : WordTrace (prefixWord ++ tailWord_3164203) baseStart_3164203 baseEnd_3164203 := by
    simpa [prefixWord, tailWord_3164203, baseEnd_3164203] using wordTrace_append hprefix tailTrace_3164203
  have hstable : (prefixWord ++ tailWord_3164203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164203).length < 2 ^ (prefixWord ++ tailWord_3164203).sum := by decide
  have hdescent : baseEnd_3164203 < baseStart_3164203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164250 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_3164250 : Nat := 118140960795 + 3164250 * 2 ^ 59
def prefixEnd_3164250 : Nat := 4983230072969 + 3 ^ 40 * 3164250 * 2
def baseEnd_3164250 : Nat := 541593720329783363674295

theorem tailTrace_3164250 : CollatzResearch.WordTrace tailWord_3164250 prefixEnd_3164250 541593720329783363674295 := by
  unfold tailWord_3164250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28852419696617533930200551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76939785857646757147201469 28852419696617533930200551)
  ·
    refine ⟨43278629544926300895300827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28852419696617533930200551 43278629544926300895300827)
    ·
      refine ⟨64917944317389451342951241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43278629544926300895300827 64917944317389451342951241)
      ·
        refine ⟨48688458238042088507213431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64917944317389451342951241 48688458238042088507213431)
        ·
          refine ⟨73032687357063132760820147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48688458238042088507213431 73032687357063132760820147)
          ·
            refine ⟨109549031035594699141230221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73032687357063132760820147 109549031035594699141230221)
            ·
              refine ⟨41080886638348012177961333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109549031035594699141230221 41080886638348012177961333)
              ·
                refine ⟨3851333122345126141683875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41080886638348012177961333 3851333122345126141683875)
                ·
                  refine ⟨5776999683517689212525813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851333122345126141683875 5776999683517689212525813)
                  ·
                    refine ⟨541593720329783363674295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5776999683517689212525813 541593720329783363674295)
                    ·
                      rfl

theorem cell23_3164250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_3164250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164250 prefixEnd_3164250 := by exact prefixLift 3164250
  have htrace : WordTrace (prefixWord ++ tailWord_3164250) baseStart_3164250 baseEnd_3164250 := by
    simpa [prefixWord, tailWord_3164250, baseEnd_3164250] using wordTrace_append hprefix tailTrace_3164250
  have hstable : (prefixWord ++ tailWord_3164250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164250).length < 2 ^ (prefixWord ++ tailWord_3164250).sum := by decide
  have hdescent : baseEnd_3164250 < baseStart_3164250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164258 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3164258 : Nat := 118140960795 + 3164258 * 2 ^ 59
def prefixEnd_3164258 : Nat := 4983230072969 + 3 ^ 40 * 3164258 * 2
def baseEnd_3164258 : Nat := 541595089611528686574283

theorem tailTrace_3164258 : CollatzResearch.WordTrace tailWord_3164258 prefixEnd_3164258 541595089611528686574283 := by
  unfold tailWord_3164258
  simp only [CollatzResearch.WordTrace]
  refine ⟨28852492642610288271773357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76939980380294102058062285 28852492642610288271773357)
  ·
    refine ⟨10819684740978858101915009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28852492642610288271773357 10819684740978858101915009)
    ·
      refine ⟨8114763555734143576436257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10819684740978858101915009 8114763555734143576436257)
      ·
        refine ⟨6086072666800607682327193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8114763555734143576436257 6086072666800607682327193)
        ·
          refine ⟨4564554500100455761745395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6086072666800607682327193 4564554500100455761745395)
          ·
            refine ⟨6846831750150683642618093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564554500100455761745395 6846831750150683642618093)
            ·
              refine ⟨2567561906306506365981785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6846831750150683642618093 2567561906306506365981785)
              ·
                refine ⟨1925671429729879774486339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567561906306506365981785 1925671429729879774486339)
                ·
                  refine ⟨2888507144594819661729509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925671429729879774486339 2888507144594819661729509)
                  ·
                    refine ⟨541595089611528686574283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2888507144594819661729509 541595089611528686574283)
                    ·
                      rfl

theorem cell23_3164258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3164258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164258 prefixEnd_3164258 := by exact prefixLift 3164258
  have htrace : WordTrace (prefixWord ++ tailWord_3164258) baseStart_3164258 baseEnd_3164258 := by
    simpa [prefixWord, tailWord_3164258, baseEnd_3164258] using wordTrace_append hprefix tailTrace_3164258
  have hstable : (prefixWord ++ tailWord_3164258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164258).length < 2 ^ (prefixWord ++ tailWord_3164258).sum := by decide
  have hdescent : baseEnd_3164258 < baseStart_3164258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164347 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 3, 3, 2]
def baseStart_3164347 : Nat := 118140960795 + 3164347 * 2 ^ 59
def prefixEnd_3164347 : Nat := 4983230072969 + 3 ^ 40 * 3164347 * 2
def baseEnd_3164347 : Nat := 1624830968612836211509939

theorem tailTrace_3164347 : CollatzResearch.WordTrace tailWord_3164347 prefixEnd_3164347 1624830968612836211509939 := by
  unfold tailWord_3164347
  simp only [CollatzResearch.WordTrace]
  refine ⟨115413216667118721287083295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76942144444745814191388863 115413216667118721287083295)
  ·
    refine ⟨173119825000678081930624943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115413216667118721287083295 173119825000678081930624943)
    ·
      refine ⟨259679737501017122895937415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173119825000678081930624943 259679737501017122895937415)
      ·
        refine ⟨389519606251525684343906123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259679737501017122895937415 389519606251525684343906123)
        ·
          refine ⟨584279409377288526515859185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389519606251525684343906123 584279409377288526515859185)
          ·
            refine ⟨438209557032966394886894389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584279409377288526515859185 438209557032966394886894389)
            ·
              refine ⟨41082145971840599520646349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 438209557032966394886894389 41082145971840599520646349)
              ·
                refine ⟨15405804739440224820242381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41082145971840599520646349 15405804739440224820242381)
                ·
                  refine ⟨5777176777290084307590893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15405804739440224820242381 5777176777290084307590893)
                  ·
                    refine ⟨2166441291483781615346585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5777176777290084307590893 2166441291483781615346585)
                    ·
                      refine ⟨1624830968612836211509939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166441291483781615346585 1624830968612836211509939)
                      ·
                        rfl

theorem cell23_3164347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3, 2].length) (baseStart_3164347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164347 prefixEnd_3164347 := by exact prefixLift 3164347
  have htrace : WordTrace (prefixWord ++ tailWord_3164347) baseStart_3164347 baseEnd_3164347 := by
    simpa [prefixWord, tailWord_3164347, baseEnd_3164347] using wordTrace_append hprefix tailTrace_3164347
  have hstable : (prefixWord ++ tailWord_3164347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164347).length < 2 ^ (prefixWord ++ tailWord_3164347).sum := by decide
  have hdescent : baseEnd_3164347 < baseStart_3164347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164377 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 3, 4, 2]
def baseStart_3164377 : Nat := 118140960795 + 3164377 * 2 ^ 59
def prefixEnd_3164377 : Nat := 4983230072969 + 3 ^ 40 * 3164377 * 2
def baseEnd_3164377 : Nat := 1624846373032471094134801

theorem tailTrace_3164377 : CollatzResearch.WordTrace tailWord_3164377 prefixEnd_3164377 1624846373032471094134801 := by
  unfold tailWord_3164377
  simp only [CollatzResearch.WordTrace]
  refine ⟨115414310857010036410675385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76942873904673357607116923 115414310857010036410675385)
  ·
    refine ⟨86560733142757527308006539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115414310857010036410675385 86560733142757527308006539)
    ·
      refine ⟨129841099714136290962009809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86560733142757527308006539 129841099714136290962009809)
      ·
        refine ⟨97380824785602218221507357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129841099714136290962009809 97380824785602218221507357)
        ·
          refine ⟨36517809294600831833065259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97380824785602218221507357 36517809294600831833065259)
          ·
            refine ⟨54776713941901247749597889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36517809294600831833065259 54776713941901247749597889)
            ·
              refine ⟨41082535456425935812198417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54776713941901247749597889 41082535456425935812198417)
              ·
                refine ⟨30811901592319451859148813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41082535456425935812198417 30811901592319451859148813)
                ·
                  refine ⟨11554463097119794447180805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30811901592319451859148813 11554463097119794447180805)
                  ·
                    refine ⟨2166461830709961458846401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11554463097119794447180805 2166461830709961458846401)
                    ·
                      refine ⟨1624846373032471094134801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166461830709961458846401 1624846373032471094134801)
                      ·
                        rfl

theorem cell23_3164377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_3164377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164377 prefixEnd_3164377 := by exact prefixLift 3164377
  have htrace : WordTrace (prefixWord ++ tailWord_3164377) baseStart_3164377 baseEnd_3164377 := by
    simpa [prefixWord, tailWord_3164377, baseEnd_3164377] using wordTrace_append hprefix tailTrace_3164377
  have hstable : (prefixWord ++ tailWord_3164377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164377).length < 2 ^ (prefixWord ++ tailWord_3164377).sum := by decide
  have hdescent : baseEnd_3164377 < baseStart_3164377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164460 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_3164460 : Nat := 118140960795 + 3164460 * 2 ^ 59
def prefixEnd_3164460 : Nat := 4983230072969 + 3 ^ 40 * 3164460 * 2
def baseEnd_3164460 : Nat := 541629663975598089798973

theorem tailTrace_3164460 : CollatzResearch.WordTrace tailWord_3164460 prefixEnd_3164460 541629663975598089798973 := by
  unfold tailWord_3164460
  simp only [CollatzResearch.WordTrace]
  refine ⟨57708669057854670792973417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76944892077139561057297889 57708669057854670792973417)
  ·
    refine ⟨43281501793391003094730063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57708669057854670792973417 43281501793391003094730063)
    ·
      refine ⟨64922252690086504642095095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43281501793391003094730063 64922252690086504642095095)
      ·
        refine ⟨97383379035129756963142643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64922252690086504642095095 97383379035129756963142643)
        ·
          refine ⟨146075068552694635444713965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97383379035129756963142643 146075068552694635444713965)
          ·
            refine ⟨54778150707260488291767737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146075068552694635444713965 54778150707260488291767737)
            ·
              refine ⟨41083613030445366218825803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54778150707260488291767737 41083613030445366218825803)
              ·
                refine ⟨61625419545668049328238705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41083613030445366218825803 61625419545668049328238705)
                ·
                  refine ⟨46219064659251036996179029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61625419545668049328238705 46219064659251036996179029)
                  ·
                    refine ⟨541629663975598089798973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46219064659251036996179029 541629663975598089798973)
                    ·
                      rfl

theorem cell23_3164460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_3164460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164460 prefixEnd_3164460 := by exact prefixLift 3164460
  have htrace : WordTrace (prefixWord ++ tailWord_3164460) baseStart_3164460 baseEnd_3164460 := by
    simpa [prefixWord, tailWord_3164460, baseEnd_3164460] using wordTrace_append hprefix tailTrace_3164460
  have hstable : (prefixWord ++ tailWord_3164460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164460).length < 2 ^ (prefixWord ++ tailWord_3164460).sum := by decide
  have hdescent : baseEnd_3164460 < baseStart_3164460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164501 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_3164501 : Nat := 118140960795 + 3164501 * 2 ^ 59
def prefixEnd_3164501 : Nat := 4983230072969 + 3 ^ 40 * 3164501 * 2
def baseEnd_3164501 : Nat := 1624910044633628608984231

theorem tailTrace_3164501 : CollatzResearch.WordTrace tailWord_3164501 prefixEnd_3164501 1624910044633628608984231 := by
  unfold tailWord_3164501
  simp only [CollatzResearch.WordTrace]
  refine ⟨115418833508560805588189357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76945889005707203725459571 115418833508560805588189357)
  ·
    refine ⟨43282062565710302095571009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115418833508560805588189357 43282062565710302095571009)
    ·
      refine ⟨32461546924282726571678257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43282062565710302095571009 32461546924282726571678257)
      ·
        refine ⟨24346160193212044928758693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32461546924282726571678257 24346160193212044928758693)
        ·
          refine ⟨4564905036227258424142255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24346160193212044928758693 4564905036227258424142255)
          ·
            refine ⟨6847357554340887636213383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564905036227258424142255 6847357554340887636213383)
            ·
              refine ⟨10271036331511331454320075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6847357554340887636213383 10271036331511331454320075)
              ·
                refine ⟨15406554497266997181480113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10271036331511331454320075 15406554497266997181480113)
                ·
                  refine ⟨11554915872950247886110085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15406554497266997181480113 11554915872950247886110085)
                  ·
                    refine ⟨2166546726178171478645641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11554915872950247886110085 2166546726178171478645641)
                    ·
                      refine ⟨1624910044633628608984231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166546726178171478645641 1624910044633628608984231)
                      ·
                        rfl

theorem cell23_3164501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_3164501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164501 prefixEnd_3164501 := by exact prefixLift 3164501
  have htrace : WordTrace (prefixWord ++ tailWord_3164501) baseStart_3164501 baseEnd_3164501 := by
    simpa [prefixWord, tailWord_3164501, baseEnd_3164501] using wordTrace_append hprefix tailTrace_3164501
  have hstable : (prefixWord ++ tailWord_3164501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164501).length < 2 ^ (prefixWord ++ tailWord_3164501).sum := by decide
  have hdescent : baseEnd_3164501 < baseStart_3164501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164551 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_3164551 : Nat := 118140960795 + 3164551 * 2 ^ 59
def prefixEnd_3164551 : Nat := 4983230072969 + 3 ^ 40 * 3164551 * 2
def baseEnd_3164551 : Nat := 1624935718666353413359001

theorem tailTrace_3164551 : CollatzResearch.WordTrace tailWord_3164551 prefixEnd_3164551 1624935718666353413359001 := by
  unfold tailWord_3164551
  simp only [CollatzResearch.WordTrace]
  refine ⟨115420657158379664127509507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76947104772253109418339671 115420657158379664127509507)
  ·
    refine ⟨173130985737569496191264261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115420657158379664127509507 173130985737569496191264261)
    ·
      refine ⟨32462059825794280535862049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173130985737569496191264261 32462059825794280535862049)
      ·
        refine ⟨24346544869345710401896537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32462059825794280535862049 24346544869345710401896537)
        ·
          refine ⟨18259908652009282801422403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24346544869345710401896537 18259908652009282801422403)
          ·
            refine ⟨27389862978013924202133605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18259908652009282801422403 27389862978013924202133605)
            ·
              refine ⟨5135599308377610787900051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27389862978013924202133605 5135599308377610787900051)
              ·
                refine ⟨7703398962566416181850077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135599308377610787900051 7703398962566416181850077)
                ·
                  refine ⟨2888774610962406068193779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7703398962566416181850077 2888774610962406068193779)
                  ·
                    refine ⟨4333161916443609102290669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2888774610962406068193779 4333161916443609102290669)
                    ·
                      refine ⟨1624935718666353413359001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333161916443609102290669 1624935718666353413359001)
                      ·
                        rfl

theorem cell23_3164551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_3164551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164551 prefixEnd_3164551 := by exact prefixLift 3164551
  have htrace : WordTrace (prefixWord ++ tailWord_3164551) baseStart_3164551 baseEnd_3164551 := by
    simpa [prefixWord, tailWord_3164551, baseEnd_3164551] using wordTrace_append hprefix tailTrace_3164551
  have hstable : (prefixWord ++ tailWord_3164551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164551).length < 2 ^ (prefixWord ++ tailWord_3164551).sum := by decide
  have hdescent : baseEnd_3164551 < baseStart_3164551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164594 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3164594 : Nat := 118140960795 + 3164594 * 2 ^ 59
def prefixEnd_3164594 : Nat := 4983230072969 + 3 ^ 40 * 3164594 * 2
def baseEnd_3164594 : Nat := 1624957798334496745121303

theorem tailTrace_3164594 : CollatzResearch.WordTrace tailWord_3164594 prefixEnd_3164594 1624957798334496745121303 := by
  unfold tailWord_3164594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28855556374305970617831209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76948150331482588314216557 28855556374305970617831209)
  ·
    refine ⟨21641667280729477963373407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28855556374305970617831209 21641667280729477963373407)
    ·
      refine ⟨32462500921094216945060111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21641667280729477963373407 32462500921094216945060111)
      ·
        refine ⟨48693751381641325417590167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32462500921094216945060111 48693751381641325417590167)
        ·
          refine ⟨73040627072461988126385251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48693751381641325417590167 73040627072461988126385251)
          ·
            refine ⟨109560940608692982189577877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73040627072461988126385251 109560940608692982189577877)
            ·
              refine ⟨5135669091032483540136463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109560940608692982189577877 5135669091032483540136463)
              ·
                refine ⟨7703503636548725310204695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135669091032483540136463 7703503636548725310204695)
                ·
                  refine ⟨11555255454823087965307043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7703503636548725310204695 11555255454823087965307043)
                  ·
                    refine ⟨17332883182234631947960565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11555255454823087965307043 17332883182234631947960565)
                    ·
                      refine ⟨1624957798334496745121303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17332883182234631947960565 1624957798334496745121303)
                      ·
                        rfl

theorem cell23_3164594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3164594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164594 prefixEnd_3164594 := by exact prefixLift 3164594
  have htrace : WordTrace (prefixWord ++ tailWord_3164594) baseStart_3164594 baseEnd_3164594 := by
    simpa [prefixWord, tailWord_3164594, baseEnd_3164594] using wordTrace_append hprefix tailTrace_3164594
  have hstable : (prefixWord ++ tailWord_3164594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164594).length < 2 ^ (prefixWord ++ tailWord_3164594).sum := by decide
  have hdescent : baseEnd_3164594 < baseStart_3164594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164604 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3164604 : Nat := 118140960795 + 3164604 * 2 ^ 59
def prefixEnd_3164604 : Nat := 4983230072969 + 3 ^ 40 * 3164604 * 2
def baseEnd_3164604 : Nat := 1624962933141041705996257

theorem tailTrace_3164604 : CollatzResearch.WordTrace tailWord_3164604 prefixEnd_3164604 1624962933141041705996257 := by
  unfold tailWord_3164604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57711295113593827089594433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76948393484791769452792577 57711295113593827089594433)
  ·
    refine ⟨43283471335195370317195825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57711295113593827089594433 43283471335195370317195825)
    ·
      refine ⟨32462603501396527737896869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43283471335195370317195825 32462603501396527737896869)
      ·
        refine ⟨6086738156511848950855663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32462603501396527737896869 6086738156511848950855663)
        ·
          refine ⟨9130107234767773426283495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6086738156511848950855663 9130107234767773426283495)
          ·
            refine ⟨13695160852151660139425243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130107234767773426283495 13695160852151660139425243)
            ·
              refine ⟨20542741278227490209137865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13695160852151660139425243 20542741278227490209137865)
              ·
                refine ⟨15407055958670617656853399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20542741278227490209137865 15407055958670617656853399)
                ·
                  refine ⟨23110583938005926485280099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15407055958670617656853399 23110583938005926485280099)
                  ·
                    refine ⟨34665875907008889727920149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23110583938005926485280099 34665875907008889727920149)
                    ·
                      refine ⟨1624962933141041705996257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34665875907008889727920149 1624962933141041705996257)
                      ·
                        rfl

theorem cell23_3164604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3164604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164604 prefixEnd_3164604 := by exact prefixLift 3164604
  have htrace : WordTrace (prefixWord ++ tailWord_3164604) baseStart_3164604 baseEnd_3164604 := by
    simpa [prefixWord, tailWord_3164604, baseEnd_3164604] using wordTrace_append hprefix tailTrace_3164604
  have hstable : (prefixWord ++ tailWord_3164604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164604).length < 2 ^ (prefixWord ++ tailWord_3164604).sum := by decide
  have hdescent : baseEnd_3164604 < baseStart_3164604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164628 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3164628 : Nat := 118140960795 + 3164628 * 2 ^ 59
def prefixEnd_3164628 : Nat := 4983230072969 + 3 ^ 40 * 3164628 * 2
def baseEnd_3164628 : Nat := 1624975256676749612096147

theorem tailTrace_3164628 : CollatzResearch.WordTrace tailWord_3164628 prefixEnd_3164628 1624975256676749612096147 := by
  unfold tailWord_3164628
  simp only [CollatzResearch.WordTrace]
  refine ⟨57711732789550353139031269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76948977052733804185375025 57711732789550353139031269)
  ·
    refine ⟨10820949898040691213568363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57711732789550353139031269 10820949898040691213568363)
    ·
      refine ⟨16231424847061036820352545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10820949898040691213568363 16231424847061036820352545)
      ·
        refine ⟨12173568635295777615264409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16231424847061036820352545 12173568635295777615264409)
        ·
          refine ⟨9130176476471833211448307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12173568635295777615264409 9130176476471833211448307)
          ·
            refine ⟨13695264714707749817172461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130176476471833211448307 13695264714707749817172461)
            ·
              refine ⟨5135724268015406181439673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13695264714707749817172461 5135724268015406181439673)
              ·
                refine ⟨3851793201011554636079755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5135724268015406181439673 3851793201011554636079755)
                ·
                  refine ⟨5777689801517331954119633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851793201011554636079755 5777689801517331954119633)
                  ·
                    refine ⟨4333267351137998965589725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5777689801517331954119633 4333267351137998965589725)
                    ·
                      refine ⟨1624975256676749612096147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333267351137998965589725 1624975256676749612096147)
                      ·
                        rfl

theorem cell23_3164628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3164628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164628 prefixEnd_3164628 := by exact prefixLift 3164628
  have htrace : WordTrace (prefixWord ++ tailWord_3164628) baseStart_3164628 baseEnd_3164628 := by
    simpa [prefixWord, tailWord_3164628, baseEnd_3164628] using wordTrace_append hprefix tailTrace_3164628
  have hstable : (prefixWord ++ tailWord_3164628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164628).length < 2 ^ (prefixWord ++ tailWord_3164628).sum := by decide
  have hdescent : baseEnd_3164628 < baseStart_3164628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164642 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3164642 : Nat := 118140960795 + 3164642 * 2 ^ 59
def prefixEnd_3164642 : Nat := 4983230072969 + 3 ^ 40 * 3164642 * 2
def baseEnd_3164642 : Nat := 1624982445405912557321083

theorem tailTrace_3164642 : CollatzResearch.WordTrace tailWord_3164642 prefixEnd_3164642 1624982445405912557321083 := by
  unfold tailWord_3164642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28855994050262496667268045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76949317467366657779381453 28855994050262496667268045)
  ·
    refine ⟨10820997768848436250225517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28855994050262496667268045 10820997768848436250225517)
    ·
      refine ⟨4057874163318163593834569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10820997768848436250225517 4057874163318163593834569)
      ·
        refine ⟨3043405622488622695375927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4057874163318163593834569 3043405622488622695375927)
        ·
          refine ⟨4565108433732934043063891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043405622488622695375927 4565108433732934043063891)
          ·
            refine ⟨6847662650599401064595837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565108433732934043063891 6847662650599401064595837)
            ·
              refine ⟨2567873493974775399223439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6847662650599401064595837 2567873493974775399223439)
              ·
                refine ⟨3851810240962163098835159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567873493974775399223439 3851810240962163098835159)
                ·
                  refine ⟨5777715361443244648252739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851810240962163098835159 5777715361443244648252739)
                  ·
                    refine ⟨8666573042164866972379109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5777715361443244648252739 8666573042164866972379109)
                    ·
                      refine ⟨1624982445405912557321083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8666573042164866972379109 1624982445405912557321083)
                      ·
                        rfl

theorem cell23_3164642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3164642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164642 prefixEnd_3164642 := by exact prefixLift 3164642
  have htrace : WordTrace (prefixWord ++ tailWord_3164642) baseStart_3164642 baseEnd_3164642 := by
    simpa [prefixWord, tailWord_3164642, baseEnd_3164642] using wordTrace_append hprefix tailTrace_3164642
  have hstable : (prefixWord ++ tailWord_3164642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164642).length < 2 ^ (prefixWord ++ tailWord_3164642).sum := by decide
  have hdescent : baseEnd_3164642 < baseStart_3164642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164645 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 1, 2, 3]
def baseStart_3164645 : Nat := 118140960795 + 3164645 * 2 ^ 59
def prefixEnd_3164645 : Nat := 4983230072969 + 3 ^ 40 * 3164645 * 2
def baseEnd_3164645 : Nat := 1624983985847876045583569

theorem tailTrace_3164645 : CollatzResearch.WordTrace tailWord_3164645 prefixEnd_3164645 1624983985847876045583569 := by
  unfold tailWord_3164645
  simp only [CollatzResearch.WordTrace]
  refine ⟨115424085620039118181431389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76949390413359412120954259 115424085620039118181431389)
  ·
    refine ⟨43284032107514669318036771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115424085620039118181431389 43284032107514669318036771)
    ·
      refine ⟨64926048161272003977055157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43284032107514669318036771 64926048161272003977055157)
      ·
        refine ⟨6086817015119250372848921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64926048161272003977055157 6086817015119250372848921)
        ·
          refine ⟨4565112761339437779636691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6086817015119250372848921 4565112761339437779636691)
          ·
            refine ⟨6847669142009156669455037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565112761339437779636691 6847669142009156669455037)
            ·
              refine ⟨2567875928253433751045639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6847669142009156669455037 2567875928253433751045639)
              ·
                refine ⟨3851813892380150626568459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567875928253433751045639 3851813892380150626568459)
                ·
                  refine ⟨5777720838570225939852689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851813892380150626568459 5777720838570225939852689)
                  ·
                    refine ⟨4333290628927669454889517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5777720838570225939852689 4333290628927669454889517)
                    ·
                      refine ⟨1624983985847876045583569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333290628927669454889517 1624983985847876045583569)
                      ·
                        rfl

theorem cell23_3164645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_3164645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164645 prefixEnd_3164645 := by exact prefixLift 3164645
  have htrace : WordTrace (prefixWord ++ tailWord_3164645) baseStart_3164645 baseEnd_3164645 := by
    simpa [prefixWord, tailWord_3164645, baseEnd_3164645] using wordTrace_append hprefix tailTrace_3164645
  have hstable : (prefixWord ++ tailWord_3164645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164645).length < 2 ^ (prefixWord ++ tailWord_3164645).sum := by decide
  have hdescent : baseEnd_3164645 < baseStart_3164645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164687 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 9]
def baseStart_3164687 : Nat := 118140960795 + 3164687 * 2 ^ 59
def prefixEnd_3164687 : Nat := 4983230072969 + 3 ^ 40 * 3164687 * 2
def baseEnd_3164687 : Nat := 180556172448373875695375

theorem tailTrace_3164687 : CollatzResearch.WordTrace tailWord_3164687 prefixEnd_3164687 180556172448373875695375 := by
  unfold tailWord_3164687
  simp only [CollatzResearch.WordTrace]
  refine ⟨115425617485886959354460315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76950411657257972902973543 115425617485886959354460315)
  ·
    refine ⟨173138426228830439031690473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115425617485886959354460315 173138426228830439031690473)
    ·
      refine ⟨129853819671622829273767855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173138426228830439031690473 129853819671622829273767855)
      ·
        refine ⟨194780729507434243910651783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129853819671622829273767855 194780729507434243910651783)
        ·
          refine ⟨292171094261151365865977675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194780729507434243910651783 292171094261151365865977675)
          ·
            refine ⟨438256641391727048798966513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292171094261151365865977675 438256641391727048798966513)
            ·
              refine ⟨328692481043795286599224885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438256641391727048798966513 328692481043795286599224885)
              ·
                refine ⟨30814920097855808118677333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 328692481043795286599224885 30814920097855808118677333)
                ·
                  refine ⟨180556172448373875695375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30814920097855808118677333 180556172448373875695375)
                  ·
                    rfl

theorem cell23_3164687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 9].length) (baseStart_3164687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164687 prefixEnd_3164687 := by exact prefixLift 3164687
  have htrace : WordTrace (prefixWord ++ tailWord_3164687) baseStart_3164687 baseEnd_3164687 := by
    simpa [prefixWord, tailWord_3164687, baseEnd_3164687] using wordTrace_append hprefix tailTrace_3164687
  have hstable : (prefixWord ++ tailWord_3164687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164687).length < 2 ^ (prefixWord ++ tailWord_3164687).sum := by decide
  have hdescent : baseEnd_3164687 < baseStart_3164687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164721 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 5]
def baseStart_3164721 : Nat := 118140960795 + 3164721 * 2 ^ 59
def prefixEnd_3164721 : Nat := 4983230072969 + 3 ^ 40 * 3164721 * 2
def baseEnd_3164721 : Nat := 180558112264179749803691

theorem tailTrace_3164721 : CollatzResearch.WordTrace tailWord_3164721 prefixEnd_3164721 180558112264179749803691 := by
  unfold tailWord_3164721
  simp only [CollatzResearch.WordTrace]
  refine ⟨115426857567763783161198017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76951238378509188774132011 115426857567763783161198017)
  ·
    refine ⟨86570143175822837370898513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115426857567763783161198017 86570143175822837370898513)
    ·
      refine ⟨64927607381867128028173885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86570143175822837370898513 64927607381867128028173885)
      ·
        refine ⟨24347852768200173010565207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64927607381867128028173885 24347852768200173010565207)
        ·
          refine ⟨36521779152300259515847811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24347852768200173010565207 36521779152300259515847811)
          ·
            refine ⟨54782668728450389273771717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36521779152300259515847811 54782668728450389273771717)
            ·
              refine ⟨10271750386584447988832197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54782668728450389273771717 10271750386584447988832197)
              ·
                refine ⟨1925953197484583997906037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10271750386584447988832197 1925953197484583997906037)
                ·
                  refine ⟨180558112264179749803691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1925953197484583997906037 180558112264179749803691)
                  ·
                    rfl

theorem cell23_3164721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 5].length) (baseStart_3164721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164721 prefixEnd_3164721 := by exact prefixLift 3164721
  have htrace : WordTrace (prefixWord ++ tailWord_3164721) baseStart_3164721 baseEnd_3164721 := by
    simpa [prefixWord, tailWord_3164721, baseEnd_3164721] using wordTrace_append hprefix tailTrace_3164721
  have hstable : (prefixWord ++ tailWord_3164721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164721).length < 2 ^ (prefixWord ++ tailWord_3164721).sum := by decide
  have hdescent : baseEnd_3164721 < baseStart_3164721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164732 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_3164732 : Nat := 118140960795 + 3164732 * 2 ^ 59
def prefixEnd_3164732 : Nat := 4983230072969 + 3 ^ 40 * 3164732 * 2
def baseEnd_3164732 : Nat := 1625028658664817205195669

theorem tailTrace_3164732 : CollatzResearch.WordTrace tailWord_3164732 prefixEnd_3164732 1625028658664817205195669 := by
  unfold tailWord_3164732
  simp only [CollatzResearch.WordTrace]
  refine ⟨57713629385361966019924225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76951505847149288026565633 57713629385361966019924225)
  ·
    refine ⟨43285222039021474514943169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57713629385361966019924225 43285222039021474514943169)
    ·
      refine ⟨32463916529266105886207377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43285222039021474514943169 32463916529266105886207377)
      ·
        refine ⟨24347937396949579414655533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32463916529266105886207377 24347937396949579414655533)
        ·
          refine ⟨9130476523856092280495825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24347937396949579414655533 9130476523856092280495825)
          ·
            refine ⟨6847857392892069210371869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9130476523856092280495825 6847857392892069210371869)
            ·
              refine ⟨2567946522334525953889451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6847857392892069210371869 2567946522334525953889451)
              ·
                refine ⟨3851919783501788930834177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567946522334525953889451 3851919783501788930834177)
                ·
                  refine ⟨2888939837626341698125633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3851919783501788930834177 2888939837626341698125633)
                  ·
                    refine ⟨2166704878219756273594225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2888939837626341698125633 2166704878219756273594225)
                    ·
                      refine ⟨1625028658664817205195669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166704878219756273594225 1625028658664817205195669)
                      ·
                        rfl

theorem cell23_3164732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_3164732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164732 prefixEnd_3164732 := by exact prefixLift 3164732
  have htrace : WordTrace (prefixWord ++ tailWord_3164732) baseStart_3164732 baseEnd_3164732 := by
    simpa [prefixWord, tailWord_3164732, baseEnd_3164732] using wordTrace_append hprefix tailTrace_3164732
  have hstable : (prefixWord ++ tailWord_3164732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164732).length < 2 ^ (prefixWord ++ tailWord_3164732).sum := by decide
  have hdescent : baseEnd_3164732 < baseStart_3164732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164771 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3164771 : Nat := 118140960795 + 3164771 * 2 ^ 59
def prefixEnd_3164771 : Nat := 4983230072969 + 3 ^ 40 * 3164771 * 2
def baseEnd_3164771 : Nat := 1625048684410342552607989

theorem tailTrace_3164771 : CollatzResearch.WordTrace tailWord_3164771 prefixEnd_3164771 1625048684410342552607989 := by
  unfold tailWord_3164771
  simp only [CollatzResearch.WordTrace]
  refine ⟨115428681217582641700518167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76952454145055094467012111 115428681217582641700518167)
  ·
    refine ⟨173143021826373962550777251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115428681217582641700518167 173143021826373962550777251)
    ·
      refine ⟨259714532739560943826165877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173143021826373962550777251 259714532739560943826165877)
      ·
        refine ⟨24348237444333838483703051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259714532739560943826165877 24348237444333838483703051)
        ·
          refine ⟨36522356166500757725554577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24348237444333838483703051 36522356166500757725554577)
          ·
            refine ⟨27391767124875568294165933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36522356166500757725554577 27391767124875568294165933)
            ·
              refine ⟨10271912671828338110312225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27391767124875568294165933 10271912671828338110312225)
              ·
                refine ⟨7703934503871253582734169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10271912671828338110312225 7703934503871253582734169)
                ·
                  refine ⟨5777950877903440187050627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7703934503871253582734169 5777950877903440187050627)
                  ·
                    refine ⟨8666926316855160280575941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5777950877903440187050627 8666926316855160280575941)
                    ·
                      refine ⟨1625048684410342552607989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8666926316855160280575941 1625048684410342552607989)
                      ·
                        rfl

theorem cell23_3164771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3164771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164771 prefixEnd_3164771 := by exact prefixLift 3164771
  have htrace : WordTrace (prefixWord ++ tailWord_3164771) baseStart_3164771 baseEnd_3164771 := by
    simpa [prefixWord, tailWord_3164771, baseEnd_3164771] using wordTrace_append hprefix tailTrace_3164771
  have hstable : (prefixWord ++ tailWord_3164771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164771).length < 2 ^ (prefixWord ++ tailWord_3164771).sum := by decide
  have hdescent : baseEnd_3164771 < baseStart_3164771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164828 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 6]
def baseStart_3164828 : Nat := 118140960795 + 3164828 * 2 ^ 59
def prefixEnd_3164828 : Nat := 4983230072969 + 3 ^ 40 * 3164828 * 2
def baseEnd_3164828 : Nat := 180564216978627647732803

theorem tailTrace_3164828 : CollatzResearch.WordTrace tailWord_3164828 prefixEnd_3164828 180564216978627647732803 := by
  unfold tailWord_3164828
  simp only [CollatzResearch.WordTrace]
  refine ⟨57715380089188070217671569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76953840118917426956895425 57715380089188070217671569)
  ·
    refine ⟨43286535066891052663253677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57715380089188070217671569 43286535066891052663253677)
    ·
      refine ⟨16232450650084144748720129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43286535066891052663253677 16232450650084144748720129)
      ·
        refine ⟨12174337987563108561540097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16232450650084144748720129 12174337987563108561540097)
        ·
          refine ⟨9130753490672331421155073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12174337987563108561540097 9130753490672331421155073)
          ·
            refine ⟨6848065118004248565866305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9130753490672331421155073 6848065118004248565866305)
            ·
              refine ⟨5136048838503186424399729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848065118004248565866305 5136048838503186424399729)
              ·
                refine ⟨3852036628877389818299797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136048838503186424399729 3852036628877389818299797)
                ·
                  refine ⟨180564216978627647732803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3852036628877389818299797 180564216978627647732803)
                  ·
                    rfl

theorem cell23_3164828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_3164828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164828 prefixEnd_3164828 := by exact prefixLift 3164828
  have htrace : WordTrace (prefixWord ++ tailWord_3164828) baseStart_3164828 baseEnd_3164828 := by
    simpa [prefixWord, tailWord_3164828, baseEnd_3164828] using wordTrace_append hprefix tailTrace_3164828
  have hstable : (prefixWord ++ tailWord_3164828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164828).length < 2 ^ (prefixWord ++ tailWord_3164828).sum := by decide
  have hdescent : baseEnd_3164828 < baseStart_3164828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164855 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_3164855 : Nat := 118140960795 + 3164855 * 2 ^ 59
def prefixEnd_3164855 : Nat := 4983230072969 + 3 ^ 40 * 3164855 * 2
def baseEnd_3164855 : Nat := 1625091816785320223957603

theorem tailTrace_3164855 : CollatzResearch.WordTrace tailWord_3164855 prefixEnd_3164855 1625091816785320223957603 := by
  unfold tailWord_3164855
  simp only [CollatzResearch.WordTrace]
  refine ⟨115431744949278324046576019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76954496632852216031050679 115431744949278324046576019)
  ·
    refine ⟨173147617423917486069864029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115431744949278324046576019 173147617423917486069864029)
    ·
      refine ⟨64930356533969057276199011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173147617423917486069864029 64930356533969057276199011)
      ·
        refine ⟨97395534800953585914298517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64930356533969057276199011 97395534800953585914298517)
        ·
          refine ⟨4565415693794699339732743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97395534800953585914298517 4565415693794699339732743)
          ·
            refine ⟨6848123540692049009599115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565415693794699339732743 6848123540692049009599115)
            ·
              refine ⟨10272185311038073514398673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848123540692049009599115 10272185311038073514398673)
              ·
                refine ⟨7704138983278555135799005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10272185311038073514398673 7704138983278555135799005)
                ·
                  refine ⟨2889052118729458175924627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7704138983278555135799005 2889052118729458175924627)
                  ·
                    refine ⟨4333578178094187263886941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889052118729458175924627 4333578178094187263886941)
                    ·
                      refine ⟨1625091816785320223957603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333578178094187263886941 1625091816785320223957603)
                      ·
                        rfl

theorem cell23_3164855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_3164855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164855 prefixEnd_3164855 := by exact prefixLift 3164855
  have htrace : WordTrace (prefixWord ++ tailWord_3164855) baseStart_3164855 baseEnd_3164855 := by
    simpa [prefixWord, tailWord_3164855, baseEnd_3164855] using wordTrace_append hprefix tailTrace_3164855
  have hstable : (prefixWord ++ tailWord_3164855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164855).length < 2 ^ (prefixWord ++ tailWord_3164855).sum := by decide
  have hdescent : baseEnd_3164855 < baseStart_3164855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164872 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_3164872 : Nat := 118140960795 + 3164872 * 2 ^ 59
def prefixEnd_3164872 : Nat := 4983230072969 + 3 ^ 40 * 3164872 * 2
def baseEnd_3164872 : Nat := 1625100545956446657445025

theorem tailTrace_3164872 : CollatzResearch.WordTrace tailWord_3164872 prefixEnd_3164872 1625100545956446657445025 := by
  unfold tailWord_3164872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57716182495108367974972435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76954909993477823966629913 57716182495108367974972435)
  ·
    refine ⟨86574273742662551962458653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57716182495108367974972435 86574273742662551962458653)
    ·
      refine ⟨32465352653498456985921995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86574273742662551962458653 32465352653498456985921995)
      ·
        refine ⟨48698028980247685478882993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32465352653498456985921995 48698028980247685478882993)
        ·
          refine ⟨36523521735185764109162245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48698028980247685478882993 36523521735185764109162245)
          ·
            refine ⟨6848160325347330770467921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36523521735185764109162245 6848160325347330770467921)
            ·
              refine ⟨5136120244010498077850941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848160325347330770467921 5136120244010498077850941)
              ·
                refine ⟨1926045091503936779194103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5136120244010498077850941 1926045091503936779194103)
                ·
                  refine ⟨2889067637255905168791155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926045091503936779194103 2889067637255905168791155)
                  ·
                    refine ⟨4333601455883857753186733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889067637255905168791155 4333601455883857753186733)
                    ·
                      refine ⟨1625100545956446657445025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333601455883857753186733 1625100545956446657445025)
                      ·
                        rfl

theorem cell23_3164872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_3164872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164872 prefixEnd_3164872 := by exact prefixLift 3164872
  have htrace : WordTrace (prefixWord ++ tailWord_3164872) baseStart_3164872 baseEnd_3164872 := by
    simpa [prefixWord, tailWord_3164872, baseEnd_3164872] using wordTrace_append hprefix tailTrace_3164872
  have hstable : (prefixWord ++ tailWord_3164872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164872).length < 2 ^ (prefixWord ++ tailWord_3164872).sum := by decide
  have hdescent : baseEnd_3164872 < baseStart_3164872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164881 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_3164881 : Nat := 118140960795 + 3164881 * 2 ^ 59
def prefixEnd_3164881 : Nat := 4983230072969 + 3 ^ 40 * 3164881 * 2
def baseEnd_3164881 : Nat := 1625105167282337122232483

theorem tailTrace_3164881 : CollatzResearch.WordTrace tailWord_3164881 prefixEnd_3164881 1625105167282337122232483 := by
  unfold tailWord_3164881
  simp only [CollatzResearch.WordTrace]
  refine ⟨115432693247184130487022497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76955128831456086991348331 115432693247184130487022497)
  ·
    refine ⟨86574519935388097865266873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115432693247184130487022497 86574519935388097865266873)
    ·
      refine ⟨64930889951541073398950155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86574519935388097865266873 64930889951541073398950155)
      ·
        refine ⟨97396334927311610098425233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64930889951541073398950155 97396334927311610098425233)
        ·
          refine ⟨73047251195483707573818925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97396334927311610098425233 73047251195483707573818925)
          ·
            refine ⟨27392719198306390340182097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73047251195483707573818925 27392719198306390340182097)
            ·
              refine ⟨20544539398729792755136573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27392719198306390340182097 20544539398729792755136573)
              ·
                refine ⟨7704202274523672283176215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20544539398729792755136573 7704202274523672283176215)
                ·
                  refine ⟨11556303411785508424764323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7704202274523672283176215 11556303411785508424764323)
                  ·
                    refine ⟨17334455117678262637146485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11556303411785508424764323 17334455117678262637146485)
                    ·
                      refine ⟨1625105167282337122232483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17334455117678262637146485 1625105167282337122232483)
                      ·
                        rfl

theorem cell23_3164881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_3164881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164881 prefixEnd_3164881 := by exact prefixLift 3164881
  have htrace : WordTrace (prefixWord ++ tailWord_3164881) baseStart_3164881 baseEnd_3164881 := by
    simpa [prefixWord, tailWord_3164881, baseEnd_3164881] using wordTrace_append hprefix tailTrace_3164881
  have hstable : (prefixWord ++ tailWord_3164881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164881).length < 2 ^ (prefixWord ++ tailWord_3164881).sum := by decide
  have hdescent : baseEnd_3164881 < baseStart_3164881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164888 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 4, 4]
def baseStart_3164888 : Nat := 118140960795 + 3164888 * 2 ^ 59
def prefixEnd_3164888 : Nat := 4983230072969 + 3 ^ 40 * 3164888 * 2
def baseEnd_3164888 : Nat := 541702920548972864948317

theorem tailTrace_3164888 : CollatzResearch.WordTrace tailWord_3164888 prefixEnd_3164888 541702920548972864948317 := by
  unfold tailWord_3164888
  simp only [CollatzResearch.WordTrace]
  refine ⟨57716474279079385341263659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76955299038772513788351545 57716474279079385341263659)
  ·
    refine ⟨86574711418619078011895489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57716474279079385341263659 86574711418619078011895489)
    ·
      refine ⟨64931033563964308508921617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86574711418619078011895489 64931033563964308508921617)
      ·
        refine ⟨48698275172973231381691213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64931033563964308508921617 48698275172973231381691213)
        ·
          refine ⟨18261853189864961768134205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48698275172973231381691213 18261853189864961768134205)
          ·
            refine ⟨6848194946199360663050327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18261853189864961768134205 6848194946199360663050327)
            ·
              refine ⟨10272292419299040994575491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848194946199360663050327 10272292419299040994575491)
              ·
                refine ⟨15408438628948561491863237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10272292419299040994575491 15408438628948561491863237)
                ·
                  refine ⟨2889082242927855279724357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15408438628948561491863237 2889082242927855279724357)
                  ·
                    refine ⟨541702920548972864948317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2889082242927855279724357 541702920548972864948317)
                    ·
                      rfl

theorem cell23_3164888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_3164888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164888 prefixEnd_3164888 := by exact prefixLift 3164888
  have htrace : WordTrace (prefixWord ++ tailWord_3164888) baseStart_3164888 baseEnd_3164888 := by
    simpa [prefixWord, tailWord_3164888, baseEnd_3164888] using wordTrace_append hprefix tailTrace_3164888
  have hstable : (prefixWord ++ tailWord_3164888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164888).length < 2 ^ (prefixWord ++ tailWord_3164888).sum := by decide
  have hdescent : baseEnd_3164888 < baseStart_3164888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164895 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 3, 2, 2]
def baseStart_3164895 : Nat := 118140960795 + 3164895 * 2 ^ 59
def prefixEnd_3164895 : Nat := 4983230072969 + 3 ^ 40 * 3164895 * 2
def baseEnd_3164895 : Nat := 1625112356011500067457419

theorem tailTrace_3164895 : CollatzResearch.WordTrace tailWord_3164895 prefixEnd_3164895 1625112356011500067457419 := by
  unfold tailWord_3164895
  simp only [CollatzResearch.WordTrace]
  refine ⟨115433203869133410878032139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76955469246088940585354759 115433203869133410878032139)
  ·
    refine ⟨173149805803700116317048209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115433203869133410878032139 173149805803700116317048209)
    ·
      refine ⟨129862354352775087237786157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173149805803700116317048209 129862354352775087237786157)
      ·
        refine ⟨48698382882290657714169809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129862354352775087237786157 48698382882290657714169809)
        ·
          refine ⟨36523787161717993285627357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48698382882290657714169809 36523787161717993285627357)
          ·
            refine ⟨13696420185644247482110259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36523787161717993285627357 13696420185644247482110259)
            ·
              refine ⟨20544630278466371223165389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13696420185644247482110259 20544630278466371223165389)
              ·
                refine ⟨7704236354424889208687021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20544630278466371223165389 7704236354424889208687021)
                ·
                  refine ⟨2889088632909333453257633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7704236354424889208687021 2889088632909333453257633)
                  ·
                    refine ⟨2166816474682000089943225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2889088632909333453257633 2166816474682000089943225)
                    ·
                      refine ⟨1625112356011500067457419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166816474682000089943225 1625112356011500067457419)
                      ·
                        rfl

theorem cell23_3164895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_3164895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164895 prefixEnd_3164895 := by exact prefixLift 3164895
  have htrace : WordTrace (prefixWord ++ tailWord_3164895) baseStart_3164895 baseEnd_3164895 := by
    simpa [prefixWord, tailWord_3164895, baseEnd_3164895] using wordTrace_append hprefix tailTrace_3164895
  have hstable : (prefixWord ++ tailWord_3164895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164895).length < 2 ^ (prefixWord ++ tailWord_3164895).sum := by decide
  have hdescent : baseEnd_3164895 < baseStart_3164895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164946 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3164946 : Nat := 118140960795 + 3164946 * 2 ^ 59
def prefixEnd_3164946 : Nat := 4983230072969 + 3 ^ 40 * 3164946 * 2
def baseEnd_3164946 : Nat := 1625138543524879367919685

theorem tailTrace_3164946 : CollatzResearch.WordTrace tailWord_3164946 prefixEnd_3164946 1625138543524879367919685 := by
  unfold tailWord_3164946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28858765997987161647034673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76956709327965764392092461 28858765997987161647034673)
  ·
    refine ⟨21644074498490371235276005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28858765997987161647034673 21644074498490371235276005)
    ·
      refine ⟨4058263968466944606614251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21644074498490371235276005 4058263968466944606614251)
      ·
        refine ⟨6087395952700416909921377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058263968466944606614251 6087395952700416909921377)
        ·
          refine ⟨4565546964525312682441033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087395952700416909921377 4565546964525312682441033)
          ·
            refine ⟨3424160223393984511830775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4565546964525312682441033 3424160223393984511830775)
            ·
              refine ⟨5136240335090976767746163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424160223393984511830775 5136240335090976767746163)
              ·
                refine ⟨7704360502636465151619245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136240335090976767746163 7704360502636465151619245)
                ·
                  refine ⟨2889135188488674431857217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7704360502636465151619245 2889135188488674431857217)
                  ·
                    refine ⟨2166851391366505823892913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2889135188488674431857217 2166851391366505823892913)
                    ·
                      refine ⟨1625138543524879367919685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2166851391366505823892913 1625138543524879367919685)
                      ·
                        rfl

theorem cell23_3164946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3164946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164946 prefixEnd_3164946 := by exact prefixLift 3164946
  have htrace : WordTrace (prefixWord ++ tailWord_3164946) baseStart_3164946 baseEnd_3164946 := by
    simpa [prefixWord, tailWord_3164946, baseEnd_3164946] using wordTrace_append hprefix tailTrace_3164946
  have hstable : (prefixWord ++ tailWord_3164946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164946).length < 2 ^ (prefixWord ++ tailWord_3164946).sum := by decide
  have hdescent : baseEnd_3164946 < baseStart_3164946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164961 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3164961 : Nat := 118140960795 + 3164961 * 2 ^ 59
def prefixEnd_3164961 : Nat := 4983230072969 + 3 ^ 40 * 3164961 * 2
def baseEnd_3164961 : Nat := 541715415244898936410705

theorem tailTrace_3164961 : CollatzResearch.WordTrace tailWord_3164961 prefixEnd_3164961 541715415244898936410705 := by
  unfold tailWord_3164961
  simp only [CollatzResearch.WordTrace]
  refine ⟨115435611086894304149934737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76957074057929536099956491 115435611086894304149934737)
  ·
    refine ⟨86576708315170728112451053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115435611086894304149934737 86576708315170728112451053)
    ·
      refine ⟨32466265618189023042169145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86576708315170728112451053 32466265618189023042169145)
      ·
        refine ⟨24349699213641767281626859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32466265618189023042169145 24349699213641767281626859)
        ·
          refine ⟨36524548820462650922440289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24349699213641767281626859 36524548820462650922440289)
          ·
            refine ⟨27393411615346988191830217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36524548820462650922440289 27393411615346988191830217)
            ·
              refine ⟨20545058711510241143872663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27393411615346988191830217 20545058711510241143872663)
              ·
                refine ⟨30817588067265361715808995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20545058711510241143872663 30817588067265361715808995)
                ·
                  refine ⟨46226382100898042573713493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30817588067265361715808995 46226382100898042573713493)
                  ·
                    refine ⟨541715415244898936410705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46226382100898042573713493 541715415244898936410705)
                    ·
                      rfl

theorem cell23_3164961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3164961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164961 prefixEnd_3164961 := by exact prefixLift 3164961
  have htrace : WordTrace (prefixWord ++ tailWord_3164961) baseStart_3164961 baseEnd_3164961 := by
    simpa [prefixWord, tailWord_3164961, baseEnd_3164961] using wordTrace_append hprefix tailTrace_3164961
  have hstable : (prefixWord ++ tailWord_3164961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164961).length < 2 ^ (prefixWord ++ tailWord_3164961).sum := by decide
  have hdescent : baseEnd_3164961 < baseStart_3164961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164962 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3164962 : Nat := 118140960795 + 3164962 * 2 ^ 59
def prefixEnd_3164962 : Nat := 4983230072969 + 3 ^ 40 * 3164962 * 2
def baseEnd_3164962 : Nat := 1625146759215351305319611

theorem tailTrace_3164962 : CollatzResearch.WordTrace tailWord_3164962 prefixEnd_3164962 1625146759215351305319611 := by
  unfold tailWord_3164962
  simp only [CollatzResearch.WordTrace]
  refine ⟨28858911889972670330180285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76957098373260454213814093 28858911889972670330180285)
  ·
    refine ⟨10822091958739751373817607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28858911889972670330180285 10822091958739751373817607)
    ·
      refine ⟨16233137938109627060726411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822091958739751373817607 16233137938109627060726411)
      ·
        refine ⟨24349706907164440591089617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233137938109627060726411 24349706907164440591089617)
        ·
          refine ⟨18262280180373330443317213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24349706907164440591089617 18262280180373330443317213)
          ·
            refine ⟨6848355067639998916243955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18262280180373330443317213 6848355067639998916243955)
            ·
              refine ⟨10272532601459998374365933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848355067639998916243955 10272532601459998374365933)
              ·
                refine ⟨3852199725547499390387225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10272532601459998374365933 3852199725547499390387225)
                ·
                  refine ⟨2889149794160624542790419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852199725547499390387225 2889149794160624542790419)
                  ·
                    refine ⟨4333724691240936814185629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889149794160624542790419 4333724691240936814185629)
                    ·
                      refine ⟨1625146759215351305319611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333724691240936814185629 1625146759215351305319611)
                      ·
                        rfl

theorem cell23_3164962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3164962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164962 prefixEnd_3164962 := by exact prefixLift 3164962
  have htrace : WordTrace (prefixWord ++ tailWord_3164962) baseStart_3164962 baseEnd_3164962 := by
    simpa [prefixWord, tailWord_3164962, baseEnd_3164962] using wordTrace_append hprefix tailTrace_3164962
  have hstable : (prefixWord ++ tailWord_3164962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164962).length < 2 ^ (prefixWord ++ tailWord_3164962).sum := by decide
  have hdescent : baseEnd_3164962 < baseStart_3164962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164971 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5]
def baseStart_3164971 : Nat := 118140960795 + 3164971 * 2 ^ 59
def prefixEnd_3164971 : Nat := 4983230072969 + 3 ^ 40 * 3164971 * 2
def baseEnd_3164971 : Nat := 1625151380541241770107069

theorem tailTrace_3164971 : CollatzResearch.WordTrace tailWord_3164971 prefixEnd_3164971 1625151380541241770107069 := by
  unfold tailWord_3164971
  simp only [CollatzResearch.WordTrace]
  refine ⟨115435975816858075857798767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76957317211238717238532511 115435975816858075857798767)
  ·
    refine ⟨173153963725287113786698151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115435975816858075857798767 173153963725287113786698151)
    ·
      refine ⟨259730945587930670680047227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173153963725287113786698151 259730945587930670680047227)
      ·
        refine ⟨389596418381896006020070841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259730945587930670680047227 389596418381896006020070841)
        ·
          refine ⟨292197313786422004515053131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389596418381896006020070841 292197313786422004515053131)
          ·
            refine ⟨438295970679633006772579697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292197313786422004515053131 438295970679633006772579697)
            ·
              refine ⟨328721978009724755079434773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438295970679633006772579697 328721978009724755079434773)
              ·
                refine ⟨15408842719205847894348505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 328721978009724755079434773 15408842719205847894348505)
                ·
                  refine ⟨11556632039404385920761379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15408842719205847894348505 11556632039404385920761379)
                  ·
                    refine ⟨17334948059106578881142069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11556632039404385920761379 17334948059106578881142069)
                    ·
                      refine ⟨1625151380541241770107069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17334948059106578881142069 1625151380541241770107069)
                      ·
                        rfl

theorem cell23_3164971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_3164971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164971 prefixEnd_3164971 := by exact prefixLift 3164971
  have htrace : WordTrace (prefixWord ++ tailWord_3164971) baseStart_3164971 baseEnd_3164971 := by
    simpa [prefixWord, tailWord_3164971, baseEnd_3164971] using wordTrace_append hprefix tailTrace_3164971
  have hstable : (prefixWord ++ tailWord_3164971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164971).length < 2 ^ (prefixWord ++ tailWord_3164971).sum := by decide
  have hdescent : baseEnd_3164971 < baseStart_3164971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3164996 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3164996 : Nat := 118140960795 + 3164996 * 2 ^ 59
def prefixEnd_3164996 : Nat := 4983230072969 + 3 ^ 40 * 3164996 * 2
def baseEnd_3164996 : Nat := 1625164217557604172294455

theorem tailTrace_3164996 : CollatzResearch.WordTrace tailWord_3164996 prefixEnd_3164996 1625164217557604172294455 := by
  unfold tailWord_3164996
  simp only [CollatzResearch.WordTrace]
  refine ⟨57718443820883752563729421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76957925094511670084972561 57718443820883752563729421)
  ·
    refine ⟨21644416432831407211398533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57718443820883752563729421 21644416432831407211398533)
    ·
      refine ⟨4058328081155888852137225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21644416432831407211398533 4058328081155888852137225)
      ·
        refine ⟨3043746060866916639102919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4058328081155888852137225 3043746060866916639102919)
        ·
          refine ⟨4565619091300374958654379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043746060866916639102919 4565619091300374958654379)
          ·
            refine ⟨6848428636950562437981569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565619091300374958654379 6848428636950562437981569)
            ·
              refine ⟨5136321477712921828486177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848428636950562437981569 5136321477712921828486177)
              ·
                refine ⟨3852241108284691371364633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136321477712921828486177 3852241108284691371364633)
                ·
                  refine ⟨2889180831213518528523475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852241108284691371364633 2889180831213518528523475)
                  ·
                    refine ⟨4333771246820277792785213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889180831213518528523475 4333771246820277792785213)
                    ·
                      refine ⟨1625164217557604172294455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333771246820277792785213 1625164217557604172294455)
                      ·
                        rfl

theorem cell23_3164996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3164996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3164996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3164996 prefixEnd_3164996 := by exact prefixLift 3164996
  have htrace : WordTrace (prefixWord ++ tailWord_3164996) baseStart_3164996 baseEnd_3164996 := by
    simpa [prefixWord, tailWord_3164996, baseEnd_3164996] using wordTrace_append hprefix tailTrace_3164996
  have hstable : (prefixWord ++ tailWord_3164996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3164996).length < 2 ^ (prefixWord ++ tailWord_3164996).sum := by decide
  have hdescent : baseEnd_3164996 < baseStart_3164996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3164996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165018 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_3165018 : Nat := 118140960795 + 3165018 * 2 ^ 59
def prefixEnd_3165018 : Nat := 4983230072969 + 3 ^ 40 * 3165018 * 2
def baseEnd_3165018 : Nat := 1625175514132003086219353

theorem tailTrace_3165018 : CollatzResearch.WordTrace tailWord_3165018 prefixEnd_3165018 1625175514132003086219353 := by
  unfold tailWord_3165018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28859422511921950721189927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76958460031791868589839805 28859422511921950721189927)
  ·
    refine ⟨43289133767882926081784891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28859422511921950721189927 43289133767882926081784891)
    ·
      refine ⟨64933700651824389122677337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43289133767882926081784891 64933700651824389122677337)
      ·
        refine ⟨48700275488868291842008003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64933700651824389122677337 48700275488868291842008003)
        ·
          refine ⟨73050413233302437763012005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48700275488868291842008003 73050413233302437763012005)
          ·
            refine ⟨13696952481244207080564751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73050413233302437763012005 13696952481244207080564751)
            ·
              refine ⟨20545428721866310620847127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13696952481244207080564751 20545428721866310620847127)
              ·
                refine ⟨30818143082799465931270691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20545428721866310620847127 30818143082799465931270691)
                ·
                  refine ⟨46227214624199198896906037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30818143082799465931270691 46227214624199198896906037)
                  ·
                    refine ⟨4333801371018674896584941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46227214624199198896906037 4333801371018674896584941)
                    ·
                      refine ⟨1625175514132003086219353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4333801371018674896584941 1625175514132003086219353)
                      ·
                        rfl

theorem cell23_3165018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_3165018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165018 prefixEnd_3165018 := by exact prefixLift 3165018
  have htrace : WordTrace (prefixWord ++ tailWord_3165018) baseStart_3165018 baseEnd_3165018 := by
    simpa [prefixWord, tailWord_3165018, baseEnd_3165018] using wordTrace_append hprefix tailTrace_3165018
  have hstable : (prefixWord ++ tailWord_3165018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165018).length < 2 ^ (prefixWord ++ tailWord_3165018).sum := by decide
  have hdescent : baseEnd_3165018 < baseStart_3165018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165071 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_3165071 : Nat := 118140960795 + 3165071 * 2 ^ 59
def prefixEnd_3165071 : Nat := 4983230072969 + 3 ^ 40 * 3165071 * 2
def baseEnd_3165071 : Nat := 1625202728606691378856609

theorem tailTrace_3165071 : CollatzResearch.WordTrace tailWord_3165071 prefixEnd_3165071 1625202728606691378856609 := by
  unfold tailWord_3165071
  simp only [CollatzResearch.WordTrace]
  refine ⟨115439623116495792936439067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76959748744330528624292711 115439623116495792936439067)
  ·
    refine ⟨173159434674743689404658601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115439623116495792936439067 173159434674743689404658601)
    ·
      refine ⟨129869576006057767053493951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173159434674743689404658601 129869576006057767053493951)
      ·
        refine ⟨194804364009086650580240927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129869576006057767053493951 194804364009086650580240927)
        ·
          refine ⟨292206546013629975870361391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194804364009086650580240927 292206546013629975870361391)
          ·
            refine ⟨438309819020444963805542087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292206546013629975870361391 438309819020444963805542087)
            ·
              refine ⟨657464728530667445708313131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438309819020444963805542087 657464728530667445708313131)
              ·
                refine ⟨986197092796001168562469697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657464728530667445708313131 986197092796001168562469697)
                ·
                  refine ⟨739647819597000876421852273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 986197092796001168562469697 739647819597000876421852273)
                  ·
                    refine ⟨554735864697750657316389205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 739647819597000876421852273 554735864697750657316389205)
                    ·
                      refine ⟨1625202728606691378856609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 554735864697750657316389205 1625202728606691378856609)
                      ·
                        rfl

theorem cell23_3165071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_3165071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165071 prefixEnd_3165071 := by exact prefixLift 3165071
  have htrace : WordTrace (prefixWord ++ tailWord_3165071) baseStart_3165071 baseEnd_3165071 := by
    simpa [prefixWord, tailWord_3165071, baseEnd_3165071] using wordTrace_append hprefix tailTrace_3165071
  have hstable : (prefixWord ++ tailWord_3165071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165071).length < 2 ^ (prefixWord ++ tailWord_3165071).sum := by decide
  have hdescent : baseEnd_3165071 < baseStart_3165071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165085 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_3165085 : Nat := 118140960795 + 3165085 * 2 ^ 59
def prefixEnd_3165085 : Nat := 4983230072969 + 3 ^ 40 * 3165085 * 2
def baseEnd_3165085 : Nat := 541736639111951441360515

theorem tailTrace_3165085 : CollatzResearch.WordTrace tailWord_3165085 prefixEnd_3165085 541736639111951441360515 := by
  unfold tailWord_3165085
  simp only [CollatzResearch.WordTrace]
  refine ⟨115440133738445073327448709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76960089158963382218299139 115440133738445073327448709)
  ·
    refine ⟨21645025075958451248896633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115440133738445073327448709 21645025075958451248896633)
    ·
      refine ⟨16233768806968838436672475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21645025075958451248896633 16233768806968838436672475)
      ·
        refine ⟨24350653210453257655008713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233768806968838436672475 24350653210453257655008713)
        ·
          refine ⟨18262989907839943241256535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24350653210453257655008713 18262989907839943241256535)
          ·
            refine ⟨27394484861759914861884803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18262989907839943241256535 27394484861759914861884803)
            ·
              refine ⟨41091727292639872292827205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27394484861759914861884803 41091727292639872292827205)
              ·
                refine ⟨7704698867369976054905101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41091727292639872292827205 7704698867369976054905101)
                ·
                  refine ⟨2889262075263741020589413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7704698867369976054905101 2889262075263741020589413)
                  ·
                    refine ⟨541736639111951441360515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2889262075263741020589413 541736639111951441360515)
                    ·
                      rfl

theorem cell23_3165085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_3165085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165085 prefixEnd_3165085 := by exact prefixLift 3165085
  have htrace : WordTrace (prefixWord ++ tailWord_3165085) baseStart_3165085 baseEnd_3165085 := by
    simpa [prefixWord, tailWord_3165085, baseEnd_3165085] using wordTrace_append hprefix tailTrace_3165085
  have hstable : (prefixWord ++ tailWord_3165085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165085).length < 2 ^ (prefixWord ++ tailWord_3165085).sum := by decide
  have hdescent : baseEnd_3165085 < baseStart_3165085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165145 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_3165145 : Nat := 118140960795 + 3165145 * 2 ^ 59
def prefixEnd_3165145 : Nat := 4983230072969 + 3 ^ 40 * 3165145 * 2
def baseEnd_3165145 : Nat := 541746908725041363110423

theorem tailTrace_3165145 : CollatzResearch.WordTrace tailWord_3165145 prefixEnd_3165145 541746908725041363110423 := by
  unfold tailWord_3165145
  simp only [CollatzResearch.WordTrace]
  refine ⟨115442322118227703574632889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76961548078818469049755259 115442322118227703574632889)
  ·
    refine ⟨86581741588670777680974667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115442322118227703574632889 86581741588670777680974667)
    ·
      refine ⟨129872612383006166521462001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86581741588670777680974667 129872612383006166521462001)
      ·
        refine ⟨97404459287254624891096501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129872612383006166521462001 97404459287254624891096501)
        ·
          refine ⟨9131668058180121083540297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97404459287254624891096501 9131668058180121083540297)
          ·
            refine ⟨6848751043635090812655223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131668058180121083540297 6848751043635090812655223)
            ·
              refine ⟨10273126565452636218982835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848751043635090812655223 10273126565452636218982835)
              ·
                refine ⟨15409689848178954328474253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273126565452636218982835 15409689848178954328474253)
                ·
                  refine ⟨5778633693067107873177845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15409689848178954328474253 5778633693067107873177845)
                  ·
                    refine ⟨541746908725041363110423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5778633693067107873177845 541746908725041363110423)
                    ·
                      rfl

theorem cell23_3165145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_3165145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165145 prefixEnd_3165145 := by exact prefixLift 3165145
  have htrace : WordTrace (prefixWord ++ tailWord_3165145) baseStart_3165145 baseEnd_3165145 := by
    simpa [prefixWord, tailWord_3165145, baseEnd_3165145] using wordTrace_append hprefix tailTrace_3165145
  have hstable : (prefixWord ++ tailWord_3165145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165145).length < 2 ^ (prefixWord ++ tailWord_3165145).sum := by decide
  have hdescent : baseEnd_3165145 < baseStart_3165145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165170 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_3165170 : Nat := 118140960795 + 3165170 * 2 ^ 59
def prefixEnd_3165170 : Nat := 4983230072969 + 3 ^ 40 * 3165170 * 2
def baseEnd_3165170 : Nat := 541751187730495497172885

theorem tailTrace_3165170 : CollatzResearch.WordTrace tailWord_3165170 prefixEnd_3165170 541751187730495497172885 := by
  unfold tailWord_3165170
  simp only [CollatzResearch.WordTrace]
  refine ⟨28860808485784283211073241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76962155962091421896195309 28860808485784283211073241)
  ·
    refine ⟨21645606364338212408304931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28860808485784283211073241 21645606364338212408304931)
    ·
      refine ⟨32468409546507318612457397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21645606364338212408304931 32468409546507318612457397)
      ·
        refine ⟨3043913394985061119917881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32468409546507318612457397 3043913394985061119917881)
        ·
          refine ⟨2282935046238795839938411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043913394985061119917881 2282935046238795839938411)
          ·
            refine ⟨3424402569358193759907617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282935046238795839938411 3424402569358193759907617)
            ·
              refine ⟨2568301927018645319930713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424402569358193759907617 2568301927018645319930713)
              ·
                refine ⟨1926226445263983989948035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568301927018645319930713 1926226445263983989948035)
                ·
                  refine ⟨2889339667895975984922053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926226445263983989948035 2889339667895975984922053)
                  ·
                    refine ⟨541751187730495497172885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2889339667895975984922053 541751187730495497172885)
                    ·
                      rfl

theorem cell23_3165170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_3165170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165170 prefixEnd_3165170 := by exact prefixLift 3165170
  have htrace : WordTrace (prefixWord ++ tailWord_3165170) baseStart_3165170 baseEnd_3165170 := by
    simpa [prefixWord, tailWord_3165170, baseEnd_3165170] using wordTrace_append hprefix tailTrace_3165170
  have hstable : (prefixWord ++ tailWord_3165170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165170).length < 2 ^ (prefixWord ++ tailWord_3165170).sum := by decide
  have hdescent : baseEnd_3165170 < baseStart_3165170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165178 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_3165178 : Nat := 118140960795 + 3165178 * 2 ^ 59
def prefixEnd_3165178 : Nat := 4983230072969 + 3 ^ 40 * 3165178 * 2
def baseEnd_3165178 : Nat := 1625257671036722460218617

theorem tailTrace_3165178 : CollatzResearch.WordTrace tailWord_3165178 prefixEnd_3165178 1625257671036722460218617 := by
  unfold tailWord_3165178
  simp only [CollatzResearch.WordTrace]
  refine ⟨28860881431777037552646047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76962350484738766807056125 28860881431777037552646047)
  ·
    refine ⟨43291322147665556328969071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28860881431777037552646047 43291322147665556328969071)
    ·
      refine ⟨64936983221498334493453607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43291322147665556328969071 64936983221498334493453607)
      ·
        refine ⟨97405474832247501740180411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64936983221498334493453607 97405474832247501740180411)
        ·
          refine ⟨146108212248371252610270617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97405474832247501740180411 146108212248371252610270617)
          ·
            refine ⟨109581159186278439457702963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146108212248371252610270617 109581159186278439457702963)
            ·
              refine ⟨164371738779417659186554445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109581159186278439457702963 164371738779417659186554445)
              ·
                refine ⟨61639402042281622194957917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164371738779417659186554445 61639402042281622194957917)
                ·
                  refine ⟨23114775765855608323109219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61639402042281622194957917 23114775765855608323109219)
                  ·
                    refine ⟨34672163648783412484663829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23114775765855608323109219 34672163648783412484663829)
                    ·
                      refine ⟨1625257671036722460218617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34672163648783412484663829 1625257671036722460218617)
                      ·
                        rfl

theorem cell23_3165178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_3165178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165178 prefixEnd_3165178 := by exact prefixLift 3165178
  have htrace : WordTrace (prefixWord ++ tailWord_3165178) baseStart_3165178 baseEnd_3165178 := by
    simpa [prefixWord, tailWord_3165178, baseEnd_3165178] using wordTrace_append hprefix tailTrace_3165178
  have hstable : (prefixWord ++ tailWord_3165178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165178).length < 2 ^ (prefixWord ++ tailWord_3165178).sum := by decide
  have hdescent : baseEnd_3165178 < baseStart_3165178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165192 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 2, 4]
def baseStart_3165192 : Nat := 118140960795 + 3165192 * 2 ^ 59
def prefixEnd_3165192 : Nat := 4983230072969 + 3 ^ 40 * 3165192 * 2
def baseEnd_3165192 : Nat := 541754953255295135147851

theorem tailTrace_3165192 : CollatzResearch.WordTrace tailWord_3165192 prefixEnd_3165192 541754953255295135147851 := by
  unfold tailWord_3165192
  simp only [CollatzResearch.WordTrace]
  refine ⟨57722018174528715300796915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76962690899371620401062553 57722018174528715300796915)
  ·
    refine ⟨86583027261793072951195373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57722018174528715300796915 86583027261793072951195373)
    ·
      refine ⟨32468635223172402356698265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86583027261793072951195373 32468635223172402356698265)
      ·
        refine ⟨24351476417379301767523699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32468635223172402356698265 24351476417379301767523699)
        ·
          refine ⟨36527214626068952651285549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24351476417379301767523699 36527214626068952651285549)
          ·
            refine ⟨13697705484775857244232081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36527214626068952651285549 13697705484775857244232081)
            ·
              refine ⟨10273279113581892933174061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13697705484775857244232081 10273279113581892933174061)
              ·
                refine ⟨3852479667593209849940273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10273279113581892933174061 3852479667593209849940273)
                ·
                  refine ⟨2889359750694907387455205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852479667593209849940273 2889359750694907387455205)
                  ·
                    refine ⟨541754953255295135147851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2889359750694907387455205 541754953255295135147851)
                    ·
                      rfl

theorem cell23_3165192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_3165192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165192 prefixEnd_3165192 := by exact prefixLift 3165192
  have htrace : WordTrace (prefixWord ++ tailWord_3165192) baseStart_3165192 baseEnd_3165192 := by
    simpa [prefixWord, tailWord_3165192, baseEnd_3165192] using wordTrace_append hprefix tailTrace_3165192
  have hstable : (prefixWord ++ tailWord_3165192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165192).length < 2 ^ (prefixWord ++ tailWord_3165192).sum := by decide
  have hdescent : baseEnd_3165192 < baseStart_3165192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165195 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4]
def baseStart_3165195 : Nat := 118140960795 + 3165195 * 2 ^ 59
def prefixEnd_3165195 : Nat := 4983230072969 + 3 ^ 40 * 3165195 * 2
def baseEnd_3165195 : Nat := 1625266400207848893706039

theorem tailTrace_3165195 : CollatzResearch.WordTrace tailWord_3165195 prefixEnd_3165195 1625266400207848893706039 := by
  unfold tailWord_3165195
  simp only [CollatzResearch.WordTrace]
  refine ⟨115444145768046562113953039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76962763845364374742635359 115444145768046562113953039)
  ·
    refine ⟨173166218652069843170929559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115444145768046562113953039 173166218652069843170929559)
    ·
      refine ⟨259749327978104764756394339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173166218652069843170929559 259749327978104764756394339)
      ·
        refine ⟨389623991967157147134591509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259749327978104764756394339 389623991967157147134591509)
        ·
          refine ⟨18263624623460491271933977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 389623991967157147134591509 18263624623460491271933977)
          ·
            refine ⟨13697718467595368453950483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18263624623460491271933977 13697718467595368453950483)
            ·
              refine ⟨20546577701393052680925725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13697718467595368453950483 20546577701393052680925725)
              ·
                refine ⟨7704966638022394755347147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20546577701393052680925725 7704966638022394755347147)
                ·
                  refine ⟨11557449957033592133020721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7704966638022394755347147 11557449957033592133020721)
                  ·
                    refine ⟨8668087467775194099765541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11557449957033592133020721 8668087467775194099765541)
                    ·
                      refine ⟨1625266400207848893706039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8668087467775194099765541 1625266400207848893706039)
                      ·
                        rfl

theorem cell23_3165195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].length) (baseStart_3165195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165195 prefixEnd_3165195 := by exact prefixLift 3165195
  have htrace : WordTrace (prefixWord ++ tailWord_3165195) baseStart_3165195 baseEnd_3165195 := by
    simpa [prefixWord, tailWord_3165195, baseEnd_3165195] using wordTrace_append hprefix tailTrace_3165195
  have hstable : (prefixWord ++ tailWord_3165195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165195).length < 2 ^ (prefixWord ++ tailWord_3165195).sum := by decide
  have hdescent : baseEnd_3165195 < baseStart_3165195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165219 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 1, 2, 3]
def baseStart_3165219 : Nat := 118140960795 + 3165219 * 2 ^ 59
def prefixEnd_3165219 : Nat := 4983230072969 + 3 ^ 40 * 3165219 * 2
def baseEnd_3165219 : Nat := 1625278723743556799805929

theorem tailTrace_3165219 : CollatzResearch.WordTrace tailWord_3165219 prefixEnd_3165219 1625278723743556799805929 := by
  unfold tailWord_3165219
  simp only [CollatzResearch.WordTrace]
  refine ⟨115445021119959614212826711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76963347413306409475217807 115445021119959614212826711)
  ·
    refine ⟨173167531679939421319240067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115445021119959614212826711 173167531679939421319240067)
    ·
      refine ⟨259751297519909131978860101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173167531679939421319240067 259751297519909131978860101)
      ·
        refine ⟨48703368284982962246036269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259751297519909131978860101 48703368284982962246036269)
        ·
          refine ⟨18263763106868610842263601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48703368284982962246036269 18263763106868610842263601)
          ·
            refine ⟨13697822330151458131697701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18263763106868610842263601 13697822330151458131697701)
            ·
              refine ⟨2568341686903398399693319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13697822330151458131697701 2568341686903398399693319)
              ·
                refine ⟨3852512530355097599539979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568341686903398399693319 3852512530355097599539979)
                ·
                  refine ⟨5778768795532646399309969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852512530355097599539979 5778768795532646399309969)
                  ·
                    refine ⟨4334076596649484799482477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5778768795532646399309969 4334076596649484799482477)
                    ·
                      refine ⟨1625278723743556799805929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334076596649484799482477 1625278723743556799805929)
                      ·
                        rfl

theorem cell23_3165219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_3165219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165219 prefixEnd_3165219 := by exact prefixLift 3165219
  have htrace : WordTrace (prefixWord ++ tailWord_3165219) baseStart_3165219 baseEnd_3165219 := by
    simpa [prefixWord, tailWord_3165219, baseEnd_3165219] using wordTrace_append hprefix tailTrace_3165219
  have hstable : (prefixWord ++ tailWord_3165219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165219).length < 2 ^ (prefixWord ++ tailWord_3165219).sum := by decide
  have hdescent : baseEnd_3165219 < baseStart_3165219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165226 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3165226 : Nat := 118140960795 + 3165226 * 2 ^ 59
def prefixEnd_3165226 : Nat := 4983230072969 + 3 ^ 40 * 3165226 * 2
def baseEnd_3165226 : Nat := 541760772702712757472799

theorem tailTrace_3165226 : CollatzResearch.WordTrace tailWord_3165226 prefixEnd_3165226 541760772702712757472799 := by
  unfold tailWord_3165226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28861319107733563602082883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76963517620622836272221021 28861319107733563602082883)
  ·
    refine ⟨43291978661600345403124325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28861319107733563602082883 43291978661600345403124325)
    ·
      refine ⟨8117245999050064763085811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43291978661600345403124325 8117245999050064763085811)
      ·
        refine ⟨12175868998575097144628717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8117245999050064763085811 12175868998575097144628717)
        ·
          refine ⟨4565950874465661429235769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12175868998575097144628717 4565950874465661429235769)
          ·
            refine ⟨3424463155849246071926827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4565950874465661429235769 3424463155849246071926827)
            ·
              refine ⟨5136694733773869107890241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424463155849246071926827 5136694733773869107890241)
              ·
                refine ⟨3852521050330401830917681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136694733773869107890241 3852521050330401830917681)
                ·
                  refine ⟨2889390787747801373188261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852521050330401830917681 2889390787747801373188261)
                  ·
                    refine ⟨541760772702712757472799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2889390787747801373188261 541760772702712757472799)
                    ·
                      rfl

theorem cell23_3165226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3165226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165226 prefixEnd_3165226 := by exact prefixLift 3165226
  have htrace : WordTrace (prefixWord ++ tailWord_3165226) baseStart_3165226 baseEnd_3165226 := by
    simpa [prefixWord, tailWord_3165226, baseEnd_3165226] using wordTrace_append hprefix tailTrace_3165226
  have hstable : (prefixWord ++ tailWord_3165226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165226).length < 2 ^ (prefixWord ++ tailWord_3165226).sum := by decide
  have hdescent : baseEnd_3165226 < baseStart_3165226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165232 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 4, 1, 3]
def baseStart_3165232 : Nat := 118140960795 + 3165232 * 2 ^ 59
def prefixEnd_3165232 : Nat := 4983230072969 + 3 ^ 40 * 3165232 * 2
def baseEnd_3165232 : Nat := 1625285398992065248943369

theorem tailTrace_3165232 : CollatzResearch.WordTrace tailWord_3165232 prefixEnd_3165232 1625285398992065248943369 := by
  unfold tailWord_3165232
  simp only [CollatzResearch.WordTrace]
  refine ⟨57722747634456258716524975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76963663512608344955366633 57722747634456258716524975)
  ·
    refine ⟨86584121451684388074787463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57722747634456258716524975 86584121451684388074787463)
    ·
      refine ⟨129876182177526582112181195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86584121451684388074787463 129876182177526582112181195)
      ·
        refine ⟨194814273266289873168271793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129876182177526582112181195 194814273266289873168271793)
        ·
          refine ⟨146110704949717404876203845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194814273266289873168271793 146110704949717404876203845)
          ·
            refine ⟨27395757178072013414288221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146110704949717404876203845 27395757178072013414288221)
            ·
              refine ⟨10273408941777005030358083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27395757178072013414288221 10273408941777005030358083)
              ·
                refine ⟨15410113412665507545537125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273408941777005030358083 15410113412665507545537125)
                ·
                  refine ⟨2889396264874782664788211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15410113412665507545537125 2889396264874782664788211)
                  ·
                    refine ⟨4334094397312173997182317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889396264874782664788211 4334094397312173997182317)
                    ·
                      refine ⟨1625285398992065248943369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334094397312173997182317 1625285398992065248943369)
                      ·
                        rfl

theorem cell23_3165232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_3165232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165232 prefixEnd_3165232 := by exact prefixLift 3165232
  have htrace : WordTrace (prefixWord ++ tailWord_3165232) baseStart_3165232 baseEnd_3165232 := by
    simpa [prefixWord, tailWord_3165232, baseEnd_3165232] using wordTrace_append hprefix tailTrace_3165232
  have hstable : (prefixWord ++ tailWord_3165232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165232).length < 2 ^ (prefixWord ++ tailWord_3165232).sum := by decide
  have hdescent : baseEnd_3165232 < baseStart_3165232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165242 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2]
def baseStart_3165242 : Nat := 118140960795 + 3165242 * 2 ^ 59
def prefixEnd_3165242 : Nat := 4983230072969 + 3 ^ 40 * 3165242 * 2
def baseEnd_3165242 : Nat := 1625290533798610209818323

theorem tailTrace_3165242 : CollatzResearch.WordTrace tailWord_3165242 prefixEnd_3165242 1625290533798610209818323 := by
  unfold tailWord_3165242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28861464999719072285228495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76963906665917526093942653 28861464999719072285228495)
  ·
    refine ⟨43292197499578608427842743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28861464999719072285228495 43292197499578608427842743)
    ·
      refine ⟨64938296249367912641764115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43292197499578608427842743 64938296249367912641764115)
      ·
        refine ⟨97407444374051868962646173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64938296249367912641764115 97407444374051868962646173)
        ·
          refine ⟨36527791640269450860992315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97407444374051868962646173 36527791640269450860992315)
          ·
            refine ⟨54791687460404176291488473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36527791640269450860992315 54791687460404176291488473)
            ·
              refine ⟨41093765595303132218616355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54791687460404176291488473 41093765595303132218616355)
              ·
                refine ⟨61640648392954698327924533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41093765595303132218616355 61640648392954698327924533)
                ·
                  refine ⟨5778810786839502968242925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61640648392954698327924533 5778810786839502968242925)
                  ·
                    refine ⟨2167054045064813613091097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5778810786839502968242925 2167054045064813613091097)
                    ·
                      refine ⟨1625290533798610209818323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167054045064813613091097 1625290533798610209818323)
                      ·
                        rfl

theorem cell23_3165242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_3165242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165242 prefixEnd_3165242 := by exact prefixLift 3165242
  have htrace : WordTrace (prefixWord ++ tailWord_3165242) baseStart_3165242 baseEnd_3165242 := by
    simpa [prefixWord, tailWord_3165242, baseEnd_3165242] using wordTrace_append hprefix tailTrace_3165242
  have hstable : (prefixWord ++ tailWord_3165242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165242).length < 2 ^ (prefixWord ++ tailWord_3165242).sum := by decide
  have hdescent : baseEnd_3165242 < baseStart_3165242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165272 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 3, 4, 2]
def baseStart_3165272 : Nat := 118140960795 + 3165272 * 2 ^ 59
def prefixEnd_3165272 : Nat := 4983230072969 + 3 ^ 40 * 3165272 * 2
def baseEnd_3165272 : Nat := 1625305938218245092443185

theorem tailTrace_3165272 : CollatzResearch.WordTrace tailWord_3165272 prefixEnd_3165272 1625305938218245092443185 := by
  unfold tailWord_3165272
  simp only [CollatzResearch.WordTrace]
  refine ⟨57723477094383802132253035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76964636125845069509670713 57723477094383802132253035)
  ·
    refine ⟨86585215641575703198379553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57723477094383802132253035 86585215641575703198379553)
    ·
      refine ⟨64938911731181777398784665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86585215641575703198379553 64938911731181777398784665)
      ·
        refine ⟨48704183798386333049088499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64938911731181777398784665 48704183798386333049088499)
        ·
          refine ⟨73056275697579499573632749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48704183798386333049088499 73056275697579499573632749)
          ·
            refine ⟨27396103386592312340112281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73056275697579499573632749 27396103386592312340112281)
            ·
              refine ⟨20547077539944234255084211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27396103386592312340112281 20547077539944234255084211)
              ·
                refine ⟨30820616309916351382626317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20547077539944234255084211 30820616309916351382626317)
                ·
                  refine ⟨11557731116218631768484869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30820616309916351382626317 11557731116218631768484869)
                  ·
                    refine ⟨2167074584290993456590913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11557731116218631768484869 2167074584290993456590913)
                    ·
                      refine ⟨1625305938218245092443185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167074584290993456590913 1625305938218245092443185)
                      ·
                        rfl

theorem cell23_3165272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_3165272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165272 prefixEnd_3165272 := by exact prefixLift 3165272
  have htrace : WordTrace (prefixWord ++ tailWord_3165272) baseStart_3165272 baseEnd_3165272 := by
    simpa [prefixWord, tailWord_3165272, baseEnd_3165272] using wordTrace_append hprefix tailTrace_3165272
  have hstable : (prefixWord ++ tailWord_3165272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165272).length < 2 ^ (prefixWord ++ tailWord_3165272).sum := by decide
  have hdescent : baseEnd_3165272 < baseStart_3165272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165289 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 4, 2, 2]
def baseStart_3165289 : Nat := 118140960795 + 3165289 * 2 ^ 59
def prefixEnd_3165289 : Nat := 4983230072969 + 3 ^ 40 * 3165289 * 2
def baseEnd_3165289 : Nat := 1625314667389371525930607

theorem tailTrace_3165289 : CollatzResearch.WordTrace tailWord_3165289 prefixEnd_3165289 1625314667389371525930607 := by
  unfold tailWord_3165289
  simp only [CollatzResearch.WordTrace]
  refine ⟨115447574229706016167874921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76965049486470677445249947 115447574229706016167874921)
  ·
    refine ⟨86585680672279512125906191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115447574229706016167874921 86585680672279512125906191)
    ·
      refine ⟨129878521008419268188859287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86585680672279512125906191 129878521008419268188859287)
      ·
        refine ⟨194817781512628902283288931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129878521008419268188859287 194817781512628902283288931)
        ·
          refine ⟨292226672268943353424933397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194817781512628902283288931 292226672268943353424933397)
          ·
            refine ⟨13698125262606719691793753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292226672268943353424933397 13698125262606719691793753)
            ·
              refine ⟨10273593946955039768845315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13698125262606719691793753 10273593946955039768845315)
              ·
                refine ⟨15410390920432559653267973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273593946955039768845315 15410390920432559653267973)
                ·
                  refine ⟨2889448297581104934987745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15410390920432559653267973 2889448297581104934987745)
                  ·
                    refine ⟨2167086223185828701240809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2889448297581104934987745 2167086223185828701240809)
                    ·
                      refine ⟨1625314667389371525930607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167086223185828701240809 1625314667389371525930607)
                      ·
                        rfl

theorem cell23_3165289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 2, 2].length) (baseStart_3165289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165289 prefixEnd_3165289 := by exact prefixLift 3165289
  have htrace : WordTrace (prefixWord ++ tailWord_3165289) baseStart_3165289 baseEnd_3165289 := by
    simpa [prefixWord, tailWord_3165289, baseEnd_3165289] using wordTrace_append hprefix tailTrace_3165289
  have hstable : (prefixWord ++ tailWord_3165289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165289).length < 2 ^ (prefixWord ++ tailWord_3165289).sum := by decide
  have hdescent : baseEnd_3165289 < baseStart_3165289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165302 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3165302 : Nat := 118140960795 + 3165302 * 2 ^ 59
def prefixEnd_3165302 : Nat := 4983230072969 + 3 ^ 40 * 3165302 * 2
def baseEnd_3165302 : Nat := 1625321342637879975068047

theorem tailTrace_3165302 : CollatzResearch.WordTrace tailWord_3165302 prefixEnd_3165302 1625321342637879975068047 := by
  unfold tailWord_3165302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215503023666182461756135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76965365585772612925398773 7215503023666182461756135)
  ·
    refine ⟨10823254535499273692634203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7215503023666182461756135 10823254535499273692634203)
    ·
      refine ⟨16234881803248910538951305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10823254535499273692634203 16234881803248910538951305)
      ·
        refine ⟨12176161352436682904213479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16234881803248910538951305 12176161352436682904213479)
        ·
          refine ⟨18264242028655024356320219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12176161352436682904213479 18264242028655024356320219)
          ·
            refine ⟨27396363042982536534480329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18264242028655024356320219 27396363042982536534480329)
            ·
              refine ⟨20547272282236902400860247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27396363042982536534480329 20547272282236902400860247)
              ·
                refine ⟨30820908423355353601290371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20547272282236902400860247 30820908423355353601290371)
                ·
                  refine ⟨46231362635033030401935557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30820908423355353601290371 46231362635033030401935557)
                  ·
                    refine ⟨8668380494068693200362917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46231362635033030401935557 8668380494068693200362917)
                    ·
                      refine ⟨1625321342637879975068047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8668380494068693200362917 1625321342637879975068047)
                      ·
                        rfl

theorem cell23_3165302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3165302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165302 prefixEnd_3165302 := by exact prefixLift 3165302
  have htrace : WordTrace (prefixWord ++ tailWord_3165302) baseStart_3165302 baseEnd_3165302 := by
    simpa [prefixWord, tailWord_3165302, baseEnd_3165302] using wordTrace_append hprefix tailTrace_3165302
  have hstable : (prefixWord ++ tailWord_3165302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165302).length < 2 ^ (prefixWord ++ tailWord_3165302).sum := by decide
  have hdescent : baseEnd_3165302 < baseStart_3165302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165310 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3165310 : Nat := 118140960795 + 3165310 * 2 ^ 59
def prefixEnd_3165310 : Nat := 4983230072969 + 3 ^ 40 * 3165310 * 2
def baseEnd_3165310 : Nat := 1625325450483115943768011

theorem tailTrace_3165310 : CollatzResearch.WordTrace tailWord_3165310 prefixEnd_3165310 1625325450483115943768011 := by
  unfold tailWord_3165310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14431042520328742094298673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76965560108419957836259589 14431042520328742094298673)
  ·
    refine ⟨10823281890246556570724005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14431042520328742094298673 10823281890246556570724005)
    ·
      refine ⟨2029365354421229357010751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10823281890246556570724005 2029365354421229357010751)
      ·
        refine ⟨3044048031631844035516127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029365354421229357010751 3044048031631844035516127)
        ·
          refine ⟨4566072047447766053274191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044048031631844035516127 4566072047447766053274191)
          ·
            refine ⟨6849108071171649079911287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566072047447766053274191 6849108071171649079911287)
            ·
              refine ⟨10273662106757473619866931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849108071171649079911287 10273662106757473619866931)
              ·
                refine ⟨15410493160136210429800397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273662106757473619866931 15410493160136210429800397)
                ·
                  refine ⟨5778934935051078911175149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15410493160136210429800397 5778934935051078911175149)
                  ·
                    refine ⟨2167100600644154591690681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5778934935051078911175149 2167100600644154591690681)
                    ·
                      refine ⟨1625325450483115943768011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167100600644154591690681 1625325450483115943768011)
                      ·
                        rfl

theorem cell23_3165310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3165310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165310 prefixEnd_3165310 := by exact prefixLift 3165310
  have htrace : WordTrace (prefixWord ++ tailWord_3165310) baseStart_3165310 baseEnd_3165310 := by
    simpa [prefixWord, tailWord_3165310, baseEnd_3165310] using wordTrace_append hprefix tailTrace_3165310
  have hstable : (prefixWord ++ tailWord_3165310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165310).length < 2 ^ (prefixWord ++ tailWord_3165310).sum := by decide
  have hdescent : baseEnd_3165310 < baseStart_3165310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165346 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3165346 : Nat := 118140960795 + 3165346 * 2 ^ 59
def prefixEnd_3165346 : Nat := 4983230072969 + 3 ^ 40 * 3165346 * 2
def baseEnd_3165346 : Nat := 180593770642964200324205

theorem tailTrace_3165346 : CollatzResearch.WordTrace tailWord_3165346 prefixEnd_3165346 180593770642964200324205 := by
  unfold tailWord_3165346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28862413297624878725674973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76966435460333009935133261 28862413297624878725674973)
  ·
    refine ⟨10823404986609329522128115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28862413297624878725674973 10823404986609329522128115)
    ·
      refine ⟨16235107479913994283192173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10823404986609329522128115 16235107479913994283192173)
      ·
        refine ⟨6088165304967747856197065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16235107479913994283192173 6088165304967747856197065)
        ·
          refine ⟨4566123978725810892147799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6088165304967747856197065 4566123978725810892147799)
          ·
            refine ⟨6849185968088716338221699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566123978725810892147799 6849185968088716338221699)
            ·
              refine ⟨10273778952133074507332549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849185968088716338221699 10273778952133074507332549)
              ·
                refine ⟨1926333553524951470124853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10273778952133074507332549 1926333553524951470124853)
                ·
                  refine ⟨180593770642964200324205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1926333553524951470124853 180593770642964200324205)
                  ·
                    rfl

theorem cell23_3165346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3165346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165346 prefixEnd_3165346 := by exact prefixLift 3165346
  have htrace : WordTrace (prefixWord ++ tailWord_3165346) baseStart_3165346 baseEnd_3165346 := by
    simpa [prefixWord, tailWord_3165346, baseEnd_3165346] using wordTrace_append hprefix tailTrace_3165346
  have hstable : (prefixWord ++ tailWord_3165346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165346).length < 2 ^ (prefixWord ++ tailWord_3165346).sum := by decide
  have hdescent : baseEnd_3165346 < baseStart_3165346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165376 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 2, 5]
def baseStart_3165376 : Nat := 118140960795 + 3165376 * 2 ^ 59
def prefixEnd_3165376 : Nat := 4983230072969 + 3 ^ 40 * 3165376 * 2
def baseEnd_3165376 : Nat := 541786446735437561847569

theorem tailTrace_3165376 : CollatzResearch.WordTrace tailWord_3165376 prefixEnd_3165376 541786446735437561847569 := by
  unfold tailWord_3165376
  simp only [CollatzResearch.WordTrace]
  refine ⟨57725373690195415013145991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76967164920260553350861321 57725373690195415013145991)
  ·
    refine ⟨86588060535293122519718987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57725373690195415013145991 86588060535293122519718987)
    ·
      refine ⟨129882090802939683779578481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86588060535293122519718987 129882090802939683779578481)
      ·
        refine ⟨97411568102204762834683861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129882090802939683779578481 97411568102204762834683861)
        ·
          refine ⟨2283083627395424128937903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97411568102204762834683861 2283083627395424128937903)
          ·
            refine ⟨3424625441093136193406855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283083627395424128937903 3424625441093136193406855)
            ·
              refine ⟨5136938161639704290110283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424625441093136193406855 5136938161639704290110283)
              ·
                refine ⟨7705407242459556435165425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136938161639704290110283 7705407242459556435165425)
                ·
                  refine ⟨5779055431844667326374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7705407242459556435165425 5779055431844667326374069)
                  ·
                    refine ⟨541786446735437561847569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5779055431844667326374069 541786446735437561847569)
                    ·
                      rfl

theorem cell23_3165376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 5].length) (baseStart_3165376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165376 prefixEnd_3165376 := by exact prefixLift 3165376
  have htrace : WordTrace (prefixWord ++ tailWord_3165376) baseStart_3165376 baseEnd_3165376 := by
    simpa [prefixWord, tailWord_3165376, baseEnd_3165376] using wordTrace_append hprefix tailTrace_3165376
  have hstable : (prefixWord ++ tailWord_3165376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165376).length < 2 ^ (prefixWord ++ tailWord_3165376).sum := by decide
  have hdescent : baseEnd_3165376 < baseStart_3165376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165419 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 6]
def baseStart_3165419 : Nat := 118140960795 + 3165419 * 2 ^ 59
def prefixEnd_3165419 : Nat := 4983230072969 + 3 ^ 40 * 3165419 * 2
def baseEnd_3165419 : Nat := 180597935541606224145001

theorem tailTrace_3165419 : CollatzResearch.WordTrace tailWord_3165419 prefixEnd_3165419 180597935541606224145001 := by
  unfold tailWord_3165419
  simp only [CollatzResearch.WordTrace]
  refine ⟨115452315719235048370107311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76968210479490032246738207 115452315719235048370107311)
  ·
    refine ⟨173178473578852572555160967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115452315719235048370107311 173178473578852572555160967)
    ·
      refine ⟨259767710368278858832741451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173178473578852572555160967 259767710368278858832741451)
      ·
        refine ⟨389651565552418288249112177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259767710368278858832741451 389651565552418288249112177)
        ·
          refine ⟨292238674164313716186834133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389651565552418288249112177 292238674164313716186834133)
          ·
            refine ⟨6849343925726102723128925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 292238674164313716186834133 6849343925726102723128925)
            ·
              refine ⟨2568503972147288521173347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6849343925726102723128925 2568503972147288521173347)
              ·
                refine ⟨3852755958220932781760021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568503972147288521173347 3852755958220932781760021)
                ·
                  refine ⟨180597935541606224145001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3852755958220932781760021 180597935541606224145001)
                  ·
                    rfl

theorem cell23_3165419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 6].length) (baseStart_3165419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165419 prefixEnd_3165419 := by exact prefixLift 3165419
  have htrace : WordTrace (prefixWord ++ tailWord_3165419) baseStart_3165419 baseEnd_3165419 := by
    simpa [prefixWord, tailWord_3165419, baseEnd_3165419] using wordTrace_append hprefix tailTrace_3165419
  have hstable : (prefixWord ++ tailWord_3165419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165419).length < 2 ^ (prefixWord ++ tailWord_3165419).sum := by decide
  have hdescent : baseEnd_3165419 < baseStart_3165419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165439 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 1, 5, 2]
def baseStart_3165439 : Nat := 118140960795 + 3165439 * 2 ^ 59
def prefixEnd_3165439 : Nat := 4983230072969 + 3 ^ 40 * 3165439 * 2
def baseEnd_3165439 : Nat := 1625391689487545939054917

theorem tailTrace_3165439 : CollatzResearch.WordTrace tailWord_3165439 prefixEnd_3165439 1625391689487545939054917 := by
  unfold tailWord_3165439
  simp only [CollatzResearch.WordTrace]
  refine ⟨115453045179162591785835371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76968696786108394523890247 115453045179162591785835371)
  ·
    refine ⟨173179567768743887678753057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115453045179162591785835371 173179567768743887678753057)
    ·
      refine ⟨129884675826557915759064793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173179567768743887678753057 129884675826557915759064793)
      ·
        refine ⟨97413506869918436819298595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129884675826557915759064793 97413506869918436819298595)
        ·
          refine ⟨146120260304877655228947893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97413506869918436819298595 146120260304877655228947893)
          ·
            refine ⟨13698774403582280177713865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146120260304877655228947893 13698774403582280177713865)
            ·
              refine ⟨10274080802686710133285399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13698774403582280177713865 10274080802686710133285399)
              ·
                refine ⟨15411121204030065199928099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274080802686710133285399 15411121204030065199928099)
                ·
                  refine ⟨23116681806045097799892149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15411121204030065199928099 23116681806045097799892149)
                  ·
                    refine ⟨2167188919316727918739889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23116681806045097799892149 2167188919316727918739889)
                    ·
                      refine ⟨1625391689487545939054917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167188919316727918739889 1625391689487545939054917)
                      ·
                        rfl

theorem cell23_3165439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_3165439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165439 prefixEnd_3165439 := by exact prefixLift 3165439
  have htrace : WordTrace (prefixWord ++ tailWord_3165439) baseStart_3165439 baseEnd_3165439 := by
    simpa [prefixWord, tailWord_3165439, baseEnd_3165439] using wordTrace_append hprefix tailTrace_3165439
  have hstable : (prefixWord ++ tailWord_3165439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165439).length < 2 ^ (prefixWord ++ tailWord_3165439).sum := by decide
  have hdescent : baseEnd_3165439 < baseStart_3165439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165470 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_3165470 : Nat := 118140960795 + 3165470 * 2 ^ 59
def prefixEnd_3165470 : Nat := 4983230072969 + 3 ^ 40 * 3165470 * 2
def baseEnd_3165470 : Nat := 180600845265315035307475

theorem tailTrace_3165470 : CollatzResearch.WordTrace tailWord_3165470 prefixEnd_3165470 180600845265315035307475 := by
  unfold tailWord_3165470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14431771980256285510026733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76969450561366856053475909 14431771980256285510026733)
  ·
    refine ⟨5411914492596107066260025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14431771980256285510026733 5411914492596107066260025)
    ·
      refine ⟨4058935869447080299695019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5411914492596107066260025 4058935869447080299695019)
      ·
        refine ⟨6088403804170620449542529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058935869447080299695019 6088403804170620449542529)
        ·
          refine ⟨4566302853127965337156897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6088403804170620449542529 4566302853127965337156897)
          ·
            refine ⟨3424727139845974002867673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4566302853127965337156897 3424727139845974002867673)
            ·
              refine ⟨2568545354884480502150755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424727139845974002867673 2568545354884480502150755)
              ·
                refine ⟨3852818032326720753226133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568545354884480502150755 3852818032326720753226133)
                ·
                  refine ⟨180600845265315035307475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3852818032326720753226133 180600845265315035307475)
                  ·
                    rfl

theorem cell23_3165470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_3165470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165470 prefixEnd_3165470 := by exact prefixLift 3165470
  have htrace : WordTrace (prefixWord ++ tailWord_3165470) baseStart_3165470 baseEnd_3165470 := by
    simpa [prefixWord, tailWord_3165470, baseEnd_3165470] using wordTrace_append hprefix tailTrace_3165470
  have hstable : (prefixWord ++ tailWord_3165470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165470).length < 2 ^ (prefixWord ++ tailWord_3165470).sum := by decide
  have hdescent : baseEnd_3165470 < baseStart_3165470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165519 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 3]
def baseStart_3165519 : Nat := 118140960795 + 3165519 * 2 ^ 59
def prefixEnd_3165519 : Nat := 4983230072969 + 3 ^ 40 * 3165519 * 2
def baseEnd_3165519 : Nat := 1625432767939905626054549

theorem tailTrace_3165519 : CollatzResearch.WordTrace tailWord_3165519 prefixEnd_3165519 1625432767939905626054549 := by
  unfold tailWord_3165519
  simp only [CollatzResearch.WordTrace]
  refine ⟨115455963018872765448747611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76970642012581843632498407 115455963018872765448747611)
  ·
    refine ⟨173183944528309148173121417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115455963018872765448747611 173183944528309148173121417)
    ·
      refine ⟨129887958396231861129841063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173183944528309148173121417 129887958396231861129841063)
      ·
        refine ⟨194831937594347791694761595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129887958396231861129841063 194831937594347791694761595)
        ·
          refine ⟨292247906391521687542142393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194831937594347791694761595 292247906391521687542142393)
          ·
            refine ⟨219185929793641265656606795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292247906391521687542142393 219185929793641265656606795)
            ·
              refine ⟨328778894690461898484910193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219185929793641265656606795 328778894690461898484910193)
              ·
                refine ⟨246584171017846423863682645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328778894690461898484910193 246584171017846423863682645)
                ·
                  refine ⟨2889658254115387779652531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 246584171017846423863682645 2889658254115387779652531)
                  ·
                    refine ⟨4334487381173081669478797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889658254115387779652531 4334487381173081669478797)
                    ·
                      refine ⟨1625432767939905626054549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334487381173081669478797 1625432767939905626054549)
                      ·
                        rfl

theorem cell23_3165519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_3165519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165519 prefixEnd_3165519 := by exact prefixLift 3165519
  have htrace : WordTrace (prefixWord ++ tailWord_3165519) baseStart_3165519 baseEnd_3165519 := by
    simpa [prefixWord, tailWord_3165519, baseEnd_3165519] using wordTrace_append hprefix tailTrace_3165519
  have hstable : (prefixWord ++ tailWord_3165519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165519).length < 2 ^ (prefixWord ++ tailWord_3165519).sum := by decide
  have hdescent : baseEnd_3165519 < baseStart_3165519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165536 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_3165536 : Nat := 118140960795 + 3165536 * 2 ^ 59
def prefixEnd_3165536 : Nat := 4983230072969 + 3 ^ 40 * 3165536 * 2
def baseEnd_3165536 : Nat := 1625441497111032059541971

theorem tailTrace_3165536 : CollatzResearch.WordTrace tailWord_3165536 prefixEnd_3165536 1625441497111032059541971 := by
  unfold tailWord_3165536
  simp only [CollatzResearch.WordTrace]
  refine ⟨57728291529905588676058231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76971055373207451568077641 57728291529905588676058231)
  ·
    refine ⟨86592437294858383014087347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57728291529905588676058231 86592437294858383014087347)
    ·
      refine ⟨129888655942287574521131021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86592437294858383014087347 129888655942287574521131021)
      ·
        refine ⟨48708245978357840445424133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129888655942287574521131021 48708245978357840445424133)
        ·
          refine ⟨9132796120942095083517025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48708245978357840445424133 9132796120942095083517025)
          ·
            refine ⟨6849597090706571312637769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9132796120942095083517025 6849597090706571312637769)
            ·
              refine ⟨5137197818029928484478327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6849597090706571312637769 5137197818029928484478327)
              ·
                refine ⟨7705796727044892726717491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137197818029928484478327 7705796727044892726717491)
                ·
                  refine ⟨11558695090567339090076237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7705796727044892726717491 11558695090567339090076237)
                  ·
                    refine ⟨4334510658962752158778589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11558695090567339090076237 4334510658962752158778589)
                    ·
                      refine ⟨1625441497111032059541971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334510658962752158778589 1625441497111032059541971)
                      ·
                        rfl

theorem cell23_3165536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_3165536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165536 prefixEnd_3165536 := by exact prefixLift 3165536
  have htrace : WordTrace (prefixWord ++ tailWord_3165536) baseStart_3165536 baseEnd_3165536 := by
    simpa [prefixWord, tailWord_3165536, baseEnd_3165536] using wordTrace_append hprefix tailTrace_3165536
  have hstable : (prefixWord ++ tailWord_3165536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165536).length < 2 ^ (prefixWord ++ tailWord_3165536).sum := by decide
  have hdescent : baseEnd_3165536 < baseStart_3165536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165552 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_3165552 : Nat := 118140960795 + 3165552 * 2 ^ 59
def prefixEnd_3165552 : Nat := 4983230072969 + 3 ^ 40 * 3165552 * 2
def baseEnd_3165552 : Nat := 541816570933834665647299

theorem tailTrace_3165552 : CollatzResearch.WordTrace tailWord_3165552 prefixEnd_3165552 541816570933834665647299 := by
  unfold tailWord_3165552
  simp only [CollatzResearch.WordTrace]
  refine ⟨57728583313876606042349455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76971444418502141389799273 57728583313876606042349455)
  ·
    refine ⟨86592874970814909063524183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57728583313876606042349455 86592874970814909063524183)
    ·
      refine ⟨129889312456222363595286275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86592874970814909063524183 129889312456222363595286275)
      ·
        refine ⟨194833968684333545392929413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129889312456222363595286275 194833968684333545392929413)
        ·
          refine ⟨36531369128312539761174265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194833968684333545392929413 36531369128312539761174265)
          ·
            refine ⟨27398526846234404820880699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36531369128312539761174265 27398526846234404820880699)
            ·
              refine ⟨41097790269351607231321049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27398526846234404820880699 41097790269351607231321049)
              ·
                refine ⟨30823342702013705423490787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41097790269351607231321049 30823342702013705423490787)
                ·
                  refine ⟨46235014053020558135236181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30823342702013705423490787 46235014053020558135236181)
                  ·
                    refine ⟨541816570933834665647299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46235014053020558135236181 541816570933834665647299)
                    ·
                      rfl

theorem cell23_3165552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_3165552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165552 prefixEnd_3165552 := by exact prefixLift 3165552
  have htrace : WordTrace (prefixWord ++ tailWord_3165552) baseStart_3165552 baseEnd_3165552 := by
    simpa [prefixWord, tailWord_3165552, baseEnd_3165552] using wordTrace_append hprefix tailTrace_3165552
  have hstable : (prefixWord ++ tailWord_3165552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165552).length < 2 ^ (prefixWord ++ tailWord_3165552).sum := by decide
  have hdescent : baseEnd_3165552 < baseStart_3165552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165557 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_3165557 : Nat := 118140960795 + 3165557 * 2 ^ 59
def prefixEnd_3165557 : Nat := 4983230072969 + 3 ^ 40 * 3165557 * 2
def baseEnd_3165557 : Nat := 1625452280204776477379375

theorem tailTrace_3165557 : CollatzResearch.WordTrace tailWord_3165557 prefixEnd_3165557 1625452280204776477379375 := by
  unfold tailWord_3165557
  simp only [CollatzResearch.WordTrace]
  refine ⟨115457348992735097938630925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76971565995156731959087283 115457348992735097938630925)
  ·
    refine ⟨43296505872275661726986597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115457348992735097938630925 43296505872275661726986597)
    ·
      refine ⟨8118094851051686573809987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43296505872275661726986597 8118094851051686573809987)
      ·
        refine ⟨12177142276577529860714981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8118094851051686573809987 12177142276577529860714981)
        ·
          refine ⟨2283214176858286848884059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12177142276577529860714981 2283214176858286848884059)
          ·
            refine ⟨3424821265287430273326089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283214176858286848884059 3424821265287430273326089)
            ·
              refine ⟨2568615948965572704994567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424821265287430273326089 2568615948965572704994567)
              ·
                refine ⟨3852923923448359057491851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568615948965572704994567 3852923923448359057491851)
                ·
                  refine ⟨5779385885172538586237777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852923923448359057491851 5779385885172538586237777)
                  ·
                    refine ⟨4334539413879403939678333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5779385885172538586237777 4334539413879403939678333)
                    ·
                      refine ⟨1625452280204776477379375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334539413879403939678333 1625452280204776477379375)
                      ·
                        rfl

theorem cell23_3165557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_3165557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165557 prefixEnd_3165557 := by exact prefixLift 3165557
  have htrace : WordTrace (prefixWord ++ tailWord_3165557) baseStart_3165557 baseEnd_3165557 := by
    simpa [prefixWord, tailWord_3165557, baseEnd_3165557] using wordTrace_append hprefix tailTrace_3165557
  have hstable : (prefixWord ++ tailWord_3165557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165557).length < 2 ^ (prefixWord ++ tailWord_3165557).sum := by decide
  have hdescent : baseEnd_3165557 < baseStart_3165557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165570 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3165570 : Nat := 118140960795 + 3165570 * 2 ^ 59
def prefixEnd_3165570 : Nat := 4983230072969 + 3 ^ 40 * 3165570 * 2
def baseEnd_3165570 : Nat := 1625458955453284926516815

theorem tailTrace_3165570 : CollatzResearch.WordTrace tailWord_3165570 prefixEnd_3165570 1625458955453284926516815 := by
  unfold tailWord_3165570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28864455785422000289713541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76971882094458667439236109 28864455785422000289713541)
  ·
    refine ⟨5412085459766625054321289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28864455785422000289713541 5412085459766625054321289)
    ·
      refine ⟨4059064094824968790740967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5412085459766625054321289 4059064094824968790740967)
      ·
        refine ⟨6088596142237453186111451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059064094824968790740967 6088596142237453186111451)
        ·
          refine ⟨9132894213356179779167177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6088596142237453186111451 9132894213356179779167177)
          ·
            refine ⟨6849670660017134834375383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9132894213356179779167177 6849670660017134834375383)
            ·
              refine ⟨10274505990025702251563075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849670660017134834375383 10274505990025702251563075)
              ·
                refine ⟨15411758985038553377344613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274505990025702251563075 15411758985038553377344613)
                ·
                  refine ⟨2889704809694728758252115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15411758985038553377344613 2889704809694728758252115)
                  ·
                    refine ⟨4334557214542093137378173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889704809694728758252115 4334557214542093137378173)
                    ·
                      refine ⟨1625458955453284926516815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334557214542093137378173 1625458955453284926516815)
                      ·
                        rfl

theorem cell23_3165570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3165570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165570 prefixEnd_3165570 := by exact prefixLift 3165570
  have htrace : WordTrace (prefixWord ++ tailWord_3165570) baseStart_3165570 baseEnd_3165570 := by
    simpa [prefixWord, tailWord_3165570, baseEnd_3165570] using wordTrace_append hprefix tailTrace_3165570
  have hstable : (prefixWord ++ tailWord_3165570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165570).length < 2 ^ (prefixWord ++ tailWord_3165570).sum := by decide
  have hdescent : baseEnd_3165570 < baseStart_3165570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165589 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3165589 : Nat := 118140960795 + 3165589 * 2 ^ 59
def prefixEnd_3165589 : Nat := 4983230072969 + 3 ^ 40 * 3165589 * 2
def baseEnd_3165589 : Nat := 1625468711585720352179227

theorem tailTrace_3165589 : CollatzResearch.WordTrace tailWord_3165589 prefixEnd_3165589 1625468711585720352179227 := by
  unfold tailWord_3165589
  simp only [CollatzResearch.WordTrace]
  refine ⟨115458516128619167403795821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76972344085746111602530547 115458516128619167403795821)
  ·
    refine ⟨43296943548232187776423433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115458516128619167403795821 43296943548232187776423433)
    ·
      refine ⟨32472707661174140832317575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43296943548232187776423433 32472707661174140832317575)
      ·
        refine ⟨48709061491761211248476363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32472707661174140832317575 48709061491761211248476363)
        ·
          refine ⟨73063592237641816872714545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48709061491761211248476363 73063592237641816872714545)
          ·
            refine ⟨54797694178231362654535909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73063592237641816872714545 54797694178231362654535909)
            ·
              refine ⟨10274567658418380497725483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54797694178231362654535909 10274567658418380497725483)
              ·
                refine ⟨15411851487627570746588225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274567658418380497725483 15411851487627570746588225)
                ·
                  refine ⟨11558888615720678059941169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15411851487627570746588225 11558888615720678059941169)
                  ·
                    refine ⟨8669166461790508544955877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11558888615720678059941169 8669166461790508544955877)
                    ·
                      refine ⟨1625468711585720352179227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8669166461790508544955877 1625468711585720352179227)
                      ·
                        rfl

theorem cell23_3165589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3165589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165589 prefixEnd_3165589 := by exact prefixLift 3165589
  have htrace : WordTrace (prefixWord ++ tailWord_3165589) baseStart_3165589 baseEnd_3165589 := by
    simpa [prefixWord, tailWord_3165589, baseEnd_3165589] using wordTrace_append hprefix tailTrace_3165589
  have hstable : (prefixWord ++ tailWord_3165589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165589).length < 2 ^ (prefixWord ++ tailWord_3165589).sum := by decide
  have hdescent : baseEnd_3165589 < baseStart_3165589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165593 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 1, 4, 2]
def baseStart_3165593 : Nat := 118140960795 + 3165593 * 2 ^ 59
def prefixEnd_3165593 : Nat := 4983230072969 + 3 ^ 40 * 3165593 * 2
def baseEnd_3165593 : Nat := 1625470765508338336529209

theorem tailTrace_3165593 : CollatzResearch.WordTrace tailWord_3165593 prefixEnd_3165593 1625470765508338336529209 := by
  unfold tailWord_3165593
  simp only [CollatzResearch.WordTrace]
  refine ⟨115458662020604676086941433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76972441347069784057960955 115458662020604676086941433)
  ·
    refine ⟨86593996515453507065206075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115458662020604676086941433 86593996515453507065206075)
    ·
      refine ⟨129890994773180260597809113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86593996515453507065206075 129890994773180260597809113)
      ·
        refine ⟨97418246079885195448356835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129890994773180260597809113 97418246079885195448356835)
        ·
          refine ⟨146127369119827793172535253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97418246079885195448356835 146127369119827793172535253)
          ·
            refine ⟨3424860213745963902481295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 146127369119827793172535253 3424860213745963902481295)
            ·
              refine ⟨5137290320618945853721943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424860213745963902481295 5137290320618945853721943)
              ·
                refine ⟨7705935480928418780582915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137290320618945853721943 7705935480928418780582915)
                ·
                  refine ⟨11558903221392628170874373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7705935480928418780582915 11558903221392628170874373)
                  ·
                    refine ⟨2167294354011117782038945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11558903221392628170874373 2167294354011117782038945)
                    ·
                      refine ⟨1625470765508338336529209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167294354011117782038945 1625470765508338336529209)
                      ·
                        rfl

theorem cell23_3165593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_3165593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165593 prefixEnd_3165593 := by exact prefixLift 3165593
  have htrace : WordTrace (prefixWord ++ tailWord_3165593) baseStart_3165593 baseEnd_3165593 := by
    simpa [prefixWord, tailWord_3165593, baseEnd_3165593] using wordTrace_append hprefix tailTrace_3165593
  have hstable : (prefixWord ++ tailWord_3165593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165593).length < 2 ^ (prefixWord ++ tailWord_3165593).sum := by decide
  have hdescent : baseEnd_3165593 < baseStart_3165593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165599 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 7]
def baseStart_3165599 : Nat := 118140960795 + 3165599 * 2 ^ 59
def prefixEnd_3165599 : Nat := 4983230072969 + 3 ^ 40 * 3165599 * 2
def baseEnd_3165599 : Nat := 180608205154696145894909

theorem tailTrace_3165599 : CollatzResearch.WordTrace tailWord_3165599 prefixEnd_3165599 180608205154696145894909 := by
  unfold tailWord_3165599
  simp only [CollatzResearch.WordTrace]
  refine ⟨115458880858582939111659851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76972587239055292741106567 115458880858582939111659851)
  ·
    refine ⟨173188321287874408667489777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115458880858582939111659851 173188321287874408667489777)
    ·
      refine ⟨129891240965905806500617333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173188321287874408667489777 129891240965905806500617333)
      ·
        refine ⟨12177303840553669359432875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129891240965905806500617333 12177303840553669359432875)
        ·
          refine ⟨18265955760830504039149313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12177303840553669359432875 18265955760830504039149313)
          ·
            refine ⟨13699466820622878029361985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18265955760830504039149313 13699466820622878029361985)
            ·
              refine ⟨10274600115467158522021489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13699466820622878029361985 10274600115467158522021489)
              ·
                refine ⟨7705950086600368891516117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10274600115467158522021489 7705950086600368891516117)
                ·
                  refine ⟨180608205154696145894909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7705950086600368891516117 180608205154696145894909)
                  ·
                    rfl

theorem cell23_3165599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 7].length) (baseStart_3165599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165599 prefixEnd_3165599 := by exact prefixLift 3165599
  have htrace : WordTrace (prefixWord ++ tailWord_3165599) baseStart_3165599 baseEnd_3165599 := by
    simpa [prefixWord, tailWord_3165599, baseEnd_3165599] using wordTrace_append hprefix tailTrace_3165599
  have hstable : (prefixWord ++ tailWord_3165599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165599).length < 2 ^ (prefixWord ++ tailWord_3165599).sum := by decide
  have hdescent : baseEnd_3165599 < baseStart_3165599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165639 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_3165639 : Nat := 118140960795 + 3165639 * 2 ^ 59
def prefixEnd_3165639 : Nat := 4983230072969 + 3 ^ 40 * 3165639 * 2
def baseEnd_3165639 : Nat := 1625494385618445156553997

theorem tailTrace_3165639 : CollatzResearch.WordTrace tailWord_3165639 prefixEnd_3165639 1625494385618445156553997 := by
  unfold tailWord_3165639
  simp only [CollatzResearch.WordTrace]
  refine ⟨115460339778438025943115971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76973559852292017295410647 115460339778438025943115971)
  ·
    refine ⟨173190509667657038914673957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115460339778438025943115971 173190509667657038914673957)
    ·
      refine ⟨32473220562685694796501367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173190509667657038914673957 32473220562685694796501367)
      ·
        refine ⟨48709830844028542194752051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32473220562685694796501367 48709830844028542194752051)
        ·
          refine ⟨73064746266042813292128077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48709830844028542194752051 73064746266042813292128077)
          ·
            refine ⟨27399279849766054984548029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73064746266042813292128077 27399279849766054984548029)
            ·
              refine ⟨10274729943662270619205511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27399279849766054984548029 10274729943662270619205511)
              ·
                refine ⟨15412094915493405928808267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274729943662270619205511 15412094915493405928808267)
                ·
                  refine ⟨23118142373240108893212401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15412094915493405928808267 23118142373240108893212401)
                  ·
                    refine ⟨17338606779930081669909301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23118142373240108893212401 17338606779930081669909301)
                    ·
                      refine ⟨1625494385618445156553997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17338606779930081669909301 1625494385618445156553997)
                      ·
                        rfl

theorem cell23_3165639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_3165639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165639 prefixEnd_3165639 := by exact prefixLift 3165639
  have htrace : WordTrace (prefixWord ++ tailWord_3165639) baseStart_3165639 baseEnd_3165639 := by
    simpa [prefixWord, tailWord_3165639, baseEnd_3165639] using wordTrace_append hprefix tailTrace_3165639
  have hstable : (prefixWord ++ tailWord_3165639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165639).length < 2 ^ (prefixWord ++ tailWord_3165639).sum := by decide
  have hdescent : baseEnd_3165639 < baseStart_3165639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165700 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3165700 : Nat := 118140960795 + 3165700 * 2 ^ 59
def prefixEnd_3165700 : Nat := 4983230072969 + 3 ^ 40 * 3165700 * 2
def baseEnd_3165700 : Nat := 1625525707938369417891217

theorem tailTrace_3165700 : CollatzResearch.WordTrace tailWord_3165700 prefixEnd_3165700 1625525707938369417891217 := by
  unfold tailWord_3165700
  simp only [CollatzResearch.WordTrace]
  refine ⟨57731282315608516680543277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76975043087478022240724369 57731282315608516680543277)
  ·
    refine ⟨21649230868353193755203729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57731282315608516680543277 21649230868353193755203729)
    ·
      refine ⟨16236923151264895316402797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21649230868353193755203729 16236923151264895316402797)
      ·
        refine ⟨6088846181724335743651049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16236923151264895316402797 6088846181724335743651049)
        ·
          refine ⟨4566634636293251807738287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6088846181724335743651049 4566634636293251807738287)
          ·
            refine ⟨6849951954439877711607431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566634636293251807738287 6849951954439877711607431)
            ·
              refine ⟨10274927931659816567411147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849951954439877711607431 10274927931659816567411147)
              ·
                refine ⟨15412391897489724851116721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274927931659816567411147 15412391897489724851116721)
                ·
                  refine ⟨11559293923117293638337541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15412391897489724851116721 11559293923117293638337541)
                  ·
                    refine ⟨2167367610584492557188289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11559293923117293638337541 2167367610584492557188289)
                    ·
                      refine ⟨1625525707938369417891217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167367610584492557188289 1625525707938369417891217)
                      ·
                        rfl

theorem cell23_3165700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3165700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165700 prefixEnd_3165700 := by exact prefixLift 3165700
  have htrace : WordTrace (prefixWord ++ tailWord_3165700) baseStart_3165700 baseEnd_3165700 := by
    simpa [prefixWord, tailWord_3165700, baseEnd_3165700] using wordTrace_append hprefix tailTrace_3165700
  have hstable : (prefixWord ++ tailWord_3165700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165700).length < 2 ^ (prefixWord ++ tailWord_3165700).sum := by decide
  have hdescent : baseEnd_3165700 < baseStart_3165700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165706 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_3165706 : Nat := 118140960795 + 3165706 * 2 ^ 59
def prefixEnd_3165706 : Nat := 4983230072969 + 3 ^ 40 * 3165706 * 2
def baseEnd_3165706 : Nat := 180614309869144043824021

theorem tailTrace_3165706 : CollatzResearch.WordTrace tailWord_3165706 prefixEnd_3165706 180614309869144043824021 := by
  unfold tailWord_3165706
  simp only [CollatzResearch.WordTrace]
  refine ⟨28865695867298824096451243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76975188979463530923869981 28865695867298824096451243)
  ·
    refine ⟨43298543800948236144676865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28865695867298824096451243 43298543800948236144676865)
    ·
      refine ⟨32473907850711177108507649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43298543800948236144676865 32473907850711177108507649)
      ·
        refine ⟨24355430888033382831380737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32473907850711177108507649 24355430888033382831380737)
        ·
          refine ⟨18266573166025037123535553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24355430888033382831380737 18266573166025037123535553)
          ·
            refine ⟨13699929874518777842651665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18266573166025037123535553 13699929874518777842651665)
            ·
              refine ⟨10274947405889083381988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13699929874518777842651665 10274947405889083381988749)
              ·
                refine ⟨3853105277208406268245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10274947405889083381988749 3853105277208406268245781)
                ·
                  refine ⟨180614309869144043824021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3853105277208406268245781 180614309869144043824021)
                  ·
                    rfl

theorem cell23_3165706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_3165706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165706 prefixEnd_3165706 := by exact prefixLift 3165706
  have htrace : WordTrace (prefixWord ++ tailWord_3165706) baseStart_3165706 baseEnd_3165706 := by
    simpa [prefixWord, tailWord_3165706, baseEnd_3165706] using wordTrace_append hprefix tailTrace_3165706
  have hstable : (prefixWord ++ tailWord_3165706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165706).length < 2 ^ (prefixWord ++ tailWord_3165706).sum := by decide
  have hdescent : baseEnd_3165706 < baseStart_3165706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165720 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3165720 : Nat := 118140960795 + 3165720 * 2 ^ 59
def prefixEnd_3165720 : Nat := 4983230072969 + 3 ^ 40 * 3165720 * 2
def baseEnd_3165720 : Nat := 1625535977551459339641125

theorem tailTrace_3165720 : CollatzResearch.WordTrace tailWord_3165720 prefixEnd_3165720 1625535977551459339641125 := by
  unfold tailWord_3165720
  simp only [CollatzResearch.WordTrace]
  refine ⟨57731647045572288388407307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76975529394096384517876409 57731647045572288388407307)
  ·
    refine ⟨86597470568358432582610961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57731647045572288388407307 86597470568358432582610961)
    ·
      refine ⟨64948102926268824436958221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86597470568358432582610961 64948102926268824436958221)
      ·
        refine ⟨24355538597350809163859333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64948102926268824436958221 24355538597350809163859333)
        ·
          refine ⟨4566663487003276718223625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24355538597350809163859333 4566663487003276718223625)
          ·
            refine ⟨3424997615252457538667719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4566663487003276718223625 3424997615252457538667719)
            ·
              refine ⟨5137496422878686308001579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424997615252457538667719 5137496422878686308001579)
              ·
                refine ⟨7706244634318029462002369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137496422878686308001579 7706244634318029462002369)
                ·
                  refine ⟨5779683475738522096501777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7706244634318029462002369 5779683475738522096501777)
                  ·
                    refine ⟨4334762606803891572376333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5779683475738522096501777 4334762606803891572376333)
                    ·
                      refine ⟨1625535977551459339641125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334762606803891572376333 1625535977551459339641125)
                      ·
                        rfl

theorem cell23_3165720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3165720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165720 prefixEnd_3165720 := by exact prefixLift 3165720
  have htrace : WordTrace (prefixWord ++ tailWord_3165720) baseStart_3165720 baseEnd_3165720 := by
    simpa [prefixWord, tailWord_3165720, baseEnd_3165720] using wordTrace_append hprefix tailTrace_3165720
  have hstable : (prefixWord ++ tailWord_3165720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165720).length < 2 ^ (prefixWord ++ tailWord_3165720).sum := by decide
  have hdescent : baseEnd_3165720 < baseStart_3165720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165786 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_3165786 : Nat := 118140960795 + 3165786 * 2 ^ 59
def prefixEnd_3165786 : Nat := 4983230072969 + 3 ^ 40 * 3165786 * 2
def baseEnd_3165786 : Nat := 1625569867274656081415821

theorem tailTrace_3165786 : CollatzResearch.WordTrace tailWord_3165786 prefixEnd_3165786 1625569867274656081415821 := by
  unfold tailWord_3165786
  simp only [CollatzResearch.WordTrace]
  refine ⟨28866425327226367512179303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76977134205936980032478141 28866425327226367512179303)
  ·
    refine ⟨43299637990839551268268955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28866425327226367512179303 43299637990839551268268955)
    ·
      refine ⟨64949456986259326902403433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43299637990839551268268955 64949456986259326902403433)
      ·
        refine ⟨48712092739694495176802575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64949456986259326902403433 48712092739694495176802575)
        ·
          refine ⟨73068139109541742765203863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48712092739694495176802575 73068139109541742765203863)
          ·
            refine ⟨109602208664312614147805795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73068139109541742765203863 109602208664312614147805795)
            ·
              refine ⟨164403312996468921221708693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109602208664312614147805795 164403312996468921221708693)
              ·
                refine ⟨7706405296709480682267595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164403312996468921221708693 7706405296709480682267595)
                ·
                  refine ⟨11559607945064221023401393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706405296709480682267595 11559607945064221023401393)
                  ·
                    refine ⟨8669705958798165767551045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11559607945064221023401393 8669705958798165767551045)
                    ·
                      refine ⟨1625569867274656081415821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8669705958798165767551045 1625569867274656081415821)
                      ·
                        rfl

theorem cell23_3165786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_3165786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165786 prefixEnd_3165786 := by exact prefixLift 3165786
  have htrace : WordTrace (prefixWord ++ tailWord_3165786) baseStart_3165786 baseEnd_3165786 := by
    simpa [prefixWord, tailWord_3165786, baseEnd_3165786] using wordTrace_append hprefix tailTrace_3165786
  have hstable : (prefixWord ++ tailWord_3165786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165786).length < 2 ^ (prefixWord ++ tailWord_3165786).sum := by decide
  have hdescent : baseEnd_3165786 < baseStart_3165786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165793 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_3165793 : Nat := 118140960795 + 3165793 * 2 ^ 59
def prefixEnd_3165793 : Nat := 4983230072969 + 3 ^ 40 * 3165793 * 2
def baseEnd_3165793 : Nat := 1625573461639237554028289

theorem tailTrace_3165793 : CollatzResearch.WordTrace tailWord_3165793 prefixEnd_3165793 1625573461639237554028289 := by
  unfold tailWord_3165793
  simp only [CollatzResearch.WordTrace]
  refine ⟨115465956619880110244222033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76977304413253406829481355 115465956619880110244222033)
  ·
    refine ⟨86599467464910082683166525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115465956619880110244222033 86599467464910082683166525)
    ·
      refine ⟨32474800299341281006187447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86599467464910082683166525 32474800299341281006187447)
      ·
        refine ⟨48712200449011921509281171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32474800299341281006187447 48712200449011921509281171)
        ·
          refine ⟨73068300673517882263921757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48712200449011921509281171 73068300673517882263921757)
          ·
            refine ⟨27400612752569205848970659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73068300673517882263921757 27400612752569205848970659)
            ·
              refine ⟨41100919128853808773455989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27400612752569205848970659 41100919128853808773455989)
              ·
                refine ⟨3853211168330044572511499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41100919128853808773455989 3853211168330044572511499)
                ·
                  refine ⟨5779816752495066858767249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853211168330044572511499 5779816752495066858767249)
                  ·
                    refine ⟨4334862564371300144075437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5779816752495066858767249 4334862564371300144075437)
                    ·
                      refine ⟨1625573461639237554028289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334862564371300144075437 1625573461639237554028289)
                      ·
                        rfl

theorem cell23_3165793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_3165793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165793 prefixEnd_3165793 := by exact prefixLift 3165793
  have htrace : WordTrace (prefixWord ++ tailWord_3165793) baseStart_3165793 baseEnd_3165793 := by
    simpa [prefixWord, tailWord_3165793, baseEnd_3165793] using wordTrace_append hprefix tailTrace_3165793
  have hstable : (prefixWord ++ tailWord_3165793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165793).length < 2 ^ (prefixWord ++ tailWord_3165793).sum := by decide
  have hdescent : baseEnd_3165793 < baseStart_3165793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165796 : List Nat := [2, 3, 1, 1, 2, 5, 9]
def baseStart_3165796 : Nat := 118140960795 + 3165796 * 2 ^ 59
def prefixEnd_3165796 : Nat := 4983230072969 + 3 ^ 40 * 3165796 * 2
def baseEnd_3165796 : Nat := 20068827186187667188775

theorem tailTrace_3165796 : CollatzResearch.WordTrace tailWord_3165796 prefixEnd_3165796 20068827186187667188775 := by
  unfold tailWord_3165796
  simp only [CollatzResearch.WordTrace]
  refine ⟨57733033019434620878290621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76977377359246161171054161 57733033019434620878290621)
  ·
    refine ⟨21649887382287982829358983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57733033019434620878290621 21649887382287982829358983)
    ·
      refine ⟨32474831073431974244038475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21649887382287982829358983 32474831073431974244038475)
      ·
        refine ⟨48712246610147961366057713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32474831073431974244038475 48712246610147961366057713)
        ·
          refine ⟨36534184957610971024543285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48712246610147961366057713 36534184957610971024543285)
          ·
            refine ⟨3425079839776028533550933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36534184957610971024543285 3425079839776028533550933)
            ·
              refine ⟨20068827186187667188775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3425079839776028533550933 20068827186187667188775)
              ·
                rfl

theorem cell23_3165796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 9].length) (baseStart_3165796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165796 prefixEnd_3165796 := by exact prefixLift 3165796
  have htrace : WordTrace (prefixWord ++ tailWord_3165796) baseStart_3165796 baseEnd_3165796 := by
    simpa [prefixWord, tailWord_3165796, baseEnd_3165796] using wordTrace_append hprefix tailTrace_3165796
  have hstable : (prefixWord ++ tailWord_3165796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165796).length < 2 ^ (prefixWord ++ tailWord_3165796).sum := by decide
  have hdescent : baseEnd_3165796 < baseStart_3165796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165813 : List Nat := [1, 3, 4, 2, 1, 2, 2, 8]
def baseStart_3165813 : Nat := 118140960795 + 3165813 * 2 ^ 59
def prefixEnd_3165813 : Nat := 4983230072969 + 3 ^ 40 * 3165813 * 2
def baseEnd_3165813 : Nat := 60206804861197313917711

theorem tailTrace_3165813 : CollatzResearch.WordTrace tailWord_3165813 prefixEnd_3165813 60206804861197313917711 := by
  unfold tailWord_3165813
  simp only [CollatzResearch.WordTrace]
  refine ⟨115466686079807653659950093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76977790719871769106633395 115466686079807653659950093)
  ·
    refine ⟨43300007279927870122481285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115466686079807653659950093 43300007279927870122481285)
    ·
      refine ⟨8118751364986475647965241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43300007279927870122481285 8118751364986475647965241)
      ·
        refine ⟨6089063523739856735973931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8118751364986475647965241 6089063523739856735973931)
        ·
          refine ⟨9133595285609785103960897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6089063523739856735973931 9133595285609785103960897)
          ·
            refine ⟨6850196464207338827970673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9133595285609785103960897 6850196464207338827970673)
            ·
              refine ⟨5137647348155504120978005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6850196464207338827970673 5137647348155504120978005)
              ·
                refine ⟨60206804861197313917711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5137647348155504120978005 60206804861197313917711)
                ·
                  rfl

theorem cell23_3165813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 8].length) (baseStart_3165813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165813 prefixEnd_3165813 := by exact prefixLift 3165813
  have htrace : WordTrace (prefixWord ++ tailWord_3165813) baseStart_3165813 baseEnd_3165813 := by
    simpa [prefixWord, tailWord_3165813, baseEnd_3165813] using wordTrace_append hprefix tailTrace_3165813
  have hstable : (prefixWord ++ tailWord_3165813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165813).length < 2 ^ (prefixWord ++ tailWord_3165813).sum := by decide
  have hdescent : baseEnd_3165813 < baseStart_3165813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165844 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_3165844 : Nat := 118140960795 + 3165844 * 2 ^ 59
def prefixEnd_3165844 : Nat := 4983230072969 + 3 ^ 40 * 3165844 * 2
def baseEnd_3165844 : Nat := 1625599649152616854490555

theorem tailTrace_3165844 : CollatzResearch.WordTrace tailWord_3165844 prefixEnd_3165844 1625599649152616854490555 := by
  unfold tailWord_3165844
  simp only [CollatzResearch.WordTrace]
  refine ⟨57733908371347672977164293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76978544495130230636219057 57733908371347672977164293)
  ·
    refine ⟨10825107819627688683218305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57733908371347672977164293 10825107819627688683218305)
    ·
      refine ⟨8118830864720766512413729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10825107819627688683218305 8118830864720766512413729)
      ·
        refine ⟨6089123148540574884310297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8118830864720766512413729 6089123148540574884310297)
        ·
          refine ⟨4566842361405431163232723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6089123148540574884310297 4566842361405431163232723)
          ·
            refine ⟨6850263542108146744849085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566842361405431163232723 6850263542108146744849085)
            ·
              refine ⟨2568848828290555029318407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6850263542108146744849085 2568848828290555029318407)
              ·
                refine ⟨3853273242435832543977611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568848828290555029318407 3853273242435832543977611)
                ·
                  refine ⟨5779909863653748815966417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853273242435832543977611 5779909863653748815966417)
                  ·
                    refine ⟨4334932397740311611974813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5779909863653748815966417 4334932397740311611974813)
                    ·
                      refine ⟨1625599649152616854490555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334932397740311611974813 1625599649152616854490555)
                      ·
                        rfl

theorem cell23_3165844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_3165844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165844 prefixEnd_3165844 := by exact prefixLift 3165844
  have htrace : WordTrace (prefixWord ++ tailWord_3165844) baseStart_3165844 baseEnd_3165844 := by
    simpa [prefixWord, tailWord_3165844, baseEnd_3165844] using wordTrace_append hprefix tailTrace_3165844
  have hstable : (prefixWord ++ tailWord_3165844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165844).length < 2 ^ (prefixWord ++ tailWord_3165844).sum := by decide
  have hdescent : baseEnd_3165844 < baseStart_3165844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165857 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3165857 : Nat := 118140960795 + 3165857 * 2 ^ 59
def prefixEnd_3165857 : Nat := 4983230072969 + 3 ^ 40 * 3165857 * 2
def baseEnd_3165857 : Nat := 1625606324401125303627995

theorem tailTrace_3165857 : CollatzResearch.WordTrace tailWord_3165857 prefixEnd_3165857 1625606324401125303627995 := by
  unfold tailWord_3165857
  simp only [CollatzResearch.WordTrace]
  refine ⟨115468290891648249174551825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76978860594432166116367883 115468290891648249174551825)
  ·
    refine ⟨86601218168736186880913869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115468290891648249174551825 86601218168736186880913869)
    ·
      refine ⟨32475456813276070080342701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86601218168736186880913869 32475456813276070080342701)
      ·
        refine ⟨12178296304978526280128513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32475456813276070080342701 12178296304978526280128513)
        ·
          refine ⟨9133722228733894710096385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12178296304978526280128513 9133722228733894710096385)
          ·
            refine ⟨6850291671550421032572289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9133722228733894710096385 6850291671550421032572289)
            ·
              refine ⟨5137718753662815774429217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6850291671550421032572289 5137718753662815774429217)
              ·
                refine ⟨3853289065247111830821913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137718753662815774429217 3853289065247111830821913)
                ·
                  refine ⟨2889966798935333873116435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853289065247111830821913 2889966798935333873116435)
                  ·
                    refine ⟨4334950198403000809674653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889966798935333873116435 4334950198403000809674653)
                    ·
                      refine ⟨1625606324401125303627995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4334950198403000809674653 1625606324401125303627995)
                      ·
                        rfl

theorem cell23_3165857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3165857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165857 prefixEnd_3165857 := by exact prefixLift 3165857
  have htrace : WordTrace (prefixWord ++ tailWord_3165857) baseStart_3165857 baseEnd_3165857 := by
    simpa [prefixWord, tailWord_3165857, baseEnd_3165857] using wordTrace_append hprefix tailTrace_3165857
  have hstable : (prefixWord ++ tailWord_3165857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165857).length < 2 ^ (prefixWord ++ tailWord_3165857).sum := by decide
  have hdescent : baseEnd_3165857 < baseStart_3165857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165864 : List Nat := [2, 1, 7, 1, 2, 1, 1, 8]
def baseStart_3165864 : Nat := 118140960795 + 3165864 * 2 ^ 59
def prefixEnd_3165864 : Nat := 4983230072969 + 3 ^ 40 * 3165864 * 2
def baseEnd_3165864 : Nat := 60207774769100250971869

theorem tailTrace_3165864 : CollatzResearch.WordTrace tailWord_3165864 prefixEnd_3165864 60207774769100250971869 := by
  unfold tailWord_3165864
  simp only [CollatzResearch.WordTrace]
  refine ⟨57734273101311444685028323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76979030801748592913371097 57734273101311444685028323)
  ·
    refine ⟨86601409651967167027542485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57734273101311444685028323 86601409651967167027542485)
    ·
      refine ⟨2029720538717980477208027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 86601409651967167027542485 2029720538717980477208027)
      ·
        refine ⟨3044580808076970715812041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029720538717980477208027 3044580808076970715812041)
        ·
          refine ⟨2283435606057728036859031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3044580808076970715812041 2283435606057728036859031)
          ·
            refine ⟨3425153409086592055288547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283435606057728036859031 3425153409086592055288547)
            ·
              refine ⟨5137730113629888082932821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425153409086592055288547 5137730113629888082932821)
              ·
                refine ⟨60207774769100250971869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5137730113629888082932821 60207774769100250971869)
                ·
                  rfl

theorem cell23_3165864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 8].length) (baseStart_3165864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165864 prefixEnd_3165864 := by exact prefixLift 3165864
  have htrace : WordTrace (prefixWord ++ tailWord_3165864) baseStart_3165864 baseEnd_3165864 := by
    simpa [prefixWord, tailWord_3165864, baseEnd_3165864] using wordTrace_append hprefix tailTrace_3165864
  have hstable : (prefixWord ++ tailWord_3165864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165864).length < 2 ^ (prefixWord ++ tailWord_3165864).sum := by decide
  have hdescent : baseEnd_3165864 < baseStart_3165864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165901 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3165901 : Nat := 118140960795 + 3165901 * 2 ^ 59
def prefixEnd_3165901 : Nat := 4983230072969 + 3 ^ 40 * 3165901 * 2
def baseEnd_3165901 : Nat := 1625628917549923131477793

theorem tailTrace_3165901 : CollatzResearch.WordTrace tailWord_3165901 prefixEnd_3165901 1625628917549923131477793 := by
  unfold tailWord_3165901
  simp only [CollatzResearch.WordTrace]
  refine ⟨115469895703488844689153557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76979930468992563126102371 115469895703488844689153557)
  ·
    refine ⟨5412651361101039594804073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115469895703488844689153557 5412651361101039594804073)
    ·
      refine ⟨4059488520825779696103055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5412651361101039594804073 4059488520825779696103055)
      ·
        refine ⟨6089232781238669544154583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059488520825779696103055 6089232781238669544154583)
        ·
          refine ⟨9133849171858004316231875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6089232781238669544154583 9133849171858004316231875)
          ·
            refine ⟨13700773757787006474347813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9133849171858004316231875 13700773757787006474347813)
            ·
              refine ⟨2568895079585063713940215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13700773757787006474347813 2568895079585063713940215)
              ·
                refine ⟨3853342619377595570910323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568895079585063713940215 3853342619377595570910323)
                ·
                  refine ⟨5780013929066393356365485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853342619377595570910323 5780013929066393356365485)
                  ·
                    refine ⟨2167505223399897508637057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5780013929066393356365485 2167505223399897508637057)
                    ·
                      refine ⟨1625628917549923131477793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167505223399897508637057 1625628917549923131477793)
                      ·
                        rfl

theorem cell23_3165901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3165901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165901 prefixEnd_3165901 := by exact prefixLift 3165901
  have htrace : WordTrace (prefixWord ++ tailWord_3165901) baseStart_3165901 baseEnd_3165901 := by
    simpa [prefixWord, tailWord_3165901, baseEnd_3165901] using wordTrace_append hprefix tailTrace_3165901
  have hstable : (prefixWord ++ tailWord_3165901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165901).length < 2 ^ (prefixWord ++ tailWord_3165901).sum := by decide
  have hdescent : baseEnd_3165901 < baseStart_3165901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165913 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_3165913 : Nat := 118140960795 + 3165913 * 2 ^ 59
def prefixEnd_3165913 : Nat := 4983230072969 + 3 ^ 40 * 3165913 * 2
def baseEnd_3165913 : Nat := 1625635079317777084527737

theorem tailTrace_3165913 : CollatzResearch.WordTrace tailWord_3165913 prefixEnd_3165913 1625635079317777084527737 := by
  unfold tailWord_3165913
  simp only [CollatzResearch.WordTrace]
  refine ⟨115470333379445370738590393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76980222252963580492393595 115470333379445370738590393)
  ·
    refine ⟨86602750034584028053942795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115470333379445370738590393 86602750034584028053942795)
    ·
      refine ⟨129904125051876042080914193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86602750034584028053942795 129904125051876042080914193)
      ·
        refine ⟨97428093788907031560685645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129904125051876042080914193 97428093788907031560685645)
        ·
          refine ⟨36535535170840136835257117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97428093788907031560685645 36535535170840136835257117)
          ·
            refine ⟨13700825689065051313221419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36535535170840136835257117 13700825689065051313221419)
            ·
              refine ⟨20551238533597576969832129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13700825689065051313221419 20551238533597576969832129)
              ·
                refine ⟨15413428900198182727374097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20551238533597576969832129 15413428900198182727374097)
                ·
                  refine ⟨11560071675148637045530573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15413428900198182727374097 11560071675148637045530573)
                  ·
                    refine ⟨4335026878180738892073965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11560071675148637045530573 4335026878180738892073965)
                    ·
                      refine ⟨1625635079317777084527737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4335026878180738892073965 1625635079317777084527737)
                      ·
                        rfl

theorem cell23_3165913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_3165913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165913 prefixEnd_3165913 := by exact prefixLift 3165913
  have htrace : WordTrace (prefixWord ++ tailWord_3165913) baseStart_3165913 baseEnd_3165913 := by
    simpa [prefixWord, tailWord_3165913, baseEnd_3165913] using wordTrace_append hprefix tailTrace_3165913
  have hstable : (prefixWord ++ tailWord_3165913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165913).length < 2 ^ (prefixWord ++ tailWord_3165913).sum := by decide
  have hdescent : baseEnd_3165913 < baseStart_3165913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165914 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2]
def baseStart_3165914 : Nat := 118140960795 + 3165914 * 2 ^ 59
def prefixEnd_3165914 : Nat := 4983230072969 + 3 ^ 40 * 3165914 * 2
def baseEnd_3165914 : Nat := 1625635592798431580615233

theorem tailTrace_3165914 : CollatzResearch.WordTrace tailWord_3165914 prefixEnd_3165914 1625635592798431580615233 := by
  unfold tailWord_3165914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28867592463110436977344199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76980246568294498606251197 28867592463110436977344199)
  ·
    refine ⟨43301388694665655466016299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28867592463110436977344199 43301388694665655466016299)
    ·
      refine ⟨64952083041998483199024449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43301388694665655466016299 64952083041998483199024449)
      ·
        refine ⟨48714062281498862399268337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64952083041998483199024449 48714062281498862399268337)
        ·
          refine ⟨36535546711124146799451253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48714062281498862399268337 36535546711124146799451253)
          ·
            refine ⟨3425207504167888762448555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36535546711124146799451253 3425207504167888762448555)
            ·
              refine ⟨5137811256251833143672833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425207504167888762448555 5137811256251833143672833)
              ·
                refine ⟨3853358442188874857754625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137811256251833143672833 3853358442188874857754625)
                ·
                  refine ⟨2890018831641656143315969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853358442188874857754625 2890018831641656143315969)
                  ·
                    refine ⟨2167514123731242107486977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890018831641656143315969 2167514123731242107486977)
                    ·
                      refine ⟨1625635592798431580615233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167514123731242107486977 1625635592798431580615233)
                      ·
                        rfl

theorem cell23_3165914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_3165914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165914 prefixEnd_3165914 := by exact prefixLift 3165914
  have htrace : WordTrace (prefixWord ++ tailWord_3165914) baseStart_3165914 baseEnd_3165914 := by
    simpa [prefixWord, tailWord_3165914, baseEnd_3165914] using wordTrace_append hprefix tailTrace_3165914
  have hstable : (prefixWord ++ tailWord_3165914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165914).length < 2 ^ (prefixWord ++ tailWord_3165914).sum := by decide
  have hdescent : baseEnd_3165914 < baseStart_3165914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165933 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3165933 : Nat := 118140960795 + 3165933 * 2 ^ 59
def prefixEnd_3165933 : Nat := 4983230072969 + 3 ^ 40 * 3165933 * 2
def baseEnd_3165933 : Nat := 541881782976955668759215

theorem tailTrace_3165933 : CollatzResearch.WordTrace tailWord_3165933 prefixEnd_3165933 541881782976955668759215 := by
  unfold tailWord_3165933
  simp only [CollatzResearch.WordTrace]
  refine ⟨115471062839372914154318453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76980708559581942769545635 115471062839372914154318453)
  ·
    refine ⟨10825412141191210701967355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115471062839372914154318453 10825412141191210701967355)
    ·
      refine ⟨16238118211786816052951033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825412141191210701967355 16238118211786816052951033)
      ·
        refine ⟨12178588658840112039713275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16238118211786816052951033 12178588658840112039713275)
        ·
          refine ⟨18267882988260168059569913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12178588658840112039713275 18267882988260168059569913)
          ·
            refine ⟨13700912241195126044677435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18267882988260168059569913 13700912241195126044677435)
            ·
              refine ⟨20551368361792689067016153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13700912241195126044677435 20551368361792689067016153)
              ·
                refine ⟨15413526271344516800262115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20551368361792689067016153 15413526271344516800262115)
                ·
                  refine ⟨23120289407016775200393173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15413526271344516800262115 23120289407016775200393173)
                  ·
                    refine ⟨541881782976955668759215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23120289407016775200393173 541881782976955668759215)
                    ·
                      rfl

theorem cell23_3165933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3165933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165933 prefixEnd_3165933 := by exact prefixLift 3165933
  have htrace : WordTrace (prefixWord ++ tailWord_3165933) baseStart_3165933 baseEnd_3165933 := by
    simpa [prefixWord, tailWord_3165933, baseEnd_3165933] using wordTrace_append hprefix tailTrace_3165933
  have hstable : (prefixWord ++ tailWord_3165933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165933).length < 2 ^ (prefixWord ++ tailWord_3165933).sum := by decide
  have hdescent : baseEnd_3165933 < baseStart_3165933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165946 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_3165946 : Nat := 118140960795 + 3165946 * 2 ^ 59
def prefixEnd_3165946 : Nat := 4983230072969 + 3 ^ 40 * 3165946 * 2
def baseEnd_3165946 : Nat := 541884008059791818471695

theorem tailTrace_3165946 : CollatzResearch.WordTrace tailWord_3165946 prefixEnd_3165946 541884008059791818471695 := by
  unfold tailWord_3165946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28867884247081454343635423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76981024658883878249694461 28867884247081454343635423)
  ·
    refine ⟨43301826370622181515453135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28867884247081454343635423 43301826370622181515453135)
    ·
      refine ⟨64952739555933272273179703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43301826370622181515453135 64952739555933272273179703)
      ·
        refine ⟨97429109333899908409769555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64952739555933272273179703 97429109333899908409769555)
        ·
          refine ⟨146143664000849862614654333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97429109333899908409769555 146143664000849862614654333)
          ·
            refine ⟨54803874000318698480495375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146143664000849862614654333 54803874000318698480495375)
            ·
              refine ⟨82205811000478047720743063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54803874000318698480495375 82205811000478047720743063)
              ·
                refine ⟨123308716500717071581114595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82205811000478047720743063 123308716500717071581114595)
                ·
                  refine ⟨184963074751075607371671893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123308716500717071581114595 184963074751075607371671893)
                  ·
                    refine ⟨541884008059791818471695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 184963074751075607371671893 541884008059791818471695)
                    ·
                      rfl

theorem cell23_3165946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_3165946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165946 prefixEnd_3165946 := by exact prefixLift 3165946
  have htrace : WordTrace (prefixWord ++ tailWord_3165946) baseStart_3165946 baseEnd_3165946 := by
    simpa [prefixWord, tailWord_3165946, baseEnd_3165946] using wordTrace_append hprefix tailTrace_3165946
  have hstable : (prefixWord ++ tailWord_3165946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165946).length < 2 ^ (prefixWord ++ tailWord_3165946).sum := by decide
  have hdescent : baseEnd_3165946 < baseStart_3165946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165953 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3165953 : Nat := 118140960795 + 3165953 * 2 ^ 59
def prefixEnd_3165953 : Nat := 4983230072969 + 3 ^ 40 * 3165953 * 2
def baseEnd_3165953 : Nat := 1625655618543956928027553

theorem tailTrace_3165953 : CollatzResearch.WordTrace tailWord_3165953 prefixEnd_3165953 1625655618543956928027553 := by
  unfold tailWord_3165953
  simp only [CollatzResearch.WordTrace]
  refine ⟨115471792299300457570046513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76981194866200305046697675 115471792299300457570046513)
  ·
    refine ⟨86603844224475343177534885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115471792299300457570046513 86603844224475343177534885)
    ·
      refine ⟨16238220792089126845787791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86603844224475343177534885 16238220792089126845787791)
      ·
        refine ⟨24357331188133690268681687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238220792089126845787791 24357331188133690268681687)
        ·
          refine ⟨36535996782200535403022531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24357331188133690268681687 36535996782200535403022531)
          ·
            refine ⟨54803995173300803104533797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36535996782200535403022531 54803995173300803104533797)
            ·
              refine ⟨10275749094993900582100087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54803995173300803104533797 10275749094993900582100087)
              ·
                refine ⟨15413623642490850873150131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10275749094993900582100087 15413623642490850873150131)
                ·
                  refine ⟨23120435463736276309725197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15413623642490850873150131 23120435463736276309725197)
                  ·
                    refine ⟨8670163298901103616146949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23120435463736276309725197 8670163298901103616146949)
                    ·
                      refine ⟨1625655618543956928027553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8670163298901103616146949 1625655618543956928027553)
                      ·
                        rfl

theorem cell23_3165953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3165953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165953 prefixEnd_3165953 := by exact prefixLift 3165953
  have htrace : WordTrace (prefixWord ++ tailWord_3165953) baseStart_3165953 baseEnd_3165953 := by
    simpa [prefixWord, tailWord_3165953, baseEnd_3165953] using wordTrace_append hprefix tailTrace_3165953
  have hstable : (prefixWord ++ tailWord_3165953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165953).length < 2 ^ (prefixWord ++ tailWord_3165953).sum := by decide
  have hdescent : baseEnd_3165953 < baseStart_3165953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165963 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 5, 4]
def baseStart_3165963 : Nat := 118140960795 + 3165963 * 2 ^ 59
def prefixEnd_3165963 : Nat := 4983230072969 + 3 ^ 40 * 3165963 * 2
def baseEnd_3165963 : Nat := 541886917783500629634169

theorem tailTrace_3165963 : CollatzResearch.WordTrace tailWord_3165963 prefixEnd_3165963 541886917783500629634169 := by
  unfold tailWord_3165963
  simp only [CollatzResearch.WordTrace]
  refine ⟨115472157029264229277910543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76981438019509486185273695 115472157029264229277910543)
  ·
    refine ⟨173208235543896343916865815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115472157029264229277910543 173208235543896343916865815)
    ·
      refine ⟨259812353315844515875298723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173208235543896343916865815 259812353315844515875298723)
      ·
        refine ⟨389718529973766773812948085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259812353315844515875298723 389718529973766773812948085)
        ·
          refine ⟨36536112185040635044963883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 389718529973766773812948085 36536112185040635044963883)
          ·
            refine ⟨54804168277560952567445825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36536112185040635044963883 54804168277560952567445825)
            ·
              refine ⟨41103126208170714425584369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54804168277560952567445825 41103126208170714425584369)
              ·
                refine ⟨30827344656128035819188277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41103126208170714425584369 30827344656128035819188277)
                ·
                  refine ⟨2890063561512003358048901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30827344656128035819188277 2890063561512003358048901)
                  ·
                    refine ⟨541886917783500629634169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890063561512003358048901 541886917783500629634169)
                    ·
                      rfl

theorem cell23_3165963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 4].length) (baseStart_3165963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165963 prefixEnd_3165963 := by exact prefixLift 3165963
  have htrace : WordTrace (prefixWord ++ tailWord_3165963) baseStart_3165963 baseEnd_3165963 := by
    simpa [prefixWord, tailWord_3165963, baseEnd_3165963] using wordTrace_append hprefix tailTrace_3165963
  have hstable : (prefixWord ++ tailWord_3165963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165963).length < 2 ^ (prefixWord ++ tailWord_3165963).sum := by decide
  have hdescent : baseEnd_3165963 < baseStart_3165963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165982 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3165982 : Nat := 118140960795 + 3165982 * 2 ^ 59
def prefixEnd_3165982 : Nat := 4983230072969 + 3 ^ 40 * 3165982 * 2
def baseEnd_3165982 : Nat := 1625670509482937314564921

theorem tailTrace_3165982 : CollatzResearch.WordTrace tailWord_3165982 prefixEnd_3165982 1625670509482937314564921 := by
  unfold tailWord_3165982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434106252024424440356525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76981900010796930348568133 14434106252024424440356525)
  ·
    refine ⟨5412789844509159165133697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14434106252024424440356525 5412789844509159165133697)
    ·
      refine ⟨4059592383381869373850273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5412789844509159165133697 4059592383381869373850273)
      ·
        refine ⟨3044694287536402030387705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4059592383381869373850273 3044694287536402030387705)
        ·
          refine ⟨2283520715652301522790779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3044694287536402030387705 2283520715652301522790779)
          ·
            refine ⟨3425281073478452284186169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283520715652301522790779 3425281073478452284186169)
            ·
              refine ⟨2568960805108839213139627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425281073478452284186169 2568960805108839213139627)
              ·
                refine ⟨3853441207663258819709441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568960805108839213139627 3853441207663258819709441)
                ·
                  refine ⟨2890080905747444114782081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853441207663258819709441 2890080905747444114782081)
                  ·
                    refine ⟨2167560679310583086086561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890080905747444114782081 2167560679310583086086561)
                    ·
                      refine ⟨1625670509482937314564921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167560679310583086086561 1625670509482937314564921)
                      ·
                        rfl

theorem cell23_3165982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3165982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3165982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3165982 prefixEnd_3165982 := by exact prefixLift 3165982
  have htrace : WordTrace (prefixWord ++ tailWord_3165982) baseStart_3165982 baseEnd_3165982 := by
    simpa [prefixWord, tailWord_3165982, baseEnd_3165982] using wordTrace_append hprefix tailTrace_3165982
  have hstable : (prefixWord ++ tailWord_3165982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165982).length < 2 ^ (prefixWord ++ tailWord_3165982).sum := by decide
  have hdescent : baseEnd_3165982 < baseStart_3165982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166030 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_3166030 : Nat := 118140960795 + 3166030 * 2 ^ 59
def prefixEnd_3166030 : Nat := 4983230072969 + 3 ^ 40 * 3166030 * 2
def baseEnd_3166030 : Nat := 1625695156554353126764699

theorem tailTrace_3166030 : CollatzResearch.WordTrace tailWord_3166030 prefixEnd_3166030 1625695156554353126764699 := by
  unfold tailWord_3166030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434325090002687465074943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76983067146680999813733029 14434325090002687465074943)
  ·
    refine ⟨21651487635004031197612415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14434325090002687465074943 21651487635004031197612415)
    ·
      refine ⟨32477231452506046796418623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21651487635004031197612415 32477231452506046796418623)
      ·
        refine ⟨48715847178759070194627935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32477231452506046796418623 48715847178759070194627935)
        ·
          refine ⟨73073770768138605291941903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48715847178759070194627935 73073770768138605291941903)
          ·
            refine ⟨109610656152207907937912855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73073770768138605291941903 109610656152207907937912855)
            ·
              refine ⟨164415984228311861906869283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109610656152207907937912855 164415984228311861906869283)
              ·
                refine ⟨246623976342467792860303925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164415984228311861906869283 246623976342467792860303925)
                ·
                  refine ⟨23120997782106355580653493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246623976342467792860303925 23120997782106355580653493)
                  ·
                    refine ⟨2167593542072470835686265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23120997782106355580653493 2167593542072470835686265)
                    ·
                      refine ⟨1625695156554353126764699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167593542072470835686265 1625695156554353126764699)
                      ·
                        rfl

theorem cell23_3166030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_3166030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166030 prefixEnd_3166030 := by exact prefixLift 3166030
  have htrace : WordTrace (prefixWord ++ tailWord_3166030) baseStart_3166030 baseEnd_3166030 := by
    simpa [prefixWord, tailWord_3166030, baseEnd_3166030] using wordTrace_append hprefix tailTrace_3166030
  have hstable : (prefixWord ++ tailWord_3166030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166030).length < 2 ^ (prefixWord ++ tailWord_3166030).sum := by decide
  have hdescent : baseEnd_3166030 < baseStart_3166030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166060 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_3166060 : Nat := 118140960795 + 3166060 * 2 ^ 59
def prefixEnd_3166060 : Nat := 4983230072969 + 3 ^ 40 * 3166060 * 2
def baseEnd_3166060 : Nat := 1625710560973988009389561

theorem tailTrace_3166060 : CollatzResearch.WordTrace tailWord_3166060 prefixEnd_3166060 1625710560973988009389561 := by
  unfold tailWord_3166060
  simp only [CollatzResearch.WordTrace]
  refine ⟨57737847454956407422095817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76983796606608543229461089 57737847454956407422095817)
  ·
    refine ⟨43303385591217305566571863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57737847454956407422095817 43303385591217305566571863)
    ·
      refine ⟨64955078386825958349857795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43303385591217305566571863 64955078386825958349857795)
      ·
        refine ⟨97432617580238937524786693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64955078386825958349857795 97432617580238937524786693)
        ·
          refine ⟨18268615796294800785897505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97432617580238937524786693 18268615796294800785897505)
          ·
            refine ⟨13701461847221100589423129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18268615796294800785897505 13701461847221100589423129)
            ·
              refine ⟨10276096385415825442067347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13701461847221100589423129 10276096385415825442067347)
              ·
                refine ⟨15414144578123738163101021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10276096385415825442067347 15414144578123738163101021)
                ·
                  refine ⟨5780304216796401811162883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15414144578123738163101021 5780304216796401811162883)
                  ·
                    refine ⟨8670456325194602716744325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5780304216796401811162883 8670456325194602716744325)
                    ·
                      refine ⟨1625710560973988009389561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8670456325194602716744325 1625710560973988009389561)
                      ·
                        rfl

theorem cell23_3166060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_3166060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166060 prefixEnd_3166060 := by exact prefixLift 3166060
  have htrace : WordTrace (prefixWord ++ tailWord_3166060) baseStart_3166060 baseEnd_3166060 := by
    simpa [prefixWord, tailWord_3166060, baseEnd_3166060] using wordTrace_append hprefix tailTrace_3166060
  have hstable : (prefixWord ++ tailWord_3166060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166060).length < 2 ^ (prefixWord ++ tailWord_3166060).sum := by decide
  have hdescent : baseEnd_3166060 < baseStart_3166060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166077 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_3166077 : Nat := 118140960795 + 3166077 * 2 ^ 59
def prefixEnd_3166077 : Nat := 4983230072969 + 3 ^ 40 * 3166077 * 2
def baseEnd_3166077 : Nat := 1625719290145114442876983

theorem tailTrace_3166077 : CollatzResearch.WordTrace tailWord_3166077 prefixEnd_3166077 1625719290145114442876983 := by
  unfold tailWord_3166077
  simp only [CollatzResearch.WordTrace]
  refine ⟨115476314950851226747560485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76984209967234151165040323 115476314950851226747560485)
  ·
    refine ⟨21651809053284605015167591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115476314950851226747560485 21651809053284605015167591)
    ·
      refine ⟨32477713579926907522751387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21651809053284605015167591 32477713579926907522751387)
      ·
        refine ⟨48716570369890361284127081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32477713579926907522751387 48716570369890361284127081)
        ·
          refine ⟨36537427777417770963095311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48716570369890361284127081 36537427777417770963095311)
          ·
            refine ⟨54806141666126656444642967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36537427777417770963095311 54806141666126656444642967)
            ·
              refine ⟨82209212499189984666964451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54806141666126656444642967 82209212499189984666964451)
              ·
                refine ⟨123313818748784977000446677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82209212499189984666964451 123313818748784977000446677)
                ·
                  refine ⟨2890167626924647898447969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123313818748784977000446677 2890167626924647898447969)
                  ·
                    refine ⟨2167625720193485923835977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890167626924647898447969 2167625720193485923835977)
                    ·
                      refine ⟨1625719290145114442876983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167625720193485923835977 1625719290145114442876983)
                      ·
                        rfl

theorem cell23_3166077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_3166077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166077 prefixEnd_3166077 := by exact prefixLift 3166077
  have htrace : WordTrace (prefixWord ++ tailWord_3166077) baseStart_3166077 baseEnd_3166077 := by
    simpa [prefixWord, tailWord_3166077, baseEnd_3166077] using wordTrace_append hprefix tailTrace_3166077
  have hstable : (prefixWord ++ tailWord_3166077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166077).length < 2 ^ (prefixWord ++ tailWord_3166077).sum := by decide
  have hdescent : baseEnd_3166077 < baseStart_3166077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166083 : List Nat := [1, 1, 1, 3, 4, 3, 10]
def baseStart_3166083 : Nat := 118140960795 + 3166083 * 2 ^ 59
def prefixEnd_3166083 : Nat := 4983230072969 + 3 ^ 40 * 3166083 * 2
def baseEnd_3166083 : Nat := 20070646555914091597555

theorem tailTrace_3166083 : CollatzResearch.WordTrace tailWord_3166083 prefixEnd_3166083 20070646555914091597555 := by
  unfold tailWord_3166083
  simp only [CollatzResearch.WordTrace]
  refine ⟨115476533788829489772278903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76984355859219659848185935 115476533788829489772278903)
  ·
    refine ⟨173214800683244234658418355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115476533788829489772278903 173214800683244234658418355)
    ·
      refine ⟨259822201024866351987627533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173214800683244234658418355 259822201024866351987627533)
      ·
        refine ⟨97433325384324881995360325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259822201024866351987627533 97433325384324881995360325)
        ·
          refine ⟨18268748509560915374130061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97433325384324881995360325 18268748509560915374130061)
          ·
            refine ⟨6850780691085343265298773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18268748509560915374130061 6850780691085343265298773)
            ·
              refine ⟨20070646555914091597555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6850780691085343265298773 20070646555914091597555)
              ·
                rfl

theorem cell23_3166083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 10].length) (baseStart_3166083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166083 prefixEnd_3166083 := by exact prefixLift 3166083
  have htrace : WordTrace (prefixWord ++ tailWord_3166083) baseStart_3166083 baseEnd_3166083 := by
    simpa [prefixWord, tailWord_3166083, baseEnd_3166083] using wordTrace_append hprefix tailTrace_3166083
  have hstable : (prefixWord ++ tailWord_3166083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166083).length < 2 ^ (prefixWord ++ tailWord_3166083).sum := by decide
  have hdescent : baseEnd_3166083 < baseStart_3166083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166087 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 4, 4]
def baseStart_3166087 : Nat := 118140960795 + 3166087 * 2 ^ 59
def prefixEnd_3166087 : Nat := 4983230072969 + 3 ^ 40 * 3166087 * 2
def baseEnd_3166087 : Nat := 541908141650553134583979

theorem tailTrace_3166087 : CollatzResearch.WordTrace tailWord_3166087 prefixEnd_3166087 541908141650553134583979 := by
  unfold tailWord_3166087
  simp only [CollatzResearch.WordTrace]
  refine ⟨115476679680814998455424515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76984453120543332303616343 115476679680814998455424515)
  ·
    refine ⟨173215019521222497683136773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115476679680814998455424515 173215019521222497683136773)
    ·
      refine ⟨32477816160229218315588145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173215019521222497683136773 32477816160229218315588145)
      ·
        refine ⟨24358362120171913736691109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32477816160229218315588145 24358362120171913736691109)
        ·
          refine ⟨4567192897532233825629583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24358362120171913736691109 4567192897532233825629583)
          ·
            refine ⟨6850789346298350738444375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567192897532233825629583 6850789346298350738444375)
            ·
              refine ⟨10276184019447526107666563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6850789346298350738444375 10276184019447526107666563)
              ·
                refine ⟨15414276029171289161499845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10276184019447526107666563 15414276029171289161499845)
                ·
                  refine ⟨2890176755469616717781221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15414276029171289161499845 2890176755469616717781221)
                  ·
                    refine ⟨541908141650553134583979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890176755469616717781221 541908141650553134583979)
                    ·
                      rfl

theorem cell23_3166087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_3166087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166087 prefixEnd_3166087 := by exact prefixLift 3166087
  have htrace : WordTrace (prefixWord ++ tailWord_3166087) baseStart_3166087 baseEnd_3166087 := by
    simpa [prefixWord, tailWord_3166087, baseEnd_3166087] using wordTrace_append hprefix tailTrace_3166087
  have hstable : (prefixWord ++ tailWord_3166087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166087).length < 2 ^ (prefixWord ++ tailWord_3166087).sum := by decide
  have hdescent : baseEnd_3166087 < baseStart_3166087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166104 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 1, 6]
def baseStart_3166104 : Nat := 118140960795 + 3166104 * 2 ^ 59
def prefixEnd_3166104 : Nat := 4983230072969 + 3 ^ 40 * 3166104 * 2
def baseEnd_3166104 : Nat := 541911051374261945746453

theorem tailTrace_3166104 : CollatzResearch.WordTrace tailWord_3166104 prefixEnd_3166104 541911051374261945746453 := by
  unfold tailWord_3166104
  simp only [CollatzResearch.WordTrace]
  refine ⟨57738649860876705179396683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76984866481168940239195577 57738649860876705179396683)
  ·
    refine ⟨86607974791315057769095025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57738649860876705179396683 86607974791315057769095025)
    ·
      refine ⟨64955981093486293326821269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86607974791315057769095025 64955981093486293326821269)
      ·
        refine ⟨3044811613757169999694747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64955981093486293326821269 3044811613757169999694747)
        ·
          refine ⟨4567217420635754999542121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044811613757169999694747 4567217420635754999542121)
          ·
            refine ⟨3425413065476816249656591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4567217420635754999542121 3425413065476816249656591)
            ·
              refine ⟨5138119598215224374484887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425413065476816249656591 5138119598215224374484887)
              ·
                refine ⟨7707179397322836561727331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138119598215224374484887 7707179397322836561727331)
                ·
                  refine ⟨11560769095984254842590997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707179397322836561727331 11560769095984254842590997)
                  ·
                    refine ⟨541911051374261945746453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11560769095984254842590997 541911051374261945746453)
                    ·
                      rfl

theorem cell23_3166104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_3166104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166104 prefixEnd_3166104 := by exact prefixLift 3166104
  have htrace : WordTrace (prefixWord ++ tailWord_3166104) baseStart_3166104 baseEnd_3166104 := by
    simpa [prefixWord, tailWord_3166104, baseEnd_3166104] using wordTrace_append hprefix tailTrace_3166104
  have hstable : (prefixWord ++ tailWord_3166104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166104).length < 2 ^ (prefixWord ++ tailWord_3166104).sum := by decide
  have hdescent : baseEnd_3166104 < baseStart_3166104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166167 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 1, 4, 2]
def baseStart_3166167 : Nat := 118140960795 + 3166167 * 2 ^ 59
def prefixEnd_3166167 : Nat := 4983230072969 + 3 ^ 40 * 3166167 * 2
def baseEnd_3166167 : Nat := 1625765503404019090751569

theorem tailTrace_3166167 : CollatzResearch.WordTrace tailWord_3166167 prefixEnd_3166167 1625765503404019090751569 := by
  unfold tailWord_3166167
  simp only [CollatzResearch.WordTrace]
  refine ⟨115479597520525172118336755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76986398347016781412224503 115479597520525172118336755)
  ·
    refine ⟨173219396280787758177505133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115479597520525172118336755 173219396280787758177505133)
    ·
      refine ⟨64957273605295409316564425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173219396280787758177505133 64957273605295409316564425)
      ·
        refine ⟨48717955203971556987423319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64957273605295409316564425 48717955203971556987423319)
        ·
          refine ⟨73076932805957335481134979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48717955203971556987423319 73076932805957335481134979)
          ·
            refine ⟨109615399208936003221702469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73076932805957335481134979 109615399208936003221702469)
            ·
              refine ⟨20552887351675500604069213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109615399208936003221702469 20552887351675500604069213)
              ·
                refine ⟨7707332756878312726525955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20552887351675500604069213 7707332756878312726525955)
                ·
                  refine ⟨11560999135317469089788933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707332756878312726525955 11560999135317469089788933)
                  ·
                    refine ⟨2167687337872025454335425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11560999135317469089788933 2167687337872025454335425)
                    ·
                      refine ⟨1625765503404019090751569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167687337872025454335425 1625765503404019090751569)
                      ·
                        rfl

theorem cell23_3166167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_3166167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166167 prefixEnd_3166167 := by exact prefixLift 3166167
  have htrace : WordTrace (prefixWord ++ tailWord_3166167) baseStart_3166167 baseEnd_3166167 := by
    simpa [prefixWord, tailWord_3166167, baseEnd_3166167] using wordTrace_append hprefix tailTrace_3166167
  have hstable : (prefixWord ++ tailWord_3166167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166167).length < 2 ^ (prefixWord ++ tailWord_3166167).sum := by decide
  have hdescent : baseEnd_3166167 < baseStart_3166167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166201 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 2, 2, 2]
def baseStart_3166201 : Nat := 118140960795 + 3166201 * 2 ^ 59
def prefixEnd_3166201 : Nat := 4983230072969 + 3 ^ 40 * 3166201 * 2
def baseEnd_3166201 : Nat := 1625782961746271957726413

theorem tailTrace_3166201 : CollatzResearch.WordTrace tailWord_3166201 prefixEnd_3166201 1625782961746271957726413 := by
  unfold tailWord_3166201
  simp only [CollatzResearch.WordTrace]
  refine ⟨115480837602401995925074457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76987225068267997283382971 115480837602401995925074457)
  ·
    refine ⟨86610628201801496943805843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115480837602401995925074457 86610628201801496943805843)
    ·
      refine ⟨129915942302702245415708765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86610628201801496943805843 129915942302702245415708765)
      ·
        refine ⟨48718478363513342030890787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129915942302702245415708765 48718478363513342030890787)
        ·
          refine ⟨73077717545270013046336181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48718478363513342030890787 73077717545270013046336181)
          ·
            refine ⟨6851036019869063723094017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73077717545270013046336181 6851036019869063723094017)
            ·
              refine ⟨5138277014901797792320513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6851036019869063723094017 5138277014901797792320513)
              ·
                refine ⟨3853707761176348344240385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138277014901797792320513 3853707761176348344240385)
                ·
                  refine ⟨2890280820882261258180289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853707761176348344240385 2890280820882261258180289)
                  ·
                    refine ⟨2167710615661695943635217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890280820882261258180289 2167710615661695943635217)
                    ·
                      refine ⟨1625782961746271957726413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167710615661695943635217 1625782961746271957726413)
                      ·
                        rfl

theorem cell23_3166201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_3166201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166201 prefixEnd_3166201 := by exact prefixLift 3166201
  have htrace : WordTrace (prefixWord ++ tailWord_3166201) baseStart_3166201 baseEnd_3166201 := by
    simpa [prefixWord, tailWord_3166201, baseEnd_3166201] using wordTrace_append hprefix tailTrace_3166201
  have hstable : (prefixWord ++ tailWord_3166201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166201).length < 2 ^ (prefixWord ++ tailWord_3166201).sum := by decide
  have hdescent : baseEnd_3166201 < baseStart_3166201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166220 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_3166220 : Nat := 118140960795 + 3166220 * 2 ^ 59
def prefixEnd_3166220 : Nat := 4983230072969 + 3 ^ 40 * 3166220 * 2
def baseEnd_3166220 : Nat := 541930905959569127796275

theorem tailTrace_3166220 : CollatzResearch.WordTrace tailWord_3166220 prefixEnd_3166220 541930905959569127796275 := by
  unfold tailWord_3166220
  simp only [CollatzResearch.WordTrace]
  refine ⟨57740765294666581085008057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76987687059555441446677409 57740765294666581085008057)
  ·
    refine ⟨43305573970999935813756043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57740765294666581085008057 43305573970999935813756043)
    ·
      refine ⟨64958360956499903720634065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43305573970999935813756043 64958360956499903720634065)
      ·
        refine ⟨48718770717374927790475549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64958360956499903720634065 48718770717374927790475549)
        ·
          refine ⟨18269539019015597921428331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48718770717374927790475549 18269539019015597921428331)
          ·
            refine ⟨27404308528523396882142497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18269539019015597921428331 27404308528523396882142497)
            ·
              refine ⟨20553231396392547661606873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27404308528523396882142497 20553231396392547661606873)
              ·
                refine ⟨15414923547294410746205155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20553231396392547661606873 15414923547294410746205155)
                ·
                  refine ⟨23122385320941616119307733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15414923547294410746205155 23122385320941616119307733)
                  ·
                    refine ⟨541930905959569127796275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23122385320941616119307733 541930905959569127796275)
                    ·
                      rfl

theorem cell23_3166220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_3166220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166220 prefixEnd_3166220 := by exact prefixLift 3166220
  have htrace : WordTrace (prefixWord ++ tailWord_3166220) baseStart_3166220 baseEnd_3166220 := by
    simpa [prefixWord, tailWord_3166220, baseEnd_3166220] using wordTrace_append hprefix tailTrace_3166220
  have hstable : (prefixWord ++ tailWord_3166220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166220).length < 2 ^ (prefixWord ++ tailWord_3166220).sum := by decide
  have hdescent : baseEnd_3166220 < baseStart_3166220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166237 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_3166237 : Nat := 118140960795 + 3166237 * 2 ^ 59
def prefixEnd_3166237 : Nat := 4983230072969 + 3 ^ 40 * 3166237 * 2
def baseEnd_3166237 : Nat := 541933815683277938958749

theorem tailTrace_3166237 : CollatzResearch.WordTrace tailWord_3166237 prefixEnd_3166237 541933815683277938958749 := by
  unfold tailWord_3166237
  simp only [CollatzResearch.WordTrace]
  refine ⟨115482150630271574073384965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76988100420181049382256643 115482150630271574073384965)
  ·
    refine ⟨21652903243175920138759681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115482150630271574073384965 21652903243175920138759681)
    ·
      refine ⟨16239677432381940104069761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21652903243175920138759681 16239677432381940104069761)
      ·
        refine ⟨12179758074286455078052321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16239677432381940104069761 12179758074286455078052321)
        ·
          refine ⟨9134818555714841308539241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12179758074286455078052321 9134818555714841308539241)
          ·
            refine ⟨6851113916786130981404431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9134818555714841308539241 6851113916786130981404431)
            ·
              refine ⟨10276670875179196472106647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6851113916786130981404431 10276670875179196472106647)
              ·
                refine ⟨15415006312768794708159971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10276670875179196472106647 15415006312768794708159971)
                ·
                  refine ⟨23122509469153192062239957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15415006312768794708159971 23122509469153192062239957)
                  ·
                    refine ⟨541933815683277938958749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23122509469153192062239957 541933815683277938958749)
                    ·
                      rfl

theorem cell23_3166237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_3166237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166237 prefixEnd_3166237 := by exact prefixLift 3166237
  have htrace : WordTrace (prefixWord ++ tailWord_3166237) baseStart_3166237 baseEnd_3166237 := by
    simpa [prefixWord, tailWord_3166237, baseEnd_3166237] using wordTrace_append hprefix tailTrace_3166237
  have hstable : (prefixWord ++ tailWord_3166237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166237).length < 2 ^ (prefixWord ++ tailWord_3166237).sum := by decide
  have hdescent : baseEnd_3166237 < baseStart_3166237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166318 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3166318 : Nat := 118140960795 + 3166318 * 2 ^ 59
def prefixEnd_3166318 : Nat := 4983230072969 + 3 ^ 40 * 3166318 * 2
def baseEnd_3166318 : Nat := 541947679660949333321125

theorem tailTrace_3166318 : CollatzResearch.WordTrace tailWord_3166318 prefixEnd_3166318 541947679660949333321125 := by
  unfold tailWord_3166318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14435638117872265613385451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76990069961985416604722405 14435638117872265613385451)
  ·
    refine ⟨21653457176808398420078177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14435638117872265613385451 21653457176808398420078177)
    ·
      refine ⟨16240092882606298815058633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21653457176808398420078177 16240092882606298815058633)
      ·
        refine ⟨12180069661954724111293975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16240092882606298815058633 12180069661954724111293975)
        ·
          refine ⟨18270104492932086166940963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12180069661954724111293975 18270104492932086166940963)
          ·
            refine ⟨27405156739398129250411445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18270104492932086166940963 27405156739398129250411445)
            ·
              refine ⟨2569233444318574617226073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27405156739398129250411445 2569233444318574617226073)
              ·
                refine ⟨1926925083238930962919555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569233444318574617226073 1926925083238930962919555)
                ·
                  refine ⟨2890387624858396444379333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926925083238930962919555 2890387624858396444379333)
                  ·
                    refine ⟨541947679660949333321125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890387624858396444379333 541947679660949333321125)
                    ·
                      rfl

theorem cell23_3166318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3166318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166318 prefixEnd_3166318 := by exact prefixLift 3166318
  have htrace : WordTrace (prefixWord ++ tailWord_3166318) baseStart_3166318 baseEnd_3166318 := by
    simpa [prefixWord, tailWord_3166318, baseEnd_3166318] using wordTrace_append hprefix tailTrace_3166318
  have hstable : (prefixWord ++ tailWord_3166318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166318).length < 2 ^ (prefixWord ++ tailWord_3166318).sum := by decide
  have hdescent : baseEnd_3166318 < baseStart_3166318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166330 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_3166330 : Nat := 118140960795 + 3166330 * 2 ^ 59
def prefixEnd_3166330 : Nat := 4983230072969 + 3 ^ 40 * 3166330 * 2
def baseEnd_3166330 : Nat := 1625849200750701953013319

theorem tailTrace_3166330 : CollatzResearch.WordTrace tailWord_3166330 prefixEnd_3166330 1625849200750701953013319 := by
  unfold tailWord_3166330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28871385654733662739130111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76990361745956433971013629 28871385654733662739130111)
  ·
    refine ⟨43307078482100494108695167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28871385654733662739130111 43307078482100494108695167)
    ·
      refine ⟨64960617723150741163042751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43307078482100494108695167 64960617723150741163042751)
      ·
        refine ⟨97440926584726111744564127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64960617723150741163042751 97440926584726111744564127)
        ·
          refine ⟨146161389877089167616846191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97440926584726111744564127 146161389877089167616846191)
          ·
            refine ⟨219242084815633751425269287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146161389877089167616846191 219242084815633751425269287)
            ·
              refine ⟨328863127223450627137903931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219242084815633751425269287 328863127223450627137903931)
              ·
                refine ⟨493294690835175940706855897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328863127223450627137903931 493294690835175940706855897)
                ·
                  refine ⟨369971018126381955530141923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493294690835175940706855897 369971018126381955530141923)
                  ·
                    refine ⟨554956527189572933295212885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369971018126381955530141923 554956527189572933295212885)
                    ·
                      refine ⟨1625849200750701953013319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 554956527189572933295212885 1625849200750701953013319)
                      ·
                        rfl

theorem cell23_3166330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_3166330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166330 prefixEnd_3166330 := by exact prefixLift 3166330
  have htrace : WordTrace (prefixWord ++ tailWord_3166330) baseStart_3166330 baseEnd_3166330 := by
    simpa [prefixWord, tailWord_3166330, baseEnd_3166330] using wordTrace_append hprefix tailTrace_3166330
  have hstable : (prefixWord ++ tailWord_3166330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166330).length < 2 ^ (prefixWord ++ tailWord_3166330).sum := by decide
  have hdescent : baseEnd_3166330 < baseStart_3166330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166344 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_3166344 : Nat := 118140960795 + 3166344 * 2 ^ 59
def prefixEnd_3166344 : Nat := 4983230072969 + 3 ^ 40 * 3166344 * 2
def baseEnd_3166344 : Nat := 541952129826621632746085

theorem tailTrace_3166344 : CollatzResearch.WordTrace tailWord_3166344 prefixEnd_3166344 541952129826621632746085 := by
  unfold tailWord_3166344
  simp only [CollatzResearch.WordTrace]
  refine ⟨57743026620441965673765043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76990702160589287565020057 57743026620441965673765043)
  ·
    refine ⟨86614539930662948510647565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57743026620441965673765043 86614539930662948510647565)
    ·
      refine ⟨32480452473998605691492837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86614539930662948510647565 32480452473998605691492837)
      ·
        refine ⟨6090084838874738567154907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32480452473998605691492837 6090084838874738567154907)
        ·
          refine ⟨9135127258312107850732361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090084838874738567154907 9135127258312107850732361)
          ·
            refine ⟨6851345443734080888049271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9135127258312107850732361 6851345443734080888049271)
            ·
              refine ⟨10277018165601121332073907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6851345443734080888049271 10277018165601121332073907)
              ·
                refine ⟨15415527248401681998110861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10277018165601121332073907 15415527248401681998110861)
                ·
                  refine ⟨5780822718150630749291573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15415527248401681998110861 5780822718150630749291573)
                  ·
                    refine ⟨541952129826621632746085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5780822718150630749291573 541952129826621632746085)
                    ·
                      rfl

theorem cell23_3166344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_3166344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166344 prefixEnd_3166344 := by exact prefixLift 3166344
  have htrace : WordTrace (prefixWord ++ tailWord_3166344) baseStart_3166344 baseEnd_3166344 := by
    simpa [prefixWord, tailWord_3166344, baseEnd_3166344] using wordTrace_append hprefix tailTrace_3166344
  have hstable : (prefixWord ++ tailWord_3166344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166344).length < 2 ^ (prefixWord ++ tailWord_3166344).sum := by decide
  have hdescent : baseEnd_3166344 < baseStart_3166344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166357 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_3166357 : Nat := 118140960795 + 3166357 * 2 ^ 59
def prefixEnd_3166357 : Nat := 4983230072969 + 3 ^ 40 * 3166357 * 2
def baseEnd_3166357 : Nat := 541954354909457782458565

theorem tailTrace_3166357 : CollatzResearch.WordTrace tailWord_3166357 prefixEnd_3166357 541954354909457782458565 := by
  unfold tailWord_3166357
  simp only [CollatzResearch.WordTrace]
  refine ⟨115486527389836834567753325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76991018259891223045168883 115486527389836834567753325)
  ·
    refine ⟨43307447771188812962907497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115486527389836834567753325 43307447771188812962907497)
    ·
      refine ⟨32480585828391609722180623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43307447771188812962907497 32480585828391609722180623)
      ·
        refine ⟨48720878742587414583270935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32480585828391609722180623 48720878742587414583270935)
        ·
          refine ⟨73081318113881121874906403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48720878742587414583270935 73081318113881121874906403)
          ·
            refine ⟨109621977170821682812359605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73081318113881121874906403 109621977170821682812359605)
            ·
              refine ⟨10277060359764532763658713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109621977170821682812359605 10277060359764532763658713)
              ·
                refine ⟨7707795269823399572744035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10277060359764532763658713 7707795269823399572744035)
                ·
                  refine ⟨11561692904735099359116053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7707795269823399572744035 11561692904735099359116053)
                  ·
                    refine ⟨541954354909457782458565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11561692904735099359116053 541954354909457782458565)
                    ·
                      rfl

theorem cell23_3166357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_3166357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166357 prefixEnd_3166357 := by exact prefixLift 3166357
  have htrace : WordTrace (prefixWord ++ tailWord_3166357) baseStart_3166357 baseEnd_3166357 := by
    simpa [prefixWord, tailWord_3166357, baseEnd_3166357] using wordTrace_append hprefix tailTrace_3166357
  have hstable : (prefixWord ++ tailWord_3166357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166357).length < 2 ^ (prefixWord ++ tailWord_3166357).sum := by decide
  have hdescent : baseEnd_3166357 < baseStart_3166357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166375 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_3166375 : Nat := 118140960795 + 3166375 * 2 ^ 59
def prefixEnd_3166375 : Nat := 4983230072969 + 3 ^ 40 * 3166375 * 2
def baseEnd_3166375 : Nat := 1625872307380154276950613

theorem tailTrace_3166375 : CollatzResearch.WordTrace tailWord_3166375 prefixEnd_3166375 1625872307380154276950613 := by
  unfold tailWord_3166375
  simp only [CollatzResearch.WordTrace]
  refine ⟨115487183903771623641908579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76991455935847749094605719 115487183903771623641908579)
  ·
    refine ⟨173230775855657435462862869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115487183903771623641908579 173230775855657435462862869)
    ·
      refine ⟨8120192618233942287321697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173230775855657435462862869 8120192618233942287321697)
      ·
        refine ⟨6090144463675456715491273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8120192618233942287321697 6090144463675456715491273)
        ·
          refine ⟨4567608347756592536618455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6090144463675456715491273 4567608347756592536618455)
          ·
            refine ⟨6851412521634888804927683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567608347756592536618455 6851412521634888804927683)
            ·
              refine ⟨10277118782452333207391525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6851412521634888804927683 10277118782452333207391525)
              ·
                refine ⟨1926959771709812476385911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10277118782452333207391525 1926959771709812476385911)
                ·
                  refine ⟨2890439657564718714578867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926959771709812476385911 2890439657564718714578867)
                  ·
                    refine ⟨4335659486347078071868301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2890439657564718714578867 4335659486347078071868301)
                    ·
                      refine ⟨1625872307380154276950613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4335659486347078071868301 1625872307380154276950613)
                      ·
                        rfl

theorem cell23_3166375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_3166375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166375 prefixEnd_3166375 := by exact prefixLift 3166375
  have htrace : WordTrace (prefixWord ++ tailWord_3166375) baseStart_3166375 baseEnd_3166375 := by
    simpa [prefixWord, tailWord_3166375, baseEnd_3166375] using wordTrace_append hprefix tailTrace_3166375
  have hstable : (prefixWord ++ tailWord_3166375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166375).length < 2 ^ (prefixWord ++ tailWord_3166375).sum := by decide
  have hdescent : baseEnd_3166375 < baseStart_3166375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166402 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_3166402 : Nat := 118140960795 + 3166402 * 2 ^ 59
def prefixEnd_3166402 : Nat := 4983230072969 + 3 ^ 40 * 3166402 * 2
def baseEnd_3166402 : Nat := 1625886171357825671312989

theorem tailTrace_3166402 : CollatzResearch.WordTrace tailWord_3166402 prefixEnd_3166402 1625886171357825671312989 := by
  unfold tailWord_3166402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872042168668451813285365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76992112449782538168760973 28872042168668451813285365)
  ·
    refine ⟨2706753953312667357495503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28872042168668451813285365 2706753953312667357495503)
    ·
      refine ⟨4060130929969001036243255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706753953312667357495503 4060130929969001036243255)
      ·
        refine ⟨6090196394953501554364883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060130929969001036243255 6090196394953501554364883)
        ·
          refine ⟨9135294592430252331547325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090196394953501554364883 9135294592430252331547325)
          ·
            refine ⟨3425735472161344624330247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9135294592430252331547325 3425735472161344624330247)
            ·
              refine ⟨5138603208242016936495371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425735472161344624330247 5138603208242016936495371)
              ·
                refine ⟨7707904812363025404743057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138603208242016936495371 7707904812363025404743057)
                ·
                  refine ⟨5780928609272269053557293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7707904812363025404743057 5780928609272269053557293)
                  ·
                    refine ⟨2167848228477100895083985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5780928609272269053557293 2167848228477100895083985)
                    ·
                      refine ⟨1625886171357825671312989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167848228477100895083985 1625886171357825671312989)
                      ·
                        rfl

theorem cell23_3166402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_3166402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166402 prefixEnd_3166402 := by exact prefixLift 3166402
  have htrace : WordTrace (prefixWord ++ tailWord_3166402) baseStart_3166402 baseEnd_3166402 := by
    simpa [prefixWord, tailWord_3166402, baseEnd_3166402] using wordTrace_append hprefix tailTrace_3166402
  have hstable : (prefixWord ++ tailWord_3166402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166402).length < 2 ^ (prefixWord ++ tailWord_3166402).sum := by decide
  have hdescent : baseEnd_3166402 < baseStart_3166402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166418 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_3166418 : Nat := 118140960795 + 3166418 * 2 ^ 59
def prefixEnd_3166418 : Nat := 4983230072969 + 3 ^ 40 * 3166418 * 2
def baseEnd_3166418 : Nat := 1625894387048297608712915

theorem tailTrace_3166418 : CollatzResearch.WordTrace tailWord_3166418 prefixEnd_3166418 1625894387048297608712915 := by
  unfold tailWord_3166418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872188060653960496430977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76992501495077227990482605 28872188060653960496430977)
  ·
    refine ⟨21654141045490470372323233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28872188060653960496430977 21654141045490470372323233)
    ·
      refine ⟨16240605784117852779242425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21654141045490470372323233 16240605784117852779242425)
      ·
        refine ⟨12180454338088389584431819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16240605784117852779242425 12180454338088389584431819)
        ·
          refine ⟨18270681507132584376647729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12180454338088389584431819 18270681507132584376647729)
          ·
            refine ⟨13703011130349438282485797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18270681507132584376647729 13703011130349438282485797)
            ·
              refine ⟨2569314586940519677966087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13703011130349438282485797 2569314586940519677966087)
              ·
                refine ⟨3853971880410779516949131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569314586940519677966087 3853971880410779516949131)
                ·
                  refine ⟨5780957820616169275423697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853971880410779516949131 5780957820616169275423697)
                  ·
                    refine ⟨4335718365462126956567773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5780957820616169275423697 4335718365462126956567773)
                    ·
                      refine ⟨1625894387048297608712915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4335718365462126956567773 1625894387048297608712915)
                      ·
                        rfl

theorem cell23_3166418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_3166418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166418 prefixEnd_3166418 := by exact prefixLift 3166418
  have htrace : WordTrace (prefixWord ++ tailWord_3166418) baseStart_3166418 baseEnd_3166418 := by
    simpa [prefixWord, tailWord_3166418, baseEnd_3166418] using wordTrace_append hprefix tailTrace_3166418
  have hstable : (prefixWord ++ tailWord_3166418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166418).length < 2 ^ (prefixWord ++ tailWord_3166418).sum := by decide
  have hdescent : baseEnd_3166418 < baseStart_3166418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166454 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3166454 : Nat := 118140960795 + 3166454 * 2 ^ 59
def prefixEnd_3166454 : Nat := 4983230072969 + 3 ^ 40 * 3166454 * 2
def baseEnd_3166454 : Nat := 1625912872351859467862749

theorem tailTrace_3166454 : CollatzResearch.WordTrace tailWord_3166454 prefixEnd_3166454 1625912872351859467862749 := by
  unfold tailWord_3166454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218129079405338758377151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76993376846990280089356277 7218129079405338758377151)
  ·
    refine ⟨10827193619108008137565727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7218129079405338758377151 10827193619108008137565727)
    ·
      refine ⟨16240790428662012206348591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10827193619108008137565727 16240790428662012206348591)
      ·
        refine ⟨24361185642993018309522887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16240790428662012206348591 24361185642993018309522887)
        ·
          refine ⟨36541778464489527464284331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24361185642993018309522887 36541778464489527464284331)
          ·
            refine ⟨54812667696734291196426497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36541778464489527464284331 54812667696734291196426497)
            ·
              refine ⟨41109500772550718397319873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54812667696734291196426497 41109500772550718397319873)
              ·
                refine ⟨30832125579413038797989905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41109500772550718397319873 30832125579413038797989905)
                ·
                  refine ⟨23124094184559779098492429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30832125579413038797989905 23124094184559779098492429)
                  ·
                    refine ⟨8671535319209917161934661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23124094184559779098492429 8671535319209917161934661)
                    ·
                      refine ⟨1625912872351859467862749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8671535319209917161934661 1625912872351859467862749)
                      ·
                        rfl

theorem cell23_3166454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3166454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166454 prefixEnd_3166454 := by exact prefixLift 3166454
  have htrace : WordTrace (prefixWord ++ tailWord_3166454) baseStart_3166454 baseEnd_3166454 := by
    simpa [prefixWord, tailWord_3166454, baseEnd_3166454] using wordTrace_append hprefix tailTrace_3166454
  have hstable : (prefixWord ++ tailWord_3166454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166454).length < 2 ^ (prefixWord ++ tailWord_3166454).sum := by decide
  have hdescent : baseEnd_3166454 < baseStart_3166454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166458 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2]
def baseStart_3166458 : Nat := 118140960795 + 3166458 * 2 ^ 59
def prefixEnd_3166458 : Nat := 4983230072969 + 3 ^ 40 * 3166458 * 2
def baseEnd_3166458 : Nat := 1625914926274477452212731

theorem tailTrace_3166458 : CollatzResearch.WordTrace tailWord_3166458 prefixEnd_3166458 1625914926274477452212731 := by
  unfold tailWord_3166458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872552790617732204295007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76993474108313952544786685 28872552790617732204295007)
  ·
    refine ⟨43308829185926598306442511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28872552790617732204295007 43308829185926598306442511)
    ·
      refine ⟨64963243778889897459663767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43308829185926598306442511 64963243778889897459663767)
      ·
        refine ⟨97444865668334846189495651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64963243778889897459663767 97444865668334846189495651)
        ·
          refine ⟨146167298502502269284243477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97444865668334846189495651 146167298502502269284243477)
          ·
            refine ⟨6851592117304793872698913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146167298502502269284243477 6851592117304793872698913)
            ·
              refine ⟨5138694087978595404524185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6851592117304793872698913 5138694087978595404524185)
              ·
                refine ⟨3854020565983946553393139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138694087978595404524185 3854020565983946553393139)
                ·
                  refine ⟨5781030848975919830089709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854020565983946553393139 5781030848975919830089709)
                  ·
                    refine ⟨2167886568365969936283641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5781030848975919830089709 2167886568365969936283641)
                    ·
                      refine ⟨1625914926274477452212731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167886568365969936283641 1625914926274477452212731)
                      ·
                        rfl

theorem cell23_3166458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_3166458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166458 prefixEnd_3166458 := by exact prefixLift 3166458
  have htrace : WordTrace (prefixWord ++ tailWord_3166458) baseStart_3166458 baseEnd_3166458 := by
    simpa [prefixWord, tailWord_3166458, baseEnd_3166458] using wordTrace_append hprefix tailTrace_3166458
  have hstable : (prefixWord ++ tailWord_3166458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166458).length < 2 ^ (prefixWord ++ tailWord_3166458).sum := by decide
  have hdescent : baseEnd_3166458 < baseStart_3166458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166488 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3166488 : Nat := 118140960795 + 3166488 * 2 ^ 59
def prefixEnd_3166488 : Nat := 4983230072969 + 3 ^ 40 * 3166488 * 2
def baseEnd_3166488 : Nat := 1625930330694112334837593

theorem tailTrace_3166488 : CollatzResearch.WordTrace tailWord_3166488 prefixEnd_3166488 1625930330694112334837593 := by
  unfold tailWord_3166488
  simp only [CollatzResearch.WordTrace]
  refine ⟨57745652676181121970386059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76994203568241495960514745 57745652676181121970386059)
  ·
    refine ⟨86618479014271682955579089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57745652676181121970386059 86618479014271682955579089)
    ·
      refine ⟨64963859260703762216684317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86618479014271682955579089 64963859260703762216684317)
      ·
        refine ⟨24361447222763910831256619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64963859260703762216684317 24361447222763910831256619)
        ·
          refine ⟨36542170834145866246884929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24361447222763910831256619 36542170834145866246884929)
          ·
            refine ⟨27406628125609399685163697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36542170834145866246884929 27406628125609399685163697)
            ·
              refine ⟨20554971094207049763872773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27406628125609399685163697 20554971094207049763872773)
              ·
                refine ⟨3854057080163821830726145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20554971094207049763872773 3854057080163821830726145)
                ·
                  refine ⟨2890542810122866373044609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854057080163821830726145 2890542810122866373044609)
                  ·
                    refine ⟨2167907107592149779783457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890542810122866373044609 2167907107592149779783457)
                    ·
                      refine ⟨1625930330694112334837593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167907107592149779783457 1625930330694112334837593)
                      ·
                        rfl

theorem cell23_3166488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3166488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166488 prefixEnd_3166488 := by exact prefixLift 3166488
  have htrace : WordTrace (prefixWord ++ tailWord_3166488) baseStart_3166488 baseEnd_3166488 := by
    simpa [prefixWord, tailWord_3166488, baseEnd_3166488] using wordTrace_append hprefix tailTrace_3166488
  have hstable : (prefixWord ++ tailWord_3166488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166488).length < 2 ^ (prefixWord ++ tailWord_3166488).sum := by decide
  have hdescent : baseEnd_3166488 < baseStart_3166488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166509 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3166509 : Nat := 118140960795 + 3166509 * 2 ^ 59
def prefixEnd_3166509 : Nat := 4983230072969 + 3 ^ 40 * 3166509 * 2
def baseEnd_3166509 : Nat := 1625941113787856752674997

theorem tailTrace_3166509 : CollatzResearch.WordTrace tailWord_3166509 prefixEnd_3166509 1625941113787856752674997 := by
  unfold tailWord_3166509
  simp only [CollatzResearch.WordTrace]
  refine ⟨115492071285286164527286581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76994714190190776351524387 115492071285286164527286581)
  ·
    refine ⟨10827381682995577924433117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115492071285286164527286581 10827381682995577924433117)
    ·
      refine ⟨4060268131123341721662419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10827381682995577924433117 4060268131123341721662419)
      ·
        refine ⟨6090402196685012582493629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060268131123341721662419 6090402196685012582493629)
        ·
          refine ⟨2283900823756879718435111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6090402196685012582493629 2283900823756879718435111)
          ·
            refine ⟨3425851235635319577652667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283900823756879718435111 3425851235635319577652667)
            ·
              refine ⟨5138776853452979366479001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425851235635319577652667 5138776853452979366479001)
              ·
                refine ⟨3854082640089734524859251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138776853452979366479001 3854082640089734524859251)
                ·
                  refine ⟨5781123960134601787288877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854082640089734524859251 5781123960134601787288877)
                  ·
                    refine ⟨2167921485050475670233329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5781123960134601787288877 2167921485050475670233329)
                    ·
                      refine ⟨1625941113787856752674997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2167921485050475670233329 1625941113787856752674997)
                      ·
                        rfl

theorem cell23_3166509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3166509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166509 prefixEnd_3166509 := by exact prefixLift 3166509
  have htrace : WordTrace (prefixWord ++ tailWord_3166509) baseStart_3166509 baseEnd_3166509 := by
    simpa [prefixWord, tailWord_3166509, baseEnd_3166509] using wordTrace_append hprefix tailTrace_3166509
  have hstable : (prefixWord ++ tailWord_3166509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166509).length < 2 ^ (prefixWord ++ tailWord_3166509).sum := by decide
  have hdescent : baseEnd_3166509 < baseStart_3166509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166578 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3166578 : Nat := 118140960795 + 3166578 * 2 ^ 59
def prefixEnd_3166578 : Nat := 4983230072969 + 3 ^ 40 * 3166578 * 2
def baseEnd_3166578 : Nat := 1625976543953016982712179

theorem tailTrace_3166578 : CollatzResearch.WordTrace tailWord_3166578 prefixEnd_3166578 1625976543953016982712179 := by
  unfold tailWord_3166578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28873646980509047327887097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76996391948024126207698925 28873646980509047327887097)
  ·
    refine ⟨21655235235381785495915323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28873646980509047327887097 21655235235381785495915323)
    ·
      refine ⟨32482852853072678243872985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21655235235381785495915323 32482852853072678243872985)
      ·
        refine ⟨24362139639804508682904739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32482852853072678243872985 24362139639804508682904739)
        ·
          refine ⟨36543209459706763024357109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24362139639804508682904739 36543209459706763024357109)
          ·
            refine ⟨3425925886847509033533479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36543209459706763024357109 3425925886847509033533479)
            ·
              refine ⟨5138888830271263550300219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425925886847509033533479 5138888830271263550300219)
              ·
                refine ⟨7708333245406895325450329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138888830271263550300219 7708333245406895325450329)
                ·
                  refine ⟨5781249934055171494087747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7708333245406895325450329 5781249934055171494087747)
                  ·
                    refine ⟨8671874901082757241131621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5781249934055171494087747 8671874901082757241131621)
                    ·
                      refine ⟨1625976543953016982712179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8671874901082757241131621 1625976543953016982712179)
                      ·
                        rfl

theorem cell23_3166578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3166578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166578 prefixEnd_3166578 := by exact prefixLift 3166578
  have htrace : WordTrace (prefixWord ++ tailWord_3166578) baseStart_3166578 baseEnd_3166578 := by
    simpa [prefixWord, tailWord_3166578, baseEnd_3166578] using wordTrace_append hprefix tailTrace_3166578
  have hstable : (prefixWord ++ tailWord_3166578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166578).length < 2 ^ (prefixWord ++ tailWord_3166578).sum := by decide
  have hdescent : baseEnd_3166578 < baseStart_3166578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166601 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 6]
def baseStart_3166601 : Nat := 118140960795 + 3166601 * 2 ^ 59
def prefixEnd_3166601 : Nat := 4983230072969 + 3 ^ 40 * 3166601 * 2
def baseEnd_3166601 : Nat := 180665372667563376969397

theorem tailTrace_3166601 : CollatzResearch.WordTrace tailWord_3166601 prefixEnd_3166601 180665372667563376969397 := by
  unfold tailWord_3166601
  simp only [CollatzResearch.WordTrace]
  refine ⟨115495426800952864239635657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76996951200635242826423771 115495426800952864239635657)
  ·
    refine ⟨86621570100714648179726743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115495426800952864239635657 86621570100714648179726743)
    ·
      refine ⟨129932355151071972269590115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86621570100714648179726743 129932355151071972269590115)
      ·
        refine ⟨194898532726607958404385173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129932355151071972269590115 194898532726607958404385173)
        ·
          refine ⟨9135868721559748050205555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194898532726607958404385173 9135868721559748050205555)
          ·
            refine ⟨13703803082339622075308333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135868721559748050205555 13703803082339622075308333)
            ·
              refine ⟨5138926155877358278240625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13703803082339622075308333 5138926155877358278240625)
              ·
                refine ⟨3854194616908018708680469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138926155877358278240625 3854194616908018708680469)
                ·
                  refine ⟨180665372667563376969397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3854194616908018708680469 180665372667563376969397)
                  ·
                    rfl

theorem cell23_3166601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_3166601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166601 prefixEnd_3166601 := by exact prefixLift 3166601
  have htrace : WordTrace (prefixWord ++ tailWord_3166601) baseStart_3166601 baseEnd_3166601 := by
    simpa [prefixWord, tailWord_3166601, baseEnd_3166601] using wordTrace_append hprefix tailTrace_3166601
  have hstable : (prefixWord ++ tailWord_3166601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166601).length < 2 ^ (prefixWord ++ tailWord_3166601).sum := by decide
  have hdescent : baseEnd_3166601 < baseStart_3166601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166604 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3166604 : Nat := 118140960795 + 3166604 * 2 ^ 59
def prefixEnd_3166604 : Nat := 4983230072969 + 3 ^ 40 * 3166604 * 2
def baseEnd_3166604 : Nat := 1625989894450033880987059

theorem tailTrace_3166604 : CollatzResearch.WordTrace tailWord_3166604 prefixEnd_3166604 1625989894450033880987059 := by
  unfold tailWord_3166604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57747768109970997875997433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76997024146627997167996577 57747768109970997875997433)
  ·
    refine ⟨43310826082478248406998075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57747768109970997875997433 43310826082478248406998075)
    ·
      refine ⟨64966239123717372610497113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43310826082478248406998075 64966239123717372610497113)
      ·
        refine ⟨48724679342788029457872835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64966239123717372610497113 48724679342788029457872835)
        ·
          refine ⟨73087019014182044186809253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48724679342788029457872835 73087019014182044186809253)
          ·
            refine ⟨13703816065159133285026735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73087019014182044186809253 13703816065159133285026735)
            ·
              refine ⟨20555724097738699927540103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703816065159133285026735 20555724097738699927540103)
              ·
                refine ⟨30833586146608049891310155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20555724097738699927540103 30833586146608049891310155)
                ·
                  refine ⟨46250379219912074836965233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30833586146608049891310155 46250379219912074836965233)
                  ·
                    refine ⟨34687784414934056127723925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46250379219912074836965233 34687784414934056127723925)
                    ·
                      refine ⟨1625989894450033880987059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34687784414934056127723925 1625989894450033880987059)
                      ·
                        rfl

theorem cell23_3166604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3166604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166604 prefixEnd_3166604 := by exact prefixLift 3166604
  have htrace : WordTrace (prefixWord ++ tailWord_3166604) baseStart_3166604 baseEnd_3166604 := by
    simpa [prefixWord, tailWord_3166604, baseEnd_3166604] using wordTrace_append hprefix tailTrace_3166604
  have hstable : (prefixWord ++ tailWord_3166604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166604).length < 2 ^ (prefixWord ++ tailWord_3166604).sum := by decide
  have hdescent : baseEnd_3166604 < baseStart_3166604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166618 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_3166618 : Nat := 118140960795 + 3166618 * 2 ^ 59
def prefixEnd_3166618 : Nat := 4983230072969 + 3 ^ 40 * 3166618 * 2
def baseEnd_3166618 : Nat := 180666342575466314023555

theorem tailTrace_3166618 : CollatzResearch.WordTrace tailWord_3166618 prefixEnd_3166618 180666342575466314023555 := by
  unfold tailWord_3166618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28874011710472819035751127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76997364561260850762003005 28874011710472819035751127)
  ·
    refine ⟨43311017565709228553626691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28874011710472819035751127 43311017565709228553626691)
    ·
      refine ⟨64966526348563842830440037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43311017565709228553626691 64966526348563842830440037)
      ·
        refine ⟨12181223690355720530707507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64966526348563842830440037 12181223690355720530707507)
        ·
          refine ⟨18271835535533580796061261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181223690355720530707507 18271835535533580796061261)
          ·
            refine ⟨6851938325825092798522973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18271835535533580796061261 6851938325825092798522973)
            ·
              refine ⟨2569476872184409799446115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6851938325825092798522973 2569476872184409799446115)
              ·
                refine ⟨3854215308276614699169173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569476872184409799446115 3854215308276614699169173)
                ·
                  refine ⟨180666342575466314023555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3854215308276614699169173 180666342575466314023555)
                  ·
                    rfl

theorem cell23_3166618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_3166618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166618 prefixEnd_3166618 := by exact prefixLift 3166618
  have htrace : WordTrace (prefixWord ++ tailWord_3166618) baseStart_3166618 baseEnd_3166618 := by
    simpa [prefixWord, tailWord_3166618, baseEnd_3166618] using wordTrace_append hprefix tailTrace_3166618
  have hstable : (prefixWord ++ tailWord_3166618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166618).length < 2 ^ (prefixWord ++ tailWord_3166618).sum := by decide
  have hdescent : baseEnd_3166618 < baseStart_3166618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166628 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_3166628 : Nat := 118140960795 + 3166628 * 2 ^ 59
def prefixEnd_3166628 : Nat := 4983230072969 + 3 ^ 40 * 3166628 * 2
def baseEnd_3166628 : Nat := 1626002217985741787086949

theorem tailTrace_3166628 : CollatzResearch.WordTrace tailWord_3166628 prefixEnd_3166628 1626002217985741787086949 := by
  unfold tailWord_3166628
  simp only [CollatzResearch.WordTrace]
  refine ⟨57748205785927523925434269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76997607714570031900579025 57748205785927523925434269)
  ·
    refine ⟨21655577169722821472037851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57748205785927523925434269 21655577169722821472037851)
    ·
      refine ⟨32483365754584232208056777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21655577169722821472037851 32483365754584232208056777)
      ·
        refine ⟨24362524315938174156042583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32483365754584232208056777 24362524315938174156042583)
        ·
          refine ⟨36543786473907261234063875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24362524315938174156042583 36543786473907261234063875)
          ·
            refine ⟨54815679710860891851095813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36543786473907261234063875 54815679710860891851095813)
            ·
              refine ⟨10277939945786417222080465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54815679710860891851095813 10277939945786417222080465)
              ·
                refine ⟨7708454959339812916560349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10277939945786417222080465 7708454959339812916560349)
                ·
                  refine ⟨2890670609752429843710131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7708454959339812916560349 2890670609752429843710131)
                  ·
                    refine ⟨4336005914628644765565197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2890670609752429843710131 4336005914628644765565197)
                    ·
                      refine ⟨1626002217985741787086949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336005914628644765565197 1626002217985741787086949)
                      ·
                        rfl

theorem cell23_3166628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_3166628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166628 prefixEnd_3166628 := by exact prefixLift 3166628
  have htrace : WordTrace (prefixWord ++ tailWord_3166628) baseStart_3166628 baseEnd_3166628 := by
    simpa [prefixWord, tailWord_3166628, baseEnd_3166628] using wordTrace_append hprefix tailTrace_3166628
  have hstable : (prefixWord ++ tailWord_3166628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166628).length < 2 ^ (prefixWord ++ tailWord_3166628).sum := by decide
  have hdescent : baseEnd_3166628 < baseStart_3166628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166671 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_3166671 : Nat := 118140960795 + 3166671 * 2 ^ 59
def prefixEnd_3166671 : Nat := 4983230072969 + 3 ^ 40 * 3166671 * 2
def baseEnd_3166671 : Nat := 1626024297653885118849251

theorem tailTrace_3166671 : CollatzResearch.WordTrace tailWord_3166671 prefixEnd_3166671 1626024297653885118849251 := by
  unfold tailWord_3166671
  simp only [CollatzResearch.WordTrace]
  refine ⟨115497979910699266194683867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76998653273799510796455911 115497979910699266194683867)
  ·
    refine ⟨173246969866048899292025801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115497979910699266194683867 173246969866048899292025801)
    ·
      refine ⟨129935227399536674469019351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173246969866048899292025801 129935227399536674469019351)
      ·
        refine ⟨194902841099305011703529027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129935227399536674469019351 194902841099305011703529027)
        ·
          refine ⟨292354261648957517555293541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194902841099305011703529027 292354261648957517555293541)
          ·
            refine ⟨54816424059179534541617539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292354261648957517555293541 54816424059179534541617539)
            ·
              refine ⟨82224636088769301812426309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54816424059179534541617539 82224636088769301812426309)
              ·
                refine ⟨15417119266644244089829933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82224636088769301812426309 15417119266644244089829933)
                ·
                  refine ⟨5781419724991591533686225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15417119266644244089829933 5781419724991591533686225)
                  ·
                    refine ⟨4336064793743693650264669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781419724991591533686225 4336064793743693650264669)
                    ·
                      refine ⟨1626024297653885118849251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336064793743693650264669 1626024297653885118849251)
                      ·
                        rfl

theorem cell23_3166671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_3166671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166671 prefixEnd_3166671 := by exact prefixLift 3166671
  have htrace : WordTrace (prefixWord ++ tailWord_3166671) baseStart_3166671 baseEnd_3166671 := by
    simpa [prefixWord, tailWord_3166671, baseEnd_3166671] using wordTrace_append hprefix tailTrace_3166671
  have hstable : (prefixWord ++ tailWord_3166671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166671).length < 2 ^ (prefixWord ++ tailWord_3166671).sum := by decide
  have hdescent : baseEnd_3166671 < baseStart_3166671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166678 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3166678 : Nat := 118140960795 + 3166678 * 2 ^ 59
def prefixEnd_3166678 : Nat := 4983230072969 + 3 ^ 40 * 3166678 * 2
def baseEnd_3166678 : Nat := 542009297339488863820573

theorem tailTrace_3166678 : CollatzResearch.WordTrace tailWord_3166678 prefixEnd_3166678 542009297339488863820573 := by
  unfold tailWord_3166678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218639701354619149386793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76998823481115937593459125 7218639701354619149386793)
  ·
    refine ⟨5413979776015964362040095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7218639701354619149386793 5413979776015964362040095)
    ·
      refine ⟨8120969664023946543060143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413979776015964362040095 8120969664023946543060143)
      ·
        refine ⟨12181454496035919814590215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120969664023946543060143 12181454496035919814590215)
        ·
          refine ⟨18272181744053879721885323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181454496035919814590215 18272181744053879721885323)
          ·
            refine ⟨27408272616080819582827985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272181744053879721885323 27408272616080819582827985)
            ·
              refine ⟨20556204462060614687120989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27408272616080819582827985 20556204462060614687120989)
              ·
                refine ⟨7708576673272730507670371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20556204462060614687120989 7708576673272730507670371)
                ·
                  refine ⟨11562865009909095761505557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708576673272730507670371 11562865009909095761505557)
                  ·
                    refine ⟨542009297339488863820573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11562865009909095761505557 542009297339488863820573)
                    ·
                      rfl

theorem cell23_3166678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3166678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166678 prefixEnd_3166678 := by exact prefixLift 3166678
  have htrace : WordTrace (prefixWord ++ tailWord_3166678) baseStart_3166678 baseEnd_3166678 := by
    simpa [prefixWord, tailWord_3166678, baseEnd_3166678] using wordTrace_append hprefix tailTrace_3166678
  have hstable : (prefixWord ++ tailWord_3166678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166678).length < 2 ^ (prefixWord ++ tailWord_3166678).sum := by decide
  have hdescent : baseEnd_3166678 < baseStart_3166678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166681 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_3166681 : Nat := 118140960795 + 3166681 * 2 ^ 59
def prefixEnd_3166681 : Nat := 4983230072969 + 3 ^ 40 * 3166681 * 2
def baseEnd_3166681 : Nat := 1626029432460430079724205

theorem tailTrace_3166681 : CollatzResearch.WordTrace tailWord_3166681 prefixEnd_3166681 1626029432460430079724205 := by
  unfold tailWord_3166681
  simp only [CollatzResearch.WordTrace]
  refine ⟨115498344640663037902547897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76998896427108691935031931 115498344640663037902547897)
  ·
    refine ⟨86623758480497278426910923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115498344640663037902547897 86623758480497278426910923)
    ·
      refine ⟨129935637720745917640366385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86623758480497278426910923 129935637720745917640366385)
      ·
        refine ⟨97451728290559438230274789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129935637720745917640366385 97451728290559438230274789)
        ·
          refine ⟨18272199054479894668176523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97451728290559438230274789 18272199054479894668176523)
          ·
            refine ⟨27408298581719842002264785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272199054479894668176523 27408298581719842002264785)
            ·
              refine ⟨20556223936289881501698589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27408298581719842002264785 20556223936289881501698589)
              ·
                refine ⟨7708583976108705563136971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20556223936289881501698589 7708583976108705563136971)
                ·
                  refine ⟨11562875964163058344705457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708583976108705563136971 11562875964163058344705457)
                  ·
                    refine ⟨8672156973122293758529093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11562875964163058344705457 8672156973122293758529093)
                    ·
                      refine ⟨1626029432460430079724205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8672156973122293758529093 1626029432460430079724205)
                      ·
                        rfl

theorem cell23_3166681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_3166681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166681 prefixEnd_3166681 := by exact prefixLift 3166681
  have htrace : WordTrace (prefixWord ++ tailWord_3166681) baseStart_3166681 baseEnd_3166681 := by
    simpa [prefixWord, tailWord_3166681, baseEnd_3166681] using wordTrace_append hprefix tailTrace_3166681
  have hstable : (prefixWord ++ tailWord_3166681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166681).length < 2 ^ (prefixWord ++ tailWord_3166681).sum := by decide
  have hdescent : baseEnd_3166681 < baseStart_3166681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166685 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_3166685 : Nat := 118140960795 + 3166685 * 2 ^ 59
def prefixEnd_3166685 : Nat := 4983230072969 + 3 ^ 40 * 3166685 * 2
def baseEnd_3166685 : Nat := 1626031486383048064074187

theorem tailTrace_3166685 : CollatzResearch.WordTrace tailWord_3166685 prefixEnd_3166685 1626031486383048064074187 := by
  unfold tailWord_3166685
  simp only [CollatzResearch.WordTrace]
  refine ⟨115498490532648546585693509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76998993688432364390462339 115498490532648546585693509)
  ·
    refine ⟨21655966974871602484817533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115498490532648546585693509 21655966974871602484817533)
    ·
      refine ⟨8120987615576850931806575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21655966974871602484817533 8120987615576850931806575)
      ·
        refine ⟨12181481423365276397709863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120987615576850931806575 12181481423365276397709863)
        ·
          refine ⟨18272222135047914596564795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181481423365276397709863 18272222135047914596564795)
          ·
            refine ⟨27408333202571871894847193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272222135047914596564795 27408333202571871894847193)
            ·
              refine ⟨20556249901928903921135395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27408333202571871894847193 20556249901928903921135395)
              ·
                refine ⟨30834374852893355881703093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20556249901928903921135395 30834374852893355881703093)
                ·
                  refine ⟨2890722642458752113909665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30834374852893355881703093 2890722642458752113909665)
                  ·
                    refine ⟨2168041981844064085432249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890722642458752113909665 2168041981844064085432249)
                    ·
                      refine ⟨1626031486383048064074187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168041981844064085432249 1626031486383048064074187)
                      ·
                        rfl

theorem cell23_3166685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_3166685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166685 prefixEnd_3166685 := by exact prefixLift 3166685
  have htrace : WordTrace (prefixWord ++ tailWord_3166685) baseStart_3166685 baseEnd_3166685 := by
    simpa [prefixWord, tailWord_3166685, baseEnd_3166685] using wordTrace_append hprefix tailTrace_3166685
  have hstable : (prefixWord ++ tailWord_3166685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166685).length < 2 ^ (prefixWord ++ tailWord_3166685).sum := by decide
  have hdescent : baseEnd_3166685 < baseStart_3166685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166698 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3166698 : Nat := 118140960795 + 3166698 * 2 ^ 59
def prefixEnd_3166698 : Nat := 4983230072969 + 3 ^ 40 * 3166698 * 2
def baseEnd_3166698 : Nat := 1626038161631556513211627

theorem tailTrace_3166698 : CollatzResearch.WordTrace tailWord_3166698 prefixEnd_3166698 1626038161631556513211627 := by
  unfold tailWord_3166698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28874741170400362451479187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76999309787734299870611165 28874741170400362451479187)
  ·
    refine ⟨43312111755600543677218781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28874741170400362451479187 43312111755600543677218781)
    ·
      refine ⟨16242041908350203878957043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43312111755600543677218781 16242041908350203878957043)
      ·
        refine ⟨24363062862525305818435565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16242041908350203878957043 24363062862525305818435565)
        ·
          refine ⟨9136148573446989681913337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24363062862525305818435565 9136148573446989681913337)
          ·
            refine ⟨6852111430085242261435003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9136148573446989681913337 6852111430085242261435003)
            ·
              refine ⟨10278167145127863392152505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852111430085242261435003 10278167145127863392152505)
              ·
                refine ⟨7708625358845897544114379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10278167145127863392152505 7708625358845897544114379)
                ·
                  refine ⟨11562938038268846316171569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708625358845897544114379 11562938038268846316171569)
                  ·
                    refine ⟨8672203528701634737128677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11562938038268846316171569 8672203528701634737128677)
                    ·
                      refine ⟨1626038161631556513211627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8672203528701634737128677 1626038161631556513211627)
                      ·
                        rfl

theorem cell23_3166698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3166698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166698 prefixEnd_3166698 := by exact prefixLift 3166698
  have htrace : WordTrace (prefixWord ++ tailWord_3166698) baseStart_3166698 baseEnd_3166698 := by
    simpa [prefixWord, tailWord_3166698, baseEnd_3166698] using wordTrace_append hprefix tailTrace_3166698
  have hstable : (prefixWord ++ tailWord_3166698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166698).length < 2 ^ (prefixWord ++ tailWord_3166698).sum := by decide
  have hdescent : baseEnd_3166698 < baseStart_3166698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166705 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 1, 2, 3]
def baseStart_3166705 : Nat := 118140960795 + 3166705 * 2 ^ 59
def prefixEnd_3166705 : Nat := 4983230072969 + 3 ^ 40 * 3166705 * 2
def baseEnd_3166705 : Nat := 1626041755996137985824095

theorem tailTrace_3166705 : CollatzResearch.WordTrace tailWord_3166705 prefixEnd_3166705 1626041755996137985824095 := by
  unfold tailWord_3166705
  simp only [CollatzResearch.WordTrace]
  refine ⟨115499219992576090001421569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76999479995050726667614379 115499219992576090001421569)
  ·
    refine ⟨86624414994432067501066177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115499219992576090001421569 86624414994432067501066177)
    ·
      refine ⟨64968311245824050625799633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86624414994432067501066177 64968311245824050625799633)
      ·
        refine ⟨48726233434368037969349725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64968311245824050625799633 48726233434368037969349725)
        ·
          refine ⟨18272337537888014238506147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48726233434368037969349725 18272337537888014238506147)
          ·
            refine ⟨27408506306832021357759221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272337537888014238506147 27408506306832021357759221)
            ·
              refine ⟨2569547466265502002289927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27408506306832021357759221 2569547466265502002289927)
              ·
                refine ⟨3854321199398253003434891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569547466265502002289927 3854321199398253003434891)
                ·
                  refine ⟨5781481799097379505152337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854321199398253003434891 5781481799097379505152337)
                  ·
                    refine ⟨4336111349323034628864253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781481799097379505152337 4336111349323034628864253)
                    ·
                      refine ⟨1626041755996137985824095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336111349323034628864253 1626041755996137985824095)
                      ·
                        rfl

theorem cell23_3166705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_3166705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166705 prefixEnd_3166705 := by exact prefixLift 3166705
  have htrace : WordTrace (prefixWord ++ tailWord_3166705) baseStart_3166705 baseEnd_3166705 := by
    simpa [prefixWord, tailWord_3166705, baseEnd_3166705] using wordTrace_append hprefix tailTrace_3166705
  have hstable : (prefixWord ++ tailWord_3166705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166705).length < 2 ^ (prefixWord ++ tailWord_3166705).sum := by decide
  have hdescent : baseEnd_3166705 < baseStart_3166705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166721 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3166721 : Nat := 118140960795 + 3166721 * 2 ^ 59
def prefixEnd_3166721 : Nat := 4983230072969 + 3 ^ 40 * 3166721 * 2
def baseEnd_3166721 : Nat := 542016657228869974408007

theorem tailTrace_3166721 : CollatzResearch.WordTrace tailWord_3166721 prefixEnd_3166721 542016657228869974408007 := by
  unfold tailWord_3166721
  simp only [CollatzResearch.WordTrace]
  refine ⟨115499803560518124734004017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76999869040345416489336011 115499803560518124734004017)
  ·
    refine ⟨86624852670388593550503013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115499803560518124734004017 86624852670388593550503013)
    ·
      refine ⟨16242159875697861290719315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86624852670388593550503013 16242159875697861290719315)
      ·
        refine ⟨24363239813546791936078973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16242159875697861290719315 24363239813546791936078973)
        ·
          refine ⟨9136214930080046976029615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24363239813546791936078973 9136214930080046976029615)
          ·
            refine ⟨13704322395120070464044423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9136214930080046976029615 13704322395120070464044423)
            ·
              refine ⟨20556483592680105696066635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13704322395120070464044423 20556483592680105696066635)
              ·
                refine ⟨30834725389020158544099953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20556483592680105696066635 30834725389020158544099953)
                ·
                  refine ⟨23126044041765118908074965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30834725389020158544099953 23126044041765118908074965)
                  ·
                    refine ⟨542016657228869974408007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23126044041765118908074965 542016657228869974408007)
                    ·
                      rfl

theorem cell23_3166721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3166721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166721 prefixEnd_3166721 := by exact prefixLift 3166721
  have htrace : WordTrace (prefixWord ++ tailWord_3166721) baseStart_3166721 baseEnd_3166721 := by
    simpa [prefixWord, tailWord_3166721, baseEnd_3166721] using wordTrace_append hprefix tailTrace_3166721
  have hstable : (prefixWord ++ tailWord_3166721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166721).length < 2 ^ (prefixWord ++ tailWord_3166721).sum := by decide
  have hdescent : baseEnd_3166721 < baseStart_3166721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166741 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3166741 : Nat := 118140960795 + 3166741 * 2 ^ 59
def prefixEnd_3166741 : Nat := 4983230072969 + 3 ^ 40 * 3166741 * 2
def baseEnd_3166741 : Nat := 1626060241299699844973929

theorem tailTrace_3166741 : CollatzResearch.WordTrace tailWord_3166741 prefixEnd_3166741 1626060241299699844973929 := by
  unfold tailWord_3166741
  simp only [CollatzResearch.WordTrace]
  refine ⟨115500533020445668149732077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77000355346963778766488051 115500533020445668149732077)
  ·
    refine ⟨43312699882667125556149529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115500533020445668149732077 43312699882667125556149529)
    ·
      refine ⟨32484524912000344167112147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43312699882667125556149529 32484524912000344167112147)
      ·
        refine ⟨48726787368000516250668221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32484524912000344167112147 48726787368000516250668221)
        ·
          refine ⟨18272545263000193594000583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48726787368000516250668221 18272545263000193594000583)
          ·
            refine ⟨27408817894500290391000875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272545263000193594000583 27408817894500290391000875)
            ·
              refine ⟨41113226841750435586501313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27408817894500290391000875 41113226841750435586501313)
              ·
                refine ⟨30834920131312826689875985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41113226841750435586501313 30834920131312826689875985)
                ·
                  refine ⟨23126190098484620017406989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30834920131312826689875985 23126190098484620017406989)
                  ·
                    refine ⟨8672321286931732506527621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23126190098484620017406989 8672321286931732506527621)
                    ·
                      refine ⟨1626060241299699844973929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8672321286931732506527621 1626060241299699844973929)
                      ·
                        rfl

theorem cell23_3166741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3166741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166741 prefixEnd_3166741 := by exact prefixLift 3166741
  have htrace : WordTrace (prefixWord ++ tailWord_3166741) baseStart_3166741 baseEnd_3166741 := by
    simpa [prefixWord, tailWord_3166741, baseEnd_3166741] using wordTrace_append hprefix tailTrace_3166741
  have hstable : (prefixWord ++ tailWord_3166741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166741).length < 2 ^ (prefixWord ++ tailWord_3166741).sum := by decide
  have hdescent : baseEnd_3166741 < baseStart_3166741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166756 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3166756 : Nat := 118140960795 + 3166756 * 2 ^ 59
def prefixEnd_3166756 : Nat := 4983230072969 + 3 ^ 40 * 3166756 * 2
def baseEnd_3166756 : Nat := 1626067943509517286286361

theorem tailTrace_3166756 : CollatzResearch.WordTrace tailWord_3166756 prefixEnd_3166756 1626067943509517286286361 := by
  unfold tailWord_3166756
  simp only [CollatzResearch.WordTrace]
  refine ⟨57750540057695662855764061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77000720076927550474352081 57750540057695662855764061)
  ·
    refine ⟨21656452521635873570911523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57750540057695662855764061 21656452521635873570911523)
    ·
      refine ⟨32484678782453810356367285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21656452521635873570911523 32484678782453810356367285)
      ·
        refine ⟨3045438635855044720909433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32484678782453810356367285 3045438635855044720909433)
        ·
          refine ⟨2284078976891283540682075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045438635855044720909433 2284078976891283540682075)
          ·
            refine ⟨3426118465336925311023113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284078976891283540682075 3426118465336925311023113)
            ·
              refine ⟨2569588849002693983267335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426118465336925311023113 2569588849002693983267335)
              ·
                refine ⟨3854383273504040974901003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569588849002693983267335 3854383273504040974901003)
                ·
                  refine ⟨5781574910256061462351505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854383273504040974901003 5781574910256061462351505)
                  ·
                    refine ⟨4336181182692046096763629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5781574910256061462351505 4336181182692046096763629)
                    ·
                      refine ⟨1626067943509517286286361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336181182692046096763629 1626067943509517286286361)
                      ·
                        rfl

theorem cell23_3166756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3166756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166756 prefixEnd_3166756 := by exact prefixLift 3166756
  have htrace : WordTrace (prefixWord ++ tailWord_3166756) baseStart_3166756 baseEnd_3166756 := by
    simpa [prefixWord, tailWord_3166756, baseEnd_3166756] using wordTrace_append hprefix tailTrace_3166756
  have hstable : (prefixWord ++ tailWord_3166756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166756).length < 2 ^ (prefixWord ++ tailWord_3166756).sum := by decide
  have hdescent : baseEnd_3166756 < baseStart_3166756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166762 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3166762 : Nat := 118140960795 + 3166762 * 2 ^ 59
def prefixEnd_3166762 : Nat := 4983230072969 + 3 ^ 40 * 3166762 * 2
def baseEnd_3166762 : Nat := 1626071024393444262811333

theorem tailTrace_3166762 : CollatzResearch.WordTrace tailWord_3166762 prefixEnd_3166762 1626071024393444262811333 := by
  unfold tailWord_3166762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28875324738342397184061635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77000865968913059157497693 28875324738342397184061635)
  ·
    refine ⟨43312987107513595776092453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28875324738342397184061635 43312987107513595776092453)
    ·
      refine ⟨8121185082658799208017335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43312987107513595776092453 8121185082658799208017335)
      ·
        refine ⟨12181777623988198812026003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8121185082658799208017335 12181777623988198812026003)
        ·
          refine ⟨18272666435982298218039005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181777623988198812026003 18272666435982298218039005)
          ·
            refine ⟨6852249913493361831764627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18272666435982298218039005 6852249913493361831764627)
            ·
              refine ⟨10278374870240042747646941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852249913493361831764627 10278374870240042747646941)
              ·
                refine ⟨3854390576340016030367603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10278374870240042747646941 3854390576340016030367603)
                ·
                  refine ⟨5781585864510024045551405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854390576340016030367603 5781585864510024045551405)
                  ·
                    refine ⟨2168094699191259017081777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5781585864510024045551405 2168094699191259017081777)
                    ·
                      refine ⟨1626071024393444262811333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168094699191259017081777 1626071024393444262811333)
                      ·
                        rfl

theorem cell23_3166762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3166762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166762 prefixEnd_3166762 := by exact prefixLift 3166762
  have htrace : WordTrace (prefixWord ++ tailWord_3166762) baseStart_3166762 baseEnd_3166762 := by
    simpa [prefixWord, tailWord_3166762, baseEnd_3166762] using wordTrace_append hprefix tailTrace_3166762
  have hstable : (prefixWord ++ tailWord_3166762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166762).length < 2 ^ (prefixWord ++ tailWord_3166762).sum := by decide
  have hdescent : baseEnd_3166762 < baseStart_3166762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166771 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4]
def baseStart_3166771 : Nat := 118140960795 + 3166771 * 2 ^ 59
def prefixEnd_3166771 : Nat := 4983230072969 + 3 ^ 40 * 3166771 * 2
def baseEnd_3166771 : Nat := 1626075645719334727598791

theorem tailTrace_3166771 : CollatzResearch.WordTrace tailWord_3166771 prefixEnd_3166771 1626075645719334727598791 := by
  unfold tailWord_3166771
  simp only [CollatzResearch.WordTrace]
  refine ⟨115501627210336983273324167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77001084806891322182216111 115501627210336983273324167)
  ·
    refine ⟨173252440815505474909986251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115501627210336983273324167 173252440815505474909986251)
    ·
      refine ⟨259878661223258212364979377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173252440815505474909986251 259878661223258212364979377)
      ·
        refine ⟨194908995917443659273734533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259878661223258212364979377 194908995917443659273734533)
        ·
          refine ⟨36545436734520686113825225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194908995917443659273734533 36545436734520686113825225)
          ·
            refine ⟨27409077550890514585368919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36545436734520686113825225 27409077550890514585368919)
            ·
              refine ⟨41113616326335771878053379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27409077550890514585368919 41113616326335771878053379)
              ·
                refine ⟨61670424489503657817080069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41113616326335771878053379 61670424489503657817080069)
                ·
                  refine ⟨11563204591781935840702513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61670424489503657817080069 11563204591781935840702513)
                  ·
                    refine ⟨8672403443836451880526885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11563204591781935840702513 8672403443836451880526885)
                    ·
                      refine ⟨1626075645719334727598791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8672403443836451880526885 1626075645719334727598791)
                      ·
                        rfl

theorem cell23_3166771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_3166771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166771 prefixEnd_3166771 := by exact prefixLift 3166771
  have htrace : WordTrace (prefixWord ++ tailWord_3166771) baseStart_3166771 baseEnd_3166771 := by
    simpa [prefixWord, tailWord_3166771, baseEnd_3166771] using wordTrace_append hprefix tailTrace_3166771
  have hstable : (prefixWord ++ tailWord_3166771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166771).length < 2 ^ (prefixWord ++ tailWord_3166771).sum := by decide
  have hdescent : baseEnd_3166771 < baseStart_3166771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166775 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 4, 2, 2]
def baseStart_3166775 : Nat := 118140960795 + 3166775 * 2 ^ 59
def prefixEnd_3166775 : Nat := 4983230072969 + 3 ^ 40 * 3166775 * 2
def baseEnd_3166775 : Nat := 1626077699641952711948773

theorem tailTrace_3166775 : CollatzResearch.WordTrace tailWord_3166775 prefixEnd_3166775 1626077699641952711948773 := by
  unfold tailWord_3166775
  simp only [CollatzResearch.WordTrace]
  refine ⟨115501773102322491956469779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77001182068214994637646519 115501773102322491956469779)
  ·
    refine ⟨173252659653483737934704669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115501773102322491956469779 173252659653483737934704669)
    ·
      refine ⟨64969747370056401725514251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173252659653483737934704669 64969747370056401725514251)
      ·
        refine ⟨97454621055084602588271377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64969747370056401725514251 97454621055084602588271377)
        ·
          refine ⟨73090965791313451941203533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97454621055084602588271377 73090965791313451941203533)
          ·
            refine ⟨27409112171742544477951325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73090965791313451941203533 27409112171742544477951325)
            ·
              refine ⟨10278417064403454179231747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27409112171742544477951325 10278417064403454179231747)
              ·
                refine ⟨15417625596605181268847621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10278417064403454179231747 15417625596605181268847621)
                ·
                  refine ⟨2890804799363471487908929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15417625596605181268847621 2890804799363471487908929)
                  ·
                    refine ⟨2168103599522603615931697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890804799363471487908929 2168103599522603615931697)
                    ·
                      refine ⟨1626077699641952711948773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168103599522603615931697 1626077699641952711948773)
                      ·
                        rfl

theorem cell23_3166775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_3166775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166775 prefixEnd_3166775 := by exact prefixLift 3166775
  have htrace : WordTrace (prefixWord ++ tailWord_3166775) baseStart_3166775 baseEnd_3166775 := by
    simpa [prefixWord, tailWord_3166775, baseEnd_3166775] using wordTrace_append hprefix tailTrace_3166775
  have hstable : (prefixWord ++ tailWord_3166775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166775).length < 2 ^ (prefixWord ++ tailWord_3166775).sum := by decide
  have hdescent : baseEnd_3166775 < baseStart_3166775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166832 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 5]
def baseStart_3166832 : Nat := 118140960795 + 3166832 * 2 ^ 59
def prefixEnd_3166832 : Nat := 4983230072969 + 3 ^ 40 * 3166832 * 2
def baseEnd_3166832 : Nat := 180678552004362109881779

theorem tailTrace_3166832 : CollatzResearch.WordTrace tailWord_3166832 prefixEnd_3166832 180678552004362109881779 := by
  unfold tailWord_3166832
  simp only [CollatzResearch.WordTrace]
  refine ⟨57751926031557995345647375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77002568042077327127529833 57751926031557995345647375)
  ·
    refine ⟨86627889047336993018471063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57751926031557995345647375 86627889047336993018471063)
    ·
      refine ⟨129941833571005489527706595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86627889047336993018471063 129941833571005489527706595)
      ·
        refine ⟨194912750356508234291559893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129941833571005489527706595 194912750356508234291559893)
        ·
          refine ⟨4568267586480661741208435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194912750356508234291559893 4568267586480661741208435)
          ·
            refine ⟨6852401379720992611812653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568267586480661741208435 6852401379720992611812653)
            ·
              refine ⟨2569650517395372229429745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6852401379720992611812653 2569650517395372229429745)
              ·
                refine ⟨1927237888046529172072309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569650517395372229429745 1927237888046529172072309)
                ·
                  refine ⟨180678552004362109881779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1927237888046529172072309 180678552004362109881779)
                  ·
                    rfl

theorem cell23_3166832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 5].length) (baseStart_3166832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166832 prefixEnd_3166832 := by exact prefixLift 3166832
  have htrace : WordTrace (prefixWord ++ tailWord_3166832) baseStart_3166832 baseEnd_3166832 := by
    simpa [prefixWord, tailWord_3166832, baseEnd_3166832] using wordTrace_append hprefix tailTrace_3166832
  have hstable : (prefixWord ++ tailWord_3166832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166832).length < 2 ^ (prefixWord ++ tailWord_3166832).sum := by decide
  have hdescent : baseEnd_3166832 < baseStart_3166832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166898 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3166898 : Nat := 118140960795 + 3166898 * 2 ^ 59
def prefixEnd_3166898 : Nat := 4983230072969 + 3 ^ 40 * 3166898 * 2
def baseEnd_3166898 : Nat := 1626140857762455730710707

theorem tailTrace_3166898 : CollatzResearch.WordTrace tailWord_3166898 prefixEnd_3166898 1626140857762455730710707 := by
  unfold tailWord_3166898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28876564820219220990799337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77004172853917922642131565 28876564820219220990799337)
  ·
    refine ⟨21657423615164415743099503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28876564820219220990799337 21657423615164415743099503)
    ·
      refine ⟨32486135422746623614649255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21657423615164415743099503 32486135422746623614649255)
      ·
        refine ⟨48729203134119935421973883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32486135422746623614649255 48729203134119935421973883)
        ·
          refine ⟨73093804701179903132960825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48729203134119935421973883 73093804701179903132960825)
          ·
            refine ⟨54820353525884927349720619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73093804701179903132960825 54820353525884927349720619)
            ·
              refine ⟨82230530288827391024580929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54820353525884927349720619 82230530288827391024580929)
              ·
                refine ⟨61672897716620543268435697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82230530288827391024580929 61672897716620543268435697)
                ·
                  refine ⟨46254673287465407451326773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61672897716620543268435697 46254673287465407451326773)
                  ·
                    refine ⟨4336375620699881948561885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46254673287465407451326773 4336375620699881948561885)
                    ·
                      refine ⟨1626140857762455730710707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336375620699881948561885 1626140857762455730710707)
                      ·
                        rfl

theorem cell23_3166898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3166898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166898 prefixEnd_3166898 := by exact prefixLift 3166898
  have htrace : WordTrace (prefixWord ++ tailWord_3166898) baseStart_3166898 baseEnd_3166898 := by
    simpa [prefixWord, tailWord_3166898, baseEnd_3166898] using wordTrace_append hprefix tailTrace_3166898
  have hstable : (prefixWord ++ tailWord_3166898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166898).length < 2 ^ (prefixWord ++ tailWord_3166898).sum := by decide
  have hdescent : baseEnd_3166898 < baseStart_3166898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166935 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 1, 5]
def baseStart_3166935 : Nat := 118140960795 + 3166935 * 2 ^ 59
def prefixEnd_3166935 : Nat := 4983230072969 + 3 ^ 40 * 3166935 * 2
def baseEnd_3166935 : Nat := 542053285515557361982679

theorem tailTrace_3166935 : CollatzResearch.WordTrace tailWord_3166935 prefixEnd_3166935 542053285515557361982679 := by
  unfold tailWord_3166935
  simp only [CollatzResearch.WordTrace]
  refine ⟨115507608781742839282294259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77005072521161892854862839 115507608781742839282294259)
  ·
    refine ⟨173261413172614258923441389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115507608781742839282294259 173261413172614258923441389)
    ·
      refine ⟨64973029939730347096290521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173261413172614258923441389 64973029939730347096290521)
      ·
        refine ⟨48729772454797760322217891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64973029939730347096290521 48729772454797760322217891)
        ·
          refine ⟨73094658682196640483326837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48729772454797760322217891 73094658682196640483326837)
          ·
            refine ⟨6852624251455935045311891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73094658682196640483326837 6852624251455935045311891)
            ·
              refine ⟨10278936377183902567967837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852624251455935045311891 10278936377183902567967837)
              ·
                refine ⟨3854601141443963462987939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10278936377183902567967837 3854601141443963462987939)
                ·
                  refine ⟨5781901712165945194481909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854601141443963462987939 5781901712165945194481909)
                  ·
                    refine ⟨542053285515557361982679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5781901712165945194481909 542053285515557361982679)
                    ·
                      rfl

theorem cell23_3166935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_3166935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166935 prefixEnd_3166935 := by exact prefixLift 3166935
  have htrace : WordTrace (prefixWord ++ tailWord_3166935) baseStart_3166935 baseEnd_3166935 := by
    simpa [prefixWord, tailWord_3166935, baseEnd_3166935] using wordTrace_append hprefix tailTrace_3166935
  have hstable : (prefixWord ++ tailWord_3166935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166935).length < 2 ^ (prefixWord ++ tailWord_3166935).sum := by decide
  have hdescent : baseEnd_3166935 < baseStart_3166935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166949 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 1, 1, 3]
def baseStart_3166949 : Nat := 118140960795 + 3166949 * 2 ^ 59
def prefixEnd_3166949 : Nat := 4983230072969 + 3 ^ 40 * 3166949 * 2
def baseEnd_3166949 : Nat := 1626167045275835031172973

theorem tailTrace_3166949 : CollatzResearch.WordTrace tailWord_3166949 prefixEnd_3166949 1626167045275835031172973 := by
  unfold tailWord_3166949
  simp only [CollatzResearch.WordTrace]
  refine ⟨115508119403692119673303901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77005412935794746448869267 115508119403692119673303901)
  ·
    refine ⟨43315544776384544877488963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115508119403692119673303901 43315544776384544877488963)
    ·
      refine ⟨64973317164576817316233445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43315544776384544877488963 64973317164576817316233445)
      ·
        refine ⟨12182496968358153246793771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64973317164576817316233445 12182496968358153246793771)
        ·
          refine ⟨18273745452537229870190657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12182496968358153246793771 18273745452537229870190657)
          ·
            refine ⟨13705309089402922402642993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18273745452537229870190657 13705309089402922402642993)
            ·
              refine ⟨10278981817052191801982245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13705309089402922402642993 10278981817052191801982245)
              ·
                refine ⟨1927309090697285962871671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10278981817052191801982245 1927309090697285962871671)
                ·
                  refine ⟨2890963636045928944307507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927309090697285962871671 2890963636045928944307507)
                  ·
                    refine ⟨4336445454068893416461261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2890963636045928944307507 4336445454068893416461261)
                    ·
                      refine ⟨1626167045275835031172973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336445454068893416461261 1626167045275835031172973)
                      ·
                        rfl

theorem cell23_3166949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_3166949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166949 prefixEnd_3166949 := by exact prefixLift 3166949
  have htrace : WordTrace (prefixWord ++ tailWord_3166949) baseStart_3166949 baseEnd_3166949 := by
    simpa [prefixWord, tailWord_3166949, baseEnd_3166949] using wordTrace_append hprefix tailTrace_3166949
  have hstable : (prefixWord ++ tailWord_3166949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166949).length < 2 ^ (prefixWord ++ tailWord_3166949).sum := by decide
  have hdescent : baseEnd_3166949 < baseStart_3166949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166968 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3166968 : Nat := 118140960795 + 3166968 * 2 ^ 59
def prefixEnd_3166968 : Nat := 4983230072969 + 3 ^ 40 * 3166968 * 2
def baseEnd_3166968 : Nat := 1626176801408270456835385

theorem tailTrace_3166968 : CollatzResearch.WordTrace tailWord_3166968 prefixEnd_3166968 1626176801408270456835385 := by
  unfold tailWord_3166968
  simp only [CollatzResearch.WordTrace]
  refine ⟨57754406195311642959122779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77005874927082190612163705 57754406195311642959122779)
  ·
    refine ⟨86631609292967464438684169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57754406195311642959122779 86631609292967464438684169)
    ·
      refine ⟨64973706969725598329013127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86631609292967464438684169 64973706969725598329013127)
      ·
        refine ⟨97460560454588397493519691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64973706969725598329013127 97460560454588397493519691)
        ·
          refine ⟨146190840681882596240279537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97460560454588397493519691 146190840681882596240279537)
          ·
            refine ⟨109643130511411947180209653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146190840681882596240279537 109643130511411947180209653)
            ·
              refine ⟨10279043485444870048144655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109643130511411947180209653 10279043485444870048144655)
              ·
                refine ⟨15418565228167305072216983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279043485444870048144655 15418565228167305072216983)
                ·
                  refine ⟨23127847842250957608325475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15418565228167305072216983 23127847842250957608325475)
                  ·
                    refine ⟨34691771763376436412488213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23127847842250957608325475 34691771763376436412488213)
                    ·
                      refine ⟨1626176801408270456835385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34691771763376436412488213 1626176801408270456835385)
                      ·
                        rfl

theorem cell23_3166968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3166968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166968 prefixEnd_3166968 := by exact prefixLift 3166968
  have htrace : WordTrace (prefixWord ++ tailWord_3166968) baseStart_3166968 baseEnd_3166968 := by
    simpa [prefixWord, tailWord_3166968, baseEnd_3166968] using wordTrace_append hprefix tailTrace_3166968
  have hstable : (prefixWord ++ tailWord_3166968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166968).length < 2 ^ (prefixWord ++ tailWord_3166968).sum := by decide
  have hdescent : baseEnd_3166968 < baseStart_3166968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166972 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_3166972 : Nat := 118140960795 + 3166972 * 2 ^ 59
def prefixEnd_3166972 : Nat := 4983230072969 + 3 ^ 40 * 3166972 * 2
def baseEnd_3166972 : Nat := 1626178855330888441185367

theorem tailTrace_3166972 : CollatzResearch.WordTrace tailWord_3166972 prefixEnd_3166972 1626178855330888441185367 := by
  unfold tailWord_3166972
  simp only [CollatzResearch.WordTrace]
  refine ⟨57754479141304397300695585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77005972188405863067594113 57754479141304397300695585)
  ·
    refine ⟨43315859355978297975521689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57754479141304397300695585 43315859355978297975521689)
    ·
      refine ⟨32486894516983723481641267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43315859355978297975521689 32486894516983723481641267)
      ·
        refine ⟨48730341775475585222461901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32486894516983723481641267 48730341775475585222461901)
        ·
          refine ⟨18273878165803344458423213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48730341775475585222461901 18273878165803344458423213)
          ·
            refine ⟨6852704312176254171908705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18273878165803344458423213 6852704312176254171908705)
            ·
              refine ⟨5139528234132190628931529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6852704312176254171908705 5139528234132190628931529)
              ·
                refine ⟨3854646175599142971698647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139528234132190628931529 3854646175599142971698647)
                ·
                  refine ⟨5781969263398714457547971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854646175599142971698647 5781969263398714457547971)
                  ·
                    refine ⟨8672953895098071686321957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5781969263398714457547971 8672953895098071686321957)
                    ·
                      refine ⟨1626178855330888441185367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8672953895098071686321957 1626178855330888441185367)
                      ·
                        rfl

theorem cell23_3166972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_3166972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3166972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3166972 prefixEnd_3166972 := by exact prefixLift 3166972
  have htrace : WordTrace (prefixWord ++ tailWord_3166972) baseStart_3166972 baseEnd_3166972 := by
    simpa [prefixWord, tailWord_3166972, baseEnd_3166972] using wordTrace_append hprefix tailTrace_3166972
  have hstable : (prefixWord ++ tailWord_3166972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166972).length < 2 ^ (prefixWord ++ tailWord_3166972).sum := by decide
  have hdescent : baseEnd_3166972 < baseStart_3166972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167032 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 3, 3, 2]
def baseStart_3167032 : Nat := 118140960795 + 3167032 * 2 ^ 59
def prefixEnd_3167032 : Nat := 4983230072969 + 3 ^ 40 * 3167032 * 2
def baseEnd_3167032 : Nat := 1626209664170158206435091

theorem tailTrace_3167032 : CollatzResearch.WordTrace tailWord_3167032 prefixEnd_3167032 1626209664170158206435091 := by
  unfold tailWord_3167032
  simp only [CollatzResearch.WordTrace]
  refine ⟨57755573331195712424287675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77007431108260949899050233 57755573331195712424287675)
  ·
    refine ⟨86633359996793568636431513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57755573331195712424287675 86633359996793568636431513)
    ·
      refine ⟨64975019997595176477323635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86633359996793568636431513 64975019997595176477323635)
      ·
        refine ⟨97462529996392764715985453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64975019997595176477323635 97462529996392764715985453)
        ·
          refine ⟨36548448748647286768494545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97462529996392764715985453 36548448748647286768494545)
          ·
            refine ⟨27411336561485465076370909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36548448748647286768494545 27411336561485465076370909)
            ·
              refine ⟨10279251210557049403639091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27411336561485465076370909 10279251210557049403639091)
              ·
                refine ⟨15418876815835574105458637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279251210557049403639091 15418876815835574105458637)
                ·
                  refine ⟨5782078805938340289546989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15418876815835574105458637 5782078805938340289546989)
                  ·
                    refine ⟨2168279552226877608580121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5782078805938340289546989 2168279552226877608580121)
                    ·
                      refine ⟨1626209664170158206435091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168279552226877608580121 1626209664170158206435091)
                      ·
                        rfl

theorem cell23_3167032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_3167032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167032 prefixEnd_3167032 := by exact prefixLift 3167032
  have htrace : WordTrace (prefixWord ++ tailWord_3167032) baseStart_3167032 baseEnd_3167032 := by
    simpa [prefixWord, tailWord_3167032, baseEnd_3167032] using wordTrace_append hprefix tailTrace_3167032
  have hstable : (prefixWord ++ tailWord_3167032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167032).length < 2 ^ (prefixWord ++ tailWord_3167032).sum := by decide
  have hdescent : baseEnd_3167032 < baseStart_3167032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167065 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_3167065 : Nat := 118140960795 + 3167065 * 2 ^ 59
def prefixEnd_3167065 : Nat := 4983230072969 + 3 ^ 40 * 3167065 * 2
def baseEnd_3167065 : Nat := 1626226609031756577322439

theorem tailTrace_3167065 : CollatzResearch.WordTrace tailWord_3167065 prefixEnd_3167065 1626226609031756577322439 := by
  unfold tailWord_3167065
  simp only [CollatzResearch.WordTrace]
  refine ⟨115512350271271871484526649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77008233514181247656351099 115512350271271871484526649)
  ·
    refine ⟨86634262703453903613394987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115512350271271871484526649 86634262703453903613394987)
    ·
      refine ⟨129951394055180855420092481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86634262703453903613394987 129951394055180855420092481)
      ·
        refine ⟨97463545541385641565069361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129951394055180855420092481 97463545541385641565069361)
        ·
          refine ⟨73097659156039231173802021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97463545541385641565069361 73097659156039231173802021)
          ·
            refine ⟨13705811091757355845087879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73097659156039231173802021 13705811091757355845087879)
            ·
              refine ⟨20558716637636033767631819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13705811091757355845087879 20558716637636033767631819)
              ·
                refine ⟨30838074956454050651447729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20558716637636033767631819 30838074956454050651447729)
                ·
                  refine ⟨23128556217340537988585797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30838074956454050651447729 23128556217340537988585797)
                  ·
                    refine ⟨4336604290751350872859837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23128556217340537988585797 4336604290751350872859837)
                    ·
                      refine ⟨1626226609031756577322439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336604290751350872859837 1626226609031756577322439)
                      ·
                        rfl

theorem cell23_3167065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_3167065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167065 prefixEnd_3167065 := by exact prefixLift 3167065
  have htrace : WordTrace (prefixWord ++ tailWord_3167065) baseStart_3167065 baseEnd_3167065 := by
    simpa [prefixWord, tailWord_3167065, baseEnd_3167065] using wordTrace_append hprefix tailTrace_3167065
  have hstable : (prefixWord ++ tailWord_3167065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167065).length < 2 ^ (prefixWord ++ tailWord_3167065).sum := by decide
  have hdescent : baseEnd_3167065 < baseStart_3167065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167075 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3167075 : Nat := 118140960795 + 3167075 * 2 ^ 59
def prefixEnd_3167075 : Nat := 4983230072969 + 3 ^ 40 * 3167075 * 2
def baseEnd_3167075 : Nat := 1626231743838301538197393

theorem tailTrace_3167075 : CollatzResearch.WordTrace tailWord_3167075 prefixEnd_3167075 1626231743838301538197393 := by
  unfold tailWord_3167075
  simp only [CollatzResearch.WordTrace]
  refine ⟨115512715001235643192390679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77008476667490428794927119 115512715001235643192390679)
  ·
    refine ⟨173269072501853464788586019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115512715001235643192390679 173269072501853464788586019)
    ·
      refine ⟨259903608752780197182879029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173269072501853464788586019 259903608752780197182879029)
      ·
        refine ⟨24365963320573143485894909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259903608752780197182879029 24365963320573143485894909)
        ·
          refine ⟨9137236245214928807210591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24365963320573143485894909 9137236245214928807210591)
          ·
            refine ⟨13705854367822393210815887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137236245214928807210591 13705854367822393210815887)
            ·
              refine ⟨20558781551733589816223831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13705854367822393210815887 20558781551733589816223831)
              ·
                refine ⟨30838172327600384724335747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20558781551733589816223831 30838172327600384724335747)
                ·
                  refine ⟨46257258491400577086503621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30838172327600384724335747 46257258491400577086503621)
                  ·
                    refine ⟨8673235967137608203719429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46257258491400577086503621 8673235967137608203719429)
                    ·
                      refine ⟨1626231743838301538197393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8673235967137608203719429 1626231743838301538197393)
                      ·
                        rfl

theorem cell23_3167075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3167075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167075 prefixEnd_3167075 := by exact prefixLift 3167075
  have htrace : WordTrace (prefixWord ++ tailWord_3167075) baseStart_3167075 baseEnd_3167075 := by
    simpa [prefixWord, tailWord_3167075, baseEnd_3167075] using wordTrace_append hprefix tailTrace_3167075
  have hstable : (prefixWord ++ tailWord_3167075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167075).length < 2 ^ (prefixWord ++ tailWord_3167075).sum := by decide
  have hdescent : baseEnd_3167075 < baseStart_3167075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167079 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_3167079 : Nat := 118140960795 + 3167079 * 2 ^ 59
def prefixEnd_3167079 : Nat := 4983230072969 + 3 ^ 40 * 3167079 * 2
def baseEnd_3167079 : Nat := 1626233797760919522547375

theorem tailTrace_3167079 : CollatzResearch.WordTrace tailWord_3167079 prefixEnd_3167079 1626233797760919522547375 := by
  unfold tailWord_3167079
  simp only [CollatzResearch.WordTrace]
  refine ⟨115512860893221151875536291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77008573928814101250357527 115512860893221151875536291)
  ·
    refine ⟨173269291339831727813304437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115512860893221151875536291 173269291339831727813304437)
    ·
      refine ⟨16243996063109224482497291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173269291339831727813304437 16243996063109224482497291)
      ·
        refine ⟨24365994094663836723745937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16243996063109224482497291 24365994094663836723745937)
        ·
          refine ⟨18274495570997877542809453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24365994094663836723745937 18274495570997877542809453)
          ·
            refine ⟨6852935839124204078553545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18274495570997877542809453 6852935839124204078553545)
            ·
              refine ⟨5139701879343153058915159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6852935839124204078553545 5139701879343153058915159)
              ·
                refine ⟨7709552819014729588372739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5139701879343153058915159 7709552819014729588372739)
                ·
                  refine ⟨11564329228522094382559109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7709552819014729588372739 11564329228522094382559109)
                  ·
                    refine ⟨2168311730347892696729833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11564329228522094382559109 2168311730347892696729833)
                    ·
                      refine ⟨1626233797760919522547375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168311730347892696729833 1626233797760919522547375)
                      ·
                        rfl

theorem cell23_3167079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_3167079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167079 prefixEnd_3167079 := by exact prefixLift 3167079
  have htrace : WordTrace (prefixWord ++ tailWord_3167079) baseStart_3167079 baseEnd_3167079 := by
    simpa [prefixWord, tailWord_3167079, baseEnd_3167079] using wordTrace_append hprefix tailTrace_3167079
  have hstable : (prefixWord ++ tailWord_3167079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167079).length < 2 ^ (prefixWord ++ tailWord_3167079).sum := by decide
  have hdescent : baseEnd_3167079 < baseStart_3167079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167112 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3167112 : Nat := 118140960795 + 3167112 * 2 ^ 59
def prefixEnd_3167112 : Nat := 4983230072969 + 3 ^ 40 * 3167112 * 2
def baseEnd_3167112 : Nat := 1626250742622517893434723

theorem tailTrace_3167112 : CollatzResearch.WordTrace tailWord_3167112 prefixEnd_3167112 1626250742622517893434723 := by
  unfold tailWord_3167112
  simp only [CollatzResearch.WordTrace]
  refine ⟨57757032251050799255743795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77009376334734399007658393 57757032251050799255743795)
  ·
    refine ⟨86635548376576198883615693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57757032251050799255743795 86635548376576198883615693)
    ·
      refine ⟨32488330641216074581355885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86635548376576198883615693 32488330641216074581355885)
      ·
        refine ⟨12183123990456027968008457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32488330641216074581355885 12183123990456027968008457)
        ·
          refine ⟨9137342992842020976006343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12183123990456027968008457 9137342992842020976006343)
          ·
            refine ⟨13706014489263031464009515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137342992842020976006343 13706014489263031464009515)
            ·
              refine ⟨20559021733894547196014273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13706014489263031464009515 20559021733894547196014273)
              ·
                refine ⟨15419266300420910397010705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20559021733894547196014273 15419266300420910397010705)
                ·
                  refine ⟨11564449725315682797758029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15419266300420910397010705 11564449725315682797758029)
                  ·
                    refine ⟨4336668646993381049159261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11564449725315682797758029 4336668646993381049159261)
                    ·
                      refine ⟨1626250742622517893434723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4336668646993381049159261 1626250742622517893434723)
                      ·
                        rfl

theorem cell23_3167112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3167112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167112 prefixEnd_3167112 := by exact prefixLift 3167112
  have htrace : WordTrace (prefixWord ++ tailWord_3167112) baseStart_3167112 baseEnd_3167112 := by
    simpa [prefixWord, tailWord_3167112, baseEnd_3167112] using wordTrace_append hprefix tailTrace_3167112
  have hstable : (prefixWord ++ tailWord_3167112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167112).length < 2 ^ (prefixWord ++ tailWord_3167112).sum := by decide
  have hdescent : baseEnd_3167112 < baseStart_3167112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167115 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 2, 5]
def baseStart_3167115 : Nat := 118140960795 + 3167115 * 2 ^ 59
def prefixEnd_3167115 : Nat := 4983230072969 + 3 ^ 40 * 3167115 * 2
def baseEnd_3167115 : Nat := 542084094354827127232403

theorem tailTrace_3167115 : CollatzResearch.WordTrace tailWord_3167115 prefixEnd_3167115 542084094354827127232403 := by
  unfold tailWord_3167115
  simp only [CollatzResearch.WordTrace]
  refine ⟨115514173921090730023846799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77009449280727153349231199 115514173921090730023846799)
  ·
    refine ⟨173271260881636095035770199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115514173921090730023846799 173271260881636095035770199)
    ·
      refine ⟨259906891322454142553655299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173271260881636095035770199 259906891322454142553655299)
      ·
        refine ⟨389860336983681213830482949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259906891322454142553655299 389860336983681213830482949)
        ·
          refine ⟨73098813184440227593215553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389860336983681213830482949 73098813184440227593215553)
          ·
            refine ⟨54824109888330170694911665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73098813184440227593215553 54824109888330170694911665)
            ·
              refine ⟨41118082416247628021183749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54824109888330170694911665 41118082416247628021183749)
              ·
                refine ⟨7709640453046430253971953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41118082416247628021183749 7709640453046430253971953)
                ·
                  refine ⟨5782230339784822690478965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7709640453046430253971953 5782230339784822690478965)
                  ·
                    refine ⟨542084094354827127232403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5782230339784822690478965 542084094354827127232403)
                    ·
                      rfl

theorem cell23_3167115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 5].length) (baseStart_3167115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167115 prefixEnd_3167115 := by exact prefixLift 3167115
  have htrace : WordTrace (prefixWord ++ tailWord_3167115) baseStart_3167115 baseEnd_3167115 := by
    simpa [prefixWord, tailWord_3167115, baseEnd_3167115] using wordTrace_append hprefix tailTrace_3167115
  have hstable : (prefixWord ++ tailWord_3167115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167115).length < 2 ^ (prefixWord ++ tailWord_3167115).sum := by decide
  have hdescent : baseEnd_3167115 < baseStart_3167115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167126 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3167126 : Nat := 118140960795 + 3167126 * 2 ^ 59
def prefixEnd_3167126 : Nat := 4983230072969 + 3 ^ 40 * 3167126 * 2
def baseEnd_3167126 : Nat := 1626257931351680838659659

theorem tailTrace_3167126 : CollatzResearch.WordTrace tailWord_3167126 prefixEnd_3167126 1626257931351680838659659 := by
  unfold tailWord_3167126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219660945253179931406077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77009716749367252601664821 7219660945253179931406077)
  ·
    refine ⟨2707372854469942474277279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7219660945253179931406077 2707372854469942474277279)
    ·
      refine ⟨4061059281704913711415919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707372854469942474277279 4061059281704913711415919)
      ·
        refine ⟨6091588922557370567123879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061059281704913711415919 6091588922557370567123879)
        ·
          refine ⟨9137383383836055850685819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091588922557370567123879 9137383383836055850685819)
          ·
            refine ⟨13706075075754083776028729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137383383836055850685819 13706075075754083776028729)
            ·
              refine ⟨10279556306815562832021547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13706075075754083776028729 10279556306815562832021547)
              ·
                refine ⟨15419334460223344248032321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279556306815562832021547 15419334460223344248032321)
                ·
                  refine ⟨11564500845167508186024241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15419334460223344248032321 11564500845167508186024241)
                  ·
                    refine ⟨8673375633875631139518181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11564500845167508186024241 8673375633875631139518181)
                    ·
                      refine ⟨1626257931351680838659659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8673375633875631139518181 1626257931351680838659659)
                      ·
                        rfl

theorem cell23_3167126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3167126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167126 prefixEnd_3167126 := by exact prefixLift 3167126
  have htrace : WordTrace (prefixWord ++ tailWord_3167126) baseStart_3167126 baseEnd_3167126 := by
    simpa [prefixWord, tailWord_3167126, baseEnd_3167126] using wordTrace_append hprefix tailTrace_3167126
  have hstable : (prefixWord ++ tailWord_3167126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167126).length < 2 ^ (prefixWord ++ tailWord_3167126).sum := by decide
  have hdescent : baseEnd_3167126 < baseStart_3167126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167175 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 8]
def baseStart_3167175 : Nat := 118140960795 + 3167175 * 2 ^ 59
def prefixEnd_3167175 : Nat := 4983230072969 + 3 ^ 40 * 3167175 * 2
def baseEnd_3167175 : Nat := 180698121322639016327437

theorem tailTrace_3167175 : CollatzResearch.WordTrace tailWord_3167175 prefixEnd_3167175 180698121322639016327437 := by
  unfold tailWord_3167175
  simp only [CollatzResearch.WordTrace]
  refine ⟨115516362300873360271030979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77010908200582240180687319 115516362300873360271030979)
  ·
    refine ⟨173274543451310040406546469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115516362300873360271030979 173274543451310040406546469)
    ·
      refine ⟨32488976897120632576227463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173274543451310040406546469 32488976897120632576227463)
      ·
        refine ⟨48733465345680948864341195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32488976897120632576227463 48733465345680948864341195)
        ·
          refine ⟨73100198018521423296511793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48733465345680948864341195 73100198018521423296511793)
          ·
            refine ⟨54825148513891067472383845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73100198018521423296511793 54825148513891067472383845)
            ·
              refine ⟨10279715346354575151071971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54825148513891067472383845 10279715346354575151071971)
              ·
                refine ⟨15419573019531862726607957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279715346354575151071971 15419573019531862726607957)
                ·
                  refine ⟨180698121322639016327437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15419573019531862726607957 180698121322639016327437)
                  ·
                    rfl

theorem cell23_3167175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 8].length) (baseStart_3167175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167175 prefixEnd_3167175 := by exact prefixLift 3167175
  have htrace : WordTrace (prefixWord ++ tailWord_3167175) baseStart_3167175 baseEnd_3167175 := by
    simpa [prefixWord, tailWord_3167175, baseEnd_3167175] using wordTrace_append hprefix tailTrace_3167175
  have hstable : (prefixWord ++ tailWord_3167175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167175).length < 2 ^ (prefixWord ++ tailWord_3167175).sum := by decide
  have hdescent : baseEnd_3167175 < baseStart_3167175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167179 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 3, 4]
def baseStart_3167179 : Nat := 118140960795 + 3167179 * 2 ^ 59
def prefixEnd_3167179 : Nat := 4983230072969 + 3 ^ 40 * 3167179 * 2
def baseEnd_3167179 : Nat := 542095048608789710432305

theorem tailTrace_3167179 : CollatzResearch.WordTrace tailWord_3167179 prefixEnd_3167179 542095048608789710432305 := by
  unfold tailWord_3167179
  simp only [CollatzResearch.WordTrace]
  refine ⟨115516508192858868954176591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77011005461905912636117727 115516508192858868954176591)
  ·
    refine ⟨173274762289288303431264887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115516508192858868954176591 173274762289288303431264887)
    ·
      refine ⟨259912143433932455146897331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173274762289288303431264887 259912143433932455146897331)
      ·
        refine ⟨389868215150898682720345997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259912143433932455146897331 389868215150898682720345997)
        ·
          refine ⟨146200580681587006020129749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389868215150898682720345997 146200580681587006020129749)
          ·
            refine ⟨3426576109724695453596791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 146200580681587006020129749 3426576109724695453596791)
            ·
              refine ⟨5139864164587043180395187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426576109724695453596791 5139864164587043180395187)
              ·
                refine ⟨7709796246880564770592781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5139864164587043180395187 7709796246880564770592781)
                ·
                  refine ⟨2891173592580211788972293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7709796246880564770592781 2891173592580211788972293)
                  ·
                    refine ⟨542095048608789710432305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891173592580211788972293 542095048608789710432305)
                    ·
                      rfl

theorem cell23_3167179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 4].length) (baseStart_3167179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167179 prefixEnd_3167179 := by exact prefixLift 3167179
  have htrace : WordTrace (prefixWord ++ tailWord_3167179) baseStart_3167179 baseEnd_3167179 := by
    simpa [prefixWord, tailWord_3167179, baseEnd_3167179] using wordTrace_append hprefix tailTrace_3167179
  have hstable : (prefixWord ++ tailWord_3167179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167179).length < 2 ^ (prefixWord ++ tailWord_3167179).sum := by decide
  have hdescent : baseEnd_3167179 < baseStart_3167179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167181 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3167181 : Nat := 118140960795 + 3167181 * 2 ^ 59
def prefixEnd_3167181 : Nat := 4983230072969 + 3 ^ 40 * 3167181 * 2
def baseEnd_3167181 : Nat := 1626286172787678123471907

theorem tailTrace_3167181 : CollatzResearch.WordTrace tailWord_3167181 prefixEnd_3167181 1626286172787678123471907 := by
  unfold tailWord_3167181
  simp only [CollatzResearch.WordTrace]
  refine ⟨115516581138851623295749397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77011054092567748863832931 115516581138851623295749397)
  ·
    refine ⟨5414839740883669841988253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115516581138851623295749397 5414839740883669841988253)
    ·
      refine ⟨2030564902831376190745595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5414839740883669841988253 2030564902831376190745595)
      ·
        refine ⟨3045847354247064286118393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030564902831376190745595 3045847354247064286118393)
        ·
          refine ⟨2284385515685298214588795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045847354247064286118393 2284385515685298214588795)
          ·
            refine ⟨3426578273527947321883193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284385515685298214588795 3426578273527947321883193)
            ·
              refine ⟨2569933705145960491412395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426578273527947321883193 2569933705145960491412395)
              ·
                refine ⟨3854900557718940737118593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569933705145960491412395 3854900557718940737118593)
                ·
                  refine ⟨2891175418289205552838945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854900557718940737118593 2891175418289205552838945)
                  ·
                    refine ⟨2168381563716904164629209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2891175418289205552838945 2168381563716904164629209)
                    ·
                      refine ⟨1626286172787678123471907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168381563716904164629209 1626286172787678123471907)
                      ·
                        rfl

theorem cell23_3167181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3167181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167181 prefixEnd_3167181 := by exact prefixLift 3167181
  have htrace : WordTrace (prefixWord ++ tailWord_3167181) baseStart_3167181 baseEnd_3167181 := by
    simpa [prefixWord, tailWord_3167181, baseEnd_3167181] using wordTrace_append hprefix tailTrace_3167181
  have hstable : (prefixWord ++ tailWord_3167181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167181).length < 2 ^ (prefixWord ++ tailWord_3167181).sum := by decide
  have hdescent : baseEnd_3167181 < baseStart_3167181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167192 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 6]
def baseStart_3167192 : Nat := 118140960795 + 3167192 * 2 ^ 59
def prefixEnd_3167192 : Nat := 4983230072969 + 3 ^ 40 * 3167192 * 2
def baseEnd_3167192 : Nat := 180699091230541953381595

theorem tailTrace_3167192 : CollatzResearch.WordTrace tailWord_3167192 prefixEnd_3167192 180699091230541953381595 := by
  unfold tailWord_3167192
  simp only [CollatzResearch.WordTrace]
  refine ⟨57758491170905886087199915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77011321561207848116266553 57758491170905886087199915)
  ·
    refine ⟨86637736756358829130799873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57758491170905886087199915 86637736756358829130799873)
    ·
      refine ⟨64978302567269121848099905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86637736756358829130799873 64978302567269121848099905)
      ·
        refine ⟨48733726925451841386074929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64978302567269121848099905 48733726925451841386074929)
        ·
          refine ⟨36550295194088881039556197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48733726925451841386074929 36550295194088881039556197)
          ·
            refine ⟨6853180348891665194916787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36550295194088881039556197 6853180348891665194916787)
            ·
              refine ⟨10279770523337497792375181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853180348891665194916787 10279770523337497792375181)
              ·
                refine ⟨3854913946251561672140693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10279770523337497792375181 3854913946251561672140693)
                ·
                  refine ⟨180699091230541953381595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3854913946251561672140693 180699091230541953381595)
                  ·
                    rfl

theorem cell23_3167192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 6].length) (baseStart_3167192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167192 prefixEnd_3167192 := by exact prefixLift 3167192
  have htrace : WordTrace (prefixWord ++ tailWord_3167192) baseStart_3167192 baseEnd_3167192 := by
    simpa [prefixWord, tailWord_3167192, baseEnd_3167192] using wordTrace_append hprefix tailTrace_3167192
  have hstable : (prefixWord ++ tailWord_3167192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167192).length < 2 ^ (prefixWord ++ tailWord_3167192).sum := by decide
  have hdescent : baseEnd_3167192 < baseStart_3167192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167286 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3167286 : Nat := 118140960795 + 3167286 * 2 ^ 59
def prefixEnd_3167286 : Nat := 4983230072969 + 3 ^ 40 * 3167286 * 2
def baseEnd_3167286 : Nat := 542113362752133404219641

theorem tailTrace_3167286 : CollatzResearch.WordTrace tailWord_3167286 prefixEnd_3167286 542113362752133404219641 := by
  unfold tailWord_3167286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220025675216951639270107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77013607202314150818881141 7220025675216951639270107)
  ·
    refine ⟨10830038512825427458905161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7220025675216951639270107 10830038512825427458905161)
    ·
      refine ⟨8122528884619070594178871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10830038512825427458905161 8122528884619070594178871)
      ·
        refine ⟨12183793326928605891268307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8122528884619070594178871 12183793326928605891268307)
        ·
          refine ⟨18275689990392908836902461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183793326928605891268307 18275689990392908836902461)
          ·
            refine ⟨6853383746397340813838423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18275689990392908836902461 6853383746397340813838423)
            ·
              refine ⟨10280075619596011220757635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853383746397340813838423 10280075619596011220757635)
              ·
                refine ⟨15420113429394016831136453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280075619596011220757635 15420113429394016831136453)
                ·
                  refine ⟨2891271268011378155838085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15420113429394016831136453 2891271268011378155838085)
                  ·
                    refine ⟨542113362752133404219641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891271268011378155838085 542113362752133404219641)
                    ·
                      rfl

theorem cell23_3167286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3167286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167286 prefixEnd_3167286 := by exact prefixLift 3167286
  have htrace : WordTrace (prefixWord ++ tailWord_3167286) baseStart_3167286 baseEnd_3167286 := by
    simpa [prefixWord, tailWord_3167286, baseEnd_3167286] using wordTrace_append hprefix tailTrace_3167286
  have hstable : (prefixWord ++ tailWord_3167286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167286).length < 2 ^ (prefixWord ++ tailWord_3167286).sum := by decide
  have hdescent : baseEnd_3167286 < baseStart_3167286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167293 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_3167293 : Nat := 118140960795 + 3167293 * 2 ^ 59
def prefixEnd_3167293 : Nat := 4983230072969 + 3 ^ 40 * 3167293 * 2
def baseEnd_3167293 : Nat := 1626343682620981685271391

theorem tailTrace_3167293 : CollatzResearch.WordTrace tailWord_3167293 prefixEnd_3167293 1626343682620981685271391 := by
  unfold tailWord_3167293
  simp only [CollatzResearch.WordTrace]
  refine ⟨115520666114445866423826533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77013777409630577615884355 115520666114445866423826533)
  ·
    refine ⟨21660124896458599954467475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115520666114445866423826533 21660124896458599954467475)
    ·
      refine ⟨32490187344687899931701213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21660124896458599954467475 32490187344687899931701213)
      ·
        refine ⟨12183820254257962474387955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32490187344687899931701213 12183820254257962474387955)
        ·
          refine ⟨18275730381386943711581933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183820254257962474387955 18275730381386943711581933)
          ·
            refine ⟨6853398893020103891843225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18275730381386943711581933 6853398893020103891843225)
            ·
              refine ⟨5140049169765077918882419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6853398893020103891843225 5140049169765077918882419)
              ·
                refine ⟨7710073754647616878323629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140049169765077918882419 7710073754647616878323629)
                ·
                  refine ⟨2891277657992856329371361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7710073754647616878323629 2891277657992856329371361)
                  ·
                    refine ⟨2168458243494642247028521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2891277657992856329371361 2168458243494642247028521)
                    ·
                      refine ⟨1626343682620981685271391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168458243494642247028521 1626343682620981685271391)
                      ·
                        rfl

theorem cell23_3167293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_3167293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167293 prefixEnd_3167293 := by exact prefixLift 3167293
  have htrace : WordTrace (prefixWord ++ tailWord_3167293) baseStart_3167293 baseEnd_3167293 := by
    simpa [prefixWord, tailWord_3167293, baseEnd_3167293] using wordTrace_append hprefix tailTrace_3167293
  have hstable : (prefixWord ++ tailWord_3167293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167293).length < 2 ^ (prefixWord ++ tailWord_3167293).sum := by decide
  have hdescent : baseEnd_3167293 < baseStart_3167293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167332 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_3167332 : Nat := 118140960795 + 3167332 * 2 ^ 59
def prefixEnd_3167332 : Nat := 4983230072969 + 3 ^ 40 * 3167332 * 2
def baseEnd_3167332 : Nat := 1626363708366507032683711

theorem tailTrace_3167332 : CollatzResearch.WordTrace tailWord_3167332 prefixEnd_3167332 1626363708366507032683711 := by
  unfold tailWord_3167332
  simp only [CollatzResearch.WordTrace]
  refine ⟨57761044280652288042248125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77014725707536384056330833 57761044280652288042248125)
  ·
    refine ⟨21660391605244608015843047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57761044280652288042248125 21660391605244608015843047)
    ·
      refine ⟨32490587407866912023764571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21660391605244608015843047 32490587407866912023764571)
      ·
        refine ⟨48735881111800368035646857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32490587407866912023764571 48735881111800368035646857)
        ·
          refine ⟨36551910833850276026735143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48735881111800368035646857 36551910833850276026735143)
          ·
            refine ⟨54827866250775414040102715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36551910833850276026735143 54827866250775414040102715)
            ·
              refine ⟨82241799376163121060154073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54827866250775414040102715 82241799376163121060154073)
              ·
                refine ⟨61681349532122340795115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82241799376163121060154073 61681349532122340795115555)
                ·
                  refine ⟨92522024298183511192673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61681349532122340795115555 92522024298183511192673333)
                  ·
                    refine ⟨8673939777954704174313125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92522024298183511192673333 8673939777954704174313125)
                    ·
                      refine ⟨1626363708366507032683711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8673939777954704174313125 1626363708366507032683711)
                      ·
                        rfl

theorem cell23_3167332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3167332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167332 prefixEnd_3167332 := by exact prefixLift 3167332
  have htrace : WordTrace (prefixWord ++ tailWord_3167332) baseStart_3167332 baseEnd_3167332 := by
    simpa [prefixWord, tailWord_3167332, baseEnd_3167332] using wordTrace_append hprefix tailTrace_3167332
  have hstable : (prefixWord ++ tailWord_3167332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167332).length < 2 ^ (prefixWord ++ tailWord_3167332).sum := by decide
  have hdescent : baseEnd_3167332 < baseStart_3167332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167372 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 7]
def baseStart_3167372 : Nat := 118140960795 + 3167372 * 2 ^ 59
def prefixEnd_3167372 : Nat := 4983230072969 + 3 ^ 40 * 3167372 * 2
def baseEnd_3167372 : Nat := 180709360843631875131503

theorem tailTrace_3167372 : CollatzResearch.WordTrace tailWord_3167372 prefixEnd_3167372 180709360843631875131503 := by
  unfold tailWord_3167372
  simp only [CollatzResearch.WordTrace]
  refine ⟨57761773740579831457976185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77015698320773108610634913 57761773740579831457976185)
  ·
    refine ⟨43321330305434873593482139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57761773740579831457976185 43321330305434873593482139)
    ·
      refine ⟨64981995458152310390223209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43321330305434873593482139 64981995458152310390223209)
      ·
        refine ⟨48736496593614232792667407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64981995458152310390223209 48736496593614232792667407)
        ·
          refine ⟨73104744890421349189001111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48736496593614232792667407 73104744890421349189001111)
          ·
            refine ⟨109657117335632023783501667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73104744890421349189001111 109657117335632023783501667)
            ·
              refine ⟨164485676003448035675252501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109657117335632023783501667 164485676003448035675252501)
              ·
                refine ⟨7710266062661626672277461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164485676003448035675252501 7710266062661626672277461)
                ·
                  refine ⟨180709360843631875131503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7710266062661626672277461 180709360843631875131503)
                  ·
                    rfl

theorem cell23_3167372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_3167372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167372 prefixEnd_3167372 := by exact prefixLift 3167372
  have htrace : WordTrace (prefixWord ++ tailWord_3167372) baseStart_3167372 baseEnd_3167372 := by
    simpa [prefixWord, tailWord_3167372, baseEnd_3167372] using wordTrace_append hprefix tailTrace_3167372
  have hstable : (prefixWord ++ tailWord_3167372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167372).length < 2 ^ (prefixWord ++ tailWord_3167372).sum := by decide
  have hdescent : baseEnd_3167372 < baseStart_3167372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167439 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_3167439 : Nat := 118140960795 + 3167439 * 2 ^ 59
def prefixEnd_3167439 : Nat := 4983230072969 + 3 ^ 40 * 3167439 * 2
def baseEnd_3167439 : Nat := 1626418650796538114045719

theorem tailTrace_3167439 : CollatzResearch.WordTrace tailWord_3167439 prefixEnd_3167439 1626418650796538114045719 := by
  unfold tailWord_3167439
  simp only [CollatzResearch.WordTrace]
  refine ⟨115525991171916933358641371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77017327447944622239094247 115525991171916933358641371)
  ·
    refine ⟨173288986757875400037962057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115525991171916933358641371 173288986757875400037962057)
    ·
      refine ⟨129966740068406550028471543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173288986757875400037962057 129966740068406550028471543)
      ·
        refine ⟨194950110102609825042707315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129966740068406550028471543 194950110102609825042707315)
        ·
          refine ⟨292425165153914737564060973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194950110102609825042707315 292425165153914737564060973)
          ·
            refine ⟨109659436932718026586522865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292425165153914737564060973 109659436932718026586522865)
            ·
              refine ⟨82244577699538519939892149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109659436932718026586522865 82244577699538519939892149)
              ·
                refine ⟨7710429159331736244364889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82244577699538519939892149 7710429159331736244364889)
                ·
                  refine ⟨5782821869498802183273667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710429159331736244364889 5782821869498802183273667)
                  ·
                    refine ⟨8674232804248203274910501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5782821869498802183273667 8674232804248203274910501)
                    ·
                      refine ⟨1626418650796538114045719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8674232804248203274910501 1626418650796538114045719)
                      ·
                        rfl

theorem cell23_3167439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_3167439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167439 prefixEnd_3167439 := by exact prefixLift 3167439
  have htrace : WordTrace (prefixWord ++ tailWord_3167439) baseStart_3167439 baseEnd_3167439 := by
    simpa [prefixWord, tailWord_3167439, baseEnd_3167439] using wordTrace_append hprefix tailTrace_3167439
  have hstable : (prefixWord ++ tailWord_3167439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167439).length < 2 ^ (prefixWord ++ tailWord_3167439).sum := by decide
  have hdescent : baseEnd_3167439 < baseStart_3167439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167449 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 7, 4]
def baseStart_3167449 : Nat := 118140960795 + 3167449 * 2 ^ 59
def prefixEnd_3167449 : Nat := 4983230072969 + 3 ^ 40 * 3167449 * 2
def baseEnd_3167449 : Nat := 542141261867694358306891

theorem tailTrace_3167449 : CollatzResearch.WordTrace tailWord_3167449 prefixEnd_3167449 542141261867694358306891 := by
  unfold tailWord_3167449
  simp only [CollatzResearch.WordTrace]
  refine ⟨115526355901880705066505401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77017570601253803377670267 115526355901880705066505401)
  ·
    refine ⟨86644766926410528799879051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115526355901880705066505401 86644766926410528799879051)
    ·
      refine ⟨129967150389615793199818577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86644766926410528799879051 129967150389615793199818577)
      ·
        refine ⟨97475362792211844899863933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129967150389615793199818577 97475362792211844899863933)
        ·
          refine ⟨36553261047079441837448975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97475362792211844899863933 36553261047079441837448975)
          ·
            refine ⟨54829891570619162756173463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36553261047079441837448975 54829891570619162756173463)
            ·
              refine ⟨82244837355928744134260195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54829891570619162756173463 82244837355928744134260195)
              ·
                refine ⟨123367256033893116201390293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82244837355928744134260195 123367256033893116201390293)
                ·
                  refine ⟨2891420063294369910970085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123367256033893116201390293 2891420063294369910970085)
                  ·
                    refine ⟨542141261867694358306891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891420063294369910970085 542141261867694358306891)
                    ·
                      rfl

theorem cell23_3167449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_3167449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167449 prefixEnd_3167449 := by exact prefixLift 3167449
  have htrace : WordTrace (prefixWord ++ tailWord_3167449) baseStart_3167449 baseEnd_3167449 := by
    simpa [prefixWord, tailWord_3167449, baseEnd_3167449] using wordTrace_append hprefix tailTrace_3167449
  have hstable : (prefixWord ++ tailWord_3167449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167449).length < 2 ^ (prefixWord ++ tailWord_3167449).sum := by decide
  have hdescent : baseEnd_3167449 < baseStart_3167449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167456 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 2, 4, 2]
def baseStart_3167456 : Nat := 118140960795 + 3167456 * 2 ^ 59
def prefixEnd_3167456 : Nat := 4983230072969 + 3 ^ 40 * 3167456 * 2
def baseEnd_3167456 : Nat := 1626427379967664547533141

theorem tailTrace_3167456 : CollatzResearch.WordTrace tailWord_3167456 prefixEnd_3167456 1626427379967664547533141 := by
  unfold tailWord_3167456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57763305606427672631005111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77017740808570230174673481 57763305606427672631005111)
  ·
    refine ⟨86644958409641508946507667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57763305606427672631005111 86644958409641508946507667)
    ·
      refine ⟨129967437614462263419761501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86644958409641508946507667 129967437614462263419761501)
      ·
        refine ⟨48737789105423348782410563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129967437614462263419761501 48737789105423348782410563)
        ·
          refine ⟨73106683658135023173615845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48737789105423348782410563 73106683658135023173615845)
          ·
            refine ⟨13707503185900316845052971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73106683658135023173615845 13707503185900316845052971)
            ·
              refine ⟨20561254778850475267579457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13707503185900316845052971 20561254778850475267579457)
              ·
                refine ⟨15420941084137856450684593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20561254778850475267579457 15420941084137856450684593)
                ·
                  refine ⟨11565705813103392338013445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15420941084137856450684593 11565705813103392338013445)
                  ·
                    refine ⟨2168569839956886063377521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11565705813103392338013445 2168569839956886063377521)
                    ·
                      refine ⟨1626427379967664547533141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168569839956886063377521 1626427379967664547533141)
                      ·
                        rfl

theorem cell23_3167456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_3167456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167456 prefixEnd_3167456 := by exact prefixLift 3167456
  have htrace : WordTrace (prefixWord ++ tailWord_3167456) baseStart_3167456 baseEnd_3167456 := by
    simpa [prefixWord, tailWord_3167456, baseEnd_3167456] using wordTrace_append hprefix tailTrace_3167456
  have hstable : (prefixWord ++ tailWord_3167456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167456).length < 2 ^ (prefixWord ++ tailWord_3167456).sum := by decide
  have hdescent : baseEnd_3167456 < baseStart_3167456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167466 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3167466 : Nat := 118140960795 + 3167466 * 2 ^ 59
def prefixEnd_3167466 : Nat := 4983230072969 + 3 ^ 40 * 3167466 * 2
def baseEnd_3167466 : Nat := 542144171591403169469365

theorem tailTrace_3167466 : CollatzResearch.WordTrace tailWord_3167466 prefixEnd_3167466 542144171591403169469365 := by
  unfold tailWord_3167466
  simp only [CollatzResearch.WordTrace]
  refine ⟨28881743985704779242468563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77017983961879411313249501 28881743985704779242468563)
  ·
    refine ⟨43322615978557168863702845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28881743985704779242468563 43322615978557168863702845)
    ·
      refine ⟨16245980991958938323888567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43322615978557168863702845 16245980991958938323888567)
      ·
        refine ⟨24368971487938407485832851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16245980991958938323888567 24368971487938407485832851)
        ·
          refine ⟨36553457231907611228749277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24368971487938407485832851 36553457231907611228749277)
          ·
            refine ⟨13707546461965354210780979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36553457231907611228749277 13707546461965354210780979)
            ·
              refine ⟨20561319692948031316171469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13707546461965354210780979 20561319692948031316171469)
              ·
                refine ⟨7710494884855511743564301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20561319692948031316171469 7710494884855511743564301)
                ·
                  refine ⟨2891435581820816903836613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7710494884855511743564301 2891435581820816903836613)
                  ·
                    refine ⟨542144171591403169469365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891435581820816903836613 542144171591403169469365)
                    ·
                      rfl

theorem cell23_3167466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3167466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167466 prefixEnd_3167466 := by exact prefixLift 3167466
  have htrace : WordTrace (prefixWord ++ tailWord_3167466) baseStart_3167466 baseEnd_3167466 := by
    simpa [prefixWord, tailWord_3167466, baseEnd_3167466] using wordTrace_append hprefix tailTrace_3167466
  have hstable : (prefixWord ++ tailWord_3167466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167466).length < 2 ^ (prefixWord ++ tailWord_3167466).sum := by decide
  have hdescent : baseEnd_3167466 < baseStart_3167466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167500 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_3167500 : Nat := 118140960795 + 3167500 * 2 ^ 59
def prefixEnd_3167500 : Nat := 4983230072969 + 3 ^ 40 * 3167500 * 2
def baseEnd_3167500 : Nat := 542149991038820791794313

theorem tailTrace_3167500 : CollatzResearch.WordTrace tailWord_3167500 prefixEnd_3167500 542149991038820791794313 := by
  unfold tailWord_3167500
  simp only [CollatzResearch.WordTrace]
  refine ⟨57764108012347970388305977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77018810683130627184407969 57764108012347970388305977)
  ·
    refine ⟨43323081009260977791229483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57764108012347970388305977 43323081009260977791229483)
    ·
      refine ⟨64984621513891466686844225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43323081009260977791229483 64984621513891466686844225)
      ·
        refine ⟨48738466135418600015133169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64984621513891466686844225 48738466135418600015133169)
        ·
          refine ⟨36553849601563950011349877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48738466135418600015133169 36553849601563950011349877)
          ·
            refine ⟨3426923400146620313564051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36553849601563950011349877 3426923400146620313564051)
            ·
              refine ⟨5140385100219930470346077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426923400146620313564051 5140385100219930470346077)
              ·
                refine ⟨1927644412582473926379779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5140385100219930470346077 1927644412582473926379779)
                ·
                  refine ⟨2891466618873710889569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927644412582473926379779 2891466618873710889569669)
                  ·
                    refine ⟨542149991038820791794313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891466618873710889569669 542149991038820791794313)
                    ·
                      rfl

theorem cell23_3167500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_3167500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167500 prefixEnd_3167500 := by exact prefixLift 3167500
  have htrace : WordTrace (prefixWord ++ tailWord_3167500) baseStart_3167500 baseEnd_3167500 := by
    simpa [prefixWord, tailWord_3167500, baseEnd_3167500] using wordTrace_append hprefix tailTrace_3167500
  have hstable : (prefixWord ++ tailWord_3167500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167500).length < 2 ^ (prefixWord ++ tailWord_3167500).sum := by decide
  have hdescent : baseEnd_3167500 < baseStart_3167500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167509 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_3167509 : Nat := 118140960795 + 3167509 * 2 ^ 59
def prefixEnd_3167509 : Nat := 4983230072969 + 3 ^ 40 * 3167509 * 2
def baseEnd_3167509 : Nat := 542151531480784280056799

theorem tailTrace_3167509 : CollatzResearch.WordTrace tailWord_3167509 prefixEnd_3167509 542151531480784280056799 := by
  unfold tailWord_3167509
  simp only [CollatzResearch.WordTrace]
  refine ⟨115528544281663335313689581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77019029521108890209126387 115528544281663335313689581)
  ·
    refine ⟨43323204105623750742633593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115528544281663335313689581 43323204105623750742633593)
    ·
      refine ⟨32492403079217813056975195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43323204105623750742633593 32492403079217813056975195)
      ·
        refine ⟨48738604618826719585462793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32492403079217813056975195 48738604618826719585462793)
        ·
          refine ⟨36553953464120039689097095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48738604618826719585462793 36553953464120039689097095)
          ·
            refine ⟨54830930196180059533645643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36553953464120039689097095 54830930196180059533645643)
            ·
              refine ⟨82246395294270089300468465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54830930196180059533645643 82246395294270089300468465)
              ·
                refine ⟨61684796470702566975351349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82246395294270089300468465 61684796470702566975351349)
                ·
                  refine ⟨5782949669128365653939189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61684796470702566975351349 5782949669128365653939189)
                  ·
                    refine ⟨542151531480784280056799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5782949669128365653939189 542151531480784280056799)
                    ·
                      rfl

theorem cell23_3167509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_3167509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167509 prefixEnd_3167509 := by exact prefixLift 3167509
  have htrace : WordTrace (prefixWord ++ tailWord_3167509) baseStart_3167509 baseEnd_3167509 := by
    simpa [prefixWord, tailWord_3167509, baseEnd_3167509] using wordTrace_append hprefix tailTrace_3167509
  have hstable : (prefixWord ++ tailWord_3167509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167509).length < 2 ^ (prefixWord ++ tailWord_3167509).sum := by decide
  have hdescent : baseEnd_3167509 < baseStart_3167509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167517 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_3167517 : Nat := 118140960795 + 3167517 * 2 ^ 59
def prefixEnd_3167517 : Nat := 4983230072969 + 3 ^ 40 * 3167517 * 2
def baseEnd_3167517 : Nat := 542152900762529602956787

theorem tailTrace_3167517 : CollatzResearch.WordTrace tailWord_3167517 prefixEnd_3167517 542152900762529602956787 := by
  unfold tailWord_3167517
  simp only [CollatzResearch.WordTrace]
  refine ⟨115528836065634352679980805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77019224043756235119987203 115528836065634352679980805)
  ·
    refine ⟨21661656762306441127496401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115528836065634352679980805 21661656762306441127496401)
    ·
      refine ⟨16246242571729830845622301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21661656762306441127496401 16246242571729830845622301)
      ·
        refine ⟨6092340964398686567108363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16246242571729830845622301 6092340964398686567108363)
        ·
          refine ⟨9138511446598029850662545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092340964398686567108363 9138511446598029850662545)
          ·
            refine ⟨6853883584948522387996909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9138511446598029850662545 6853883584948522387996909)
            ·
              refine ⟨2570206344355695895498841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6853883584948522387996909 2570206344355695895498841)
              ·
                refine ⟨1927654758266771921624131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570206344355695895498841 1927654758266771921624131)
                ·
                  refine ⟨2891482137400157882436197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927654758266771921624131 2891482137400157882436197)
                  ·
                    refine ⟨542152900762529602956787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891482137400157882436197 542152900762529602956787)
                    ·
                      rfl

theorem cell23_3167517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_3167517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167517 prefixEnd_3167517 := by exact prefixLift 3167517
  have htrace : WordTrace (prefixWord ++ tailWord_3167517) baseStart_3167517 baseEnd_3167517 := by
    simpa [prefixWord, tailWord_3167517, baseEnd_3167517] using wordTrace_append hprefix tailTrace_3167517
  have hstable : (prefixWord ++ tailWord_3167517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167517).length < 2 ^ (prefixWord ++ tailWord_3167517).sum := by decide
  have hdescent : baseEnd_3167517 < baseStart_3167517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167523 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 3]
def baseStart_3167523 : Nat := 118140960795 + 3167523 * 2 ^ 59
def prefixEnd_3167523 : Nat := 4983230072969 + 3 ^ 40 * 3167523 * 2
def baseEnd_3167523 : Nat := 1626461783171515785395333

theorem tailTrace_3167523 : CollatzResearch.WordTrace tailWord_3167523 prefixEnd_3167523 1626461783171515785395333 := by
  unfold tailWord_3167523
  simp only [CollatzResearch.WordTrace]
  refine ⟨115529054903612615704699223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77019369935741743803132815 115529054903612615704699223)
  ·
    refine ⟨173293582355418923557048835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115529054903612615704699223 173293582355418923557048835)
    ·
      refine ⟨259940373533128385335573253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173293582355418923557048835 259940373533128385335573253)
      ·
        refine ⟨48738820037461572250419985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259940373533128385335573253 48738820037461572250419985)
        ·
          refine ⟨36554115028096179187814989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48738820037461572250419985 36554115028096179187814989)
          ·
            refine ⟨13707793135536067195430621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36554115028096179187814989 13707793135536067195430621)
            ·
              refine ⟨5140422425826025198286483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13707793135536067195430621 5140422425826025198286483)
              ·
                refine ⟨7710633638739037797429725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140422425826025198286483 7710633638739037797429725)
                ·
                  refine ⟨2891487614527139174036147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7710633638739037797429725 2891487614527139174036147)
                  ·
                    refine ⟨4337231421790708761054221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2891487614527139174036147 4337231421790708761054221)
                    ·
                      refine ⟨1626461783171515785395333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337231421790708761054221 1626461783171515785395333)
                      ·
                        rfl

theorem cell23_3167523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_3167523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167523 prefixEnd_3167523 := by exact prefixLift 3167523
  have htrace : WordTrace (prefixWord ++ tailWord_3167523) baseStart_3167523 baseEnd_3167523 := by
    simpa [prefixWord, tailWord_3167523, baseEnd_3167523] using wordTrace_append hprefix tailTrace_3167523
  have hstable : (prefixWord ++ tailWord_3167523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167523).length < 2 ^ (prefixWord ++ tailWord_3167523).sum := by decide
  have hdescent : baseEnd_3167523 < baseStart_3167523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167530 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_3167530 : Nat := 118140960795 + 3167530 * 2 ^ 59
def prefixEnd_3167530 : Nat := 4983230072969 + 3 ^ 40 * 3167530 * 2
def baseEnd_3167530 : Nat := 180718375281788584223089

theorem tailTrace_3167530 : CollatzResearch.WordTrace tailWord_3167530 prefixEnd_3167530 180718375281788584223089 := by
  unfold tailWord_3167530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882327553646813975051011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77019540143058170600136029 28882327553646813975051011)
  ·
    refine ⟨43323491330470220962576517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28882327553646813975051011 43323491330470220962576517)
    ·
      refine ⟨8123154624463166430483097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43323491330470220962576517 8123154624463166430483097)
      ·
        refine ⟨6092365968347374822862323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8123154624463166430483097 6092365968347374822862323)
        ·
          refine ⟨9138548952521062234293485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092365968347374822862323 9138548952521062234293485)
          ·
            refine ⟨3426955857195398337860057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9138548952521062234293485 3426955857195398337860057)
            ·
              refine ⟨2570216892896548753395043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426955857195398337860057 2570216892896548753395043)
              ·
                refine ⟨3855325339344823130092565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570216892896548753395043 3855325339344823130092565)
                ·
                  refine ⟨180718375281788584223089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3855325339344823130092565 180718375281788584223089)
                  ·
                    rfl

theorem cell23_3167530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_3167530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167530 prefixEnd_3167530 := by exact prefixLift 3167530
  have htrace : WordTrace (prefixWord ++ tailWord_3167530) baseStart_3167530 baseEnd_3167530 := by
    simpa [prefixWord, tailWord_3167530, baseEnd_3167530] using wordTrace_append hprefix tailTrace_3167530
  have hstable : (prefixWord ++ tailWord_3167530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167530).length < 2 ^ (prefixWord ++ tailWord_3167530).sum := by decide
  have hdescent : baseEnd_3167530 < baseStart_3167530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167546 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_3167546 : Nat := 118140960795 + 3167546 * 2 ^ 59
def prefixEnd_3167546 : Nat := 4983230072969 + 3 ^ 40 * 3167546 * 2
def baseEnd_3167546 : Nat := 1626473593226569195407727

theorem tailTrace_3167546 : CollatzResearch.WordTrace tailWord_3167546 prefixEnd_3167546 1626473593226569195407727 := by
  unfold tailWord_3167546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882473445632322658196623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77019929188352860421857661 28882473445632322658196623)
  ·
    refine ⟨43323710168448483987294935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28882473445632322658196623 43323710168448483987294935)
    ·
      refine ⟨64985565252672725980942403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43323710168448483987294935 64985565252672725980942403)
      ·
        refine ⟨97478347879009088971413605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64985565252672725980942403 97478347879009088971413605)
        ·
          refine ⟨18277190227314204182140051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97478347879009088971413605 18277190227314204182140051)
          ·
            refine ⟨27415785340971306273210077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18277190227314204182140051 27415785340971306273210077)
            ·
              refine ⟨10280919502864239852453779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27415785340971306273210077 10280919502864239852453779)
              ·
                refine ⟨15421379254296359778680669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280919502864239852453779 15421379254296359778680669)
                ·
                  refine ⟨5783017220361134917005251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15421379254296359778680669 5783017220361134917005251)
                  ·
                    refine ⟨8674525830541702375507877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5783017220361134917005251 8674525830541702375507877)
                    ·
                      refine ⟨1626473593226569195407727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8674525830541702375507877 1626473593226569195407727)
                      ·
                        rfl

theorem cell23_3167546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_3167546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167546 prefixEnd_3167546 := by exact prefixLift 3167546
  have htrace : WordTrace (prefixWord ++ tailWord_3167546) baseStart_3167546 baseEnd_3167546 := by
    simpa [prefixWord, tailWord_3167546, baseEnd_3167546] using wordTrace_append hprefix tailTrace_3167546
  have hstable : (prefixWord ++ tailWord_3167546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167546).length < 2 ^ (prefixWord ++ tailWord_3167546).sum := by decide
  have hdescent : baseEnd_3167546 < baseStart_3167546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167550 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_3167550 : Nat := 118140960795 + 3167550 * 2 ^ 59
def prefixEnd_3167550 : Nat := 4983230072969 + 3 ^ 40 * 3167550 * 2
def baseEnd_3167550 : Nat := 1626475647149187179757709

theorem tailTrace_3167550 : CollatzResearch.WordTrace tailWord_3167550 prefixEnd_3167550 1626475647149187179757709 := by
  unfold tailWord_3167550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441254959314349914491513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77020026449676532877288069 14441254959314349914491513)
  ·
    refine ⟨10830941219485762435868635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14441254959314349914491513 10830941219485762435868635)
    ·
      refine ⟨16246411829228643653802953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10830941219485762435868635 16246411829228643653802953)
      ·
        refine ⟨12184808871921482740352215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16246411829228643653802953 12184808871921482740352215)
        ·
          refine ⟨18277213307882224110528323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12184808871921482740352215 18277213307882224110528323)
          ·
            refine ⟨27415819961823336165792485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18277213307882224110528323 27415819961823336165792485)
            ·
              refine ⟨5140466242841875531086091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27415819961823336165792485 5140466242841875531086091)
              ·
                refine ⟨7710699364262813296629137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140466242841875531086091 7710699364262813296629137)
                ·
                  refine ⟨5783024523197109972471853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710699364262813296629137 5783024523197109972471853)
                  ·
                    refine ⟨2168634196198916239676945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5783024523197109972471853 2168634196198916239676945)
                    ·
                      refine ⟨1626475647149187179757709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168634196198916239676945 1626475647149187179757709)
                      ·
                        rfl

theorem cell23_3167550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_3167550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167550 prefixEnd_3167550 := by exact prefixLift 3167550
  have htrace : WordTrace (prefixWord ++ tailWord_3167550) baseStart_3167550 baseEnd_3167550 := by
    simpa [prefixWord, tailWord_3167550, baseEnd_3167550] using wordTrace_append hprefix tailTrace_3167550
  have hstable : (prefixWord ++ tailWord_3167550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167550).length < 2 ^ (prefixWord ++ tailWord_3167550).sum := by decide
  have hdescent : baseEnd_3167550 < baseStart_3167550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167573 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_3167573 : Nat := 118140960795 + 3167573 * 2 ^ 59
def prefixEnd_3167573 : Nat := 4983230072969 + 3 ^ 40 * 3167573 * 2
def baseEnd_3167573 : Nat := 542162485734746863256701

theorem tailTrace_3167573 : CollatzResearch.WordTrace tailWord_3167573 prefixEnd_3167573 542162485734746863256701 := by
  unfold tailWord_3167573
  simp only [CollatzResearch.WordTrace]
  refine ⟨115530878553431474244019373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77020585702287649496012915 115530878553431474244019373)
  ·
    refine ⟨43324079457536802841507265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115530878553431474244019373 43324079457536802841507265)
    ·
      refine ⟨32493059593152602131130449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43324079457536802841507265 32493059593152602131130449)
      ·
        refine ⟨24369794694864451598347837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32493059593152602131130449 24369794694864451598347837)
        ·
          refine ⟨9138673010574169349380439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24369794694864451598347837 9138673010574169349380439)
          ·
            refine ⟨13708009515861254024070659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9138673010574169349380439 13708009515861254024070659)
            ·
              refine ⟨20562014273791881036105989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13708009515861254024070659 20562014273791881036105989)
              ·
                refine ⟨3855377676335977694269873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20562014273791881036105989 3855377676335977694269873)
                ·
                  refine ⟨2891533257251983270702405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3855377676335977694269873 2891533257251983270702405)
                  ·
                    refine ⟨542162485734746863256701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891533257251983270702405 542162485734746863256701)
                    ·
                      rfl

theorem cell23_3167573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_3167573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167573 prefixEnd_3167573 := by exact prefixLift 3167573
  have htrace : WordTrace (prefixWord ++ tailWord_3167573) baseStart_3167573 baseEnd_3167573 := by
    simpa [prefixWord, tailWord_3167573, baseEnd_3167573] using wordTrace_append hprefix tailTrace_3167573
  have hstable : (prefixWord ++ tailWord_3167573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167573).length < 2 ^ (prefixWord ++ tailWord_3167573).sum := by decide
  have hdescent : baseEnd_3167573 < baseStart_3167573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167599 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 2, 7]
def baseStart_3167599 : Nat := 118140960795 + 3167599 * 2 ^ 59
def prefixEnd_3167599 : Nat := 4983230072969 + 3 ^ 40 * 3167599 * 2
def baseEnd_3167599 : Nat := 542166935900419162681661

theorem tailTrace_3167599 : CollatzResearch.WordTrace tailWord_3167599 prefixEnd_3167599 542166935900419162681661 := by
  unfold tailWord_3167599
  simp only [CollatzResearch.WordTrace]
  refine ⟨115531826851337280684465851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77021217900891520456310567 115531826851337280684465851)
  ·
    refine ⟨173297740277005921026698777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115531826851337280684465851 173297740277005921026698777)
    ·
      refine ⟨129973305207754440770024083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173297740277005921026698777 129973305207754440770024083)
      ·
        refine ⟨194959957811631661155036125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129973305207754440770024083 194959957811631661155036125)
        ·
          refine ⟨73109984179361872933138547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194959957811631661155036125 73109984179361872933138547)
          ·
            refine ⟨109664976269042809399707821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73109984179361872933138547 109664976269042809399707821)
            ·
              refine ⟨41124366100891053524890433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109664976269042809399707821 41124366100891053524890433)
              ·
                refine ⟨30843274575668290143667825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41124366100891053524890433 30843274575668290143667825)
                ·
                  refine ⟨23132455931751217607750869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30843274575668290143667825 23132455931751217607750869)
                  ·
                    refine ⟨542166935900419162681661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23132455931751217607750869 542166935900419162681661)
                    ·
                      rfl

theorem cell23_3167599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_3167599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167599 prefixEnd_3167599 := by exact prefixLift 3167599
  have htrace : WordTrace (prefixWord ++ tailWord_3167599) baseStart_3167599 baseEnd_3167599 := by
    simpa [prefixWord, tailWord_3167599, baseEnd_3167599] using wordTrace_append hprefix tailTrace_3167599
  have hstable : (prefixWord ++ tailWord_3167599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167599).length < 2 ^ (prefixWord ++ tailWord_3167599).sum := by decide
  have hdescent : baseEnd_3167599 < baseStart_3167599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167613 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_3167613 : Nat := 118140960795 + 3167613 * 2 ^ 59
def prefixEnd_3167613 : Nat := 4983230072969 + 3 ^ 40 * 3167613 * 2
def baseEnd_3167613 : Nat := 1626507996430420433269919

theorem tailTrace_3167613 : CollatzResearch.WordTrace tailWord_3167613 prefixEnd_3167613 1626507996430420433269919 := by
  unfold tailWord_3167613
  simp only [CollatzResearch.WordTrace]
  refine ⟨115532337473286561075475493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77021558315524374050316995 115532337473286561075475493)
  ·
    refine ⟨21662313276241230201651655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115532337473286561075475493 21662313276241230201651655)
    ·
      refine ⟨32493469914361845302477483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21662313276241230201651655 32493469914361845302477483)
      ·
        refine ⟨48740204871542767953716225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32493469914361845302477483 48740204871542767953716225)
        ·
          refine ⟨36555153653657075965287169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48740204871542767953716225 36555153653657075965287169)
          ·
            refine ⟨27416365240242806973965377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36555153653657075965287169 27416365240242806973965377)
            ·
              refine ⟨20562273930182105230474033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27416365240242806973965377 20562273930182105230474033)
              ·
                refine ⟨15421705447636578922855525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20562273930182105230474033 15421705447636578922855525)
                ·
                  refine ⟨2891569771431858548035411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15421705447636578922855525 2891569771431858548035411)
                  ·
                    refine ⟨4337354657147787822053117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2891569771431858548035411 4337354657147787822053117)
                    ·
                      refine ⟨1626507996430420433269919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337354657147787822053117 1626507996430420433269919)
                      ·
                        rfl

theorem cell23_3167613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_3167613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167613 prefixEnd_3167613 := by exact prefixLift 3167613
  have htrace : WordTrace (prefixWord ++ tailWord_3167613) baseStart_3167613 baseEnd_3167613 := by
    simpa [prefixWord, tailWord_3167613, baseEnd_3167613] using wordTrace_append hprefix tailTrace_3167613
  have hstable : (prefixWord ++ tailWord_3167613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167613).length < 2 ^ (prefixWord ++ tailWord_3167613).sum := by decide
  have hdescent : baseEnd_3167613 < baseStart_3167613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167647 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 2, 1, 3]
def baseStart_3167647 : Nat := 118140960795 + 3167647 * 2 ^ 59
def prefixEnd_3167647 : Nat := 4983230072969 + 3 ^ 40 * 3167647 * 2
def baseEnd_3167647 : Nat := 1626525454772673300244763

theorem tailTrace_3167647 : CollatzResearch.WordTrace tailWord_3167647 prefixEnd_3167647 1626525454772673300244763 := by
  unfold tailWord_3167647
  simp only [CollatzResearch.WordTrace]
  refine ⟨115533577555163384882213195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77022385036775589921475463 115533577555163384882213195)
  ·
    refine ⟨173300366332745077323319793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115533577555163384882213195 173300366332745077323319793)
    ·
      refine ⟨129975274749558807992489845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173300366332745077323319793 129975274749558807992489845)
      ·
        refine ⟨12185182007771138249295923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129975274749558807992489845 12185182007771138249295923)
        ·
          refine ⟨18277773011656707373943885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12185182007771138249295923 18277773011656707373943885)
          ·
            refine ⟨6854164879371265265228957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18277773011656707373943885 6854164879371265265228957)
            ·
              refine ⟨2570311829764224474460859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6854164879371265265228957 2570311829764224474460859)
              ·
                refine ⟨3855467744646336711691289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570311829764224474460859 3855467744646336711691289)
                ·
                  refine ⟨2891600808484752533768467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3855467744646336711691289 2891600808484752533768467)
                  ·
                    refine ⟨4337401212727128800652701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2891600808484752533768467 4337401212727128800652701)
                    ·
                      refine ⟨1626525454772673300244763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337401212727128800652701 1626525454772673300244763)
                      ·
                        rfl

theorem cell23_3167647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_3167647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167647 prefixEnd_3167647 := by exact prefixLift 3167647
  have htrace : WordTrace (prefixWord ++ tailWord_3167647) baseStart_3167647 baseEnd_3167647 := by
    simpa [prefixWord, tailWord_3167647, baseEnd_3167647] using wordTrace_append hprefix tailTrace_3167647
  have hstable : (prefixWord ++ tailWord_3167647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167647).length < 2 ^ (prefixWord ++ tailWord_3167647).sum := by decide
  have hdescent : baseEnd_3167647 < baseStart_3167647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167653 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 1, 4, 2]
def baseStart_3167653 : Nat := 118140960795 + 3167653 * 2 ^ 59
def prefixEnd_3167653 : Nat := 4983230072969 + 3 ^ 40 * 3167653 * 2
def baseEnd_3167653 : Nat := 1626528535656600276769735

theorem tailTrace_3167653 : CollatzResearch.WordTrace tailWord_3167653 prefixEnd_3167653 1626528535656600276769735 := by
  unfold tailWord_3167653
  simp only [CollatzResearch.WordTrace]
  refine ⟨115533796393141647906931613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77022530928761098604621075 115533796393141647906931613)
  ·
    refine ⟨43325173647428117965099355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115533796393141647906931613 43325173647428117965099355)
    ·
      refine ⟨64987760471142176947649033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43325173647428117965099355 64987760471142176947649033)
      ·
        refine ⟨48740820353356632710736775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64987760471142176947649033 48740820353356632710736775)
        ·
          refine ⟨73111230530034949066105163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48740820353356632710736775 73111230530034949066105163)
          ·
            refine ⟨109666845795052423599157745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73111230530034949066105163 109666845795052423599157745)
            ·
              refine ⟨82250134346289317699368309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109666845795052423599157745 82250134346289317699368309)
              ·
                refine ⟨7710950094964623534315779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82250134346289317699368309 7710950094964623534315779)
                ·
                  refine ⟨11566425142446935301473669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7710950094964623534315779 11566425142446935301473669)
                  ·
                    refine ⟨2168704714208800369026313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11566425142446935301473669 2168704714208800369026313)
                    ·
                      refine ⟨1626528535656600276769735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168704714208800369026313 1626528535656600276769735)
                      ·
                        rfl

theorem cell23_3167653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_3167653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167653 prefixEnd_3167653 := by exact prefixLift 3167653
  have htrace : WordTrace (prefixWord ++ tailWord_3167653) baseStart_3167653 baseEnd_3167653 := by
    simpa [prefixWord, tailWord_3167653, baseEnd_3167653] using wordTrace_append hprefix tailTrace_3167653
  have hstable : (prefixWord ++ tailWord_3167653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167653).length < 2 ^ (prefixWord ++ tailWord_3167653).sum := by decide
  have hdescent : baseEnd_3167653 < baseStart_3167653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167659 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 13]
def baseStart_3167659 : Nat := 118140960795 + 3167659 * 2 ^ 59
def prefixEnd_3167659 : Nat := 4983230072969 + 3 ^ 40 * 3167659 * 2
def baseEnd_3167659 : Nat := 180725735171169694810523

theorem tailTrace_3167659 : CollatzResearch.WordTrace tailWord_3167659 prefixEnd_3167659 180725735171169694810523 := by
  unfold tailWord_3167659
  simp only [CollatzResearch.WordTrace]
  refine ⟨115534015231119910931650031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77022676820746607287766687 115534015231119910931650031)
  ·
    refine ⟨173301022846679866397475047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115534015231119910931650031 173301022846679866397475047)
    ·
      refine ⟨259951534270019799596212571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173301022846679866397475047 259951534270019799596212571)
      ·
        refine ⟨389927301405029699394318857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259951534270019799596212571 389927301405029699394318857)
        ·
          refine ⟨292445476053772274545739143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389927301405029699394318857 292445476053772274545739143)
          ·
            refine ⟨438668214080658411818608715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292445476053772274545739143 438668214080658411818608715)
            ·
              refine ⟨658002321120987617727913073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438668214080658411818608715 658002321120987617727913073)
              ·
                refine ⟨493501740840740713295934805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658002321120987617727913073 493501740840740713295934805)
                ·
                  refine ⟨180725735171169694810523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 493501740840740713295934805 180725735171169694810523)
                  ·
                    rfl

theorem cell23_3167659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 13].length) (baseStart_3167659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167659 prefixEnd_3167659 := by exact prefixLift 3167659
  have htrace : WordTrace (prefixWord ++ tailWord_3167659) baseStart_3167659 baseEnd_3167659 := by
    simpa [prefixWord, tailWord_3167659, baseEnd_3167659] using wordTrace_append hprefix tailTrace_3167659
  have hstable : (prefixWord ++ tailWord_3167659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167659).length < 2 ^ (prefixWord ++ tailWord_3167659).sum := by decide
  have hdescent : baseEnd_3167659 < baseStart_3167659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167666 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3167666 : Nat := 118140960795 + 3167666 * 2 ^ 59
def prefixEnd_3167666 : Nat := 4983230072969 + 3 ^ 40 * 3167666 * 2
def baseEnd_3167666 : Nat := 1626535210905108725907175

theorem tailTrace_3167666 : CollatzResearch.WordTrace tailWord_3167666 prefixEnd_3167666 1626535210905108725907175 := by
  unfold tailWord_3167666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28883567635523637781788713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77022847028063034084769901 28883567635523637781788713)
  ·
    refine ⟨21662675726642728336341535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28883567635523637781788713 21662675726642728336341535)
    ·
      refine ⟨32494013589964092504512303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21662675726642728336341535 32494013589964092504512303)
      ·
        refine ⟨48741020384946138756768455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32494013589964092504512303 48741020384946138756768455)
        ·
          refine ⟨73111530577419208135152683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48741020384946138756768455 73111530577419208135152683)
          ·
            refine ⟨109667295866128812202729025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73111530577419208135152683 109667295866128812202729025)
            ·
              refine ⟨82250471899596609152046769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109667295866128812202729025 82250471899596609152046769)
              ·
                refine ⟨61687853924697456864035077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82250471899596609152046769 61687853924697456864035077)
                ·
                  refine ⟨11566472610880773162006577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61687853924697456864035077 11566472610880773162006577)
                  ·
                    refine ⟨8674854458160579871504933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11566472610880773162006577 8674854458160579871504933)
                    ·
                      refine ⟨1626535210905108725907175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8674854458160579871504933 1626535210905108725907175)
                      ·
                        rfl

theorem cell23_3167666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3167666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167666 prefixEnd_3167666 := by exact prefixLift 3167666
  have htrace : WordTrace (prefixWord ++ tailWord_3167666) baseStart_3167666 baseEnd_3167666 := by
    simpa [prefixWord, tailWord_3167666, baseEnd_3167666] using wordTrace_append hprefix tailTrace_3167666
  have hstable : (prefixWord ++ tailWord_3167666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167666).length < 2 ^ (prefixWord ++ tailWord_3167666).sum := by decide
  have hdescent : baseEnd_3167666 < baseStart_3167666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167673 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3167673 : Nat := 118140960795 + 3167673 * 2 ^ 59
def prefixEnd_3167673 : Nat := 4983230072969 + 3 ^ 40 * 3167673 * 2
def baseEnd_3167673 : Nat := 1626538805269690198519643

theorem tailTrace_3167673 : CollatzResearch.WordTrace tailWord_3167673 prefixEnd_3167673 1626538805269690198519643 := by
  unfold tailWord_3167673
  simp only [CollatzResearch.WordTrace]
  refine ⟨115534525853069191322659673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77023017235379460881773115 115534525853069191322659673)
  ·
    refine ⟨86650894389801893491994755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115534525853069191322659673 86650894389801893491994755)
    ·
      refine ⟨129976341584702840237992133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86650894389801893491994755 129976341584702840237992133)
      ·
        refine ⟨24370564047131782544623525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129976341584702840237992133 24370564047131782544623525)
        ·
          refine ⟨4569480758837209227116911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24370564047131782544623525 4569480758837209227116911)
          ·
            refine ⟨6854221138255813840675367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569480758837209227116911 6854221138255813840675367)
            ·
              refine ⟨10281331707383720761013051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854221138255813840675367 10281331707383720761013051)
              ·
                refine ⟨15421997561075581141519577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10281331707383720761013051 15421997561075581141519577)
                ·
                  refine ⟨11566498170806685856139683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15421997561075581141519577 11566498170806685856139683)
                  ·
                    refine ⟨17349747256210028784209525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11566498170806685856139683 17349747256210028784209525)
                    ·
                      refine ⟨1626538805269690198519643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17349747256210028784209525 1626538805269690198519643)
                      ·
                        rfl

theorem cell23_3167673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3167673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167673 prefixEnd_3167673 := by exact prefixLift 3167673
  have htrace : WordTrace (prefixWord ++ tailWord_3167673) baseStart_3167673 baseEnd_3167673 := by
    simpa [prefixWord, tailWord_3167673, baseEnd_3167673] using wordTrace_append hprefix tailTrace_3167673
  have hstable : (prefixWord ++ tailWord_3167673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167673).length < 2 ^ (prefixWord ++ tailWord_3167673).sum := by decide
  have hdescent : baseEnd_3167673 < baseStart_3167673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167682 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3167682 : Nat := 118140960795 + 3167682 * 2 ^ 59
def prefixEnd_3167682 : Nat := 4983230072969 + 3 ^ 40 * 3167682 * 2
def baseEnd_3167682 : Nat := 1626543426595580663307103

theorem tailTrace_3167682 : CollatzResearch.WordTrace tailWord_3167682 prefixEnd_3167682 1626543426595580663307103 := by
  unfold tailWord_3167682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28883713527509146464934325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77023236073357723906491533 28883713527509146464934325)
  ·
    refine ⟨2707848143203982481087593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28883713527509146464934325 2707848143203982481087593)
    ·
      refine ⟨2030886107402986860815695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2707848143203982481087593 2030886107402986860815695)
      ·
        refine ⟨3046329161104480291223543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030886107402986860815695 3046329161104480291223543)
        ·
          refine ⟨4569493741656720436835315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046329161104480291223543 4569493741656720436835315)
          ·
            refine ⟨6854240612485080655252973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569493741656720436835315 6854240612485080655252973)
            ·
              refine ⟨2570340229681905245719865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6854240612485080655252973 2570340229681905245719865)
              ·
                refine ⟨1927755172261428934289899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570340229681905245719865 1927755172261428934289899)
                ·
                  refine ⟨2891632758392143401434849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927755172261428934289899 2891632758392143401434849)
                  ·
                    refine ⟨2168724568794107551076137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2891632758392143401434849 2168724568794107551076137)
                    ·
                      refine ⟨1626543426595580663307103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168724568794107551076137 1626543426595580663307103)
                      ·
                        rfl

theorem cell23_3167682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3167682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167682 prefixEnd_3167682 := by exact prefixLift 3167682
  have htrace : WordTrace (prefixWord ++ tailWord_3167682) baseStart_3167682 baseEnd_3167682 := by
    simpa [prefixWord, tailWord_3167682, baseEnd_3167682] using wordTrace_append hprefix tailTrace_3167682
  have hstable : (prefixWord ++ tailWord_3167682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167682).length < 2 ^ (prefixWord ++ tailWord_3167682).sum := by decide
  have hdescent : baseEnd_3167682 < baseStart_3167682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167753 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 3, 4]
def baseStart_3167753 : Nat := 118140960795 + 3167753 * 2 ^ 59
def prefixEnd_3167753 : Nat := 4983230072969 + 3 ^ 40 * 3167753 * 2
def baseEnd_3167753 : Nat := 542193294574016628506425

theorem tailTrace_3167753 : CollatzResearch.WordTrace tailWord_3167753 prefixEnd_3167753 542193294574016628506425 := by
  unfold tailWord_3167753
  simp only [CollatzResearch.WordTrace]
  refine ⟨115537443692779364985571913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77024962461852909990381275 115537443692779364985571913)
  ·
    refine ⟨86653082769584523739178935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115537443692779364985571913 86653082769584523739178935)
    ·
      refine ⟨129979624154376785608768403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86653082769584523739178935 129979624154376785608768403)
      ·
        refine ⟨194969436231565178413152605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129979624154376785608768403 194969436231565178413152605)
        ·
          refine ⟨73113538586836941904932227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194969436231565178413152605 73113538586836941904932227)
          ·
            refine ⟨109670307880255412857398341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73113538586836941904932227 109670307880255412857398341)
            ·
              refine ⟨20563182727547889910762189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109670307880255412857398341 20563182727547889910762189)
              ·
                refine ⟨7711193522830458716535821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20563182727547889910762189 7711193522830458716535821)
                ·
                  refine ⟨2891697571061422018700933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7711193522830458716535821 2891697571061422018700933)
                  ·
                    refine ⟨542193294574016628506425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891697571061422018700933 542193294574016628506425)
                    ·
                      rfl

theorem cell23_3167753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_3167753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167753 prefixEnd_3167753 := by exact prefixLift 3167753
  have htrace : WordTrace (prefixWord ++ tailWord_3167753) baseStart_3167753 baseEnd_3167753 := by
    simpa [prefixWord, tailWord_3167753, baseEnd_3167753] using wordTrace_append hprefix tailTrace_3167753
  have hstable : (prefixWord ++ tailWord_3167753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167753).length < 2 ^ (prefixWord ++ tailWord_3167753).sum := by decide
  have hdescent : baseEnd_3167753 < baseStart_3167753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167774 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3167774 : Nat := 118140960795 + 3167774 * 2 ^ 59
def prefixEnd_3167774 : Nat := 4983230072969 + 3 ^ 40 * 3167774 * 2
def baseEnd_3167774 : Nat := 542196888938598101118893

theorem tailTrace_3167774 : CollatzResearch.WordTrace tailWord_3167774 prefixEnd_3167774 542196888938598101118893 := by
  unfold tailWord_3167774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14442276203212910696510797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77025473083802190381390917 14442276203212910696510797)
  ·
    refine ⟨5415853576204841511191549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14442276203212910696510797 5415853576204841511191549)
    ·
      refine ⟨2030945091076815566696831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5415853576204841511191549 2030945091076815566696831)
      ·
        refine ⟨3046417636615223350045247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030945091076815566696831 3046417636615223350045247)
        ·
          refine ⟨4569626454922835025067871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046417636615223350045247 4569626454922835025067871)
          ·
            refine ⟨6854439682384252537601807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569626454922835025067871 6854439682384252537601807)
            ·
              refine ⟨10281659523576378806402711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854439682384252537601807 10281659523576378806402711)
              ·
                refine ⟨15422489285364568209604067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10281659523576378806402711 15422489285364568209604067)
                ·
                  refine ⟨23133733928046852314406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15422489285364568209604067 23133733928046852314406101)
                  ·
                    refine ⟨542196888938598101118893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23133733928046852314406101 542196888938598101118893)
                    ·
                      rfl

theorem cell23_3167774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3167774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167774 prefixEnd_3167774 := by exact prefixLift 3167774
  have htrace : WordTrace (prefixWord ++ tailWord_3167774) baseStart_3167774 baseEnd_3167774 := by
    simpa [prefixWord, tailWord_3167774, baseEnd_3167774] using wordTrace_append hprefix tailTrace_3167774
  have hstable : (prefixWord ++ tailWord_3167774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167774).length < 2 ^ (prefixWord ++ tailWord_3167774).sum := by decide
  have hdescent : baseEnd_3167774 < baseStart_3167774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167800 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 6]
def baseStart_3167800 : Nat := 118140960795 + 3167800 * 2 ^ 59
def prefixEnd_3167800 : Nat := 4983230072969 + 3 ^ 40 * 3167800 * 2
def baseEnd_3167800 : Nat := 180733779701423466847951

theorem tailTrace_3167800 : CollatzResearch.WordTrace tailWord_3167800 prefixEnd_3167800 180733779701423466847951 := by
  unfold tailWord_3167800
  simp only [CollatzResearch.WordTrace]
  refine ⟨57769578961804546006266427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77026105282406061341688569 57769578961804546006266427)
  ·
    refine ⟨86654368442706819009399641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57769578961804546006266427 86654368442706819009399641)
    ·
      refine ⟨64990776332030114257049731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86654368442706819009399641 64990776332030114257049731)
      ·
        refine ⟨97486164498045171385574597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64990776332030114257049731 97486164498045171385574597)
        ·
          refine ⟨18278655843383469634795237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97486164498045171385574597 18278655843383469634795237)
          ·
            refine ⟨3427247970634400556524107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18278655843383469634795237 3427247970634400556524107)
            ·
              refine ⟨5140871955951600834786161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427247970634400556524107 5140871955951600834786161)
              ·
                refine ⟨3855653966963700626089621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5140871955951600834786161 3855653966963700626089621)
                ·
                  refine ⟨180733779701423466847951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3855653966963700626089621 180733779701423466847951)
                  ·
                    rfl

theorem cell23_3167800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 6].length) (baseStart_3167800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167800 prefixEnd_3167800 := by exact prefixLift 3167800
  have htrace : WordTrace (prefixWord ++ tailWord_3167800) baseStart_3167800 baseEnd_3167800 := by
    simpa [prefixWord, tailWord_3167800, baseEnd_3167800] using wordTrace_append hprefix tailTrace_3167800
  have hstable : (prefixWord ++ tailWord_3167800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167800).length < 2 ^ (prefixWord ++ tailWord_3167800).sum := by decide
  have hdescent : baseEnd_3167800 < baseStart_3167800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167820 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3167820 : Nat := 118140960795 + 3167820 * 2 ^ 59
def prefixEnd_3167820 : Nat := 4983230072969 + 3 ^ 40 * 3167820 * 2
def baseEnd_3167820 : Nat := 1626614286925901123381467

theorem tailTrace_3167820 : CollatzResearch.WordTrace tailWord_3167820 prefixEnd_3167820 1626614286925901123381467 := by
  unfold tailWord_3167820
  simp only [CollatzResearch.WordTrace]
  refine ⟨57769943691768317714130457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77026591589024423618840609 57769943691768317714130457)
  ·
    refine ⟨43327457768826238285597843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57769943691768317714130457 43327457768826238285597843)
    ·
      refine ⟨64991186653239357428396765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43327457768826238285597843 64991186653239357428396765)
      ·
        refine ⟨24371694994964759035648787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64991186653239357428396765 24371694994964759035648787)
        ·
          refine ⟨36557542492447138553473181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24371694994964759035648787 36557542492447138553473181)
          ·
            refine ⟨13709078434667676957552443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36557542492447138553473181 13709078434667676957552443)
            ·
              refine ⟨20563617652001515436328665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709078434667676957552443 20563617652001515436328665)
              ·
                refine ⟨15422713239001136577246499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20563617652001515436328665 15422713239001136577246499)
                ·
                  refine ⟨23134069858501704865869749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15422713239001136577246499 23134069858501704865869749)
                  ·
                    refine ⟨2168819049234534831175289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23134069858501704865869749 2168819049234534831175289)
                    ·
                      refine ⟨1626614286925901123381467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168819049234534831175289 1626614286925901123381467)
                      ·
                        rfl

theorem cell23_3167820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3167820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167820 prefixEnd_3167820 := by exact prefixLift 3167820
  have htrace : WordTrace (prefixWord ++ tailWord_3167820) baseStart_3167820 baseEnd_3167820 := by
    simpa [prefixWord, tailWord_3167820, baseEnd_3167820] using wordTrace_append hprefix tailTrace_3167820
  have hstable : (prefixWord ++ tailWord_3167820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167820).length < 2 ^ (prefixWord ++ tailWord_3167820).sum := by decide
  have hdescent : baseEnd_3167820 < baseStart_3167820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167833 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_3167833 : Nat := 118140960795 + 3167833 * 2 ^ 59
def prefixEnd_3167833 : Nat := 4983230072969 + 3 ^ 40 * 3167833 * 2
def baseEnd_3167833 : Nat := 1626620962174409572518907

theorem tailTrace_3167833 : CollatzResearch.WordTrace tailWord_3167833 prefixEnd_3167833 1626620962174409572518907 := by
  unfold tailWord_3167833
  simp only [CollatzResearch.WordTrace]
  refine ⟨115540361532489538648484153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77026907688326359098989435 115540361532489538648484153)
  ·
    refine ⟨86655271149367153986363115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115540361532489538648484153 86655271149367153986363115)
    ·
      refine ⟨129982906724050730979544673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86655271149367153986363115 129982906724050730979544673)
      ·
        refine ⟨97487180043038048234658505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129982906724050730979544673 97487180043038048234658505)
        ·
          refine ⟨73115385032278536175993879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97487180043038048234658505 73115385032278536175993879)
          ·
            refine ⟨109673077548417804263990819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73115385032278536175993879 109673077548417804263990819)
            ·
              refine ⟨164509616322626706395986229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109673077548417804263990819 164509616322626706395986229)
              ·
                refine ⟨15422776530246253724623709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164509616322626706395986229 15422776530246253724623709)
                ·
                  refine ⟨5783541198842345146733891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15422776530246253724623709 5783541198842345146733891)
                  ·
                    refine ⟨8675311798263517720100837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5783541198842345146733891 8675311798263517720100837)
                    ·
                      refine ⟨1626620962174409572518907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8675311798263517720100837 1626620962174409572518907)
                      ·
                        rfl

theorem cell23_3167833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_3167833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167833 prefixEnd_3167833 := by exact prefixLift 3167833
  have htrace : WordTrace (prefixWord ++ tailWord_3167833) baseStart_3167833 baseEnd_3167833 := by
    simpa [prefixWord, tailWord_3167833, baseEnd_3167833] using wordTrace_append hprefix tailTrace_3167833
  have hstable : (prefixWord ++ tailWord_3167833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167833).length < 2 ^ (prefixWord ++ tailWord_3167833).sum := by decide
  have hdescent : baseEnd_3167833 < baseStart_3167833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167844 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_3167844 : Nat := 118140960795 + 3167844 * 2 ^ 59
def prefixEnd_3167844 : Nat := 4983230072969 + 3 ^ 40 * 3167844 * 2
def baseEnd_3167844 : Nat := 1626626610461609029481357

theorem tailTrace_3167844 : CollatzResearch.WordTrace tailWord_3167844 prefixEnd_3167844 1626626610461609029481357 := by
  unfold tailWord_3167844
  simp only [CollatzResearch.WordTrace]
  refine ⟨57770381367724843763567293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77027175156966458351423057 57770381367724843763567293)
  ·
    refine ⟨21663893012896816411337735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57770381367724843763567293 21663893012896816411337735)
    ·
      refine ⟨32495839519345224617006603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21663893012896816411337735 32495839519345224617006603)
      ·
        refine ⟨48743759279017836925509905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32495839519345224617006603 48743759279017836925509905)
        ·
          refine ⟨36557819459263377694132429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48743759279017836925509905 36557819459263377694132429)
          ·
            refine ⟨13709182297223766635299661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36557819459263377694132429 13709182297223766635299661)
            ·
              refine ⟨5140943361458912488237373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13709182297223766635299661 5140943361458912488237373)
              ·
                refine ⟨1927853760547092183089015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5140943361458912488237373 1927853760547092183089015)
                ·
                  refine ⟨2891780640820638274633523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927853760547092183089015 2891780640820638274633523)
                  ·
                    refine ⟨4337670961230957411950285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2891780640820638274633523 4337670961230957411950285)
                    ·
                      refine ⟨1626626610461609029481357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337670961230957411950285 1626626610461609029481357)
                      ·
                        rfl

theorem cell23_3167844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_3167844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167844 prefixEnd_3167844 := by exact prefixLift 3167844
  have htrace : WordTrace (prefixWord ++ tailWord_3167844) baseStart_3167844 baseEnd_3167844 := by
    simpa [prefixWord, tailWord_3167844, baseEnd_3167844] using wordTrace_append hprefix tailTrace_3167844
  have hstable : (prefixWord ++ tailWord_3167844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167844).length < 2 ^ (prefixWord ++ tailWord_3167844).sum := by decide
  have hdescent : baseEnd_3167844 < baseStart_3167844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167854 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_3167854 : Nat := 118140960795 + 3167854 * 2 ^ 59
def prefixEnd_3167854 : Nat := 4983230072969 + 3 ^ 40 * 3167854 * 2
def baseEnd_3167854 : Nat := 1626631745268153990356311

theorem tailTrace_3167854 : CollatzResearch.WordTrace tailWord_3167854 prefixEnd_3167854 1626631745268153990356311 := by
  unfold tailWord_3167854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14442640933176682404374827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77027418310275639489999077 14442640933176682404374827)
  ·
    refine ⟨21663961399765023606562241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14442640933176682404374827 21663961399765023606562241)
    ·
      refine ⟨16247971049823767704921681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21663961399765023606562241 16247971049823767704921681)
      ·
        refine ⟨12185978287367825778691261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16247971049823767704921681 12185978287367825778691261)
        ·
          refine ⟨4569741857762934667009223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12185978287367825778691261 4569741857762934667009223)
          ·
            refine ⟨6854612786644402000513835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569741857762934667009223 6854612786644402000513835)
            ·
              refine ⟨10281919179966603000770753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854612786644402000513835 10281919179966603000770753)
              ·
                refine ⟨7711439384974952250578065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10281919179966603000770753 7711439384974952250578065)
                ·
                  refine ⟨5783579538731214187933549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711439384974952250578065 5783579538731214187933549)
                  ·
                    refine ⟨2168842327024205320475081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5783579538731214187933549 2168842327024205320475081)
                    ·
                      refine ⟨1626631745268153990356311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168842327024205320475081 1626631745268153990356311)
                      ·
                        rfl

theorem cell23_3167854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_3167854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167854 prefixEnd_3167854 := by exact prefixLift 3167854
  have htrace : WordTrace (prefixWord ++ tailWord_3167854) baseStart_3167854 baseEnd_3167854 := by
    simpa [prefixWord, tailWord_3167854, baseEnd_3167854] using wordTrace_append hprefix tailTrace_3167854
  have hstable : (prefixWord ++ tailWord_3167854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167854).length < 2 ^ (prefixWord ++ tailWord_3167854).sum := by decide
  have hdescent : baseEnd_3167854 < baseStart_3167854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167873 : List Nat := [1, 2, 4, 2, 1, 2, 1, 10]
def baseStart_3167873 : Nat := 118140960795 + 3167873 * 2 ^ 59
def prefixEnd_3167873 : Nat := 4983230072969 + 3 ^ 40 * 3167873 * 2
def baseEnd_3167873 : Nat := 60245981533355163556249

theorem tailTrace_3167873 : CollatzResearch.WordTrace tailWord_3167873 prefixEnd_3167873 60245981533355163556249 := by
  unfold tailWord_3167873
  simp only [CollatzResearch.WordTrace]
  refine ⟨115541820452344625479940273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77027880301563083653293515 115541820452344625479940273)
  ·
    refine ⟨86656365339258469109955205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115541820452344625479940273 86656365339258469109955205)
    ·
      refine ⟨16248068501110962958116601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86656365339258469109955205 16248068501110962958116601)
      ·
        refine ⟨12186051375833222218587451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16248068501110962958116601 12186051375833222218587451)
        ·
          refine ⟨18279077063749833327881177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12186051375833222218587451 18279077063749833327881177)
          ·
            refine ⟨13709307797812374995910883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18279077063749833327881177 13709307797812374995910883)
            ·
              refine ⟨20563961696718562493866325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709307797812374995910883 20563961696718562493866325)
              ·
                refine ⟨60245981533355163556249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20563961696718562493866325 60245981533355163556249)
                ·
                  rfl

theorem cell23_3167873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 10].length) (baseStart_3167873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167873 prefixEnd_3167873 := by exact prefixLift 3167873
  have htrace : WordTrace (prefixWord ++ tailWord_3167873) baseStart_3167873 baseEnd_3167873 := by
    simpa [prefixWord, tailWord_3167873, baseEnd_3167873] using wordTrace_append hprefix tailTrace_3167873
  have hstable : (prefixWord ++ tailWord_3167873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167873).length < 2 ^ (prefixWord ++ tailWord_3167873).sum := by decide
  have hdescent : baseEnd_3167873 < baseStart_3167873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167904 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 1, 2, 3]
def baseStart_3167904 : Nat := 118140960795 + 3167904 * 2 ^ 59
def prefixEnd_3167904 : Nat := 4983230072969 + 3 ^ 40 * 3167904 * 2
def baseEnd_3167904 : Nat := 1626657419300878794731081

theorem tailTrace_3167904 : CollatzResearch.WordTrace tailWord_3167904 prefixEnd_3167904 1626657419300878794731081 := by
  unfold tailWord_3167904
  simp only [CollatzResearch.WordTrace]
  refine ⟨57771475557616158887159383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77028634076821545182879177 57771475557616158887159383)
  ·
    refine ⟨86657213336424238330739075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57771475557616158887159383 86657213336424238330739075)
    ·
      refine ⟨129985820004636357496108613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86657213336424238330739075 129985820004636357496108613)
      ·
        refine ⟨24372341250869317030520365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129985820004636357496108613 24372341250869317030520365)
        ·
          refine ⟨9139627969075993886445137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24372341250869317030520365 9139627969075993886445137)
          ·
            refine ⟨6854720976806995414833853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9139627969075993886445137 6854720976806995414833853)
            ·
              refine ⟨2570520366302623280562695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6854720976806995414833853 2570520366302623280562695)
              ·
                refine ⟨3855780549453934920844043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570520366302623280562695 3855780549453934920844043)
                ·
                  refine ⟨5783670824180902381266065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855780549453934920844043 5783670824180902381266065)
                  ·
                    refine ⟨4337753118135676785949549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5783670824180902381266065 4337753118135676785949549)
                    ·
                      refine ⟨1626657419300878794731081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337753118135676785949549 1626657419300878794731081)
                      ·
                        rfl

theorem cell23_3167904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_3167904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167904 prefixEnd_3167904 := by exact prefixLift 3167904
  have htrace : WordTrace (prefixWord ++ tailWord_3167904) baseStart_3167904 baseEnd_3167904 := by
    simpa [prefixWord, tailWord_3167904, baseEnd_3167904] using wordTrace_append hprefix tailTrace_3167904
  have hstable : (prefixWord ++ tailWord_3167904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167904).length < 2 ^ (prefixWord ++ tailWord_3167904).sum := by decide
  have hdescent : baseEnd_3167904 < baseStart_3167904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167912 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3167912 : Nat := 118140960795 + 3167912 * 2 ^ 59
def prefixEnd_3167912 : Nat := 4983230072969 + 3 ^ 40 * 3167912 * 2
def baseEnd_3167912 : Nat := 1626661527146114763431045

theorem tailTrace_3167912 : CollatzResearch.WordTrace tailWord_3167912 prefixEnd_3167912 1626661527146114763431045 := by
  unfold tailWord_3167912
  simp only [CollatzResearch.WordTrace]
  refine ⟨57771621449601667570304995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77028828599468890093739993 57771621449601667570304995)
  ·
    refine ⟨86657432174402501355457493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57771621449601667570304995 86657432174402501355457493)
    ·
      refine ⟨2031033566587558625518535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 86657432174402501355457493 2031033566587558625518535)
      ·
        refine ⟨3046550349881337938277803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031033566587558625518535 3046550349881337938277803)
        ·
          refine ⟨4569825524822006907416705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046550349881337938277803 4569825524822006907416705)
          ·
            refine ⟨3427369143616505180562529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4569825524822006907416705 3427369143616505180562529)
            ·
              refine ⟨2570526857712378885421897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427369143616505180562529 2570526857712378885421897)
              ·
                refine ⟨1927895143284284164066423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570526857712378885421897 1927895143284284164066423)
                ·
                  refine ⟨2891842714926426246099635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927895143284284164066423 2891842714926426246099635)
                  ·
                    refine ⟨4337764072389639369149453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2891842714926426246099635 4337764072389639369149453)
                    ·
                      refine ⟨1626661527146114763431045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337764072389639369149453 1626661527146114763431045)
                      ·
                        rfl

theorem cell23_3167912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3167912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167912 prefixEnd_3167912 := by exact prefixLift 3167912
  have htrace : WordTrace (prefixWord ++ tailWord_3167912) baseStart_3167912 baseEnd_3167912 := by
    simpa [prefixWord, tailWord_3167912, baseEnd_3167912] using wordTrace_append hprefix tailTrace_3167912
  have hstable : (prefixWord ++ tailWord_3167912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167912).length < 2 ^ (prefixWord ++ tailWord_3167912).sum := by decide
  have hdescent : baseEnd_3167912 < baseStart_3167912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167923 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4]
def baseStart_3167923 : Nat := 118140960795 + 3167923 * 2 ^ 59
def prefixEnd_3167923 : Nat := 4983230072969 + 3 ^ 40 * 3167923 * 2
def baseEnd_3167923 : Nat := 1626667175433314220393493

theorem tailTrace_3167923 : CollatzResearch.WordTrace tailWord_3167923 prefixEnd_3167923 1626667175433314220393493 := by
  unfold tailWord_3167923
  simp only [CollatzResearch.WordTrace]
  refine ⟨115543644102163484019260423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77029096068108989346173615 115543644102163484019260423)
  ·
    refine ⟨173315466153245226028890635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115543644102163484019260423 173315466153245226028890635)
    ·
      refine ⟨259973199229867839043335953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173315466153245226028890635 259973199229867839043335953)
      ·
        refine ⟨194979899422400879282501965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259973199229867839043335953 194979899422400879282501965)
        ·
          refine ⟨73117462283400329730938237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194979899422400879282501965 73117462283400329730938237)
          ·
            refine ⟨27419048356275123649101839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73117462283400329730938237 27419048356275123649101839)
            ·
              refine ⟨41128572534412685473652759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27419048356275123649101839 41128572534412685473652759)
              ·
                refine ⟨61692858801619028210479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41128572534412685473652759 61692858801619028210479139)
                ·
                  refine ⟨92539288202428542315718709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61692858801619028210479139 92539288202428542315718709)
                  ·
                    refine ⟨8675558268977675842098629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92539288202428542315718709 8675558268977675842098629)
                    ·
                      refine ⟨1626667175433314220393493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8675558268977675842098629 1626667175433314220393493)
                      ·
                        rfl

theorem cell23_3167923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_3167923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167923 prefixEnd_3167923 := by exact prefixLift 3167923
  have htrace : WordTrace (prefixWord ++ tailWord_3167923) baseStart_3167923 baseEnd_3167923 := by
    simpa [prefixWord, tailWord_3167923, baseEnd_3167923] using wordTrace_append hprefix tailTrace_3167923
  have hstable : (prefixWord ++ tailWord_3167923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167923).length < 2 ^ (prefixWord ++ tailWord_3167923).sum := by decide
  have hdescent : baseEnd_3167923 < baseStart_3167923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167927 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 3, 3, 2]
def baseStart_3167927 : Nat := 118140960795 + 3167927 * 2 ^ 59
def prefixEnd_3167927 : Nat := 4983230072969 + 3 ^ 40 * 3167927 * 2
def baseEnd_3167927 : Nat := 1626669229355932204743475

theorem tailTrace_3167927 : CollatzResearch.WordTrace tailWord_3167927 prefixEnd_3167927 1626669229355932204743475 := by
  unfold tailWord_3167927
  simp only [CollatzResearch.WordTrace]
  refine ⟨115543789994148992702406035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77029193329432661801604023 115543789994148992702406035)
  ·
    refine ⟨173315684991223489053609053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115543789994148992702406035 173315684991223489053609053)
    ·
      refine ⟨64993381871708808395103395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173315684991223489053609053 64993381871708808395103395)
      ·
        refine ⟨97490072807563212592655093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64993381871708808395103395 97490072807563212592655093)
        ·
          refine ⟨9139694325709051180561415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97490072807563212592655093 9139694325709051180561415)
          ·
            refine ⟨13709541488563576770842123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9139694325709051180561415 13709541488563576770842123)
            ·
              refine ⟨20564312232845365156263185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709541488563576770842123 20564312232845365156263185)
              ·
                refine ⟨15423234174634023867197389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20564312232845365156263185 15423234174634023867197389)
                ·
                  refine ⟨5783712815487758950199021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15423234174634023867197389 5783712815487758950199021)
                  ·
                    refine ⟨2168892305807909606324633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5783712815487758950199021 2168892305807909606324633)
                    ·
                      refine ⟨1626669229355932204743475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168892305807909606324633 1626669229355932204743475)
                      ·
                        rfl

theorem cell23_3167927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_3167927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167927 prefixEnd_3167927 := by exact prefixLift 3167927
  have htrace : WordTrace (prefixWord ++ tailWord_3167927) baseStart_3167927 baseEnd_3167927 := by
    simpa [prefixWord, tailWord_3167927, baseEnd_3167927] using wordTrace_append hprefix tailTrace_3167927
  have hstable : (prefixWord ++ tailWord_3167927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167927).length < 2 ^ (prefixWord ++ tailWord_3167927).sum := by decide
  have hdescent : baseEnd_3167927 < baseStart_3167927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167934 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3167934 : Nat := 118140960795 + 3167934 * 2 ^ 59
def prefixEnd_3167934 : Nat := 4983230072969 + 3 ^ 40 * 3167934 * 2
def baseEnd_3167934 : Nat := 1626672823720513677355943

theorem tailTrace_3167934 : CollatzResearch.WordTrace tailWord_3167934 prefixEnd_3167934 1626672823720513677355943 := by
  unfold tailWord_3167934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14443005663140454112238857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77029363536749088598607237 14443005663140454112238857)
  ·
    refine ⟨10832254247355340584179143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14443005663140454112238857 10832254247355340584179143)
    ·
      refine ⟨16248381371033010876268715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10832254247355340584179143 16248381371033010876268715)
      ·
        refine ⟨24372572056549516314403073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16248381371033010876268715 24372572056549516314403073)
        ·
          refine ⟨18279429042412137235802305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24372572056549516314403073 18279429042412137235802305)
          ·
            refine ⟨13709571781809102926851729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18279429042412137235802305 13709571781809102926851729)
            ·
              refine ⟨10282178836356827195138797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13709571781809102926851729 10282178836356827195138797)
              ·
                refine ⟨3855817063633810198177049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10282178836356827195138797 3855817063633810198177049)
                ·
                  refine ⟨2891862797725357648632787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3855817063633810198177049 2891862797725357648632787)
                  ·
                    refine ⟨4337794196588036472949181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2891862797725357648632787 4337794196588036472949181)
                    ·
                      refine ⟨1626672823720513677355943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337794196588036472949181 1626672823720513677355943)
                      ·
                        rfl

theorem cell23_3167934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3167934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167934 prefixEnd_3167934 := by exact prefixLift 3167934
  have htrace : WordTrace (prefixWord ++ tailWord_3167934) baseStart_3167934 baseEnd_3167934 := by
    simpa [prefixWord, tailWord_3167934, baseEnd_3167934] using wordTrace_append hprefix tailTrace_3167934
  have hstable : (prefixWord ++ tailWord_3167934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167934).length < 2 ^ (prefixWord ++ tailWord_3167934).sum := by decide
  have hdescent : baseEnd_3167934 < baseStart_3167934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167940 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3167940 : Nat := 118140960795 + 3167940 * 2 ^ 59
def prefixEnd_3167940 : Nat := 4983230072969 + 3 ^ 40 * 3167940 * 2
def baseEnd_3167940 : Nat := 1626675904604440653880915

theorem tailTrace_3167940 : CollatzResearch.WordTrace tailWord_3167940 prefixEnd_3167940 1626675904604440653880915 := by
  unfold tailWord_3167940
  simp only [CollatzResearch.WordTrace]
  refine ⟨57772132071550947961314637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77029509428734597281752849 57772132071550947961314637)
  ·
    refine ⟨21664549526831605485492989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57772132071550947961314637 21664549526831605485492989)
    ·
      refine ⟨8124206072561852057059871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21664549526831605485492989 8124206072561852057059871)
      ·
        refine ⟨12186309108842778085589807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124206072561852057059871 12186309108842778085589807)
        ·
          refine ⟨18279463663264167128384711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12186309108842778085589807 18279463663264167128384711)
          ·
            refine ⟨27419195494896250692577067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279463663264167128384711 27419195494896250692577067)
            ·
              refine ⟨41128793242344376038865601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27419195494896250692577067 41128793242344376038865601)
              ·
                refine ⟨30846594931758282029149201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41128793242344376038865601 30846594931758282029149201)
                ·
                  refine ⟨23134946198818711521861901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30846594931758282029149201 23134946198818711521861901)
                  ·
                    refine ⟨8675604824557016820698213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23134946198818711521861901 8675604824557016820698213)
                    ·
                      refine ⟨1626675904604440653880915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8675604824557016820698213 1626675904604440653880915)
                      ·
                        rfl

theorem cell23_3167940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3167940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167940 prefixEnd_3167940 := by exact prefixLift 3167940
  have htrace : WordTrace (prefixWord ++ tailWord_3167940) baseStart_3167940 baseEnd_3167940 := by
    simpa [prefixWord, tailWord_3167940, baseEnd_3167940] using wordTrace_append hprefix tailTrace_3167940
  have hstable : (prefixWord ++ tailWord_3167940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167940).length < 2 ^ (prefixWord ++ tailWord_3167940).sum := by decide
  have hdescent : baseEnd_3167940 < baseStart_3167940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3167961 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 1, 3, 2]
def baseStart_3167961 : Nat := 118140960795 + 3167961 * 2 ^ 59
def prefixEnd_3167961 : Nat := 4983230072969 + 3 ^ 40 * 3167961 * 2
def baseEnd_3167961 : Nat := 1626686687698185071718319

theorem tailTrace_3167961 : CollatzResearch.WordTrace tailWord_3167961 prefixEnd_3167961 1626686687698185071718319 := by
  unfold tailWord_3167961
  simp only [CollatzResearch.WordTrace]
  refine ⟨115545030076025816509143737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77030020050683877672762491 115545030076025816509143737)
  ·
    refine ⟨86658772557019362381857803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115545030076025816509143737 86658772557019362381857803)
    ·
      refine ⟨129988158835529043572786705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86658772557019362381857803 129988158835529043572786705)
      ·
        refine ⟨97491119126646782679590029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129988158835529043572786705 97491119126646782679590029)
        ·
          refine ⟨36559169672492543504846261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97491119126646782679590029 36559169672492543504846261)
          ·
            refine ⟨3427422156796175953579337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36559169672492543504846261 3427422156796175953579337)
            ·
              refine ⟨2570566617597131965184503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427422156796175953579337 2570566617597131965184503)
              ·
                refine ⟨3855849926395697947776755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570566617597131965184503 3855849926395697947776755)
                ·
                  refine ⟨5783774889593546921665133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855849926395697947776755 5783774889593546921665133)
                  ·
                    refine ⟨2168915583597580095624425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5783774889593546921665133 2168915583597580095624425)
                    ·
                      refine ⟨1626686687698185071718319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2168915583597580095624425 1626686687698185071718319)
                      ·
                        rfl

theorem cell23_3167961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_3167961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3167961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3167961 prefixEnd_3167961 := by exact prefixLift 3167961
  have htrace : WordTrace (prefixWord ++ tailWord_3167961) baseStart_3167961 baseEnd_3167961 := by
    simpa [prefixWord, tailWord_3167961, baseEnd_3167961] using wordTrace_append hprefix tailTrace_3167961
  have hstable : (prefixWord ++ tailWord_3167961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3167961).length < 2 ^ (prefixWord ++ tailWord_3167961).sum := by decide
  have hdescent : baseEnd_3167961 < baseStart_3167961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3167961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168010 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3168010 : Nat := 118140960795 + 3168010 * 2 ^ 59
def prefixEnd_3168010 : Nat := 4983230072969 + 3 ^ 40 * 3168010 * 2
def baseEnd_3168010 : Nat := 542237282750085126668531

theorem tailTrace_3168010 : CollatzResearch.WordTrace tailWord_3168010 prefixEnd_3168010 542237282750085126668531 := by
  unfold tailWord_3168010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886704313212074469419371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77031211501898865251784989 28886704313212074469419371)
  ·
    refine ⟨43330056469818111704129057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28886704313212074469419371 43330056469818111704129057)
    ·
      refine ⟨32497542352363583778096793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43330056469818111704129057 32497542352363583778096793)
      ·
        refine ⟨24373156764272687833572595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32497542352363583778096793 24373156764272687833572595)
        ·
          refine ⟨36559735146409031750358893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24373156764272687833572595 36559735146409031750358893)
          ·
            refine ⟨13709900679903386906384585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36559735146409031750358893 13709900679903386906384585)
            ·
              refine ⟨10282425509927540179788439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13709900679903386906384585 10282425509927540179788439)
              ·
                refine ⟨15423638264891310269682659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10282425509927540179788439 15423638264891310269682659)
                ·
                  refine ⟨23135457397336965404523989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15423638264891310269682659 23135457397336965404523989)
                  ·
                    refine ⟨542237282750085126668531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23135457397336965404523989 542237282750085126668531)
                    ·
                      rfl

theorem cell23_3168010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3168010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168010 prefixEnd_3168010 := by exact prefixLift 3168010
  have htrace : WordTrace (prefixWord ++ tailWord_3168010) baseStart_3168010 baseEnd_3168010 := by
    simpa [prefixWord, tailWord_3168010, baseEnd_3168010] using wordTrace_append hprefix tailTrace_3168010
  have hstable : (prefixWord ++ tailWord_3168010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168010).length < 2 ^ (prefixWord ++ tailWord_3168010).sum := by decide
  have hdescent : baseEnd_3168010 < baseStart_3168010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168060 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3168060 : Nat := 118140960795 + 3168060 * 2 ^ 59
def prefixEnd_3168060 : Nat := 4983230072969 + 3 ^ 40 * 3168060 * 2
def baseEnd_3168060 : Nat := 1626737522282980184380363

theorem tailTrace_3168060 : CollatzResearch.WordTrace tailWord_3168060 prefixEnd_3168060 1626737522282980184380363 := by
  unfold tailWord_3168060
  simp only [CollatzResearch.WordTrace]
  refine ⟨57774320451333578208498817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77032427268444770944665089 57774320451333578208498817)
  ·
    refine ⟨43330740338500183656374113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57774320451333578208498817 43330740338500183656374113)
    ·
      refine ⟨32498055253875137742280585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43330740338500183656374113 32498055253875137742280585)
      ·
        refine ⟨24373541440406353306710439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32498055253875137742280585 24373541440406353306710439)
        ·
          refine ⟨36560312160609529960065659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24373541440406353306710439 36560312160609529960065659)
          ·
            refine ⟨54840468240914294940098489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36560312160609529960065659 54840468240914294940098489)
            ·
              refine ⟨41130351180685721205073867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54840468240914294940098489 41130351180685721205073867)
              ·
                refine ⟨61695526771028581807610801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41130351180685721205073867 61695526771028581807610801)
                ·
                  refine ⟨46271645078271436355708101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61695526771028581807610801 46271645078271436355708101)
                  ·
                    refine ⟨8675933452175894316695269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46271645078271436355708101 8675933452175894316695269)
                    ·
                      refine ⟨1626737522282980184380363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8675933452175894316695269 1626737522282980184380363)
                      ·
                        rfl

theorem cell23_3168060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3168060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168060 prefixEnd_3168060 := by exact prefixLift 3168060
  have htrace : WordTrace (prefixWord ++ tailWord_3168060) baseStart_3168060 baseEnd_3168060 := by
    simpa [prefixWord, tailWord_3168060, baseEnd_3168060] using wordTrace_append hprefix tailTrace_3168060
  have hstable : (prefixWord ++ tailWord_3168060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168060).length < 2 ^ (prefixWord ++ tailWord_3168060).sum := by decide
  have hdescent : baseEnd_3168060 < baseStart_3168060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168067 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 3]
def baseStart_3168067 : Nat := 118140960795 + 3168067 * 2 ^ 59
def prefixEnd_3168067 : Nat := 4983230072969 + 3 ^ 40 * 3168067 * 2
def baseEnd_3168067 : Nat := 1626741116647561656992831

theorem tailTrace_3168067 : CollatzResearch.WordTrace tailWord_3168067 prefixEnd_3168067 1626741116647561656992831 := by
  unfold tailWord_3168067
  simp only [CollatzResearch.WordTrace]
  refine ⟨115548896213641796612502455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77032597475761197741668303 115548896213641796612502455)
  ·
    refine ⟨173323344320462694918753683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115548896213641796612502455 173323344320462694918753683)
    ·
      refine ⟨259985016480694042378130525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173323344320462694918753683 259985016480694042378130525)
      ·
        refine ⟨97494381180260265891798947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259985016480694042378130525 97494381180260265891798947)
        ·
          refine ⟨146241571770390398837698421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97494381180260265891798947 146241571770390398837698421)
          ·
            refine ⟨13710147353474099891034227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146241571770390398837698421 13710147353474099891034227)
            ·
              refine ⟨20565221030211149836551341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710147353474099891034227 20565221030211149836551341)
              ·
                refine ⟨7711957886329181188706753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20565221030211149836551341 7711957886329181188706753)
                ·
                  refine ⟨5783968414746885891530065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711957886329181188706753 5783968414746885891530065)
                  ·
                    refine ⟨4337976311060164418647549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5783968414746885891530065 4337976311060164418647549)
                    ·
                      refine ⟨1626741116647561656992831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337976311060164418647549 1626741116647561656992831)
                      ·
                        rfl

theorem cell23_3168067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_3168067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168067 prefixEnd_3168067 := by exact prefixLift 3168067
  have htrace : WordTrace (prefixWord ++ tailWord_3168067) baseStart_3168067 baseEnd_3168067 := by
    simpa [prefixWord, tailWord_3168067, baseEnd_3168067] using wordTrace_append hprefix tailTrace_3168067
  have hstable : (prefixWord ++ tailWord_3168067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168067).length < 2 ^ (prefixWord ++ tailWord_3168067).sum := by decide
  have hdescent : baseEnd_3168067 < baseStart_3168067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168074 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_3168074 : Nat := 118140960795 + 3168074 * 2 ^ 59
def prefixEnd_3168074 : Nat := 4983230072969 + 3 ^ 40 * 3168074 * 2
def baseEnd_3168074 : Nat := 542248237004047709868433

theorem tailTrace_3168074 : CollatzResearch.WordTrace tailWord_3168074 prefixEnd_3168074 542248237004047709868433 := by
  unfold tailWord_3168074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887287881154109202001819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77032767683077624538671517 28887287881154109202001819)
  ·
    refine ⟨43330931821731163803002729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28887287881154109202001819 43330931821731163803002729)
    ·
      refine ⟨32498198866298372852252047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43330931821731163803002729 32498198866298372852252047)
      ·
        refine ⟨48747298299447559278378071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32498198866298372852252047 48747298299447559278378071)
        ·
          refine ⟨73120947449171338917567107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48747298299447559278378071 73120947449171338917567107)
          ·
            refine ⟨109681421173757008376350661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73120947449171338917567107 109681421173757008376350661)
            ·
              refine ⟨20565266470079439070565749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109681421173757008376350661 20565266470079439070565749)
              ·
                refine ⟨1927993731569947412865539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20565266470079439070565749 1927993731569947412865539)
                ·
                  refine ⟨2891990597354921119298309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927993731569947412865539 2891990597354921119298309)
                  ·
                    refine ⟨542248237004047709868433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891990597354921119298309 542248237004047709868433)
                    ·
                      rfl

theorem cell23_3168074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_3168074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168074 prefixEnd_3168074 := by exact prefixLift 3168074
  have htrace : WordTrace (prefixWord ++ tailWord_3168074) baseStart_3168074 baseEnd_3168074 := by
    simpa [prefixWord, tailWord_3168074, baseEnd_3168074] using wordTrace_append hprefix tailTrace_3168074
  have hstable : (prefixWord ++ tailWord_3168074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168074).length < 2 ^ (prefixWord ++ tailWord_3168074).sum := by decide
  have hdescent : baseEnd_3168074 < baseStart_3168074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168084 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3168084 : Nat := 118140960795 + 3168084 * 2 ^ 59
def prefixEnd_3168084 : Nat := 4983230072969 + 3 ^ 40 * 3168084 * 2
def baseEnd_3168084 : Nat := 1626749845818688090480253

theorem tailTrace_3168084 : CollatzResearch.WordTrace tailWord_3168084 prefixEnd_3168084 1626749845818688090480253 := by
  unfold tailWord_3168084
  simp only [CollatzResearch.WordTrace]
  refine ⟨57774758127290104257935653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77033010836386805677247537 57774758127290104257935653)
  ·
    refine ⟨10832767148866894548362935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57774758127290104257935653 10832767148866894548362935)
    ·
      refine ⟨16249150723300341822544403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10832767148866894548362935 16249150723300341822544403)
      ·
        refine ⟨24373726084950512733816605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16249150723300341822544403 24373726084950512733816605)
        ·
          refine ⟨9140147281856442275181227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24373726084950512733816605 9140147281856442275181227)
          ·
            refine ⟨13710220922784663412771841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140147281856442275181227 13710220922784663412771841)
            ·
              refine ⟨10282665692088497559578881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13710220922784663412771841 10282665692088497559578881)
              ·
                refine ⟨7711999269066373169684161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10282665692088497559578881 7711999269066373169684161)
                ·
                  refine ⟨5783999451799779877263121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7711999269066373169684161 5783999451799779877263121)
                  ·
                    refine ⟨4337999588849834907947341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5783999451799779877263121 4337999588849834907947341)
                    ·
                      refine ⟨1626749845818688090480253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4337999588849834907947341 1626749845818688090480253)
                      ·
                        rfl

theorem cell23_3168084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3168084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168084 prefixEnd_3168084 := by exact prefixLift 3168084
  have htrace : WordTrace (prefixWord ++ tailWord_3168084) baseStart_3168084 baseEnd_3168084 := by
    simpa [prefixWord, tailWord_3168084, baseEnd_3168084] using wordTrace_append hprefix tailTrace_3168084
  have hstable : (prefixWord ++ tailWord_3168084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168084).length < 2 ^ (prefixWord ++ tailWord_3168084).sum := by decide
  have hdescent : baseEnd_3168084 < baseStart_3168084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168090 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3168090 : Nat := 118140960795 + 3168090 * 2 ^ 59
def prefixEnd_3168090 : Nat := 4983230072969 + 3 ^ 40 * 3168090 * 2
def baseEnd_3168090 : Nat := 1626752926702615067005225

theorem tailTrace_3168090 : CollatzResearch.WordTrace tailWord_3168090 prefixEnd_3168090 1626752926702615067005225 := by
  unfold tailWord_3168090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887433773139617885147431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77033156728372314360393149 28887433773139617885147431)
  ·
    refine ⟨43331150659709426827721147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28887433773139617885147431 43331150659709426827721147)
    ·
      refine ⟨64996725989564140241581721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43331150659709426827721147 64996725989564140241581721)
      ·
        refine ⟨48747544492173105181186291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64996725989564140241581721 48747544492173105181186291)
        ·
          refine ⟨73121316738259657771779437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48747544492173105181186291 73121316738259657771779437)
          ·
            refine ⟨27420493776847371664417289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73121316738259657771779437 27420493776847371664417289)
            ·
              refine ⟨20565370332635528748312967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27420493776847371664417289 20565370332635528748312967)
              ·
                refine ⟨30848055498953293122469451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20565370332635528748312967 30848055498953293122469451)
                ·
                  refine ⟨46272083248429939683704177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30848055498953293122469451 46272083248429939683704177)
                  ·
                    refine ⟨34704062436322454762778133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46272083248429939683704177 34704062436322454762778133)
                    ·
                      refine ⟨1626752926702615067005225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34704062436322454762778133 1626752926702615067005225)
                      ·
                        rfl

theorem cell23_3168090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3168090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168090 prefixEnd_3168090 := by exact prefixLift 3168090
  have htrace : WordTrace (prefixWord ++ tailWord_3168090) baseStart_3168090 baseEnd_3168090 := by
    simpa [prefixWord, tailWord_3168090, baseEnd_3168090] using wordTrace_append hprefix tailTrace_3168090
  have hstable : (prefixWord ++ tailWord_3168090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168090).length < 2 ^ (prefixWord ++ tailWord_3168090).sum := by decide
  have hdescent : baseEnd_3168090 < baseStart_3168090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168107 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 1, 5, 2]
def baseStart_3168107 : Nat := 118140960795 + 3168107 * 2 ^ 59
def prefixEnd_3168107 : Nat := 4983230072969 + 3 ^ 40 * 3168107 * 2
def baseEnd_3168107 : Nat := 1626761655873741500492647

theorem tailTrace_3168107 : CollatzResearch.WordTrace tailWord_3168107 prefixEnd_3168107 1626761655873741500492647 := by
  unfold tailWord_3168107
  simp only [CollatzResearch.WordTrace]
  refine ⟨115550355133496883443958575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77033570088997922295972383 115550355133496883443958575)
  ·
    refine ⟨173325532700245325165937863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115550355133496883443958575 173325532700245325165937863)
    ·
      refine ⟨259988299050367987748906795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173325532700245325165937863 259988299050367987748906795)
      ·
        refine ⟨389982448575551981623360193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259988299050367987748906795 389982448575551981623360193)
        ·
          refine ⟨292486836431663986217520145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389982448575551981623360193 292486836431663986217520145)
          ·
            refine ⟨219365127323747989663140109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292486836431663986217520145 219365127323747989663140109)
            ·
              refine ⟨82261922746405496123677541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219365127323747989663140109 82261922746405496123677541)
              ·
                refine ⟨15424110514951030523189539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82261922746405496123677541 15424110514951030523189539)
                ·
                  refine ⟨23136165772426545784784309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15424110514951030523189539 23136165772426545784784309)
                  ·
                    refine ⟨2169015541164988667323529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23136165772426545784784309 2169015541164988667323529)
                    ·
                      refine ⟨1626761655873741500492647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169015541164988667323529 1626761655873741500492647)
                      ·
                        rfl

theorem cell23_3168107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5, 2].length) (baseStart_3168107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168107 prefixEnd_3168107 := by exact prefixLift 3168107
  have htrace : WordTrace (prefixWord ++ tailWord_3168107) baseStart_3168107 baseEnd_3168107 := by
    simpa [prefixWord, tailWord_3168107, baseEnd_3168107] using wordTrace_append hprefix tailTrace_3168107
  have hstable : (prefixWord ++ tailWord_3168107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168107).length < 2 ^ (prefixWord ++ tailWord_3168107).sum := by decide
  have hdescent : baseEnd_3168107 < baseStart_3168107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168117 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3168117 : Nat := 118140960795 + 3168117 * 2 ^ 59
def prefixEnd_3168117 : Nat := 4983230072969 + 3 ^ 40 * 3168117 * 2
def baseEnd_3168117 : Nat := 542255596893428820455867

theorem tailTrace_3168117 : CollatzResearch.WordTrace tailWord_3168117 prefixEnd_3168117 542255596893428820455867 := by
  unfold tailWord_3168117
  simp only [CollatzResearch.WordTrace]
  refine ⟨115550719863460655151822605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77033813242307103434548403 115550719863460655151822605)
  ·
    refine ⟨43331519948797745681933477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115550719863460655151822605 43331519948797745681933477)
    ·
      refine ⟨8124659990399577315362527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43331519948797745681933477 8124659990399577315362527)
      ·
        refine ⟨12186989985599365973043791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124659990399577315362527 12186989985599365973043791)
        ·
          refine ⟨18280484978399048959565687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12186989985599365973043791 18280484978399048959565687)
          ·
            refine ⟨27420727467598573439348531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18280484978399048959565687 27420727467598573439348531)
            ·
              refine ⟨41131091201397860159022797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27420727467598573439348531 41131091201397860159022797)
              ·
                refine ⟨15424159200524197559633549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41131091201397860159022797 15424159200524197559633549)
                ·
                  refine ⟨5784059700196574084862581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15424159200524197559633549 5784059700196574084862581)
                  ·
                    refine ⟨542255596893428820455867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5784059700196574084862581 542255596893428820455867)
                    ·
                      rfl

theorem cell23_3168117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3168117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168117 prefixEnd_3168117 := by exact prefixLift 3168117
  have htrace : WordTrace (prefixWord ++ tailWord_3168117) baseStart_3168117 baseEnd_3168117 := by
    simpa [prefixWord, tailWord_3168117, baseEnd_3168117] using wordTrace_append hprefix tailTrace_3168117
  have hstable : (prefixWord ++ tailWord_3168117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168117).length < 2 ^ (prefixWord ++ tailWord_3168117).sum := by decide
  have hdescent : baseEnd_3168117 < baseStart_3168117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168118 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3168118 : Nat := 118140960795 + 3168118 * 2 ^ 59
def prefixEnd_3168118 : Nat := 4983230072969 + 3 ^ 40 * 3168118 * 2
def baseEnd_3168118 : Nat := 1626767304160940957455097

theorem tailTrace_3168118 : CollatzResearch.WordTrace tailWord_3168118 prefixEnd_3168118 1626767304160940957455097 := by
  unfold tailWord_3168118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7221922271028564520163063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77033837557638021548406005 7221922271028564520163063)
  ·
    refine ⟨10832883406542846780244595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7221922271028564520163063 10832883406542846780244595)
    ·
      refine ⟨16249325109814270170366893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10832883406542846780244595 16249325109814270170366893)
      ·
        refine ⟨6093496916180351313887585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16249325109814270170366893 6093496916180351313887585)
        ·
          refine ⟨4570122687135263485415689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6093496916180351313887585 4570122687135263485415689)
          ·
            refine ⟨3427592015351447614061767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570122687135263485415689 3427592015351447614061767)
            ·
              refine ⟨5141388023027171421092651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427592015351447614061767 5141388023027171421092651)
              ·
                refine ⟨7712082034540757131638977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141388023027171421092651 7712082034540757131638977)
                ·
                  refine ⟨5784061525905567848729233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712082034540757131638977 5784061525905567848729233)
                  ·
                    refine ⟨4338046144429175886546925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784061525905567848729233 4338046144429175886546925)
                    ·
                      refine ⟨1626767304160940957455097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4338046144429175886546925 1626767304160940957455097)
                      ·
                        rfl

theorem cell23_3168118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3168118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168118 prefixEnd_3168118 := by exact prefixLift 3168118
  have htrace : WordTrace (prefixWord ++ tailWord_3168118) baseStart_3168118 baseEnd_3168118 := by
    simpa [prefixWord, tailWord_3168118, baseEnd_3168118] using wordTrace_append hprefix tailTrace_3168118
  have hstable : (prefixWord ++ tailWord_3168118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168118).length < 2 ^ (prefixWord ++ tailWord_3168118).sum := by decide
  have hdescent : baseEnd_3168118 < baseStart_3168118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168131 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 1, 1, 3]
def baseStart_3168131 : Nat := 118140960795 + 3168131 * 2 ^ 59
def prefixEnd_3168131 : Nat := 4983230072969 + 3 ^ 40 * 3168131 * 2
def baseEnd_3168131 : Nat := 1626773979409449406592537

theorem tailTrace_3168131 : CollatzResearch.WordTrace tailWord_3168131 prefixEnd_3168131 1626773979409449406592537 := by
  unfold tailWord_3168131
  simp only [CollatzResearch.WordTrace]
  refine ⟨115551230485409935542832247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77034153656939957028554831 115551230485409935542832247)
  ·
    refine ⟨173326845728114903314248371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115551230485409935542832247 173326845728114903314248371)
    ·
      refine ⟨259990268592172354971372557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173326845728114903314248371 259990268592172354971372557)
      ·
        refine ⟨97496350722064633114264709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259990268592172354971372557 97496350722064633114264709)
        ·
          refine ⟨18280565760387118708924633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97496350722064633114264709 18280565760387118708924633)
          ·
            refine ⟨13710424320290339031693475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18280565760387118708924633 13710424320290339031693475)
            ·
              refine ⟨20565636480435508547540213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710424320290339031693475 20565636480435508547540213)
              ·
                refine ⟨1928028420040828926331895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20565636480435508547540213 1928028420040828926331895)
                ·
                  refine ⟨2892042630061243389497843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928028420040828926331895 2892042630061243389497843)
                  ·
                    refine ⟨4338063945091865084246765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892042630061243389497843 4338063945091865084246765)
                    ·
                      refine ⟨1626773979409449406592537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4338063945091865084246765 1626773979409449406592537)
                      ·
                        rfl

theorem cell23_3168131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_3168131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168131 prefixEnd_3168131 := by exact prefixLift 3168131
  have htrace : WordTrace (prefixWord ++ tailWord_3168131) baseStart_3168131 baseEnd_3168131 := by
    simpa [prefixWord, tailWord_3168131, baseEnd_3168131] using wordTrace_append hprefix tailTrace_3168131
  have hstable : (prefixWord ++ tailWord_3168131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168131).length < 2 ^ (prefixWord ++ tailWord_3168131).sum := by decide
  have hdescent : baseEnd_3168131 < baseStart_3168131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168148 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_3168148 : Nat := 118140960795 + 3168148 * 2 ^ 59
def prefixEnd_3168148 : Nat := 4983230072969 + 3 ^ 40 * 3168148 * 2
def baseEnd_3168148 : Nat := 1626782708580575840079959

theorem tailTrace_3168148 : CollatzResearch.WordTrace tailWord_3168148 prefixEnd_3168148 1626782708580575840079959 := by
  unfold tailWord_3168148
  simp only [CollatzResearch.WordTrace]
  refine ⟨57775925263174173723100549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77034567017565564964134065 57775925263174173723100549)
  ·
    refine ⟨10832985986845157573081353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57775925263174173723100549 10832985986845157573081353)
    ·
      refine ⟨8124739490133868179811015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10832985986845157573081353 8124739490133868179811015)
      ·
        refine ⟨12187109235200802269716523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124739490133868179811015 12187109235200802269716523)
        ·
          refine ⟨18280663852801203404574785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12187109235200802269716523 18280663852801203404574785)
          ·
            refine ⟨13710497889600902553431089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18280663852801203404574785 13710497889600902553431089)
            ·
              refine ⟨10282873417200676915073317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13710497889600902553431089 10282873417200676915073317)
              ·
                refine ⟨1928038765725126921576247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10282873417200676915073317 1928038765725126921576247)
                ·
                  refine ⟨2892058148587690382364371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928038765725126921576247 2892058148587690382364371)
                  ·
                    refine ⟨4338087222881535573546557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892058148587690382364371 4338087222881535573546557)
                    ·
                      refine ⟨1626782708580575840079959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4338087222881535573546557 1626782708580575840079959)
                      ·
                        rfl

theorem cell23_3168148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_3168148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168148 prefixEnd_3168148 := by exact prefixLift 3168148
  have htrace : WordTrace (prefixWord ++ tailWord_3168148) baseStart_3168148 baseEnd_3168148 := by
    simpa [prefixWord, tailWord_3168148, baseEnd_3168148] using wordTrace_append hprefix tailTrace_3168148
  have hstable : (prefixWord ++ tailWord_3168148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168148).length < 2 ^ (prefixWord ++ tailWord_3168148).sum := by decide
  have hdescent : baseEnd_3168148 < baseStart_3168148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168157 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3168157 : Nat := 118140960795 + 3168157 * 2 ^ 59
def prefixEnd_3168157 : Nat := 4983230072969 + 3 ^ 40 * 3168157 * 2
def baseEnd_3168157 : Nat := 1626787329906466304867417

theorem tailTrace_3168157 : CollatzResearch.WordTrace tailWord_3168157 prefixEnd_3168157 1626787329906466304867417 := by
  unfold tailWord_3168157
  simp only [CollatzResearch.WordTrace]
  refine ⟨115552178783315741983278725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77034785855543827988852483 115552178783315741983278725)
  ·
    refine ⟨21666033521871701621864761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115552178783315741983278725 21666033521871701621864761)
    ·
      refine ⟨16249525141403776216398571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21666033521871701621864761 16249525141403776216398571)
      ·
        refine ⟨24374287712105664324597857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16249525141403776216398571 24374287712105664324597857)
        ·
          refine ⟨18280715784079248243448393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24374287712105664324597857 18280715784079248243448393)
          ·
            refine ⟨13710536838059436182586295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18280715784079248243448393 13710536838059436182586295)
            ·
              refine ⟨20565805257089154273879443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710536838059436182586295 20565805257089154273879443)
              ·
                refine ⟨30848707885633731410819165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20565805257089154273879443 30848707885633731410819165)
                ·
                  refine ⟨11568265457112649279057187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30848707885633731410819165 11568265457112649279057187)
                  ·
                    refine ⟨17352398185668973918585781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11568265457112649279057187 17352398185668973918585781)
                    ·
                      refine ⟨1626787329906466304867417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17352398185668973918585781 1626787329906466304867417)
                      ·
                        rfl

theorem cell23_3168157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3168157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168157 prefixEnd_3168157 := by exact prefixLift 3168157
  have htrace : WordTrace (prefixWord ++ tailWord_3168157) baseStart_3168157 baseEnd_3168157 := by
    simpa [prefixWord, tailWord_3168157, baseEnd_3168157] using wordTrace_append hprefix tailTrace_3168157
  have hstable : (prefixWord ++ tailWord_3168157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168157).length < 2 ^ (prefixWord ++ tailWord_3168157).sum := by decide
  have hdescent : baseEnd_3168157 < baseStart_3168157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168160 : List Nat := [2, 1, 1, 4, 1, 1, 1, 12]
def baseStart_3168160 : Nat := 118140960795 + 3168160 * 2 ^ 59
def prefixEnd_3168160 : Nat := 4983230072969 + 3 ^ 40 * 3168160 * 2
def baseEnd_3168160 : Nat := 60251439642534436782589

theorem tailTrace_3168160 : CollatzResearch.WordTrace tailWord_3168160 prefixEnd_3168160 60251439642534436782589 := by
  unfold tailWord_3168160
  simp only [CollatzResearch.WordTrace]
  refine ⟨57776144101152436747818967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77034858801536582330425289 57776144101152436747818967)
  ·
    refine ⟨86664216151728655121728451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57776144101152436747818967 86664216151728655121728451)
    ·
      refine ⟨129996324227592982682592677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86664216151728655121728451 129996324227592982682592677)
      ·
        refine ⟨24374310792673684252986127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129996324227592982682592677 24374310792673684252986127)
        ·
          refine ⟨36561466189010526379479191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24374310792673684252986127 36561466189010526379479191)
          ·
            refine ⟨54842199283515789569218787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36561466189010526379479191 54842199283515789569218787)
            ·
              refine ⟨82263298925273684353828181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54842199283515789569218787 82263298925273684353828181)
              ·
                refine ⟨60251439642534436782589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 82263298925273684353828181 60251439642534436782589)
                ·
                  rfl

theorem cell23_3168160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 12].length) (baseStart_3168160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168160 prefixEnd_3168160 := by exact prefixLift 3168160
  have htrace : WordTrace (prefixWord ++ tailWord_3168160) baseStart_3168160 baseEnd_3168160 := by
    simpa [prefixWord, tailWord_3168160, baseEnd_3168160] using wordTrace_append hprefix tailTrace_3168160
  have hstable : (prefixWord ++ tailWord_3168160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168160).length < 2 ^ (prefixWord ++ tailWord_3168160).sum := by decide
  have hdescent : baseEnd_3168160 < baseStart_3168160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168164 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_3168164 : Nat := 118140960795 + 3168164 * 2 ^ 59
def prefixEnd_3168164 : Nat := 4983230072969 + 3 ^ 40 * 3168164 * 2
def baseEnd_3168164 : Nat := 542263641423682592493295

theorem tailTrace_3168164 : CollatzResearch.WordTrace tailWord_3168164 prefixEnd_3168164 542263641423682592493295 := by
  unfold tailWord_3168164
  simp only [CollatzResearch.WordTrace]
  refine ⟨57776217047145191089391773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77034956062860254785855697 57776217047145191089391773)
  ·
    refine ⟨21666081392679446658521915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57776217047145191089391773 21666081392679446658521915)
    ·
      refine ⟨32499122089019169987782873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21666081392679446658521915 32499122089019169987782873)
      ·
        refine ⟨24374341566764377490837155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32499122089019169987782873 24374341566764377490837155)
        ·
          refine ⟨36561512350146566236255733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24374341566764377490837155 36561512350146566236255733)
          ·
            refine ⟨3427641782826240584648975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36561512350146566236255733 3427641782826240584648975)
            ·
              refine ⟨5141462674239360876973463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427641782826240584648975 5141462674239360876973463)
              ·
                refine ⟨7712194011359041315460195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141462674239360876973463 7712194011359041315460195)
                ·
                  refine ⟨11568291017038561973190293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7712194011359041315460195 11568291017038561973190293)
                  ·
                    refine ⟨542263641423682592493295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11568291017038561973190293 542263641423682592493295)
                    ·
                      rfl

theorem cell23_3168164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_3168164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168164 prefixEnd_3168164 := by exact prefixLift 3168164
  have htrace : WordTrace (prefixWord ++ tailWord_3168164) baseStart_3168164 baseEnd_3168164 := by
    simpa [prefixWord, tailWord_3168164, baseEnd_3168164] using wordTrace_append hprefix tailTrace_3168164
  have hstable : (prefixWord ++ tailWord_3168164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168164).length < 2 ^ (prefixWord ++ tailWord_3168164).sum := by decide
  have hdescent : baseEnd_3168164 < baseStart_3168164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168168 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3168168 : Nat := 118140960795 + 3168168 * 2 ^ 59
def prefixEnd_3168168 : Nat := 4983230072969 + 3 ^ 40 * 3168168 * 2
def baseEnd_3168168 : Nat := 542264326064555253943289

theorem tailTrace_3168168 : CollatzResearch.WordTrace tailWord_3168168 prefixEnd_3168168 542264326064555253943289 := by
  unfold tailWord_3168168
  simp only [CollatzResearch.WordTrace]
  refine ⟨57776289993137945430964579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77035053324183927241286105 57776289993137945430964579)
  ·
    refine ⟨86664434989706918146446869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57776289993137945430964579 86664434989706918146446869)
    ·
      refine ⟨4062395390142511788114697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86664434989706918146446869 4062395390142511788114697)
      ·
        refine ⟨3046796542606883841086023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4062395390142511788114697 3046796542606883841086023)
        ·
          refine ⟨4570194813910325761629035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046796542606883841086023 4570194813910325761629035)
          ·
            refine ⟨6855292220865488642443553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570194813910325761629035 6855292220865488642443553)
            ·
              refine ⟨5141469165649116481832665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855292220865488642443553 5141469165649116481832665)
              ·
                refine ⟨3856101874236837361374499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141469165649116481832665 3856101874236837361374499)
                ·
                  refine ⟨5784152811355256042061749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856101874236837361374499 5784152811355256042061749)
                  ·
                    refine ⟨542264326064555253943289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5784152811355256042061749 542264326064555253943289)
                    ·
                      rfl

theorem cell23_3168168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3168168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168168 prefixEnd_3168168 := by exact prefixLift 3168168
  have htrace : WordTrace (prefixWord ++ tailWord_3168168) baseStart_3168168 baseEnd_3168168 := by
    simpa [prefixWord, tailWord_3168168, baseEnd_3168168] using wordTrace_append hprefix tailTrace_3168168
  have hstable : (prefixWord ++ tailWord_3168168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168168).length < 2 ^ (prefixWord ++ tailWord_3168168).sum := by decide
  have hdescent : baseEnd_3168168 < baseStart_3168168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168177 : List Nat := [1, 2, 2, 4, 2, 2, 1, 9]
def baseStart_3168177 : Nat := 118140960795 + 3168177 * 2 ^ 59
def prefixEnd_3168177 : Nat := 4983230072969 + 3 ^ 40 * 3168177 * 2
def baseEnd_3168177 : Nat := 60251762945168749133975

theorem tailTrace_3168177 : CollatzResearch.WordTrace tailWord_3168177 prefixEnd_3168177 60251762945168749133975 := by
  unfold tailWord_3168177
  simp only [CollatzResearch.WordTrace]
  refine ⟨115552908243243285399006785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77035272162162190266004523 115552908243243285399006785)
  ·
    refine ⟨86664681182432464049255089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115552908243243285399006785 86664681182432464049255089)
    ·
      refine ⟨64998510886824348036941317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86664681182432464049255089 64998510886824348036941317)
      ·
        refine ⟨12187220791279565256926497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64998510886824348036941317 12187220791279565256926497)
        ·
          refine ⟨9140415593459673942694873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12187220791279565256926497 9140415593459673942694873)
          ·
            refine ⟨6855311695094755457021155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9140415593459673942694873 6855311695094755457021155)
            ·
              refine ⟨10282967542642133185531733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6855311695094755457021155 10282967542642133185531733)
              ·
                refine ⟨60251762945168749133975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10282967542642133185531733 60251762945168749133975)
                ·
                  rfl

theorem cell23_3168177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 9].length) (baseStart_3168177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168177 prefixEnd_3168177 := by exact prefixLift 3168177
  have htrace : WordTrace (prefixWord ++ tailWord_3168177) baseStart_3168177 baseEnd_3168177 := by
    simpa [prefixWord, tailWord_3168177, baseEnd_3168177] using wordTrace_append hprefix tailTrace_3168177
  have hstable : (prefixWord ++ tailWord_3168177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168177).length < 2 ^ (prefixWord ++ tailWord_3168177).sum := by decide
  have hdescent : baseEnd_3168177 < baseStart_3168177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168247 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_3168247 : Nat := 118140960795 + 3168247 * 2 ^ 59
def prefixEnd_3168247 : Nat := 4983230072969 + 3 ^ 40 * 3168247 * 2
def baseEnd_3168247 : Nat := 1626833543165370952742003

theorem tailTrace_3168247 : CollatzResearch.WordTrace tailWord_3168247 prefixEnd_3168247 1626833543165370952742003 := by
  unfold tailWord_3168247
  simp only [CollatzResearch.WordTrace]
  refine ⟨115555461352989687354054995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77036974235326458236036663 115555461352989687354054995)
  ·
    refine ⟨173333192029484531031082493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115555461352989687354054995 173333192029484531031082493)
    ·
      refine ⟨64999947011056699136655935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173333192029484531031082493 64999947011056699136655935)
      ·
        refine ⟨97499920516585048704983903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64999947011056699136655935 97499920516585048704983903)
        ·
          refine ⟨146249880774877573057475855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97499920516585048704983903 146249880774877573057475855)
          ·
            refine ⟨219374821162316359586213783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146249880774877573057475855 219374821162316359586213783)
            ·
              refine ⟨329062231743474539379320675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219374821162316359586213783 329062231743474539379320675)
              ·
                refine ⟨493593347615211809068981013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329062231743474539379320675 493593347615211809068981013)
                ·
                  refine ⟨23137188169463053550108485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 493593347615211809068981013 23137188169463053550108485)
                  ·
                    refine ⟨4338222781774322540645341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23137188169463053550108485 4338222781774322540645341)
                    ·
                      refine ⟨1626833543165370952742003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4338222781774322540645341 1626833543165370952742003)
                      ·
                        rfl

theorem cell23_3168247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_3168247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168247 prefixEnd_3168247 := by exact prefixLift 3168247
  have htrace : WordTrace (prefixWord ++ tailWord_3168247) baseStart_3168247 baseEnd_3168247 := by
    simpa [prefixWord, tailWord_3168247, baseEnd_3168247] using wordTrace_append hprefix tailTrace_3168247
  have hstable : (prefixWord ++ tailWord_3168247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168247).length < 2 ^ (prefixWord ++ tailWord_3168247).sum := by decide
  have hdescent : baseEnd_3168247 < baseStart_3168247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168262 : List Nat := [6, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3168262 : Nat := 118140960795 + 3168262 * 2 ^ 59
def prefixEnd_3168262 : Nat := 4983230072969 + 3 ^ 40 * 3168262 * 2
def baseEnd_3168262 : Nat := 60253379458340310890905

theorem tailTrace_3168262 : CollatzResearch.WordTrace tailWord_3168262 prefixEnd_3168262 60253379458340310890905 := by
  unfold tailWord_3168262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611125263997979528620345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77037338965290229943900693 3611125263997979528620345)
  ·
    refine ⟨2708343947998484646465259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3611125263997979528620345 2708343947998484646465259)
    ·
      refine ⟨4062515921997726969697889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2708343947998484646465259 4062515921997726969697889)
      ·
        refine ⟨3046886941498295227273417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4062515921997726969697889 3046886941498295227273417)
        ·
          refine ⟨2285165206123721420455063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046886941498295227273417 2285165206123721420455063)
          ·
            refine ⟨3427747809185582130682595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285165206123721420455063 3427747809185582130682595)
            ·
              refine ⟨5141621713778373196023893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427747809185582130682595 5141621713778373196023893)
              ·
                refine ⟨60253379458340310890905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5141621713778373196023893 60253379458340310890905)
                ·
                  rfl

theorem cell23_3168262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3168262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168262 prefixEnd_3168262 := by exact prefixLift 3168262
  have htrace : WordTrace (prefixWord ++ tailWord_3168262) baseStart_3168262 baseEnd_3168262 := by
    simpa [prefixWord, tailWord_3168262, baseEnd_3168262] using wordTrace_append hprefix tailTrace_3168262
  have hstable : (prefixWord ++ tailWord_3168262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168262).length < 2 ^ (prefixWord ++ tailWord_3168262).sum := by decide
  have hdescent : baseEnd_3168262 < baseStart_3168262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168267 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 7]
def baseStart_3168267 : Nat := 118140960795 + 3168267 * 2 ^ 59
def prefixEnd_3168267 : Nat := 4983230072969 + 3 ^ 40 * 3168267 * 2
def baseEnd_3168267 : Nat := 180760423642051208276879

theorem tailTrace_3168267 : CollatzResearch.WordTrace tailWord_3168267 prefixEnd_3168267 180760423642051208276879 := by
  unfold tailWord_3168267
  simp only [CollatzResearch.WordTrace]
  refine ⟨115556190812917230769783055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77037460541944820513188703 115556190812917230769783055)
  ·
    refine ⟨173334286219375846154674583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115556190812917230769783055 173334286219375846154674583)
    ·
      refine ⟨260001429329063769232011875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173334286219375846154674583 260001429329063769232011875)
      ·
        refine ⟨390002143993595653848017813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260001429329063769232011875 390002143993595653848017813)
        ·
          refine ⟨18281350499699796274125835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 390002143993595653848017813 18281350499699796274125835)
          ·
            refine ⟨27422025749549694411188753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18281350499699796274125835 27422025749549694411188753)
            ·
              refine ⟨20566519312162270808391565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27422025749549694411188753 20566519312162270808391565)
              ·
                refine ⟨7712444742060851553146837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20566519312162270808391565 7712444742060851553146837)
                ·
                  refine ⟨180760423642051208276879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7712444742060851553146837 180760423642051208276879)
                  ·
                    rfl

theorem cell23_3168267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 7].length) (baseStart_3168267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168267 prefixEnd_3168267 := by exact prefixLift 3168267
  have htrace : WordTrace (prefixWord ++ tailWord_3168267) baseStart_3168267 baseEnd_3168267 := by
    simpa [prefixWord, tailWord_3168267, baseEnd_3168267] using wordTrace_append hprefix tailTrace_3168267
  have hstable : (prefixWord ++ tailWord_3168267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168267).length < 2 ^ (prefixWord ++ tailWord_3168267).sum := by decide
  have hdescent : baseEnd_3168267 < baseStart_3168267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168284 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 7]
def baseStart_3168284 : Nat := 118140960795 + 3168284 * 2 ^ 59
def prefixEnd_3168284 : Nat := 4983230072969 + 3 ^ 40 * 3168284 * 2
def baseEnd_3168284 : Nat := 180761393549954145331037

theorem tailTrace_3168284 : CollatzResearch.WordTrace tailWord_3168284 prefixEnd_3168284 180761393549954145331037 := by
  unfold tailWord_3168284
  simp only [CollatzResearch.WordTrace]
  refine ⟨57778405426927821336575953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77037873902570428448767937 57778405426927821336575953)
  ·
    refine ⟨43333804070195866002431965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57778405426927821336575953 43333804070195866002431965)
    ·
      refine ⟨16250176526323449750911987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43333804070195866002431965 16250176526323449750911987)
      ·
        refine ⟨24375264789485174626367981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16250176526323449750911987 24375264789485174626367981)
        ·
          refine ⟨9140724296056940484887993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24375264789485174626367981 9140724296056940484887993)
          ·
            refine ⟨6855543222042705363665995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9140724296056940484887993 6855543222042705363665995)
            ·
              refine ⟨10283314833064058045498993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6855543222042705363665995 10283314833064058045498993)
              ·
                refine ⟨7712486124798043534124245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10283314833064058045498993 7712486124798043534124245)
                ·
                  refine ⟨180761393549954145331037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7712486124798043534124245 180761393549954145331037)
                  ·
                    rfl

theorem cell23_3168284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_3168284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168284 prefixEnd_3168284 := by exact prefixLift 3168284
  have htrace : WordTrace (prefixWord ++ tailWord_3168284) baseStart_3168284 baseEnd_3168284 := by
    simpa [prefixWord, tailWord_3168284, baseEnd_3168284] using wordTrace_append hprefix tailTrace_3168284
  have hstable : (prefixWord ++ tailWord_3168284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168284).length < 2 ^ (prefixWord ++ tailWord_3168284).sum := by decide
  have hdescent : baseEnd_3168284 < baseStart_3168284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168307 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_3168307 : Nat := 118140960795 + 3168307 * 2 ^ 59
def prefixEnd_3168307 : Nat := 4983230072969 + 3 ^ 40 * 3168307 * 2
def baseEnd_3168307 : Nat := 1626864352004640717991727

theorem tailTrace_3168307 : CollatzResearch.WordTrace tailWord_3168307 prefixEnd_3168307 1626864352004640717991727 := by
  unfold tailWord_3168307
  simp only [CollatzResearch.WordTrace]
  refine ⟨115557649732772317601239175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77038433155181545067492783 115557649732772317601239175)
  ·
    refine ⟨173336474599158476401858763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115557649732772317601239175 173336474599158476401858763)
    ·
      refine ⟨260004711898737714602788145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173336474599158476401858763 260004711898737714602788145)
      ·
        refine ⟨195003533924053285952091109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260004711898737714602788145 195003533924053285952091109)
        ·
          refine ⟨36563162610759991116017083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195003533924053285952091109 36563162610759991116017083)
          ·
            refine ⟨54844743916139986674025625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36563162610759991116017083 54844743916139986674025625)
            ·
              refine ⟨41133557937104990005519219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54844743916139986674025625 41133557937104990005519219)
              ·
                refine ⟨61700336905657485008278829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41133557937104990005519219 61700336905657485008278829)
                ·
                  refine ⟨23137626339621556878104561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61700336905657485008278829 23137626339621556878104561)
                  ·
                    refine ⟨17353219754716167658578421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23137626339621556878104561 17353219754716167658578421)
                    ·
                      refine ⟨1626864352004640717991727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17353219754716167658578421 1626864352004640717991727)
                      ·
                        rfl

theorem cell23_3168307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_3168307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168307 prefixEnd_3168307 := by exact prefixLift 3168307
  have htrace : WordTrace (prefixWord ++ tailWord_3168307) baseStart_3168307 baseEnd_3168307 := by
    simpa [prefixWord, tailWord_3168307, baseEnd_3168307] using wordTrace_append hprefix tailTrace_3168307
  have hstable : (prefixWord ++ tailWord_3168307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168307).length < 2 ^ (prefixWord ++ tailWord_3168307).sum := by decide
  have hdescent : baseEnd_3168307 < baseStart_3168307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168312 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 2, 2, 2]
def baseStart_3168312 : Nat := 118140960795 + 3168312 * 2 ^ 59
def prefixEnd_3168312 : Nat := 4983230072969 + 3 ^ 40 * 3168312 * 2
def baseEnd_3168312 : Nat := 1626866919407913198429205

theorem tailTrace_3168312 : CollatzResearch.WordTrace tailWord_3168312 prefixEnd_3168312 1626866919407913198429205 := by
  unfold tailWord_3168312
  simp only [CollatzResearch.WordTrace]
  refine ⟨57778916048877101727585595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77038554731836135636780793 57778916048877101727585595)
  ·
    refine ⟨86668374073315652591378393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57778916048877101727585595 86668374073315652591378393)
    ·
      refine ⟨65001280554986739443533795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86668374073315652591378393 65001280554986739443533795)
      ·
        refine ⟨97501920832480109165300693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65001280554986739443533795 97501920832480109165300693)
        ·
          refine ⟨2285201269511252558561735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97501920832480109165300693 2285201269511252558561735)
          ·
            refine ⟨3427801904266878837842603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285201269511252558561735 3427801904266878837842603)
            ·
              refine ⟨5141702856400318256763905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427801904266878837842603 5141702856400318256763905)
              ·
                refine ⟨3856277142300238692572929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141702856400318256763905 3856277142300238692572929)
                ·
                  refine ⟨2892207856725179019429697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856277142300238692572929 2892207856725179019429697)
                  ·
                    refine ⟨2169155892543884264572273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2892207856725179019429697 2169155892543884264572273)
                    ·
                      refine ⟨1626866919407913198429205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169155892543884264572273 1626866919407913198429205)
                      ·
                        rfl

theorem cell23_3168312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_3168312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168312 prefixEnd_3168312 := by exact prefixLift 3168312
  have htrace : WordTrace (prefixWord ++ tailWord_3168312) baseStart_3168312 baseEnd_3168312 := by
    simpa [prefixWord, tailWord_3168312, baseEnd_3168312] using wordTrace_append hprefix tailTrace_3168312
  have hstable : (prefixWord ++ tailWord_3168312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168312).length < 2 ^ (prefixWord ++ tailWord_3168312).sum := by decide
  have hdescent : baseEnd_3168312 < baseStart_3168312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168334 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3168334 : Nat := 118140960795 + 3168334 * 2 ^ 59
def prefixEnd_3168334 : Nat := 4983230072969 + 3 ^ 40 * 3168334 * 2
def baseEnd_3168334 : Nat := 1626878215982312112354103

theorem tailTrace_3168334 : CollatzResearch.WordTrace tailWord_3168334 prefixEnd_3168334 1626878215982312112354103 := by
  unfold tailWord_3168334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14444829312959312651559007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77039089669116334141648037 14444829312959312651559007)
  ·
    refine ⟨21667243969438968977338511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14444829312959312651559007 21667243969438968977338511)
    ·
      refine ⟨32500865954158453466007767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21667243969438968977338511 32500865954158453466007767)
      ·
        refine ⟨48751298931237680199011651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32500865954158453466007767 48751298931237680199011651)
        ·
          refine ⟨73126948396856520298517477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48751298931237680199011651 73126948396856520298517477)
          ·
            refine ⟨13711302824410597555972027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73126948396856520298517477 13711302824410597555972027)
            ·
              refine ⟨20566954236615896333958041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711302824410597555972027 20566954236615896333958041)
              ·
                refine ⟨15425215677461922250468531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20566954236615896333958041 15425215677461922250468531)
                ·
                  refine ⟨23137823516192883375702797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15425215677461922250468531 23137823516192883375702797)
                  ·
                    refine ⟨8676683818572331265888549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23137823516192883375702797 8676683818572331265888549)
                    ·
                      refine ⟨1626878215982312112354103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8676683818572331265888549 1626878215982312112354103)
                      ·
                        rfl

theorem cell23_3168334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3168334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168334 prefixEnd_3168334 := by exact prefixLift 3168334
  have htrace : WordTrace (prefixWord ++ tailWord_3168334) baseStart_3168334 baseEnd_3168334 := by
    simpa [prefixWord, tailWord_3168334, baseEnd_3168334] using wordTrace_append hprefix tailTrace_3168334
  have hstable : (prefixWord ++ tailWord_3168334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168334).length < 2 ^ (prefixWord ++ tailWord_3168334).sum := by decide
  have hdescent : baseEnd_3168334 < baseStart_3168334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168391 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 6]
def baseStart_3168391 : Nat := 118140960795 + 3168391 * 2 ^ 59
def prefixEnd_3168391 : Nat := 4983230072969 + 3 ^ 40 * 3168391 * 2
def baseEnd_3168391 : Nat := 180767498264402043260149

theorem tailTrace_3168391 : CollatzResearch.WordTrace tailWord_3168391 prefixEnd_3168391 180767498264402043260149 := by
  unfold tailWord_3168391
  simp only [CollatzResearch.WordTrace]
  refine ⟨115560713464467999947297027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77040475642978666631531351 115560713464467999947297027)
  ·
    refine ⟨173341070196701999920945541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115560713464467999947297027 173341070196701999920945541)
    ·
      refine ⟨32501450661881624985177289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173341070196701999920945541 32501450661881624985177289)
      ·
        refine ⟨24376087996411218738882967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32501450661881624985177289 24376087996411218738882967)
        ·
          refine ⟨36564131994616828108324451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24376087996411218738882967 36564131994616828108324451)
          ·
            refine ⟨54846197991925242162486677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36564131994616828108324451 54846197991925242162486677)
            ·
              refine ⟨2570915530871495726366563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54846197991925242162486677 2570915530871495726366563)
              ·
                refine ⟨3856373296307243589549845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570915530871495726366563 3856373296307243589549845)
                ·
                  refine ⟨180767498264402043260149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3856373296307243589549845 180767498264402043260149)
                  ·
                    rfl

theorem cell23_3168391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 6].length) (baseStart_3168391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168391 prefixEnd_3168391 := by exact prefixLift 3168391
  have htrace : WordTrace (prefixWord ++ tailWord_3168391) baseStart_3168391 baseEnd_3168391 := by
    simpa [prefixWord, tailWord_3168391, baseEnd_3168391] using wordTrace_append hprefix tailTrace_3168391
  have hstable : (prefixWord ++ tailWord_3168391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168391).length < 2 ^ (prefixWord ++ tailWord_3168391).sum := by decide
  have hdescent : baseEnd_3168391 < baseStart_3168391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168434 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_3168434 : Nat := 118140960795 + 3168434 * 2 ^ 59
def prefixEnd_3168434 : Nat := 4983230072969 + 3 ^ 40 * 3168434 * 2
def baseEnd_3168434 : Nat := 542309854682587240367881

theorem tailTrace_3168434 : CollatzResearch.WordTrace tailWord_3168434 prefixEnd_3168434 542309854682587240367881 := by
  unfold tailWord_3168434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28890570450828054572778089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77041521202208145527408237 28890570450828054572778089)
  ·
    refine ⟨21667927838121040929583567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28890570450828054572778089 21667927838121040929583567)
    ·
      refine ⟨32501891757181561394375351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21667927838121040929583567 32501891757181561394375351)
      ·
        refine ⟨48752837635772342091563027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32501891757181561394375351 48752837635772342091563027)
        ·
          refine ⟨73129256453658513137344541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48752837635772342091563027 73129256453658513137344541)
          ·
            refine ⟨27423471170121942426504203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73129256453658513137344541 27423471170121942426504203)
            ·
              refine ⟨41135206755182913639756305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27423471170121942426504203 41135206755182913639756305)
              ·
                refine ⟨30851405066387185229817229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41135206755182913639756305 30851405066387185229817229)
                ·
                  refine ⟨11569276899895194461181461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30851405066387185229817229 11569276899895194461181461)
                  ·
                    refine ⟨542309854682587240367881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11569276899895194461181461 542309854682587240367881)
                    ·
                      rfl

theorem cell23_3168434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_3168434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168434 prefixEnd_3168434 := by exact prefixLift 3168434
  have htrace : WordTrace (prefixWord ++ tailWord_3168434) baseStart_3168434 baseEnd_3168434 := by
    simpa [prefixWord, tailWord_3168434, baseEnd_3168434] using wordTrace_append hprefix tailTrace_3168434
  have hstable : (prefixWord ++ tailWord_3168434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168434).length < 2 ^ (prefixWord ++ tailWord_3168434).sum := by decide
  have hdescent : baseEnd_3168434 < baseStart_3168434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168475 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 1, 2, 2]
def baseStart_3168475 : Nat := 118140960795 + 3168475 * 2 ^ 59
def prefixEnd_3168475 : Nat := 4983230072969 + 3 ^ 40 * 3168475 * 2
def baseEnd_3168475 : Nat := 1626950616754596060690955

theorem tailTrace_3168475 : CollatzResearch.WordTrace tailWord_3168475 prefixEnd_3168475 1626950616754596060690955 := by
  unfold tailWord_3168475
  simp only [CollatzResearch.WordTrace]
  refine ⟨115563777196163682293354879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77042518130775788195569919 115563777196163682293354879)
  ·
    refine ⟨173345665794245523440032319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115563777196163682293354879 173345665794245523440032319)
    ·
      refine ⟨260018498691368285160048479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173345665794245523440032319 260018498691368285160048479)
      ·
        refine ⟨390027748037052427740072719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260018498691368285160048479 390027748037052427740072719)
        ·
          refine ⟨585041622055578641610109079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390027748037052427740072719 585041622055578641610109079)
          ·
            refine ⟨877562433083367962415163619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585041622055578641610109079 877562433083367962415163619)
            ·
              refine ⟨1316343649625051943622745429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877562433083367962415163619 1316343649625051943622745429)
              ·
                refine ⟨1928237768005447183041131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1316343649625051943622745429 1928237768005447183041131)
                ·
                  refine ⟨2892356652008170774561697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928237768005447183041131 2892356652008170774561697)
                  ·
                    refine ⟨2169267489006128080921273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2892356652008170774561697 2169267489006128080921273)
                    ·
                      refine ⟨1626950616754596060690955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169267489006128080921273 1626950616754596060690955)
                      ·
                        rfl

theorem cell23_3168475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 2, 2].length) (baseStart_3168475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168475 prefixEnd_3168475 := by exact prefixLift 3168475
  have htrace : WordTrace (prefixWord ++ tailWord_3168475) baseStart_3168475 baseEnd_3168475 := by
    simpa [prefixWord, tailWord_3168475, baseEnd_3168475] using wordTrace_append hprefix tailTrace_3168475
  have hstable : (prefixWord ++ tailWord_3168475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168475).length < 2 ^ (prefixWord ++ tailWord_3168475).sum := by decide
  have hdescent : baseEnd_3168475 < baseStart_3168475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168484 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3168484 : Nat := 118140960795 + 3168484 * 2 ^ 59
def prefixEnd_3168484 : Nat := 4983230072969 + 3 ^ 40 * 3168484 * 2
def baseEnd_3168484 : Nat := 1626955238080486525478413

theorem tailTrace_3168484 : CollatzResearch.WordTrace tailWord_3168484 prefixEnd_3168484 1626955238080486525478413 := by
  unfold tailWord_3168484
  simp only [CollatzResearch.WordTrace]
  refine ⟨57782052726565538415216253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77042736968754051220288337 57782052726565538415216253)
  ·
    refine ⟨21668269772462076905706095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57782052726565538415216253 21668269772462076905706095)
    ·
      refine ⟨32502404658693115358559143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21668269772462076905706095 32502404658693115358559143)
      ·
        refine ⟨48753606988039673037838715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32502404658693115358559143 48753606988039673037838715)
        ·
          refine ⟨73130410482059509556758073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48753606988039673037838715 73130410482059509556758073)
          ·
            refine ⟨54847807861544632167568555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73130410482059509556758073 54847807861544632167568555)
            ·
              refine ⟨82271711792316948251352833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54847807861544632167568555 82271711792316948251352833)
              ·
                refine ⟨61703783844237711188514625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82271711792316948251352833 61703783844237711188514625)
                ·
                  refine ⟨46277837883178283391385969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61703783844237711188514625 46277837883178283391385969)
                  ·
                    refine ⟨34708378412383712543539477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46277837883178283391385969 34708378412383712543539477)
                    ·
                      refine ⟨1626955238080486525478413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34708378412383712543539477 1626955238080486525478413)
                      ·
                        rfl

theorem cell23_3168484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3168484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168484 prefixEnd_3168484 := by exact prefixLift 3168484
  have htrace : WordTrace (prefixWord ++ tailWord_3168484) baseStart_3168484 baseEnd_3168484 := by
    simpa [prefixWord, tailWord_3168484, baseEnd_3168484] using wordTrace_append hprefix tailTrace_3168484
  have hstable : (prefixWord ++ tailWord_3168484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168484).length < 2 ^ (prefixWord ++ tailWord_3168484).sum := by decide
  have hdescent : baseEnd_3168484 < baseStart_3168484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168485 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_3168485 : Nat := 118140960795 + 3168485 * 2 ^ 59
def prefixEnd_3168485 : Nat := 4983230072969 + 3 ^ 40 * 3168485 * 2
def baseEnd_3168485 : Nat := 542318583853713673855303

theorem tailTrace_3168485 : CollatzResearch.WordTrace tailWord_3168485 prefixEnd_3168485 542318583853713673855303 := by
  unfold tailWord_3168485
  simp only [CollatzResearch.WordTrace]
  refine ⟨115564141926127454001218909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77042761284084969334145939 115564141926127454001218909)
  ·
    refine ⟨43336553222297795250457091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115564141926127454001218909 43336553222297795250457091)
    ·
      refine ⟨65004829833446692875685637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43336553222297795250457091 65004829833446692875685637)
      ·
        refine ⟨12188405593771254914191057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65004829833446692875685637 12188405593771254914191057)
        ·
          refine ⟨9141304195328441185643293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12188405593771254914191057 9141304195328441185643293)
          ·
            refine ⟨3427989073248165444616235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9141304195328441185643293 3427989073248165444616235)
            ·
              refine ⟨5141983609872248166924353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427989073248165444616235 5141983609872248166924353)
              ·
                refine ⟨3856487707404186125193265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141983609872248166924353 3856487707404186125193265)
                ·
                  refine ⟨2892365780553139593894949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856487707404186125193265 2892365780553139593894949)
                  ·
                    refine ⟨542318583853713673855303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2892365780553139593894949 542318583853713673855303)
                    ·
                      rfl

theorem cell23_3168485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_3168485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168485 prefixEnd_3168485 := by exact prefixLift 3168485
  have htrace : WordTrace (prefixWord ++ tailWord_3168485) baseStart_3168485 baseEnd_3168485 := by
    simpa [prefixWord, tailWord_3168485, baseEnd_3168485] using wordTrace_append hprefix tailTrace_3168485
  have hstable : (prefixWord ++ tailWord_3168485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168485).length < 2 ^ (prefixWord ++ tailWord_3168485).sum := by decide
  have hdescent : baseEnd_3168485 < baseStart_3168485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168504 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3168504 : Nat := 118140960795 + 3168504 * 2 ^ 59
def prefixEnd_3168504 : Nat := 4983230072969 + 3 ^ 40 * 3168504 * 2
def baseEnd_3168504 : Nat := 1626965507693576447228321

theorem tailTrace_3168504 : CollatzResearch.WordTrace tailWord_3168504 prefixEnd_3168504 1626965507693576447228321 := by
  unfold tailWord_3168504
  simp only [CollatzResearch.WordTrace]
  refine ⟨57782417456529310123080283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77043223275372413497440377 57782417456529310123080283)
  ·
    refine ⟨86673626184793965184620425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57782417456529310123080283 86673626184793965184620425)
    ·
      refine ⟨65005219638595473888465319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86673626184793965184620425 65005219638595473888465319)
      ·
        refine ⟨97507829457893210832697979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65005219638595473888465319 97507829457893210832697979)
        ·
          refine ⟨146261744186839816249046969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97507829457893210832697979 146261744186839816249046969)
          ·
            refine ⟨109696308140129862186785227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146261744186839816249046969 109696308140129862186785227)
            ·
              refine ⟨164544462210194793280177841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109696308140129862186785227 164544462210194793280177841)
              ·
                refine ⟨123408346657646094960133381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164544462210194793280177841 123408346657646094960133381)
                ·
                  refine ⟨23139064998308642805025009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123408346657646094960133381 23139064998308642805025009)
                  ·
                    refine ⟨17354298748731482103768757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23139064998308642805025009 17354298748731482103768757)
                    ·
                      refine ⟨1626965507693576447228321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17354298748731482103768757 1626965507693576447228321)
                      ·
                        rfl

theorem cell23_3168504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3168504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168504 prefixEnd_3168504 := by exact prefixLift 3168504
  have htrace : WordTrace (prefixWord ++ tailWord_3168504) baseStart_3168504 baseEnd_3168504 := by
    simpa [prefixWord, tailWord_3168504, baseEnd_3168504] using wordTrace_append hprefix tailTrace_3168504
  have hstable : (prefixWord ++ tailWord_3168504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168504).length < 2 ^ (prefixWord ++ tailWord_3168504).sum := by decide
  have hdescent : baseEnd_3168504 < baseStart_3168504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168508 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_3168508 : Nat := 118140960795 + 3168508 * 2 ^ 59
def prefixEnd_3168508 : Nat := 4983230072969 + 3 ^ 40 * 3168508 * 2
def baseEnd_3168508 : Nat := 1626967561616194431578303

theorem tailTrace_3168508 : CollatzResearch.WordTrace tailWord_3168508 prefixEnd_3168508 1626967561616194431578303 := by
  unfold tailWord_3168508
  simp only [CollatzResearch.WordTrace]
  refine ⟨57782490402522064464653089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77043320536696085952870785 57782490402522064464653089)
  ·
    refine ⟨43336867801891548348489817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57782490402522064464653089 43336867801891548348489817)
    ·
      refine ⟨32502650851418661261367363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43336867801891548348489817 32502650851418661261367363)
      ·
        refine ⟨48753976277127991892051045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32502650851418661261367363 48753976277127991892051045)
        ·
          refine ⟨9141370551961498479759571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48753976277127991892051045 9141370551961498479759571)
          ·
            refine ⟨13712055827942247719639357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141370551961498479759571 13712055827942247719639357)
            ·
              refine ⟨5142020935478342894864759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13712055827942247719639357 5142020935478342894864759)
              ·
                refine ⟨7713031403217514342297139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142020935478342894864759 7713031403217514342297139)
                ·
                  refine ⟨11569547104826271513445709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7713031403217514342297139 11569547104826271513445709)
                  ·
                    refine ⟨4338580164309851817542141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11569547104826271513445709 4338580164309851817542141)
                    ·
                      refine ⟨1626967561616194431578303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4338580164309851817542141 1626967561616194431578303)
                      ·
                        rfl

theorem cell23_3168508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_3168508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168508 prefixEnd_3168508 := by exact prefixLift 3168508
  have htrace : WordTrace (prefixWord ++ tailWord_3168508) baseStart_3168508 baseEnd_3168508 := by
    simpa [prefixWord, tailWord_3168508, baseEnd_3168508] using wordTrace_append hprefix tailTrace_3168508
  have hstable : (prefixWord ++ tailWord_3168508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168508).length < 2 ^ (prefixWord ++ tailWord_3168508).sum := by decide
  have hdescent : baseEnd_3168508 < baseStart_3168508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168535 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 1, 3, 2]
def baseStart_3168535 : Nat := 118140960795 + 3168535 * 2 ^ 59
def prefixEnd_3168535 : Nat := 4983230072969 + 3 ^ 40 * 3168535 * 2
def baseEnd_3168535 : Nat := 1626981425593865825940679

theorem tailTrace_3168535 : CollatzResearch.WordTrace tailWord_3168535 prefixEnd_3168535 1626981425593865825940679 := by
  unfold tailWord_3168535
  simp only [CollatzResearch.WordTrace]
  refine ⟨115565965575946312540539059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77043977050630875027026039 115565965575946312540539059)
  ·
    refine ⟨173348948363919468810808589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115565965575946312540539059 173348948363919468810808589)
    ·
      refine ⟨65005855636469800804053221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173348948363919468810808589 65005855636469800804053221)
      ·
        refine ⟨12188597931838087650759979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65005855636469800804053221 12188597931838087650759979)
        ·
          refine ⟨18282896897757131476139969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12188597931838087650759979 18282896897757131476139969)
          ·
            refine ⟨13712172673317848607104977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18282896897757131476139969 13712172673317848607104977)
            ·
              refine ⟨10284129504988386455328733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13712172673317848607104977 10284129504988386455328733)
              ·
                refine ⟨3856548564370644920748275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10284129504988386455328733 3856548564370644920748275)
                ·
                  refine ⟨5784822846555967381122413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856548564370644920748275 5784822846555967381122413)
                  ·
                    refine ⟨2169308567458487767920905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5784822846555967381122413 2169308567458487767920905)
                    ·
                      refine ⟨1626981425593865825940679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169308567458487767920905 1626981425593865825940679)
                      ·
                        rfl

theorem cell23_3168535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_3168535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168535 prefixEnd_3168535 := by exact prefixLift 3168535
  have htrace : WordTrace (prefixWord ++ tailWord_3168535) baseStart_3168535 baseEnd_3168535 := by
    simpa [prefixWord, tailWord_3168535, baseEnd_3168535] using wordTrace_append hprefix tailTrace_3168535
  have hstable : (prefixWord ++ tailWord_3168535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168535).length < 2 ^ (prefixWord ++ tailWord_3168535).sum := by decide
  have hdescent : baseEnd_3168535 < baseStart_3168535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168542 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3168542 : Nat := 118140960795 + 3168542 * 2 ^ 59
def prefixEnd_3168542 : Nat := 4983230072969 + 3 ^ 40 * 3168542 * 2
def baseEnd_3168542 : Nat := 1626985019958447298553147

theorem tailTrace_3168542 : CollatzResearch.WordTrace tailWord_3168542 prefixEnd_3168542 1626985019958447298553147 := by
  unfold tailWord_3168542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14445777610865119092005485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77044147257947301824029253 14445777610865119092005485)
  ·
    refine ⟨5417166604074419659502057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14445777610865119092005485 5417166604074419659502057)
    ·
      refine ⟨4062874953055814744626543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5417166604074419659502057 4062874953055814744626543)
      ·
        refine ⟨6094312429583722116939815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062874953055814744626543 6094312429583722116939815)
        ·
          refine ⟨9141468644375583175409723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094312429583722116939815 9141468644375583175409723)
          ·
            refine ⟨13712202966563374763114585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141468644375583175409723 13712202966563374763114585)
            ·
              refine ⟨10284152224922531072335939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13712202966563374763114585 10284152224922531072335939)
              ·
                refine ⟨15426228337383796608503909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10284152224922531072335939 15426228337383796608503909)
                ·
                  refine ⟨2892417813259461864094483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15426228337383796608503909 2892417813259461864094483)
                  ·
                    refine ⟨4338626719889192796141725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892417813259461864094483 4338626719889192796141725)
                    ·
                      refine ⟨1626985019958447298553147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4338626719889192796141725 1626985019958447298553147)
                      ·
                        rfl

theorem cell23_3168542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3168542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168542 prefixEnd_3168542 := by exact prefixLift 3168542
  have htrace : WordTrace (prefixWord ++ tailWord_3168542) baseStart_3168542 baseEnd_3168542 := by
    simpa [prefixWord, tailWord_3168542, baseEnd_3168542] using wordTrace_append hprefix tailTrace_3168542
  have hstable : (prefixWord ++ tailWord_3168542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168542).length < 2 ^ (prefixWord ++ tailWord_3168542).sum := by decide
  have hdescent : baseEnd_3168542 < baseStart_3168542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168581 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_3168581 : Nat := 118140960795 + 3168581 * 2 ^ 59
def prefixEnd_3168581 : Nat := 4983230072969 + 3 ^ 40 * 3168581 * 2
def baseEnd_3168581 : Nat := 1627005045703972645965467

theorem tailTrace_3168581 : CollatzResearch.WordTrace tailWord_3168581 prefixEnd_3168581 1627005045703972645965467 := by
  unfold tailWord_3168581
  simp only [CollatzResearch.WordTrace]
  refine ⟨115567643333779662396713597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77045095555853108264475731 115567643333779662396713597)
  ·
    refine ⟨43337866250167373398767599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115567643333779662396713597 43337866250167373398767599)
    ·
      refine ⟨65006799375251060098151399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43337866250167373398767599 65006799375251060098151399)
      ·
        refine ⟨97510199062876590147227099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65006799375251060098151399 97510199062876590147227099)
        ·
          refine ⟨146265298594314885220840649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97510199062876590147227099 146265298594314885220840649)
          ·
            refine ⟨109698973945736163915630487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146265298594314885220840649 109698973945736163915630487)
            ·
              refine ⟨164548460918604245873445731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109698973945736163915630487 164548460918604245873445731)
              ·
                refine ⟨246822691377906368810168597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164548460918604245873445731 246822691377906368810168597)
                ·
                  refine ⟨11569813658339361037976653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246822691377906368810168597 11569813658339361037976653)
                  ·
                    refine ⟨4338680121877260389241245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11569813658339361037976653 4338680121877260389241245)
                    ·
                      refine ⟨1627005045703972645965467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4338680121877260389241245 1627005045703972645965467)
                      ·
                        rfl

theorem cell23_3168581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_3168581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168581 prefixEnd_3168581 := by exact prefixLift 3168581
  have htrace : WordTrace (prefixWord ++ tailWord_3168581) baseStart_3168581 baseEnd_3168581 := by
    simpa [prefixWord, tailWord_3168581, baseEnd_3168581] using wordTrace_append hprefix tailTrace_3168581
  have hstable : (prefixWord ++ tailWord_3168581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168581).length < 2 ^ (prefixWord ++ tailWord_3168581).sum := by decide
  have hdescent : baseEnd_3168581 < baseStart_3168581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168588 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 5]
def baseStart_3168588 : Nat := 118140960795 + 3168588 * 2 ^ 59
def prefixEnd_3168588 : Nat := 4983230072969 + 3 ^ 40 * 3168588 * 2
def baseEnd_3168588 : Nat := 180778737785394902064215

theorem tailTrace_3168588 : CollatzResearch.WordTrace tailWord_3168588 prefixEnd_3168588 180778737785394902064215 := by
  unfold tailWord_3168588
  simp only [CollatzResearch.WordTrace]
  refine ⟨57783949322377151296109209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77045265763169535061478945 57783949322377151296109209)
  ·
    refine ⟨43337961991782863472081907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57783949322377151296109209 43337961991782863472081907)
    ·
      refine ⟨65006942987674295208122861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43337961991782863472081907 65006942987674295208122861)
      ·
        refine ⟨24377603620377860703046073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65006942987674295208122861 24377603620377860703046073)
        ·
          refine ⟨18283202715283395527284555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24377603620377860703046073 18283202715283395527284555)
          ·
            refine ⟨27424804072925093290926833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18283202715283395527284555 27424804072925093290926833)
            ·
              refine ⟨20568603054693819968195125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27424804072925093290926833 20568603054693819968195125)
              ·
                refine ⟨1928306536377545622018293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20568603054693819968195125 1928306536377545622018293)
                ·
                  refine ⟨180778737785394902064215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928306536377545622018293 180778737785394902064215)
                  ·
                    rfl

theorem cell23_3168588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_3168588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168588 prefixEnd_3168588 := by exact prefixLift 3168588
  have htrace : WordTrace (prefixWord ++ tailWord_3168588) baseStart_3168588 baseEnd_3168588 := by
    simpa [prefixWord, tailWord_3168588, baseEnd_3168588] using wordTrace_append hprefix tailTrace_3168588
  have hstable : (prefixWord ++ tailWord_3168588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168588).length < 2 ^ (prefixWord ++ tailWord_3168588).sum := by decide
  have hdescent : baseEnd_3168588 < baseStart_3168588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168611 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3168611 : Nat := 118140960795 + 3168611 * 2 ^ 59
def prefixEnd_3168611 : Nat := 4983230072969 + 3 ^ 40 * 3168611 * 2
def baseEnd_3168611 : Nat := 1627020450123607528590329

theorem tailTrace_3168611 : CollatzResearch.WordTrace tailWord_3168611 prefixEnd_3168611 1627020450123607528590329 := by
  unfold tailWord_3168611
  simp only [CollatzResearch.WordTrace]
  refine ⟨115568737523670977520305687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77045825015780651680203791 115568737523670977520305687)
  ·
    refine ⟨173353106285506466280458531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115568737523670977520305687 173353106285506466280458531)
    ·
      refine ⟨260029659428259699420687797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173353106285506466280458531 260029659428259699420687797)
      ·
        refine ⟨24377780571399346820689481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260029659428259699420687797 24377780571399346820689481)
        ·
          refine ⟨18283335428549510115517111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24377780571399346820689481 18283335428549510115517111)
          ·
            refine ⟨27425003142824265173275667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18283335428549510115517111 27425003142824265173275667)
            ·
              refine ⟨41137504714236397759913501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27425003142824265173275667 41137504714236397759913501)
              ·
                refine ⟨15426564267838649159967563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41137504714236397759913501 15426564267838649159967563)
                ·
                  refine ⟨23139846401757973739951345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15426564267838649159967563 23139846401757973739951345)
                  ·
                    refine ⟨17354884801318480304963509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23139846401757973739951345 17354884801318480304963509)
                    ·
                      refine ⟨1627020450123607528590329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17354884801318480304963509 1627020450123607528590329)
                      ·
                        rfl

theorem cell23_3168611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3168611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168611 prefixEnd_3168611 := by exact prefixLift 3168611
  have htrace : WordTrace (prefixWord ++ tailWord_3168611) baseStart_3168611 baseEnd_3168611 := by
    simpa [prefixWord, tailWord_3168611, baseEnd_3168611] using wordTrace_append hprefix tailTrace_3168611
  have hstable : (prefixWord ++ tailWord_3168611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168611).length < 2 ^ (prefixWord ++ tailWord_3168611).sum := by decide
  have hdescent : baseEnd_3168611 < baseStart_3168611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168648 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 5, 4]
def baseStart_3168648 : Nat := 118140960795 + 3168648 * 2 ^ 59
def prefixEnd_3168648 : Nat := 4983230072969 + 3 ^ 40 * 3168648 * 2
def baseEnd_3168648 : Nat := 542346482969274627942553

theorem tailTrace_3168648 : CollatzResearch.WordTrace tailWord_3168648 prefixEnd_3168648 542346482969274627942553 := by
  unfold tailWord_3168648
  simp only [CollatzResearch.WordTrace]
  refine ⟨57785043512268466419701299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77046724683024621892935065 57785043512268466419701299)
  ·
    refine ⟨86677565268402699629551949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57785043512268466419701299 86677565268402699629551949)
    ·
      refine ⟨32504086975651012361081981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86677565268402699629551949 32504086975651012361081981)
      ·
        refine ⟨12189032615869129635405743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32504086975651012361081981 12189032615869129635405743)
        ·
          refine ⟨18283548923803694453108615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189032615869129635405743 18283548923803694453108615)
          ·
            refine ⟨27425323385705541679662923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18283548923803694453108615 27425323385705541679662923)
            ·
              refine ⟨41137985078558312519494385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27425323385705541679662923 41137985078558312519494385)
              ·
                refine ⟨30853488808918734389620789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41137985078558312519494385 30853488808918734389620789)
                ·
                  refine ⟨2892514575836131349026949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30853488808918734389620789 2892514575836131349026949)
                  ·
                    refine ⟨542346482969274627942553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2892514575836131349026949 542346482969274627942553)
                    ·
                      rfl

theorem cell23_3168648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_3168648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168648 prefixEnd_3168648 := by exact prefixLift 3168648
  have htrace : WordTrace (prefixWord ++ tailWord_3168648) baseStart_3168648 baseEnd_3168648 := by
    simpa [prefixWord, tailWord_3168648, baseEnd_3168648] using wordTrace_append hprefix tailTrace_3168648
  have hstable : (prefixWord ++ tailWord_3168648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168648).length < 2 ^ (prefixWord ++ tailWord_3168648).sum := by decide
  have hdescent : baseEnd_3168648 < baseStart_3168648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168651 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6]
def baseStart_3168651 : Nat := 118140960795 + 3168651 * 2 ^ 59
def prefixEnd_3168651 : Nat := 4983230072969 + 3 ^ 40 * 3168651 * 2
def baseEnd_3168651 : Nat := 1627040989349787372090145

theorem tailTrace_3168651 : CollatzResearch.WordTrace tailWord_3168651 prefixEnd_3168651 1627040989349787372090145 := by
  unfold tailWord_3168651
  simp only [CollatzResearch.WordTrace]
  refine ⟨115570196443526064351761807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77046797629017376234507871 115570196443526064351761807)
  ·
    refine ⟨173355294665289096527642711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115570196443526064351761807 173355294665289096527642711)
    ·
      refine ⟨260032941997933644791464067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173355294665289096527642711 260032941997933644791464067)
      ·
        refine ⟨390049412996900467187196101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260032941997933644791464067 390049412996900467187196101)
        ·
          refine ⟨73134264936918837597599269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390049412996900467187196101 73134264936918837597599269)
          ·
            refine ⟨13712674675672282049549863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73134264936918837597599269 13712674675672282049549863)
            ·
              refine ⟨20569012013508423074324795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13712674675672282049549863 20569012013508423074324795)
              ·
                refine ⟨30853518020262634611487193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20569012013508423074324795 30853518020262634611487193)
                ·
                  refine ⟨23140138515196975958615395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30853518020262634611487193 23140138515196975958615395)
                  ·
                    refine ⟨34710207772795463937923093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23140138515196975958615395 34710207772795463937923093)
                    ·
                      refine ⟨1627040989349787372090145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34710207772795463937923093 1627040989349787372090145)
                      ·
                        rfl

theorem cell23_3168651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_3168651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168651 prefixEnd_3168651 := by exact prefixLift 3168651
  have htrace : WordTrace (prefixWord ++ tailWord_3168651) baseStart_3168651 baseEnd_3168651 := by
    simpa [prefixWord, tailWord_3168651, baseEnd_3168651] using wordTrace_append hprefix tailTrace_3168651
  have hstable : (prefixWord ++ tailWord_3168651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168651).length < 2 ^ (prefixWord ++ tailWord_3168651).sum := by decide
  have hdescent : baseEnd_3168651 < baseStart_3168651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168665 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 1, 4]
def baseStart_3168665 : Nat := 118140960795 + 3168665 * 2 ^ 59
def prefixEnd_3168665 : Nat := 4983230072969 + 3 ^ 40 * 3168665 * 2
def baseEnd_3168665 : Nat := 542349392692983439105027

theorem tailTrace_3168665 : CollatzResearch.WordTrace tailWord_3168665 prefixEnd_3168665 542349392692983439105027 := by
  unfold tailWord_3168665
  simp only [CollatzResearch.WordTrace]
  refine ⟨115570707065475344742771449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77047138043650229828514299 115570707065475344742771449)
  ·
    refine ⟨86678030299106508557078587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115570707065475344742771449 86678030299106508557078587)
    ·
      refine ⟨130017045448659762835617881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86678030299106508557078587 130017045448659762835617881)
      ·
        refine ⟨97512784086494822126713411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130017045448659762835617881 97512784086494822126713411)
        ·
          refine ⟨146269176129742233190070117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97512784086494822126713411 146269176129742233190070117)
          ·
            refine ⟨27425470524326668723138147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146269176129742233190070117 27425470524326668723138147)
            ·
              refine ⟨41138205786490003084707221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27425470524326668723138147 41138205786490003084707221)
              ·
                refine ⟨1928353396241718894595651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41138205786490003084707221 1928353396241718894595651)
                ·
                  refine ⟨2892530094362578341893477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928353396241718894595651 2892530094362578341893477)
                  ·
                    refine ⟨542349392692983439105027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2892530094362578341893477 542349392692983439105027)
                    ·
                      rfl

theorem cell23_3168665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 4].length) (baseStart_3168665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168665 prefixEnd_3168665 := by exact prefixLift 3168665
  have htrace : WordTrace (prefixWord ++ tailWord_3168665) baseStart_3168665 baseEnd_3168665 := by
    simpa [prefixWord, tailWord_3168665, baseEnd_3168665] using wordTrace_append hprefix tailTrace_3168665
  have hstable : (prefixWord ++ tailWord_3168665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168665).length < 2 ^ (prefixWord ++ tailWord_3168665).sum := by decide
  have hdescent : baseEnd_3168665 < baseStart_3168665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168728 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3168728 : Nat := 118140960795 + 3168728 * 2 ^ 59
def prefixEnd_3168728 : Nat := 4983230072969 + 3 ^ 40 * 3168728 * 2
def baseEnd_3168728 : Nat := 1627080527360183570827291

theorem tailTrace_3168728 : CollatzResearch.WordTrace tailWord_3168728 prefixEnd_3168728 1627080527360183570827291 := by
  unfold tailWord_3168728
  simp only [CollatzResearch.WordTrace]
  refine ⟨57786502432123553251157419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77048669909498071001543225 57786502432123553251157419)
  ·
    refine ⟨86679753648185329876736129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57786502432123553251157419 86679753648185329876736129)
    ·
      refine ⟨65009815236138997407552097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86679753648185329876736129 65009815236138997407552097)
      ·
        refine ⟨48757361427104248055664073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65009815236138997407552097 48757361427104248055664073)
        ·
          refine ⟨36568021070328186041748055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48757361427104248055664073 36568021070328186041748055)
          ·
            refine ⟨54852031605492279062622083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36568021070328186041748055 54852031605492279062622083)
            ·
              refine ⟨82278047408238418593933125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54852031605492279062622083 82278047408238418593933125)
              ·
                refine ⟨15427133889044703486362461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82278047408238418593933125 15427133889044703486362461)
                ·
                  refine ⟨5785175208391763807385923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15427133889044703486362461 5785175208391763807385923)
                  ·
                    refine ⟨8677762812587645711078885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5785175208391763807385923 8677762812587645711078885)
                    ·
                      refine ⟨1627080527360183570827291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8677762812587645711078885 1627080527360183570827291)
                      ·
                        rfl

theorem cell23_3168728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3168728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168728 prefixEnd_3168728 := by exact prefixLift 3168728
  have htrace : WordTrace (prefixWord ++ tailWord_3168728) baseStart_3168728 baseEnd_3168728 := by
    simpa [prefixWord, tailWord_3168728, baseEnd_3168728] using wordTrace_append hprefix tailTrace_3168728
  have hstable : (prefixWord ++ tailWord_3168728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168728).length < 2 ^ (prefixWord ++ tailWord_3168728).sum := by decide
  have hdescent : baseEnd_3168728 < baseStart_3168728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168749 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3168749 : Nat := 118140960795 + 3168749 * 2 ^ 59
def prefixEnd_3168749 : Nat := 4983230072969 + 3 ^ 40 * 3168749 * 2
def baseEnd_3168749 : Nat := 1627091310453927988664695

theorem tailTrace_3168749 : CollatzResearch.WordTrace tailWord_3168749 prefixEnd_3168749 1627091310453927988664695 := by
  unfold tailWord_3168749
  simp only [CollatzResearch.WordTrace]
  refine ⟨115573770797171027088829301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77049180531447351392552867 115573770797171027088829301)
  ·
    refine ⟨10835041012234783789577747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115573770797171027088829301 10835041012234783789577747)
    ·
      refine ⟨16252561518352175684366621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10835041012234783789577747 16252561518352175684366621)
      ·
        refine ⟨6094710569382065881637483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16252561518352175684366621 6094710569382065881637483)
        ·
          refine ⟨9142065854073098822456225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094710569382065881637483 9142065854073098822456225)
          ·
            refine ⟨6856549390554824116842169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9142065854073098822456225 6856549390554824116842169)
            ·
              refine ⟨5142412042916118087631627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6856549390554824116842169 5142412042916118087631627)
              ·
                refine ⟨7713618064374177131447441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142412042916118087631627 7713618064374177131447441)
                ·
                  refine ⟨5785213548280632848585581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7713618064374177131447441 5785213548280632848585581)
                  ·
                    refine ⟨2169455080605237318219593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5785213548280632848585581 2169455080605237318219593)
                    ·
                      refine ⟨1627091310453927988664695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169455080605237318219593 1627091310453927988664695)
                      ·
                        rfl

theorem cell23_3168749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3168749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168749 prefixEnd_3168749 := by exact prefixLift 3168749
  have htrace : WordTrace (prefixWord ++ tailWord_3168749) baseStart_3168749 baseEnd_3168749 := by
    simpa [prefixWord, tailWord_3168749, baseEnd_3168749] using wordTrace_append hprefix tailTrace_3168749
  have hstable : (prefixWord ++ tailWord_3168749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168749).length < 2 ^ (prefixWord ++ tailWord_3168749).sum := by decide
  have hdescent : baseEnd_3168749 < baseStart_3168749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168772 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_3168772 : Nat := 118140960795 + 3168772 * 2 ^ 59
def prefixEnd_3168772 : Nat := 4983230072969 + 3 ^ 40 * 3168772 * 2
def baseEnd_3168772 : Nat := 542367706836327132892363

theorem tailTrace_3168772 : CollatzResearch.WordTrace tailWord_3168772 prefixEnd_3168772 542367706836327132892363 := by
  unfold tailWord_3168772
  simp only [CollatzResearch.WordTrace]
  refine ⟨57787304838043851008458285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77049739784058468011277713 57787304838043851008458285)
  ·
    refine ⟨21670239314266444128171857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57787304838043851008458285 21670239314266444128171857)
    ·
      refine ⟨16252679485699833096128893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21670239314266444128171857 16252679485699833096128893)
      ·
        refine ⟨6094754807137437411048335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16252679485699833096128893 6094754807137437411048335)
        ·
          refine ⟨9142132210706156116572503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094754807137437411048335 9142132210706156116572503)
          ·
            refine ⟨13713198316059234174858755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9142132210706156116572503 13713198316059234174858755)
            ·
              refine ⟨20569797474088851262288133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13713198316059234174858755 20569797474088851262288133)
              ·
                refine ⟨3856837026391659611679025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20569797474088851262288133 3856837026391659611679025)
                ·
                  refine ⟨2892627769793744708759269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856837026391659611679025 2892627769793744708759269)
                  ·
                    refine ⟨542367706836327132892363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2892627769793744708759269 542367706836327132892363)
                    ·
                      rfl

theorem cell23_3168772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_3168772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168772 prefixEnd_3168772 := by exact prefixLift 3168772
  have htrace : WordTrace (prefixWord ++ tailWord_3168772) baseStart_3168772 baseEnd_3168772 := by
    simpa [prefixWord, tailWord_3168772, baseEnd_3168772] using wordTrace_append hprefix tailTrace_3168772
  have hstable : (prefixWord ++ tailWord_3168772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168772).length < 2 ^ (prefixWord ++ tailWord_3168772).sum := by decide
  have hdescent : baseEnd_3168772 < baseStart_3168772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168829 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3168829 : Nat := 118140960795 + 3168829 * 2 ^ 59
def prefixEnd_3168829 : Nat := 4983230072969 + 3 ^ 40 * 3168829 * 2
def baseEnd_3168829 : Nat := 1627132388906287675664327

theorem tailTrace_3168829 : CollatzResearch.WordTrace tailWord_3168829 prefixEnd_3168829 1627132388906287675664327 := by
  unfold tailWord_3168829
  simp only [CollatzResearch.WordTrace]
  refine ⟨115576688636881200751741541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77051125757920800501161027 115576688636881200751741541)
  ·
    refine ⟨21670629119415225140951539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115576688636881200751741541 21670629119415225140951539)
    ·
      refine ⟨32505943679122837711427309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21670629119415225140951539 32505943679122837711427309)
      ·
        refine ⟨12189728879671064141785241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32505943679122837711427309 12189728879671064141785241)
        ·
          refine ⟨9142296659753298106338931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12189728879671064141785241 9142296659753298106338931)
          ·
            refine ⟨13713444989629947159508397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9142296659753298106338931 13713444989629947159508397)
            ·
              refine ⟨5142541871111230184815649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13713444989629947159508397 5142541871111230184815649)
              ·
                refine ⟨3856906403333422638611737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5142541871111230184815649 3856906403333422638611737)
                ·
                  refine ⟨2892679802500066978958803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856906403333422638611737 2892679802500066978958803)
                  ·
                    refine ⟨4339019703750100468438205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892679802500066978958803 4339019703750100468438205)
                    ·
                      refine ⟨1627132388906287675664327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339019703750100468438205 1627132388906287675664327)
                      ·
                        rfl

theorem cell23_3168829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3168829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168829 prefixEnd_3168829 := by exact prefixLift 3168829
  have htrace : WordTrace (prefixWord ++ tailWord_3168829) baseStart_3168829 baseEnd_3168829 := by
    simpa [prefixWord, tailWord_3168829, baseEnd_3168829] using wordTrace_append hprefix tailTrace_3168829
  have hstable : (prefixWord ++ tailWord_3168829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168829).length < 2 ^ (prefixWord ++ tailWord_3168829).sum := by decide
  have hdescent : baseEnd_3168829 < baseStart_3168829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168835 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 3, 4, 2]
def baseStart_3168835 : Nat := 118140960795 + 3168835 * 2 ^ 59
def prefixEnd_3168835 : Nat := 4983230072969 + 3 ^ 40 * 3168835 * 2
def baseEnd_3168835 : Nat := 1627135469790214652189299

theorem tailTrace_3168835 : CollatzResearch.WordTrace tailWord_3168835 prefixEnd_3168835 1627135469790214652189299 := by
  unfold tailWord_3168835
  simp only [CollatzResearch.WordTrace]
  refine ⟨115576907474859463776459959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77051271649906309184306639 115576907474859463776459959)
  ·
    refine ⟨173365361212289195664689939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115576907474859463776459959 173365361212289195664689939)
    ·
      refine ⟨260048041818433793497034909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173365361212289195664689939 260048041818433793497034909)
      ·
        refine ⟨97518015681912672561388091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260048041818433793497034909 97518015681912672561388091)
        ·
          refine ⟨146277023522869008842082137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97518015681912672561388091 146277023522869008842082137)
          ·
            refine ⟨109707767642151756631561603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146277023522869008842082137 109707767642151756631561603)
            ·
              refine ⟨164561651463227634947342405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109707767642151756631561603 164561651463227634947342405)
              ·
                refine ⟨30855309649355181552626701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164561651463227634947342405 30855309649355181552626701)
                ·
                  refine ⟨11570741118508193082235013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30855309649355181552626701 11570741118508193082235013)
                  ·
                    refine ⟨2169513959720286202919065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11570741118508193082235013 2169513959720286202919065)
                    ·
                      refine ⟨1627135469790214652189299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169513959720286202919065 1627135469790214652189299)
                      ·
                        rfl

theorem cell23_3168835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_3168835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168835 prefixEnd_3168835 := by exact prefixLift 3168835
  have htrace : WordTrace (prefixWord ++ tailWord_3168835) baseStart_3168835 baseEnd_3168835 := by
    simpa [prefixWord, tailWord_3168835, baseEnd_3168835] using wordTrace_append hprefix tailTrace_3168835
  have hstable : (prefixWord ++ tailWord_3168835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168835).length < 2 ^ (prefixWord ++ tailWord_3168835).sum := by decide
  have hdescent : baseEnd_3168835 < baseStart_3168835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168848 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_3168848 : Nat := 118140960795 + 3168848 * 2 ^ 59
def prefixEnd_3168848 : Nat := 4983230072969 + 3 ^ 40 * 3168848 * 2
def baseEnd_3168848 : Nat := 1627142145038723101326739

theorem tailTrace_3168848 : CollatzResearch.WordTrace tailWord_3168848 prefixEnd_3168848 1627142145038723101326739 := by
  unfold tailWord_3168848
  simp only [CollatzResearch.WordTrace]
  refine ⟨57788690811906183498341599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77051587749208244664455465 57788690811906183498341599)
  ·
    refine ⟨86683036217859275247512399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57788690811906183498341599 86683036217859275247512399)
    ·
      refine ⟨130024554326788912871268599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86683036217859275247512399 130024554326788912871268599)
      ·
        refine ⟨195036831490183369306902899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130024554326788912871268599 195036831490183369306902899)
        ·
          refine ⟨292555247235275053960354349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195036831490183369306902899 292555247235275053960354349)
          ·
            refine ⟨109708217713228145235132881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292555247235275053960354349 109708217713228145235132881)
            ·
              refine ⟨82281163284921108926349661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109708217713228145235132881 82281163284921108926349661)
              ·
                refine ⟨30855436231845415847381123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82281163284921108926349661 30855436231845415847381123)
                ·
                  refine ⟨46283154347768123771071685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30855436231845415847381123 46283154347768123771071685)
                  ·
                    refine ⟨8678091440206523207075941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46283154347768123771071685 8678091440206523207075941)
                    ·
                      refine ⟨1627142145038723101326739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8678091440206523207075941 1627142145038723101326739)
                      ·
                        rfl

theorem cell23_3168848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_3168848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168848 prefixEnd_3168848 := by exact prefixLift 3168848
  have htrace : WordTrace (prefixWord ++ tailWord_3168848) baseStart_3168848 baseEnd_3168848 := by
    simpa [prefixWord, tailWord_3168848, baseEnd_3168848] using wordTrace_append hprefix tailTrace_3168848
  have hstable : (prefixWord ++ tailWord_3168848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168848).length < 2 ^ (prefixWord ++ tailWord_3168848).sum := by decide
  have hdescent : baseEnd_3168848 < baseStart_3168848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168872 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3168872 : Nat := 118140960795 + 3168872 * 2 ^ 59
def prefixEnd_3168872 : Nat := 4983230072969 + 3 ^ 40 * 3168872 * 2
def baseEnd_3168872 : Nat := 1627154468574431007426629

theorem tailTrace_3168872 : CollatzResearch.WordTrace tailWord_3168872 prefixEnd_3168872 1627154468574431007426629 := by
  unfold tailWord_3168872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57789128487862709547778435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77052171317150279397037913 57789128487862709547778435)
  ·
    refine ⟨86683692731794064321667653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57789128487862709547778435 86683692731794064321667653)
    ·
      refine ⟨16253192387211387060312685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86683692731794064321667653 16253192387211387060312685)
      ·
        refine ⟨6094947145204270147617257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16253192387211387060312685 6094947145204270147617257)
        ·
          refine ⟨4571210358903202610712943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6094947145204270147617257 4571210358903202610712943)
          ·
            refine ⟨6856815538354803916069415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571210358903202610712943 6856815538354803916069415)
            ·
              refine ⟨10285223307532205874104123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6856815538354803916069415 10285223307532205874104123)
              ·
                refine ⟨15427834961298308811156185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10285223307532205874104123 15427834961298308811156185)
                ·
                  refine ⟨11570876220973731608367139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15427834961298308811156185 11570876220973731608367139)
                  ·
                    refine ⟨17356314331460597412550709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11570876220973731608367139 17356314331460597412550709)
                    ·
                      refine ⟨1627154468574431007426629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17356314331460597412550709 1627154468574431007426629)
                      ·
                        rfl

theorem cell23_3168872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3168872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168872 prefixEnd_3168872 := by exact prefixLift 3168872
  have htrace : WordTrace (prefixWord ++ tailWord_3168872) baseStart_3168872 baseEnd_3168872 := by
    simpa [prefixWord, tailWord_3168872, baseEnd_3168872] using wordTrace_append hprefix tailTrace_3168872
  have hstable : (prefixWord ++ tailWord_3168872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168872).length < 2 ^ (prefixWord ++ tailWord_3168872).sum := by decide
  have hdescent : baseEnd_3168872 < baseStart_3168872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168875 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 5]
def baseStart_3168875 : Nat := 118140960795 + 3168875 * 2 ^ 59
def prefixEnd_3168875 : Nat := 4983230072969 + 3 ^ 40 * 3168875 * 2
def baseEnd_3168875 : Nat := 180795112112932721743235

theorem tailTrace_3168875 : CollatzResearch.WordTrace tailWord_3168875 prefixEnd_3168875 180795112112932721743235 := by
  unfold tailWord_3168875
  simp only [CollatzResearch.WordTrace]
  refine ⟨115578366394714550607916079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77052244263143033738610719 115578366394714550607916079)
  ·
    refine ⟨173367549592071825911874119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115578366394714550607916079 173367549592071825911874119)
    ·
      refine ⟨260051324388107738867811179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173367549592071825911874119 260051324388107738867811179)
      ·
        refine ⟨390076986582161608301716769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260051324388107738867811179 390076986582161608301716769)
        ·
          refine ⟨292557739936621206226287577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390076986582161608301716769 292557739936621206226287577)
          ·
            refine ⟨219418304952465904669715683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292557739936621206226287577 219418304952465904669715683)
            ·
              refine ⟨329127457428698857004573525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219418304952465904669715683 329127457428698857004573525)
              ·
                refine ⟨1928481195871282365261173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 329127457428698857004573525 1928481195871282365261173)
                ·
                  refine ⟨180795112112932721743235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928481195871282365261173 180795112112932721743235)
                  ·
                    rfl

theorem cell23_3168875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 5].length) (baseStart_3168875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168875 prefixEnd_3168875 := by exact prefixLift 3168875
  have htrace : WordTrace (prefixWord ++ tailWord_3168875) baseStart_3168875 baseEnd_3168875 := by
    simpa [prefixWord, tailWord_3168875, baseEnd_3168875] using wordTrace_append hprefix tailTrace_3168875
  have hstable : (prefixWord ++ tailWord_3168875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168875).length < 2 ^ (prefixWord ++ tailWord_3168875).sum := by decide
  have hdescent : baseEnd_3168875 < baseStart_3168875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168925 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3168925 : Nat := 118140960795 + 3168925 * 2 ^ 59
def prefixEnd_3168925 : Nat := 4983230072969 + 3 ^ 40 * 3168925 * 2
def baseEnd_3168925 : Nat := 1627181683049119300063885

theorem tailTrace_3168925 : CollatzResearch.WordTrace tailWord_3168925 prefixEnd_3168925 1627181683049119300063885 := by
  unfold tailWord_3168925
  simp only [CollatzResearch.WordTrace]
  refine ⟨115580190044533409147236229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77053460029688939431490819 115580190044533409147236229)
  ·
    refine ⟨21671285633350014215106793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115580190044533409147236229 21671285633350014215106793)
    ·
      refine ⟨16253464225012510661330095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21671285633350014215106793 16253464225012510661330095)
      ·
        refine ⟨24380196337518765991995143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16253464225012510661330095 24380196337518765991995143)
        ·
          refine ⟨36570294506278148987992715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24380196337518765991995143 36570294506278148987992715)
          ·
            refine ⟨54855441759417223481989073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36570294506278148987992715 54855441759417223481989073)
            ·
              refine ⟨41141581319562917611491805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54855441759417223481989073 41141581319562917611491805)
              ·
                refine ⟨15428092994836094104309427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41141581319562917611491805 15428092994836094104309427)
                ·
                  refine ⟨23142139492254141156464141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15428092994836094104309427 23142139492254141156464141)
                  ·
                    refine ⟨8678302309595302933674053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23142139492254141156464141 8678302309595302933674053)
                    ·
                      refine ⟨1627181683049119300063885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8678302309595302933674053 1627181683049119300063885)
                      ·
                        rfl

theorem cell23_3168925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3168925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168925 prefixEnd_3168925 := by exact prefixLift 3168925
  have htrace : WordTrace (prefixWord ++ tailWord_3168925) baseStart_3168925 baseEnd_3168925 := by
    simpa [prefixWord, tailWord_3168925, baseEnd_3168925] using wordTrace_append hprefix tailTrace_3168925
  have hstable : (prefixWord ++ tailWord_3168925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168925).length < 2 ^ (prefixWord ++ tailWord_3168925).sum := by decide
  have hdescent : baseEnd_3168925 < baseStart_3168925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168973 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3168973 : Nat := 118140960795 + 3168973 * 2 ^ 59
def prefixEnd_3168973 : Nat := 4983230072969 + 3 ^ 40 * 3168973 * 2
def baseEnd_3168973 : Nat := 542402110040178370754555

theorem tailTrace_3168973 : CollatzResearch.WordTrace tailWord_3168973 prefixEnd_3168973 542402110040178370754555 := by
  unfold tailWord_3168973
  simp only [CollatzResearch.WordTrace]
  refine ⟨115581940748359513344983573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77054627165573008896655715 115581940748359513344983573)
  ·
    refine ⟨5417903472579352188046105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115581940748359513344983573 5417903472579352188046105)
    ·
      refine ⟨4063427604434514141034579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5417903472579352188046105 4063427604434514141034579)
      ·
        refine ⟨6095141406651771211551869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063427604434514141034579 6095141406651771211551869)
        ·
          refine ⟨2285678027494414204331951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6095141406651771211551869 2285678027494414204331951)
          ·
            refine ⟨3428517041241621306497927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285678027494414204331951 3428517041241621306497927)
            ·
              refine ⟨5142775561862431959746891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428517041241621306497927 5142775561862431959746891)
              ·
                refine ⟨7714163342793647939620337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142775561862431959746891 7714163342793647939620337)
                ·
                  refine ⟨5785622507095235954715253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7714163342793647939620337 5785622507095235954715253)
                  ·
                    refine ⟨542402110040178370754555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5785622507095235954715253 542402110040178370754555)
                    ·
                      rfl

theorem cell23_3168973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3168973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168973 prefixEnd_3168973 := by exact prefixLift 3168973
  have htrace : WordTrace (prefixWord ++ tailWord_3168973) baseStart_3168973 baseEnd_3168973 := by
    simpa [prefixWord, tailWord_3168973, baseEnd_3168973] using wordTrace_append hprefix tailTrace_3168973
  have hstable : (prefixWord ++ tailWord_3168973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168973).length < 2 ^ (prefixWord ++ tailWord_3168973).sum := by decide
  have hdescent : baseEnd_3168973 < baseStart_3168973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3168992 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 7, 1, 3]
def baseStart_3168992 : Nat := 118140960795 + 3168992 * 2 ^ 59
def prefixEnd_3168992 : Nat := 4983230072969 + 3 ^ 40 * 3168992 * 2
def baseEnd_3168992 : Nat := 1627216086252970537926077

theorem tailTrace_3168992 : CollatzResearch.WordTrace tailWord_3168992 prefixEnd_3168992 1627216086252970537926077 := by
  unfold tailWord_3168992
  simp only [CollatzResearch.WordTrace]
  refine ⟨57791316867645339794962615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77055089156860453059950153 57791316867645339794962615)
  ·
    refine ⟨86686975301468009692443923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57791316867645339794962615 86686975301468009692443923)
    ·
      refine ⟨130030462952202014538665885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86686975301468009692443923 130030462952202014538665885)
      ·
        refine ⟨48761423607075755451999707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130030462952202014538665885 48761423607075755451999707)
        ·
          refine ⟨73142135410613633177999561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48761423607075755451999707 73142135410613633177999561)
          ·
            refine ⟨54856601557960224883499671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73142135410613633177999561 54856601557960224883499671)
            ·
              refine ⟨82284902336940337325249507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54856601557960224883499671 82284902336940337325249507)
              ·
                refine ⟨123427353505410505987874261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82284902336940337325249507 123427353505410505987874261)
                ·
                  refine ⟨2892828597783058734090803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123427353505410505987874261 2892828597783058734090803)
                  ·
                    refine ⟨4339242896674588101136205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892828597783058734090803 4339242896674588101136205)
                    ·
                      refine ⟨1627216086252970537926077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339242896674588101136205 1627216086252970537926077)
                      ·
                        rfl

theorem cell23_3168992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_3168992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3168992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3168992 prefixEnd_3168992 := by exact prefixLift 3168992
  have htrace : WordTrace (prefixWord ++ tailWord_3168992) baseStart_3168992 baseEnd_3168992 := by
    simpa [prefixWord, tailWord_3168992, baseEnd_3168992] using wordTrace_append hprefix tailTrace_3168992
  have hstable : (prefixWord ++ tailWord_3168992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3168992).length < 2 ^ (prefixWord ++ tailWord_3168992).sum := by decide
  have hdescent : baseEnd_3168992 < baseStart_3168992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3168992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169009 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_3169009 : Nat := 118140960795 + 3169009 * 2 ^ 59
def prefixEnd_3169009 : Nat := 4983230072969 + 3 ^ 40 * 3169009 * 2
def baseEnd_3169009 : Nat := 1627224815424096971413499

theorem tailTrace_3169009 : CollatzResearch.WordTrace tailWord_3169009 prefixEnd_3169009 1627224815424096971413499 := by
  unfold tailWord_3169009
  simp only [CollatzResearch.WordTrace]
  refine ⟨115583253776229091493294081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77055502517486060995529387 115583253776229091493294081)
  ·
    refine ⟨86687440332171818619970561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115583253776229091493294081 86687440332171818619970561)
    ·
      refine ⟨65015580249128863964977921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86687440332171818619970561 65015580249128863964977921)
      ·
        refine ⟨48761685186846647973733441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65015580249128863964977921 48761685186846647973733441)
        ·
          refine ⟨36571263890134985980300081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48761685186846647973733441 36571263890134985980300081)
          ·
            refine ⟨27428447917601239485225061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36571263890134985980300081 27428447917601239485225061)
            ·
              refine ⟨5142833984550232403479699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27428447917601239485225061 5142833984550232403479699)
              ·
                refine ⟨7714250976825348605219549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142833984550232403479699 7714250976825348605219549)
                ·
                  refine ⟨2892844116309505726957331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7714250976825348605219549 2892844116309505726957331)
                  ·
                    refine ⟨4339266174464258590435997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892844116309505726957331 4339266174464258590435997)
                    ·
                      refine ⟨1627224815424096971413499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339266174464258590435997 1627224815424096971413499)
                      ·
                        rfl

theorem cell23_3169009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_3169009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169009 prefixEnd_3169009 := by exact prefixLift 3169009
  have htrace : WordTrace (prefixWord ++ tailWord_3169009) baseStart_3169009 baseEnd_3169009 := by
    simpa [prefixWord, tailWord_3169009, baseEnd_3169009] using wordTrace_append hprefix tailTrace_3169009
  have hstable : (prefixWord ++ tailWord_3169009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169009).length < 2 ^ (prefixWord ++ tailWord_3169009).sum := by decide
  have hdescent : baseEnd_3169009 < baseStart_3169009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169026 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3169026 : Nat := 118140960795 + 3169026 * 2 ^ 59
def prefixEnd_3169026 : Nat := 4983230072969 + 3 ^ 40 * 3169026 * 2
def baseEnd_3169026 : Nat := 1627233544595223404900921

theorem tailTrace_3169026 : CollatzResearch.WordTrace tailWord_3169026 prefixEnd_3169026 1627233544595223404900921 := by
  unfold tailWord_3169026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28895968454291875849165733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77055915878111668931108621 28895968454291875849165733)
  ·
    refine ⟨5417994085179726721718575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28895968454291875849165733 5417994085179726721718575)
    ·
      refine ⟨8126991127769590082577863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5417994085179726721718575 8126991127769590082577863)
      ·
        refine ⟨12190486691654385123866795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126991127769590082577863 12190486691654385123866795)
        ·
          refine ⟨18285730037481577685800193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12190486691654385123866795 18285730037481577685800193)
          ·
            refine ⟨13714297528111183264350145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18285730037481577685800193 13714297528111183264350145)
            ·
              refine ⟨10285723146083387448262609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13714297528111183264350145 10285723146083387448262609)
              ·
                refine ⟨7714292359562540586196957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10285723146083387448262609 7714292359562540586196957)
                ·
                  refine ⟨2892859634835952719823859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7714292359562540586196957 2892859634835952719823859)
                  ·
                    refine ⟨4339289452253929079735789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892859634835952719823859 4339289452253929079735789)
                    ·
                      refine ⟨1627233544595223404900921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339289452253929079735789 1627233544595223404900921)
                      ·
                        rfl

theorem cell23_3169026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3169026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169026 prefixEnd_3169026 := by exact prefixLift 3169026
  have htrace : WordTrace (prefixWord ++ tailWord_3169026) baseStart_3169026 baseEnd_3169026 := by
    simpa [prefixWord, tailWord_3169026, baseEnd_3169026] using wordTrace_append hprefix tailTrace_3169026
  have hstable : (prefixWord ++ tailWord_3169026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169026).length < 2 ^ (prefixWord ++ tailWord_3169026).sum := by decide
  have hdescent : baseEnd_3169026 < baseStart_3169026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
