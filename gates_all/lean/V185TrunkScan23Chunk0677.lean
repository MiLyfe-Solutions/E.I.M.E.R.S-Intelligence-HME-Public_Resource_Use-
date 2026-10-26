import V185TrunkScan23Chunk0676

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4003599 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_4003599 : Nat := 118140960795 + 4003599 * 2 ^ 59
def prefixEnd_4003599 : Nat := 4983230072969 + 3 ^ 40 * 4003599 * 2
def baseEnd_4003599 : Nat := 2055770634859986634200289

theorem tailTrace_4003599 : CollatzResearch.WordTrace tailWord_4003599 prefixEnd_4003599 2055770634859986634200289 := by
  unfold tailWord_4003599
  simp only [CollatzResearch.WordTrace]
  refine ⟨146023251822652058117373851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97348834548434705411582567 146023251822652058117373851)
  ·
    refine ⟨219034877733978087176060777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146023251822652058117373851 219034877733978087176060777)
    ·
      refine ⟨164276158300483565382045583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219034877733978087176060777 164276158300483565382045583)
      ·
        refine ⟨246414237450725348073068375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164276158300483565382045583 246414237450725348073068375)
        ·
          refine ⟨369621356176088022109602563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246414237450725348073068375 369621356176088022109602563)
          ·
            refine ⟨554432034264132033164403845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369621356176088022109602563 554432034264132033164403845)
            ·
              refine ⟨103956006424524756218325721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 554432034264132033164403845 103956006424524756218325721)
              ·
                refine ⟨77967004818393567163744291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103956006424524756218325721 77967004818393567163744291)
                ·
                  refine ⟨116950507227590350745616437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77967004818393567163744291 116950507227590350745616437)
                  ·
                    refine ⟨10964110052586595382401541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116950507227590350745616437 10964110052586595382401541)
                    ·
                      refine ⟨2055770634859986634200289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10964110052586595382401541 2055770634859986634200289)
                      ·
                        rfl

theorem cell23_4003599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_4003599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003599 prefixEnd_4003599 := by exact prefixLift 4003599
  have htrace : WordTrace (prefixWord ++ tailWord_4003599) baseStart_4003599 baseEnd_4003599 := by
    simpa [prefixWord, tailWord_4003599, baseEnd_4003599] using wordTrace_append hprefix tailTrace_4003599
  have hstable : (prefixWord ++ tailWord_4003599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003599).length < 2 ^ (prefixWord ++ tailWord_4003599).sum := by decide
  have hdescent : baseEnd_4003599 < baseStart_4003599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003610 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_4003610 : Nat := 118140960795 + 4003610 * 2 ^ 59
def prefixEnd_4003610 : Nat := 4983230072969 + 3 ^ 40 * 4003610 * 2
def baseEnd_4003610 : Nat := 2055776283147186091162739

theorem tailTrace_4003610 : CollatzResearch.WordTrace tailWord_4003610 prefixEnd_4003610 2055776283147186091162739 := by
  unfold tailWord_4003610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36505913256403051749006071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97349102017074804664016189 36505913256403051749006071)
  ·
    refine ⟨54758869884604577623509107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36505913256403051749006071 54758869884604577623509107)
    ·
      refine ⟨82138304826906866435263661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54758869884604577623509107 82138304826906866435263661)
      ·
        refine ⟨30801864310090074913223873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82138304826906866435263661 30801864310090074913223873)
        ·
          refine ⟨23101398232567556184917905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30801864310090074913223873 23101398232567556184917905)
          ·
            refine ⟨17326048674425667138688429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23101398232567556184917905 17326048674425667138688429)
            ·
              refine ⟨6497268252909625177008161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17326048674425667138688429 6497268252909625177008161)
              ·
                refine ⟨4872951189682218882756121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497268252909625177008161 4872951189682218882756121)
                ·
                  refine ⟨3654713392261664162067091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872951189682218882756121 3654713392261664162067091)
                  ·
                    refine ⟨5482070088392496243100637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3654713392261664162067091 5482070088392496243100637)
                    ·
                      refine ⟨2055776283147186091162739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5482070088392496243100637 2055776283147186091162739)
                      ·
                        rfl

theorem cell23_4003610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_4003610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003610 prefixEnd_4003610 := by exact prefixLift 4003610
  have htrace : WordTrace (prefixWord ++ tailWord_4003610) baseStart_4003610 baseEnd_4003610 := by
    simpa [prefixWord, tailWord_4003610, baseEnd_4003610] using wordTrace_append hprefix tailTrace_4003610
  have hstable : (prefixWord ++ tailWord_4003610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003610).length < 2 ^ (prefixWord ++ tailWord_4003610).sum := by decide
  have hdescent : baseEnd_4003610 < baseStart_4003610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003637 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_4003637 : Nat := 118140960795 + 4003637 * 2 ^ 59
def prefixEnd_4003637 : Nat := 4983230072969 + 3 ^ 40 * 4003637 * 2
def baseEnd_4003637 : Nat := 2055790147124857485525115

theorem tailTrace_4003637 : CollatzResearch.WordTrace tailWord_4003637 prefixEnd_4003637 2055790147124857485525115 := by
  unfold tailWord_4003637
  simp only [CollatzResearch.WordTrace]
  refine ⟨146024637796514390607257165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97349758531009593738171443 146024637796514390607257165)
  ·
    refine ⟨54759239173692896477721437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146024637796514390607257165 54759239173692896477721437)
    ·
      refine ⟨20534714690134836179145539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54759239173692896477721437 20534714690134836179145539)
      ·
        refine ⟨30802072035202254268718309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20534714690134836179145539 30802072035202254268718309)
        ·
          refine ⟨5775388506600422675384683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30802072035202254268718309 5775388506600422675384683)
          ·
            refine ⟨8663082759900634013077025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775388506600422675384683 8663082759900634013077025)
            ·
              refine ⟨6497312069925475509807769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8663082759900634013077025 6497312069925475509807769)
              ·
                refine ⟨4872984052444106632355827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497312069925475509807769 4872984052444106632355827)
                ·
                  refine ⟨7309476078666159948533741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872984052444106632355827 7309476078666159948533741)
                  ·
                    refine ⟨2741053529499809980700153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7309476078666159948533741 2741053529499809980700153)
                    ·
                      refine ⟨2055790147124857485525115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741053529499809980700153 2055790147124857485525115)
                      ·
                        rfl

theorem cell23_4003637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_4003637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003637 prefixEnd_4003637 := by exact prefixLift 4003637
  have htrace : WordTrace (prefixWord ++ tailWord_4003637) baseStart_4003637 baseEnd_4003637 := by
    simpa [prefixWord, tailWord_4003637, baseEnd_4003637] using wordTrace_append hprefix tailTrace_4003637
  have hstable : (prefixWord ++ tailWord_4003637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003637).length < 2 ^ (prefixWord ++ tailWord_4003637).sum := by decide
  have hdescent : baseEnd_4003637 < baseStart_4003637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003639 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 9]
def baseStart_4003639 : Nat := 118140960795 + 4003639 * 2 ^ 59
def prefixEnd_4003639 : Nat := 4983230072969 + 3 ^ 40 * 4003639 * 2
def baseEnd_4003639 : Nat := 228421241565129608633345

theorem tailTrace_4003639 : CollatzResearch.WordTrace tailWord_4003639 prefixEnd_4003639 228421241565129608633345 := by
  unfold tailWord_4003639
  simp only [CollatzResearch.WordTrace]
  refine ⟨146024710742507144948829971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97349807161671429965886647 146024710742507144948829971)
  ·
    refine ⟨219037066113760717423244957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146024710742507144948829971 219037066113760717423244957)
    ·
      refine ⟨82138899792660269033716859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219037066113760717423244957 82138899792660269033716859)
      ·
        refine ⟨123208349688990403550575289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82138899792660269033716859 123208349688990403550575289)
        ·
          refine ⟨92406262266742802662931467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123208349688990403550575289 92406262266742802662931467)
          ·
            refine ⟨138609393400114203994397201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92406262266742802662931467 138609393400114203994397201)
            ·
              refine ⟨103957045050085652995797901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138609393400114203994397201 103957045050085652995797901)
              ·
                refine ⟨38983891893782119873424213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103957045050085652995797901 38983891893782119873424213)
                ·
                  refine ⟨228421241565129608633345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38983891893782119873424213 228421241565129608633345)
                  ·
                    rfl

theorem cell23_4003639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 9].length) (baseStart_4003639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003639 prefixEnd_4003639 := by exact prefixLift 4003639
  have htrace : WordTrace (prefixWord ++ tailWord_4003639) baseStart_4003639 baseEnd_4003639 := by
    simpa [prefixWord, tailWord_4003639, baseEnd_4003639] using wordTrace_append hprefix tailTrace_4003639
  have hstable : (prefixWord ++ tailWord_4003639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003639).length < 2 ^ (prefixWord ++ tailWord_4003639).sum := by decide
  have hdescent : baseEnd_4003639 < baseStart_4003639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003654 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4003654 : Nat := 118140960795 + 4003654 * 2 ^ 59
def prefixEnd_4003654 : Nat := 4983230072969 + 3 ^ 40 * 4003654 * 2
def baseEnd_4003654 : Nat := 2055798876295983919012537

theorem tailTrace_4003654 : CollatzResearch.WordTrace tailWord_4003654 prefixEnd_4003654 2055798876295983919012537 := by
  unfold tailWord_4003654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563289307420400078457063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97350171891635201673750677 4563289307420400078457063)
  ·
    refine ⟨6844933961130600117685595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4563289307420400078457063 6844933961130600117685595)
    ·
      refine ⟨10267400941695900176528393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6844933961130600117685595 10267400941695900176528393)
      ·
        refine ⟨7700550706271925132396295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10267400941695900176528393 7700550706271925132396295)
        ·
          refine ⟨11550826059407887698594443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700550706271925132396295 11550826059407887698594443)
          ·
            refine ⟨17326239089111831547891665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550826059407887698594443 17326239089111831547891665)
            ·
              refine ⟨12994679316833873660918749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17326239089111831547891665 12994679316833873660918749)
              ·
                refine ⟨4873004743812702622844531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12994679316833873660918749 4873004743812702622844531)
                ·
                  refine ⟨7309507115719053934266797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873004743812702622844531 7309507115719053934266797)
                  ·
                    refine ⟨2741065168394645225350049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7309507115719053934266797 2741065168394645225350049)
                    ·
                      refine ⟨2055798876295983919012537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741065168394645225350049 2055798876295983919012537)
                      ·
                        rfl

theorem cell23_4003654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4003654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003654 prefixEnd_4003654 := by exact prefixLift 4003654
  have htrace : WordTrace (prefixWord ++ tailWord_4003654) baseStart_4003654 baseEnd_4003654 := by
    simpa [prefixWord, tailWord_4003654, baseEnd_4003654] using wordTrace_append hprefix tailTrace_4003654
  have hstable : (prefixWord ++ tailWord_4003654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003654).length < 2 ^ (prefixWord ++ tailWord_4003654).sum := by decide
  have hdescent : baseEnd_4003654 < baseStart_4003654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003659 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_4003659 : Nat := 118140960795 + 4003659 * 2 ^ 59
def prefixEnd_4003659 : Nat := 4983230072969 + 3 ^ 40 * 4003659 * 2
def baseEnd_4003659 : Nat := 2055801443699256399450013

theorem tailTrace_4003659 : CollatzResearch.WordTrace tailWord_4003659 prefixEnd_4003659 2055801443699256399450013 := by
  unfold tailWord_4003659
  simp only [CollatzResearch.WordTrace]
  refine ⟨146025440202434688364558031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97350293468289792243038687 146025440202434688364558031)
  ·
    refine ⟨219038160303652032546837047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146025440202434688364558031 219038160303652032546837047)
    ·
      refine ⟨328557240455478048820255571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219038160303652032546837047 328557240455478048820255571)
      ·
        refine ⟨492835860683217073230383357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328557240455478048820255571 492835860683217073230383357)
        ·
          refine ⟨184813447756206402461393759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492835860683217073230383357 184813447756206402461393759)
          ·
            refine ⟨277220171634309603692090639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184813447756206402461393759 277220171634309603692090639)
            ·
              refine ⟨415830257451464405538135959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277220171634309603692090639 415830257451464405538135959)
              ·
                refine ⟨623745386177196608307203939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415830257451464405538135959 623745386177196608307203939)
                ·
                  refine ⟨935618079265794912460805909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623745386177196608307203939 935618079265794912460805909)
                  ·
                    refine ⟨43857097465584136521600277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 935618079265794912460805909 43857097465584136521600277)
                    ·
                      refine ⟨2055801443699256399450013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43857097465584136521600277 2055801443699256399450013)
                      ·
                        rfl

theorem cell23_4003659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_4003659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003659 prefixEnd_4003659 := by exact prefixLift 4003659
  have htrace : WordTrace (prefixWord ++ tailWord_4003659) baseStart_4003659 baseEnd_4003659 := by
    simpa [prefixWord, tailWord_4003659, baseEnd_4003659] using wordTrace_append hprefix tailTrace_4003659
  have hstable : (prefixWord ++ tailWord_4003659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003659).length < 2 ^ (prefixWord ++ tailWord_4003659).sum := by decide
  have hdescent : baseEnd_4003659 < baseStart_4003659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003706 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_4003706 : Nat := 118140960795 + 4003706 * 2 ^ 59
def prefixEnd_4003706 : Nat := 4983230072969 + 3 ^ 40 * 4003706 * 2
def baseEnd_4003706 : Nat := 2055825577290017715562297

theorem tailTrace_4003706 : CollatzResearch.WordTrace tailWord_4003706 prefixEnd_4003706 2055825577290017715562297 := by
  unfold tailWord_4003706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36506788608316103847879743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97351436288842943594345981 36506788608316103847879743)
  ·
    refine ⟨54760182912474155771819615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36506788608316103847879743 54760182912474155771819615)
    ·
      refine ⟨82140274368711233657729423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54760182912474155771819615 82140274368711233657729423)
      ·
        refine ⟨123210411553066850486594135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82140274368711233657729423 123210411553066850486594135)
        ·
          refine ⟨184815617329600275729891203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123210411553066850486594135 184815617329600275729891203)
          ·
            refine ⟨277223425994400413594836805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184815617329600275729891203 277223425994400413594836805)
            ·
              refine ⟨51979392373950077549031901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277223425994400413594836805 51979392373950077549031901)
              ·
                refine ⟨19492272140231279080886963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51979392373950077549031901 19492272140231279080886963)
                ·
                  refine ⟨29238408210346918621330445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19492272140231279080886963 29238408210346918621330445)
                  ·
                    refine ⟨10964403078880094482998917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29238408210346918621330445 10964403078880094482998917)
                    ·
                      refine ⟨2055825577290017715562297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10964403078880094482998917 2055825577290017715562297)
                      ·
                        rfl

theorem cell23_4003706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_4003706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003706 prefixEnd_4003706 := by exact prefixLift 4003706
  have htrace : WordTrace (prefixWord ++ tailWord_4003706) baseStart_4003706 baseEnd_4003706 := by
    simpa [prefixWord, tailWord_4003706, baseEnd_4003706] using wordTrace_append hprefix tailTrace_4003706
  have hstable : (prefixWord ++ tailWord_4003706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003706).length < 2 ^ (prefixWord ++ tailWord_4003706).sum := by decide
  have hdescent : baseEnd_4003706 < baseStart_4003706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003723 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 2, 4, 2]
def baseStart_4003723 : Nat := 118140960795 + 4003723 * 2 ^ 59
def prefixEnd_4003723 : Nat := 4983230072969 + 3 ^ 40 * 4003723 * 2
def baseEnd_4003723 : Nat := 2055834306461144149049719

theorem tailTrace_4003723 : CollatzResearch.WordTrace tailWord_4003723 prefixEnd_4003723 2055834306461144149049719 := by
  unfold tailWord_4003723
  simp only [CollatzResearch.WordTrace]
  refine ⟨146027774474202827294887823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97351849649468551529925215 146027774474202827294887823)
  ·
    refine ⟨219041661711304240942331735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146027774474202827294887823 219041661711304240942331735)
    ·
      refine ⟨328562492566956361413497603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219041661711304240942331735 328562492566956361413497603)
      ·
        refine ⟨492843738850434542120246405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328562492566956361413497603 492843738850434542120246405)
        ·
          refine ⟨92408201034456476647546201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 492843738850434542120246405 92408201034456476647546201)
          ·
            refine ⟨69306150775842357485659651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92408201034456476647546201 69306150775842357485659651)
            ·
              refine ⟨103959226163763536228489477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69306150775842357485659651 103959226163763536228489477)
              ·
                refine ⟨19492354905705663042841777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103959226163763536228489477 19492354905705663042841777)
                ·
                  refine ⟨14619266179279247282131333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19492354905705663042841777 14619266179279247282131333)
                  ·
                    refine ⟨2741112408614858865399625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14619266179279247282131333 2741112408614858865399625)
                    ·
                      refine ⟨2055834306461144149049719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741112408614858865399625 2055834306461144149049719)
                      ·
                        rfl

theorem cell23_4003723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4, 2].length) (baseStart_4003723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003723 prefixEnd_4003723 := by exact prefixLift 4003723
  have htrace : WordTrace (prefixWord ++ tailWord_4003723) baseStart_4003723 baseEnd_4003723 := by
    simpa [prefixWord, tailWord_4003723, baseEnd_4003723] using wordTrace_append hprefix tailTrace_4003723
  have hstable : (prefixWord ++ tailWord_4003723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003723).length < 2 ^ (prefixWord ++ tailWord_4003723).sum := by decide
  have hdescent : baseEnd_4003723 < baseStart_4003723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003733 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_4003733 : Nat := 118140960795 + 4003733 * 2 ^ 59
def prefixEnd_4003733 : Nat := 4983230072969 + 3 ^ 40 * 4003733 * 2
def baseEnd_4003733 : Nat := 685279813755896369974891

theorem tailTrace_4003733 : CollatzResearch.WordTrace tailWord_4003733 prefixEnd_4003733 685279813755896369974891 := by
  unfold tailWord_4003733
  simp only [CollatzResearch.WordTrace]
  refine ⟨146028139204166599002751853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97352092802777732668501235 146028139204166599002751853)
  ·
    refine ⟨54760552201562474626031945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146028139204166599002751853 54760552201562474626031945)
    ·
      refine ⟨41070414151171855969523959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54760552201562474626031945 41070414151171855969523959)
      ·
        refine ⟨61605621226757783954285939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41070414151171855969523959 61605621226757783954285939)
        ·
          refine ⟨92408431840136675931428909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61605621226757783954285939 92408431840136675931428909)
          ·
            refine ⟨34653161940051253474285841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92408431840136675931428909 34653161940051253474285841)
            ·
              refine ⟨25989871455038440105714381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34653161940051253474285841 25989871455038440105714381)
              ·
                refine ⟨9746201795639415039642893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25989871455038440105714381 9746201795639415039642893)
                ·
                  refine ⟨3654825673364780639866085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9746201795639415039642893 3654825673364780639866085)
                  ·
                    refine ⟨685279813755896369974891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654825673364780639866085 685279813755896369974891)
                    ·
                      rfl

theorem cell23_4003733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_4003733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003733 prefixEnd_4003733 := by exact prefixLift 4003733
  have htrace : WordTrace (prefixWord ++ tailWord_4003733) baseStart_4003733 baseEnd_4003733 := by
    simpa [prefixWord, tailWord_4003733, baseEnd_4003733] using wordTrace_append hprefix tailTrace_4003733
  have hstable : (prefixWord ++ tailWord_4003733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003733).length < 2 ^ (prefixWord ++ tailWord_4003733).sum := by decide
  have hdescent : baseEnd_4003733 < baseStart_4003733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003734 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4003734 : Nat := 118140960795 + 4003734 * 2 ^ 59
def prefixEnd_4003734 : Nat := 4983230072969 + 3 ^ 40 * 4003734 * 2
def baseEnd_4003734 : Nat := 2055839954748343606012169

theorem tailTrace_4003734 : CollatzResearch.WordTrace tailWord_4003734 prefixEnd_4003734 2055839954748343606012169 := by
  unfold tailWord_4003734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126760979822686010846141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97352117118108650782358837 9126760979822686010846141)
  ·
    refine ⟨3422535367433507254067303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9126760979822686010846141 3422535367433507254067303)
    ·
      refine ⟨5133803051150260881100955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422535367433507254067303 5133803051150260881100955)
      ·
        refine ⟨7700704576725391321651433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133803051150260881100955 7700704576725391321651433)
        ·
          refine ⟨5775528432544043491238575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7700704576725391321651433 5775528432544043491238575)
          ·
            refine ⟨8663292648816065236857863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775528432544043491238575 8663292648816065236857863)
            ·
              refine ⟨12994938973224097855286795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663292648816065236857863 12994938973224097855286795)
              ·
                refine ⟨19492408459836146782930193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12994938973224097855286795 19492408459836146782930193)
                ·
                  refine ⟨14619306344877110087197645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19492408459836146782930193 14619306344877110087197645)
                  ·
                    refine ⟨5482239879328916282699117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14619306344877110087197645 5482239879328916282699117)
                    ·
                      refine ⟨2055839954748343606012169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5482239879328916282699117 2055839954748343606012169)
                      ·
                        rfl

theorem cell23_4003734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4003734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003734 prefixEnd_4003734 := by exact prefixLift 4003734
  have htrace : WordTrace (prefixWord ++ tailWord_4003734) baseStart_4003734 baseEnd_4003734 := by
    simpa [prefixWord, tailWord_4003734, baseEnd_4003734] using wordTrace_append hprefix tailTrace_4003734
  have hstable : (prefixWord ++ tailWord_4003734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003734).length < 2 ^ (prefixWord ++ tailWord_4003734).sum := by decide
  have hdescent : baseEnd_4003734 < baseStart_4003734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003740 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4003740 : Nat := 118140960795 + 4003740 * 2 ^ 59
def prefixEnd_4003740 : Nat := 4983230072969 + 3 ^ 40 * 4003740 * 2
def baseEnd_4003740 : Nat := 2055843035632270582537141

theorem tailTrace_4003740 : CollatzResearch.WordTrace tailWord_4003740 prefixEnd_4003740 2055843035632270582537141 := by
  unfold tailWord_4003740
  simp only [CollatzResearch.WordTrace]
  refine ⟨73014197257570619599128337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97352263010094159465504449 73014197257570619599128337)
  ·
    refine ⟨54760647943177964699346253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73014197257570619599128337 54760647943177964699346253)
    ·
      refine ⟨20535242978691736762254845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54760647943177964699346253 20535242978691736762254845)
      ·
        refine ⟨7700716117009401285845567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20535242978691736762254845 7700716117009401285845567)
        ·
          refine ⟨11551074175514101928768351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700716117009401285845567 11551074175514101928768351)
          ·
            refine ⟨17326611263271152893152527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551074175514101928768351 17326611263271152893152527)
            ·
              refine ⟨25989916894906729339728791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17326611263271152893152527 25989916894906729339728791)
              ·
                refine ⟨38984875342360094009593187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25989916894906729339728791 38984875342360094009593187)
                ·
                  refine ⟨58477313013540141014389781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38984875342360094009593187 58477313013540141014389781)
                  ·
                    refine ⟨2741124047509694110049521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58477313013540141014389781 2741124047509694110049521)
                    ·
                      refine ⟨2055843035632270582537141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741124047509694110049521 2055843035632270582537141)
                      ·
                        rfl

theorem cell23_4003740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4003740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003740 prefixEnd_4003740 := by exact prefixLift 4003740
  have htrace : WordTrace (prefixWord ++ tailWord_4003740) baseStart_4003740 baseEnd_4003740 := by
    simpa [prefixWord, tailWord_4003740, baseEnd_4003740] using wordTrace_append hprefix tailTrace_4003740
  have hstable : (prefixWord ++ tailWord_4003740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003740).length < 2 ^ (prefixWord ++ tailWord_4003740).sum := by decide
  have hdescent : baseEnd_4003740 < baseStart_4003740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003823 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 6, 4]
def baseStart_4003823 : Nat := 118140960795 + 4003823 * 2 ^ 59
def prefixEnd_4003823 : Nat := 4983230072969 + 3 ^ 40 * 4003823 * 2
def baseEnd_4003823 : Nat := 685295218175531252599753

theorem tailTrace_4003823 : CollatzResearch.WordTrace tailWord_4003823 prefixEnd_4003823 685295218175531252599753 := by
  unfold tailWord_4003823
  simp only [CollatzResearch.WordTrace]
  refine ⟨146031421773840544373528123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97354281182560362915685415 146031421773840544373528123)
  ·
    refine ⟨219047132660760816560292185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146031421773840544373528123 219047132660760816560292185)
    ·
      refine ⟨164285349495570612420219139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219047132660760816560292185 164285349495570612420219139)
      ·
        refine ⟨246428024243355918630328709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164285349495570612420219139 246428024243355918630328709)
        ·
          refine ⟨46205254545629234743186633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246428024243355918630328709 46205254545629234743186633)
          ·
            refine ⟨34653940909221926057389975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46205254545629234743186633 34653940909221926057389975)
            ·
              refine ⟨51980911363832889086084963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34653940909221926057389975 51980911363832889086084963)
              ·
                refine ⟨77971367045749333629127445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51980911363832889086084963 77971367045749333629127445)
                ·
                  refine ⟨3654907830269500013865349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77971367045749333629127445 3654907830269500013865349)
                  ·
                    refine ⟨685295218175531252599753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654907830269500013865349 685295218175531252599753)
                    ·
                      rfl

theorem cell23_4003823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_4003823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003823 prefixEnd_4003823 := by exact prefixLift 4003823
  have htrace : WordTrace (prefixWord ++ tailWord_4003823) baseStart_4003823 baseEnd_4003823 := by
    simpa [prefixWord, tailWord_4003823, baseEnd_4003823] using wordTrace_append hprefix tailTrace_4003823
  have hstable : (prefixWord ++ tailWord_4003823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003823).length < 2 ^ (prefixWord ++ tailWord_4003823).sum := by decide
  have hdescent : baseEnd_4003823 < baseStart_4003823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003833 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_4003833 : Nat := 118140960795 + 4003833 * 2 ^ 59
def prefixEnd_4003833 : Nat := 4983230072969 + 3 ^ 40 * 4003833 * 2
def baseEnd_4003833 : Nat := 2055890789333138718674213

theorem tailTrace_4003833 : CollatzResearch.WordTrace tailWord_4003833 prefixEnd_4003833 2055890789333138718674213 := by
  unfold tailWord_4003833
  simp only [CollatzResearch.WordTrace]
  refine ⟨146031786503804316081392153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97354524335869544054261435 146031786503804316081392153)
  ·
    refine ⟨109523839877853237061044115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146031786503804316081392153 109523839877853237061044115)
    ·
      refine ⟨164285759816779855591566173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109523839877853237061044115 164285759816779855591566173)
      ·
        refine ⟨61607159931292445846837315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164285759816779855591566173 61607159931292445846837315)
        ·
          refine ⟨92410739896938668770255973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61607159931292445846837315 92410739896938668770255973)
          ·
            refine ⟨17327013730676000394422995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92410739896938668770255973 17327013730676000394422995)
            ·
              refine ⟨25990520596014000591634493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327013730676000394422995 25990520596014000591634493)
              ·
                refine ⟨9746445223505250221862935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25990520596014000591634493 9746445223505250221862935)
                ·
                  refine ⟨14619667835257875332794403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746445223505250221862935 14619667835257875332794403)
                  ·
                    refine ⟨21929501752886812999191605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14619667835257875332794403 21929501752886812999191605)
                    ·
                      refine ⟨2055890789333138718674213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21929501752886812999191605 2055890789333138718674213)
                      ·
                        rfl

theorem cell23_4003833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_4003833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003833 prefixEnd_4003833 := by exact prefixLift 4003833
  have htrace : WordTrace (prefixWord ++ tailWord_4003833) baseStart_4003833 baseEnd_4003833 := by
    simpa [prefixWord, tailWord_4003833, baseEnd_4003833] using wordTrace_append hprefix tailTrace_4003833
  have hstable : (prefixWord ++ tailWord_4003833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003833).length < 2 ^ (prefixWord ++ tailWord_4003833).sum := by decide
  have hdescent : baseEnd_4003833 < baseStart_4003833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003893 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4003893 : Nat := 118140960795 + 4003893 * 2 ^ 59
def prefixEnd_4003893 : Nat := 4983230072969 + 3 ^ 40 * 4003893 * 2
def baseEnd_4003893 : Nat := 2055921598172408483923937

theorem tailTrace_4003893 : CollatzResearch.WordTrace tailWord_4003893 prefixEnd_4003893 2055921598172408483923937 := by
  unfold tailWord_4003893
  simp only [CollatzResearch.WordTrace]
  refine ⟨146033974883586946328576333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97355983255724630885717555 146033974883586946328576333)
  ·
    refine ⟨54762740581345104873216125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146033974883586946328576333 54762740581345104873216125)
    ·
      refine ⟨20536027718004414327456047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54762740581345104873216125 20536027718004414327456047)
      ·
        refine ⟨30804041577006621491184071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20536027718004414327456047 30804041577006621491184071)
        ·
          refine ⟨46206062365509932236776107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30804041577006621491184071 46206062365509932236776107)
          ·
            refine ⟨69309093548264898355164161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46206062365509932236776107 69309093548264898355164161)
            ·
              refine ⟨51981820161198673766373121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69309093548264898355164161 51981820161198673766373121)
              ·
                refine ⟨38986365120899005324779841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51981820161198673766373121 38986365120899005324779841)
                ·
                  refine ⟨29239773840674253993584881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38986365120899005324779841 29239773840674253993584881)
                  ·
                    refine ⟨21929830380505690495188661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29239773840674253993584881 21929830380505690495188661)
                    ·
                      refine ⟨2055921598172408483923937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21929830380505690495188661 2055921598172408483923937)
                      ·
                        rfl

theorem cell23_4003893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4003893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003893 prefixEnd_4003893 := by exact prefixLift 4003893
  have htrace : WordTrace (prefixWord ++ tailWord_4003893) baseStart_4003893 baseEnd_4003893 := by
    simpa [prefixWord, tailWord_4003893, baseEnd_4003893] using wordTrace_append hprefix tailTrace_4003893
  have hstable : (prefixWord ++ tailWord_4003893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003893).length < 2 ^ (prefixWord ++ tailWord_4003893).sum := by decide
  have hdescent : baseEnd_4003893 < baseStart_4003893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003903 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_4003903 : Nat := 118140960795 + 4003903 * 2 ^ 59
def prefixEnd_4003903 : Nat := 4983230072969 + 3 ^ 40 * 4003903 * 2
def baseEnd_4003903 : Nat := 2055926732978953444798891

theorem tailTrace_4003903 : CollatzResearch.WordTrace tailWord_4003903 prefixEnd_4003903 2055926732978953444798891 := by
  unfold tailWord_4003903
  simp only [CollatzResearch.WordTrace]
  refine ⟨146034339613550718036440363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97356226409033812024293575 146034339613550718036440363)
  ·
    refine ⟨219051509420326077054660545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146034339613550718036440363 219051509420326077054660545)
    ·
      refine ⟨164288632065244557790995409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219051509420326077054660545 164288632065244557790995409)
      ·
        refine ⟨123216474048933418343246557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164288632065244557790995409 123216474048933418343246557)
        ·
          refine ⟨46206177768350031878717459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123216474048933418343246557 46206177768350031878717459)
          ·
            refine ⟨69309266652525047818076189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46206177768350031878717459 69309266652525047818076189)
            ·
              refine ⟨25990974994696892931778571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69309266652525047818076189 25990974994696892931778571)
              ·
                refine ⟨38986462492045339397667857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25990974994696892931778571 38986462492045339397667857)
                ·
                  refine ⟨29239846869034004548250893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38986462492045339397667857 29239846869034004548250893)
                  ·
                    refine ⟨10964942575887751705594085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29239846869034004548250893 10964942575887751705594085)
                    ·
                      refine ⟨2055926732978953444798891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10964942575887751705594085 2055926732978953444798891)
                      ·
                        rfl

theorem cell23_4003903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_4003903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003903 prefixEnd_4003903 := by exact prefixLift 4003903
  have htrace : WordTrace (prefixWord ++ tailWord_4003903) baseStart_4003903 baseEnd_4003903 := by
    simpa [prefixWord, tailWord_4003903, baseEnd_4003903] using wordTrace_append hprefix tailTrace_4003903
  have hstable : (prefixWord ++ tailWord_4003903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003903).length < 2 ^ (prefixWord ++ tailWord_4003903).sum := by decide
  have hdescent : baseEnd_4003903 < baseStart_4003903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003913 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_4003913 : Nat := 118140960795 + 4003913 * 2 ^ 59
def prefixEnd_4003913 : Nat := 4983230072969 + 3 ^ 40 * 4003913 * 2
def baseEnd_4003913 : Nat := 685310622595166135224615

theorem tailTrace_4003913 : CollatzResearch.WordTrace tailWord_4003913 prefixEnd_4003913 685310622595166135224615 := by
  unfold tailWord_4003913
  simp only [CollatzResearch.WordTrace]
  refine ⟨146034704343514489744304393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97356469562342993162869595 146034704343514489744304393)
  ·
    refine ⟨109526028257635867308228295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146034704343514489744304393 109526028257635867308228295)
    ·
      refine ⟨164289042386453800962342443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109526028257635867308228295 164289042386453800962342443)
      ·
        refine ⟨246433563579680701443513665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164289042386453800962342443 246433563579680701443513665)
        ·
          refine ⟨184825172684760526082635249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246433563579680701443513665 184825172684760526082635249)
          ·
            refine ⟨138618879513570394561976437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184825172684760526082635249 138618879513570394561976437)
            ·
              refine ⟨12995519954397224490185291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138618879513570394561976437 12995519954397224490185291)
              ·
                refine ⟨19493279931595836735277937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995519954397224490185291 19493279931595836735277937)
                ·
                  refine ⟨14619959948696877551458453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19493279931595836735277937 14619959948696877551458453)
                  ·
                    refine ⟨685310622595166135224615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14619959948696877551458453 685310622595166135224615)
                    ·
                      rfl

theorem cell23_4003913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_4003913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003913 prefixEnd_4003913 := by exact prefixLift 4003913
  have htrace : WordTrace (prefixWord ++ tailWord_4003913) baseStart_4003913 baseEnd_4003913 := by
    simpa [prefixWord, tailWord_4003913, baseEnd_4003913] using wordTrace_append hprefix tailTrace_4003913
  have hstable : (prefixWord ++ tailWord_4003913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003913).length < 2 ^ (prefixWord ++ tailWord_4003913).sum := by decide
  have hdescent : baseEnd_4003913 < baseStart_4003913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003923 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 3]
def baseStart_4003923 : Nat := 118140960795 + 4003923 * 2 ^ 59
def prefixEnd_4003923 : Nat := 4983230072969 + 3 ^ 40 * 4003923 * 2
def baseEnd_4003923 : Nat := 2055937002592043366548799

theorem tailTrace_4003923 : CollatzResearch.WordTrace tailWord_4003923 prefixEnd_4003923 2055937002592043366548799 := by
  unfold tailWord_4003923
  simp only [CollatzResearch.WordTrace]
  refine ⟨146035069073478261452168423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97356712715652174301445615 146035069073478261452168423)
  ·
    refine ⟨219052603610217392178252635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146035069073478261452168423 219052603610217392178252635)
    ·
      refine ⟨328578905415326088267378953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219052603610217392178252635 328578905415326088267378953)
      ·
        refine ⟨246434179061494566200534215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328578905415326088267378953 246434179061494566200534215)
        ·
          refine ⟨369651268592241849300801323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246434179061494566200534215 369651268592241849300801323)
          ·
            refine ⟨554476902888362773951201985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369651268592241849300801323 554476902888362773951201985)
            ·
              refine ⟨415857677166272080463401489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554476902888362773951201985 415857677166272080463401489)
              ·
                refine ⟨311893257874704060347551117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415857677166272080463401489 311893257874704060347551117)
                ·
                  refine ⟨116959971703014022630331669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311893257874704060347551117 116959971703014022630331669)
                  ·
                    refine ⟨5482498673578782310796797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116959971703014022630331669 5482498673578782310796797)
                    ·
                      refine ⟨2055937002592043366548799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5482498673578782310796797 2055937002592043366548799)
                      ·
                        rfl

theorem cell23_4003923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_4003923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003923 prefixEnd_4003923 := by exact prefixLift 4003923
  have htrace : WordTrace (prefixWord ++ tailWord_4003923) baseStart_4003923 baseEnd_4003923 := by
    simpa [prefixWord, tailWord_4003923, baseEnd_4003923] using wordTrace_append hprefix tailTrace_4003923
  have hstable : (prefixWord ++ tailWord_4003923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003923).length < 2 ^ (prefixWord ++ tailWord_4003923).sum := by decide
  have hdescent : baseEnd_4003923 < baseStart_4003923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003937 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_4003937 : Nat := 118140960795 + 4003937 * 2 ^ 59
def prefixEnd_4003937 : Nat := 4983230072969 + 3 ^ 40 * 4003937 * 2
def baseEnd_4003937 : Nat := 2055944191321206311773735

theorem tailTrace_4003937 : CollatzResearch.WordTrace tailWord_4003937 prefixEnd_4003937 2055944191321206311773735 := by
  unfold tailWord_4003937
  simp only [CollatzResearch.WordTrace]
  refine ⟨146035579695427541843178065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97357053130285027895452043 146035579695427541843178065)
  ·
    refine ⟨109526684771570656382383549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146035579695427541843178065 109526684771570656382383549)
    ·
      refine ⟨41072506789338996143393831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109526684771570656382383549 41072506789338996143393831)
      ·
        refine ⟨61608760184008494215090747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41072506789338996143393831 61608760184008494215090747)
        ·
          refine ⟨92413140276012741322636121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61608760184008494215090747 92413140276012741322636121)
          ·
            refine ⟨69309855207009555991977091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92413140276012741322636121 69309855207009555991977091)
            ·
              refine ⟨103964782810514333987965637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69309855207009555991977091 103964782810514333987965637)
              ·
                refine ⟨19493396776971437622743557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103964782810514333987965637 19493396776971437622743557)
                ·
                  refine ⟨3655011895682144554264417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19493396776971437622743557 3655011895682144554264417)
                  ·
                    refine ⟨2741258921761608415698313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655011895682144554264417 2741258921761608415698313)
                    ·
                      refine ⟨2055944191321206311773735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741258921761608415698313 2055944191321206311773735)
                      ·
                        rfl

theorem cell23_4003937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_4003937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003937 prefixEnd_4003937 := by exact prefixLift 4003937
  have htrace : WordTrace (prefixWord ++ tailWord_4003937) baseStart_4003937 baseEnd_4003937 := by
    simpa [prefixWord, tailWord_4003937, baseEnd_4003937] using wordTrace_append hprefix tailTrace_4003937
  have hstable : (prefixWord ++ tailWord_4003937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003937).length < 2 ^ (prefixWord ++ tailWord_4003937).sum := by decide
  have hdescent : baseEnd_4003937 < baseStart_4003937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003941 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 1, 3, 2]
def baseStart_4003941 : Nat := 118140960795 + 4003941 * 2 ^ 59
def prefixEnd_4003941 : Nat := 4983230072969 + 3 ^ 40 * 4003941 * 2
def baseEnd_4003941 : Nat := 2055946245243824296123717

theorem tailTrace_4003941 : CollatzResearch.WordTrace tailWord_4003941 prefixEnd_4003941 2055946245243824296123717 := by
  unfold tailWord_4003941
  simp only [CollatzResearch.WordTrace]
  refine ⟨146035725587413050526323677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97357150391608700350882451 146035725587413050526323677)
  ·
    refine ⟨54763397095279893947371379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146035725587413050526323677 54763397095279893947371379)
    ·
      refine ⟨82145095642919840921057069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54763397095279893947371379 82145095642919840921057069)
      ·
        refine ⟨30804410866094940345396401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82145095642919840921057069 30804410866094940345396401)
        ·
          refine ⟨23103308149571205259047301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30804410866094940345396401 23103308149571205259047301)
          ·
            refine ⟨4331870278044600986071369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23103308149571205259047301 4331870278044600986071369)
            ·
              refine ⟨3248902708533450739553527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4331870278044600986071369 3248902708533450739553527)
              ·
                refine ⟨4873354062800176109330291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248902708533450739553527 4873354062800176109330291)
                ·
                  refine ⟨7310031094200264163995437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873354062800176109330291 7310031094200264163995437)
                  ·
                    refine ⟨2741261660325099061498289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7310031094200264163995437 2741261660325099061498289)
                    ·
                      refine ⟨2055946245243824296123717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741261660325099061498289 2055946245243824296123717)
                      ·
                        rfl

theorem cell23_4003941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_4003941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003941 prefixEnd_4003941 := by exact prefixLift 4003941
  have htrace : WordTrace (prefixWord ++ tailWord_4003941) baseStart_4003941 baseEnd_4003941 := by
    simpa [prefixWord, tailWord_4003941, baseEnd_4003941] using wordTrace_append hprefix tailTrace_4003941
  have hstable : (prefixWord ++ tailWord_4003941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003941).length < 2 ^ (prefixWord ++ tailWord_4003941).sum := by decide
  have hdescent : baseEnd_4003941 < baseStart_4003941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003943 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 9]
def baseStart_4003943 : Nat := 118140960795 + 4003943 * 2 ^ 59
def prefixEnd_4003943 : Nat := 4983230072969 + 3 ^ 40 * 4003943 * 2
def baseEnd_4003943 : Nat := 228438585800570365366523

theorem tailTrace_4003943 : CollatzResearch.WordTrace tailWord_4003943 prefixEnd_4003943 228438585800570365366523 := by
  unfold tailWord_4003943
  simp only [CollatzResearch.WordTrace]
  refine ⟨146035798533405804867896483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97357199022270536578597655 146035798533405804867896483)
  ·
    refine ⟨219053697800108707301844725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146035798533405804867896483 219053697800108707301844725)
    ·
      refine ⟨20536284168760191309547943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219053697800108707301844725 20536284168760191309547943)
      ·
        refine ⟨30804426253140286964321915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20536284168760191309547943 30804426253140286964321915)
        ·
          refine ⟨46206639379710430446482873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30804426253140286964321915 46206639379710430446482873)
          ·
            refine ⟨34654979534782822834862155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46206639379710430446482873 34654979534782822834862155)
            ·
              refine ⟨51982469302174234252293233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34654979534782822834862155 51982469302174234252293233)
              ·
                refine ⟨38986851976630675689219925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51982469302174234252293233 38986851976630675689219925)
                ·
                  refine ⟨228438585800570365366523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38986851976630675689219925 228438585800570365366523)
                  ·
                    rfl

theorem cell23_4003943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 9].length) (baseStart_4003943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003943 prefixEnd_4003943 := by exact prefixLift 4003943
  have htrace : WordTrace (prefixWord ++ tailWord_4003943) baseStart_4003943 baseEnd_4003943 := by
    simpa [prefixWord, tailWord_4003943, baseEnd_4003943] using wordTrace_append hprefix tailTrace_4003943
  have hstable : (prefixWord ++ tailWord_4003943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003943).length < 2 ^ (prefixWord ++ tailWord_4003943).sum := by decide
  have hdescent : baseEnd_4003943 < baseStart_4003943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003950 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4003950 : Nat := 118140960795 + 4003950 * 2 ^ 59
def prefixEnd_4003950 : Nat := 4983230072969 + 3 ^ 40 * 4003950 * 2
def baseEnd_4003950 : Nat := 2055950866569714760911175

theorem tailTrace_4003950 : CollatzResearch.WordTrace tailWord_4003950 prefixEnd_4003950 2055950866569714760911175 := by
  unfold tailWord_4003950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18254506730547555632925163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97357369229586963375600869 18254506730547555632925163)
  ·
    refine ⟨27381760095821333449387745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18254506730547555632925163 27381760095821333449387745)
    ·
      refine ⟨20536320071866000087040809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27381760095821333449387745 20536320071866000087040809)
      ·
        refine ⟨15402240053899500065280607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20536320071866000087040809 15402240053899500065280607)
        ·
          refine ⟨23103360080849250097920911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15402240053899500065280607 23103360080849250097920911)
          ·
            refine ⟨34655040121273875146881367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23103360080849250097920911 34655040121273875146881367)
            ·
              refine ⟨51982560181910812720322051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34655040121273875146881367 51982560181910812720322051)
              ·
                refine ⟨77973840272866219080483077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51982560181910812720322051 77973840272866219080483077)
                ·
                  refine ⟨14620095051162416077590577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77973840272866219080483077 14620095051162416077590577)
                  ·
                    refine ⟨10965071288371812058192933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14620095051162416077590577 10965071288371812058192933)
                    ·
                      refine ⟨2055950866569714760911175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10965071288371812058192933 2055950866569714760911175)
                      ·
                        rfl

theorem cell23_4003950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4003950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003950 prefixEnd_4003950 := by exact prefixLift 4003950
  have htrace : WordTrace (prefixWord ++ tailWord_4003950) baseStart_4003950 baseEnd_4003950 := by
    simpa [prefixWord, tailWord_4003950, baseEnd_4003950] using wordTrace_append hprefix tailTrace_4003950
  have hstable : (prefixWord ++ tailWord_4003950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003950).length < 2 ^ (prefixWord ++ tailWord_4003950).sum := by decide
  have hdescent : baseEnd_4003950 < baseStart_4003950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003954 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4003954 : Nat := 118140960795 + 4003954 * 2 ^ 59
def prefixEnd_4003954 : Nat := 4983230072969 + 3 ^ 40 * 4003954 * 2
def baseEnd_4003954 : Nat := 2055952920492332745261157

theorem tailTrace_4003954 : CollatzResearch.WordTrace tailWord_4003954 prefixEnd_4003954 2055952920492332745261157 := by
  unfold tailWord_4003954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36509049934091488436636729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97357466490910635831031277 36509049934091488436636729)
  ·
    refine ⟨27381787450568616327477547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36509049934091488436636729 27381787450568616327477547)
    ·
      refine ⟨41072681175852924491216321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27381787450568616327477547 41072681175852924491216321)
      ·
        refine ⟨30804510881889693368412241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41072681175852924491216321 30804510881889693368412241)
        ·
          refine ⟨23103383161417270026309181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30804510881889693368412241 23103383161417270026309181)
          ·
            refine ⟨8663768685531476259865943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23103383161417270026309181 8663768685531476259865943)
            ·
              refine ⟨12995653028297214389798915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663768685531476259865943 12995653028297214389798915)
              ·
                refine ⟨19493479542445821584698373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995653028297214389798915 19493479542445821584698373)
                ·
                  refine ⟨3655027414208591547130945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19493479542445821584698373 3655027414208591547130945)
                  ·
                    refine ⟨2741270560656443660348209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655027414208591547130945 2741270560656443660348209)
                    ·
                      refine ⟨2055952920492332745261157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741270560656443660348209 2055952920492332745261157)
                      ·
                        rfl

theorem cell23_4003954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4003954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003954 prefixEnd_4003954 := by exact prefixLift 4003954
  have htrace : WordTrace (prefixWord ++ tailWord_4003954) baseStart_4003954 baseEnd_4003954 := by
    simpa [prefixWord, tailWord_4003954, baseEnd_4003954] using wordTrace_append hprefix tailTrace_4003954
  have hstable : (prefixWord ++ tailWord_4003954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003954).length < 2 ^ (prefixWord ++ tailWord_4003954).sum := by decide
  have hdescent : baseEnd_4003954 < baseStart_4003954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4003971 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 2, 2, 2]
def baseStart_4003971 : Nat := 118140960795 + 4003971 * 2 ^ 59
def prefixEnd_4003971 : Nat := 4983230072969 + 3 ^ 40 * 4003971 * 2
def baseEnd_4003971 : Nat := 2055961649663459178748579

theorem tailTrace_4003971 : CollatzResearch.WordTrace tailWord_4003971 prefixEnd_4003971 2055961649663459178748579 := by
  unfold tailWord_4003971
  simp only [CollatzResearch.WordTrace]
  refine ⟨146036819777304365649915767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97357879851536243766610511 146036819777304365649915767)
  ·
    refine ⟨219055229665956548474873651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146036819777304365649915767 219055229665956548474873651)
    ·
      refine ⟨328582844498934822712310477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219055229665956548474873651 328582844498934822712310477)
      ·
        refine ⟨123218566687100558517116429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328582844498934822712310477 123218566687100558517116429)
        ·
          refine ⟨46206962507662709443918661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123218566687100558517116429 46206962507662709443918661)
          ·
            refine ⟨8663805470186758020734749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46206962507662709443918661 8663805470186758020734749)
            ·
              refine ⟨3248927051320034257775531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8663805470186758020734749 3248927051320034257775531)
              ·
                refine ⟨4873390576980051386663297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248927051320034257775531 4873390576980051386663297)
                ·
                  refine ⟨3655042932735038539997473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4873390576980051386663297 3655042932735038539997473)
                  ·
                    refine ⟨2741282199551278904998105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655042932735038539997473 2741282199551278904998105)
                    ·
                      refine ⟨2055961649663459178748579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741282199551278904998105 2055961649663459178748579)
                      ·
                        rfl

theorem cell23_4003971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_4003971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4003971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4003971 prefixEnd_4003971 := by exact prefixLift 4003971
  have htrace : WordTrace (prefixWord ++ tailWord_4003971) baseStart_4003971 baseEnd_4003971 := by
    simpa [prefixWord, tailWord_4003971, baseEnd_4003971] using wordTrace_append hprefix tailTrace_4003971
  have hstable : (prefixWord ++ tailWord_4003971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4003971).length < 2 ^ (prefixWord ++ tailWord_4003971).sum := by decide
  have hdescent : baseEnd_4003971 < baseStart_4003971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4003971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004017 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4004017 : Nat := 118140960795 + 4004017 * 2 ^ 59
def prefixEnd_4004017 : Nat := 4983230072969 + 3 ^ 40 * 4004017 * 2
def baseEnd_4004017 : Nat := 2055985269773565998773367

theorem tailTrace_4004017 : CollatzResearch.WordTrace tailWord_4004017 prefixEnd_4004017 2055985269773565998773367 := by
  unfold tailWord_4004017
  simp only [CollatzResearch.WordTrace]
  refine ⟨146038497535137715506090305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97358998356758477004060203 146038497535137715506090305)
  ·
    refine ⟨109528873151353286629567729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146038497535137715506090305 109528873151353286629567729)
    ·
      refine ⟨82146654863514964972175797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109528873151353286629567729 82146654863514964972175797)
      ·
        refine ⟨7701248893454527966141481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82146654863514964972175797 7701248893454527966141481)
        ·
          refine ⟨5775936670090895974606111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7701248893454527966141481 5775936670090895974606111)
          ·
            refine ⟨8663905005136343961909167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775936670090895974606111 8663905005136343961909167)
            ·
              refine ⟨12995857507704515942863751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663905005136343961909167 12995857507704515942863751)
              ·
                refine ⟨19493786261556773914295627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995857507704515942863751 19493786261556773914295627)
                ·
                  refine ⟨29240679392335160871443441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19493786261556773914295627 29240679392335160871443441)
                  ·
                    refine ⟨21930509544251370653582581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29240679392335160871443441 21930509544251370653582581)
                    ·
                      refine ⟨2055985269773565998773367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21930509544251370653582581 2055985269773565998773367)
                      ·
                        rfl

theorem cell23_4004017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4004017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004017 prefixEnd_4004017 := by exact prefixLift 4004017
  have htrace : WordTrace (prefixWord ++ tailWord_4004017) baseStart_4004017 baseEnd_4004017 := by
    simpa [prefixWord, tailWord_4004017, baseEnd_4004017] using wordTrace_append hprefix tailTrace_4004017
  have hstable : (prefixWord ++ tailWord_4004017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004017).length < 2 ^ (prefixWord ++ tailWord_4004017).sum := by decide
  have hdescent : baseEnd_4004017 < baseStart_4004017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004047 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_4004047 : Nat := 118140960795 + 4004047 * 2 ^ 59
def prefixEnd_4004047 : Nat := 4983230072969 + 3 ^ 40 * 4004047 * 2
def baseEnd_4004047 : Nat := 2056000674193200881398229

theorem tailTrace_4004047 : CollatzResearch.WordTrace tailWord_4004047 prefixEnd_4004047 2056000674193200881398229 := by
  unfold tailWord_4004047
  simp only [CollatzResearch.WordTrace]
  refine ⟨146039591725029030629682395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97359727816686020419788263 146039591725029030629682395)
  ·
    refine ⟨219059387587543545944523593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146039591725029030629682395 219059387587543545944523593)
    ·
      refine ⟨164294540690657659458392695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219059387587543545944523593 164294540690657659458392695)
      ·
        refine ⟨246441811035986489187589043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164294540690657659458392695 246441811035986489187589043)
        ·
          refine ⟨369662716553979733781383565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246441811035986489187589043 369662716553979733781383565)
          ·
            refine ⟨138623518707742400168018837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369662716553979733781383565 138623518707742400168018837)
            ·
              refine ⟨6497977439425425007875883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138623518707742400168018837 6497977439425425007875883)
              ·
                refine ⟨9746966159138137511813825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497977439425425007875883 9746966159138137511813825)
                ·
                  refine ⟨7310224619353603133860369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9746966159138137511813825 7310224619353603133860369)
                  ·
                    refine ⟨5482668464515202350395277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7310224619353603133860369 5482668464515202350395277)
                    ·
                      refine ⟨2056000674193200881398229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5482668464515202350395277 2056000674193200881398229)
                      ·
                        rfl

theorem cell23_4004047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_4004047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004047 prefixEnd_4004047 := by exact prefixLift 4004047
  have htrace : WordTrace (prefixWord ++ tailWord_4004047) baseStart_4004047 baseEnd_4004047 := by
    simpa [prefixWord, tailWord_4004047, baseEnd_4004047] using wordTrace_append hprefix tailTrace_4004047
  have hstable : (prefixWord ++ tailWord_4004047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004047).length < 2 ^ (prefixWord ++ tailWord_4004047).sum := by decide
  have hdescent : baseEnd_4004047 < baseStart_4004047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004071 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 1, 4]
def baseStart_4004071 : Nat := 118140960795 + 4004071 * 2 ^ 59
def prefixEnd_4004071 : Nat := 4983230072969 + 3 ^ 40 * 4004071 * 2
def baseEnd_4004071 : Nat := 685337665909636262499373

theorem tailTrace_4004071 : CollatzResearch.WordTrace tailWord_4004071 prefixEnd_4004071 685337665909636262499373 := by
  unfold tailWord_4004071
  simp only [CollatzResearch.WordTrace]
  refine ⟨146040467076942082728556067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97360311384628055152370711 146040467076942082728556067)
  ·
    refine ⟨219060700615413124092834101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146040467076942082728556067 219060700615413124092834101)
    ·
      refine ⟨20536940682694980383703197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219060700615413124092834101 20536940682694980383703197)
      ·
        refine ⟨7701352756010617643888699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20536940682694980383703197 7701352756010617643888699)
        ·
          refine ⟨11552029134015926465833049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701352756010617643888699 11552029134015926465833049)
          ·
            refine ⟨8664021850511944849374787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11552029134015926465833049 8664021850511944849374787)
            ·
              refine ⟨12996032775767917274062181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664021850511944849374787 12996032775767917274062181)
              ·
                refine ⟨2436756145456484488886659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12996032775767917274062181 2436756145456484488886659)
                ·
                  refine ⟨3655134218184726733329989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436756145456484488886659 3655134218184726733329989)
                  ·
                    refine ⟨685337665909636262499373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655134218184726733329989 685337665909636262499373)
                    ·
                      rfl

theorem cell23_4004071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_4004071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004071 prefixEnd_4004071 := by exact prefixLift 4004071
  have htrace : WordTrace (prefixWord ++ tailWord_4004071) baseStart_4004071 baseEnd_4004071 := by
    simpa [prefixWord, tailWord_4004071, baseEnd_4004071] using wordTrace_append hprefix tailTrace_4004071
  have hstable : (prefixWord ++ tailWord_4004071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004071).length < 2 ^ (prefixWord ++ tailWord_4004071).sum := by decide
  have hdescent : baseEnd_4004071 < baseStart_4004071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004097 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 1, 5]
def baseStart_4004097 : Nat := 118140960795 + 4004097 * 2 ^ 59
def prefixEnd_4004097 : Nat := 4983230072969 + 3 ^ 40 * 4004097 * 2
def baseEnd_4004097 : Nat := 685342116075308561924333

theorem tailTrace_4004097 : CollatzResearch.WordTrace tailWord_4004097 prefixEnd_4004097 685342116075308561924333 := by
  unfold tailWord_4004097
  simp only [CollatzResearch.WordTrace]
  refine ⟨146041415374847889169002545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97360943583231926112668363 146041415374847889169002545)
  ·
    refine ⟨109531061531135916876751909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146041415374847889169002545 109531061531135916876751909)
    ·
      refine ⟨20537074037087984414390983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109531061531135916876751909 20537074037087984414390983)
      ·
        refine ⟨30805611055631976621586475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20537074037087984414390983 30805611055631976621586475)
        ·
          refine ⟨46208416583447964932379713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30805611055631976621586475 46208416583447964932379713)
          ·
            refine ⟨34656312437585973699284785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46208416583447964932379713 34656312437585973699284785)
            ·
              refine ⟨25992234328189480274463589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34656312437585973699284785 25992234328189480274463589)
              ·
                refine ⟨4873543936535527551461923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25992234328189480274463589 4873543936535527551461923)
                ·
                  refine ⟨7310315904803291327192885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873543936535527551461923 7310315904803291327192885)
                  ·
                    refine ⟨685342116075308561924333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7310315904803291327192885 685342116075308561924333)
                    ·
                      rfl

theorem cell23_4004097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_4004097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004097 prefixEnd_4004097 := by exact prefixLift 4004097
  have htrace : WordTrace (prefixWord ++ tailWord_4004097) baseStart_4004097 baseEnd_4004097 := by
    simpa [prefixWord, tailWord_4004097, baseEnd_4004097] using wordTrace_append hprefix tailTrace_4004097
  have hstable : (prefixWord ++ tailWord_4004097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004097).length < 2 ^ (prefixWord ++ tailWord_4004097).sum := by decide
  have hdescent : baseEnd_4004097 < baseStart_4004097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004104 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_4004104 : Nat := 118140960795 + 4004104 * 2 ^ 59
def prefixEnd_4004104 : Nat := 4983230072969 + 3 ^ 40 * 4004104 * 2
def baseEnd_4004104 : Nat := 2056029942590507158385467

theorem tailTrace_4004104 : CollatzResearch.WordTrace tailWord_4004104 prefixEnd_4004104 2056029942590507158385467 := by
  unfold tailWord_4004104
  simp only [CollatzResearch.WordTrace]
  refine ⟨73020835342911264682253683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97361113790548352909671577 73020835342911264682253683)
  ·
    refine ⟨109531253014366897023380525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73020835342911264682253683 109531253014366897023380525)
    ·
      refine ⟨41074219880387586383767697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109531253014366897023380525 41074219880387586383767697)
      ·
        refine ⟨30805664910290689787825773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41074219880387586383767697 30805664910290689787825773)
        ·
          refine ⟨11552124341359008670434665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30805664910290689787825773 11552124341359008670434665)
          ·
            refine ⟨8664093256019256502825999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11552124341359008670434665 8664093256019256502825999)
            ·
              refine ⟨12996139884028884754238999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664093256019256502825999 12996139884028884754238999)
              ·
                refine ⟨19494209826043327131358499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12996139884028884754238999 19494209826043327131358499)
                ·
                  refine ⟨29241314739064990697037749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19494209826043327131358499 29241314739064990697037749)
                  ·
                    refine ⟨2741373256787342877847289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29241314739064990697037749 2741373256787342877847289)
                    ·
                      refine ⟨2056029942590507158385467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741373256787342877847289 2056029942590507158385467)
                      ·
                        rfl

theorem cell23_4004104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_4004104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004104 prefixEnd_4004104 := by exact prefixLift 4004104
  have htrace : WordTrace (prefixWord ++ tailWord_4004104) baseStart_4004104 baseEnd_4004104 := by
    simpa [prefixWord, tailWord_4004104, baseEnd_4004104] using wordTrace_append hprefix tailTrace_4004104
  have hstable : (prefixWord ++ tailWord_4004104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004104).length < 2 ^ (prefixWord ++ tailWord_4004104).sum := by decide
  have hdescent : baseEnd_4004104 < baseStart_4004104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004154 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_4004154 : Nat := 118140960795 + 4004154 * 2 ^ 59
def prefixEnd_4004154 : Nat := 4983230072969 + 3 ^ 40 * 4004154 * 2
def baseEnd_4004154 : Nat := 2056055616623231962760237

theorem tailTrace_4004154 : CollatzResearch.WordTrace tailWord_4004154 prefixEnd_4004154 2056055616623231962760237 := by
  unfold tailWord_4004154
  simp only [CollatzResearch.WordTrace]
  refine ⟨36510873583910346975956879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97362329557094258602551677 36510873583910346975956879)
  ·
    refine ⟨54766310375865520463935319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36510873583910346975956879 54766310375865520463935319)
    ·
      refine ⟨82149465563798280695902979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54766310375865520463935319 82149465563798280695902979)
      ·
        refine ⟨123224198345697421043854469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82149465563798280695902979 123224198345697421043854469)
        ·
          refine ⟨23104537189818266445722713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123224198345697421043854469 23104537189818266445722713)
          ·
            refine ⟨17328402892363699834292035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23104537189818266445722713 17328402892363699834292035)
            ·
              refine ⟨25992604338545549751438053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17328402892363699834292035 25992604338545549751438053)
              ·
                refine ⟨4873613313477290578394635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25992604338545549751438053 4873613313477290578394635)
                ·
                  refine ⟨7310419970215935867591953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873613313477290578394635 7310419970215935867591953)
                  ·
                    refine ⟨5482814977661951900693965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7310419970215935867591953 5482814977661951900693965)
                    ·
                      refine ⟨2056055616623231962760237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5482814977661951900693965 2056055616623231962760237)
                      ·
                        rfl

theorem cell23_4004154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_4004154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004154 prefixEnd_4004154 := by exact prefixLift 4004154
  have htrace : WordTrace (prefixWord ++ tailWord_4004154) baseStart_4004154 baseEnd_4004154 := by
    simpa [prefixWord, tailWord_4004154, baseEnd_4004154] using wordTrace_append hprefix tailTrace_4004154
  have hstable : (prefixWord ++ tailWord_4004154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004154).length < 2 ^ (prefixWord ++ tailWord_4004154).sum := by decide
  have hdescent : baseEnd_4004154 < baseStart_4004154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004167 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_4004167 : Nat := 118140960795 + 4004167 * 2 ^ 59
def prefixEnd_4004167 : Nat := 4983230072969 + 3 ^ 40 * 4004167 * 2
def baseEnd_4004167 : Nat := 2056062291871740411897677

theorem tailTrace_4004167 : CollatzResearch.WordTrace tailWord_4004167 prefixEnd_4004167 2056062291871740411897677 := by
  unfold tailWord_4004167
  simp only [CollatzResearch.WordTrace]
  refine ⟨146043968484594291124050755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97362645656396194082700503 146043968484594291124050755)
  ·
    refine ⟨219065952726891436686076133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146043968484594291124050755 219065952726891436686076133)
    ·
      refine ⟨41074866136292144378639275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219065952726891436686076133 41074866136292144378639275)
      ·
        refine ⟨61612299204438216567958913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41074866136292144378639275 61612299204438216567958913)
        ·
          refine ⟨46209224403328662425969185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61612299204438216567958913 46209224403328662425969185)
          ·
            refine ⟨34656918302496496819476889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46209224403328662425969185 34656918302496496819476889)
            ·
              refine ⟨25992688726872372614607667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34656918302496496819476889 25992688726872372614607667)
              ·
                refine ⟨38989033090308558921911501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25992688726872372614607667 38989033090308558921911501)
                ·
                  refine ⟨14620887408865709595716813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38989033090308558921911501 14620887408865709595716813)
                  ·
                    refine ⟨5482832778324641098393805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14620887408865709595716813 5482832778324641098393805)
                    ·
                      refine ⟨2056062291871740411897677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5482832778324641098393805 2056062291871740411897677)
                      ·
                        rfl

theorem cell23_4004167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_4004167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004167 prefixEnd_4004167 := by exact prefixLift 4004167
  have htrace : WordTrace (prefixWord ++ tailWord_4004167) baseStart_4004167 baseEnd_4004167 := by
    simpa [prefixWord, tailWord_4004167, baseEnd_4004167] using wordTrace_append hprefix tailTrace_4004167
  have hstable : (prefixWord ++ tailWord_4004167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004167).length < 2 ^ (prefixWord ++ tailWord_4004167).sum := by decide
  have hdescent : baseEnd_4004167 < baseStart_4004167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004168 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_4004168 : Nat := 118140960795 + 4004168 * 2 ^ 59
def prefixEnd_4004168 : Nat := 4983230072969 + 3 ^ 40 * 4004168 * 2
def baseEnd_4004168 : Nat := 2056062805352394907985173

theorem tailTrace_4004168 : CollatzResearch.WordTrace tailWord_4004168 prefixEnd_4004168 2056062805352394907985173 := by
  unfold tailWord_4004168
  simp only [CollatzResearch.WordTrace]
  refine ⟨73022002478795334147418579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97362669971727112196558105 73022002478795334147418579)
  ·
    refine ⟨109533003718193001221127869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73022002478795334147418579 109533003718193001221127869)
    ·
      refine ⟨41074876394322375457922951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109533003718193001221127869 41074876394322375457922951)
      ·
        refine ⟨61612314591483563186884427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41074876394322375457922951 61612314591483563186884427)
        ·
          refine ⟨92418471887225344780326641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61612314591483563186884427 92418471887225344780326641)
          ·
            refine ⟨69313853915419008585244981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92418471887225344780326641 69313853915419008585244981)
            ·
              refine ⟨6498173804570532054866717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69313853915419008585244981 6498173804570532054866717)
              ·
                refine ⟨2436815176713949520575019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6498173804570532054866717 2436815176713949520575019)
                ·
                  refine ⟨3655222765070924280862529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436815176713949520575019 3655222765070924280862529)
                  ·
                    refine ⟨2741417073803193210646897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655222765070924280862529 2741417073803193210646897)
                    ·
                      refine ⟨2056062805352394907985173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741417073803193210646897 2056062805352394907985173)
                      ·
                        rfl

theorem cell23_4004168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_4004168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004168 prefixEnd_4004168 := by exact prefixLift 4004168
  have htrace : WordTrace (prefixWord ++ tailWord_4004168) baseStart_4004168 baseEnd_4004168 := by
    simpa [prefixWord, tailWord_4004168, baseEnd_4004168] using wordTrace_append hprefix tailTrace_4004168
  have hstable : (prefixWord ++ tailWord_4004168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004168).length < 2 ^ (prefixWord ++ tailWord_4004168).sum := by decide
  have hdescent : baseEnd_4004168 < baseStart_4004168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004170 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_4004170 : Nat := 118140960795 + 4004170 * 2 ^ 59
def prefixEnd_4004170 : Nat := 4983230072969 + 3 ^ 40 * 4004170 * 2
def baseEnd_4004170 : Nat := 685354610771234633386721

theorem tailTrace_4004170 : CollatzResearch.WordTrace tailWord_4004170 prefixEnd_4004170 685354610771234633386721 := by
  unfold tailWord_4004170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36511019475895855659102491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97362718602388948424273309 36511019475895855659102491)
  ·
    refine ⟨54766529213843783488653737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36511019475895855659102491 54766529213843783488653737)
    ·
      refine ⟨41074896910382837616490303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54766529213843783488653737 41074896910382837616490303)
      ·
        refine ⟨61612345365574256424735455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41074896910382837616490303 61612345365574256424735455)
        ·
          refine ⟨92418518048361384637103183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61612345365574256424735455 92418518048361384637103183)
          ·
            refine ⟨138627777072542076955654775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92418518048361384637103183 138627777072542076955654775)
            ·
              refine ⟨207941665608813115433482163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138627777072542076955654775 207941665608813115433482163)
              ·
                refine ⟨311912498413219673150223245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207941665608813115433482163 311912498413219673150223245)
                ·
                  refine ⟨116967186904957377431333717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311912498413219673150223245 116967186904957377431333717)
                  ·
                    refine ⟨685354610771234633386721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116967186904957377431333717 685354610771234633386721)
                    ·
                      rfl

theorem cell23_4004170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_4004170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004170 prefixEnd_4004170 := by exact prefixLift 4004170
  have htrace : WordTrace (prefixWord ++ tailWord_4004170) baseStart_4004170 baseEnd_4004170 := by
    simpa [prefixWord, tailWord_4004170, baseEnd_4004170] using wordTrace_append hprefix tailTrace_4004170
  have hstable : (prefixWord ++ tailWord_4004170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004170).length < 2 ^ (prefixWord ++ tailWord_4004170).sum := by decide
  have hdescent : baseEnd_4004170 < baseStart_4004170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004228 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_4004228 : Nat := 118140960795 + 4004228 * 2 ^ 59
def prefixEnd_4004228 : Nat := 4983230072969 + 3 ^ 40 * 4004228 * 2
def baseEnd_4004228 : Nat := 2056093614191664673234897

theorem tailTrace_4004228 : CollatzResearch.WordTrace tailWord_4004228 prefixEnd_4004228 2056093614191664673234897 := by
  unfold tailWord_4004228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73023096668686649271010669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97364128891582199028014225 73023096668686649271010669)
  ·
    refine ⟨27383661250757493476629001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73023096668686649271010669 27383661250757493476629001)
    ·
      refine ⟨20537745938068120107471751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27383661250757493476629001 20537745938068120107471751)
      ·
        refine ⟨30806618907102180161207627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20537745938068120107471751 30806618907102180161207627)
        ·
          refine ⟨46209928360653270241811441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30806618907102180161207627 46209928360653270241811441)
          ·
            refine ⟨34657446270489952681358581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46209928360653270241811441 34657446270489952681358581)
            ·
              refine ⟨3249135587858433063877367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34657446270489952681358581 3249135587858433063877367)
              ·
                refine ⟨4873703381787649595816051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249135587858433063877367 4873703381787649595816051)
                ·
                  refine ⟨7310555072681474393724077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873703381787649595816051 7310555072681474393724077)
                  ·
                    refine ⟨2741458152255552897646529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7310555072681474393724077 2741458152255552897646529)
                    ·
                      refine ⟨2056093614191664673234897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741458152255552897646529 2056093614191664673234897)
                      ·
                        rfl

theorem cell23_4004228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_4004228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004228 prefixEnd_4004228 := by exact prefixLift 4004228
  have htrace : WordTrace (prefixWord ++ tailWord_4004228) baseStart_4004228 baseEnd_4004228 := by
    simpa [prefixWord, tailWord_4004228, baseEnd_4004228] using wordTrace_append hprefix tailTrace_4004228
  have hstable : (prefixWord ++ tailWord_4004228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004228).length < 2 ^ (prefixWord ++ tailWord_4004228).sum := by decide
  have hdescent : baseEnd_4004228 < baseStart_4004228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004258 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_4004258 : Nat := 118140960795 + 4004258 * 2 ^ 59
def prefixEnd_4004258 : Nat := 4983230072969 + 3 ^ 40 * 4004258 * 2
def baseEnd_4004258 : Nat := 2056109018611299555859759

theorem tailTrace_4004258 : CollatzResearch.WordTrace tailWord_4004258 prefixEnd_4004258 2056109018611299555859759 := by
  unfold tailWord_4004258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36511821881816153416403357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97364858351509742443742285 36511821881816153416403357)
  ·
    refine ⟨13691933205681057531151259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36511821881816153416403357 13691933205681057531151259)
    ·
      refine ⟨20537899808521586296726889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13691933205681057531151259 20537899808521586296726889)
      ·
        refine ⟨15403424856391189722545167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20537899808521586296726889 15403424856391189722545167)
        ·
          refine ⟨23105137284586784583817751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15403424856391189722545167 23105137284586784583817751)
          ·
            refine ⟨34657705926880176875726627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23105137284586784583817751 34657705926880176875726627)
            ·
              refine ⟨51986558890320265313589941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34657705926880176875726627 51986558890320265313589941)
              ·
                refine ⟨4873739895967524873149057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51986558890320265313589941 4873739895967524873149057)
                ·
                  refine ⟨3655304921975643654861793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4873739895967524873149057 3655304921975643654861793)
                  ·
                    refine ⟨2741478691481732741146345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655304921975643654861793 2741478691481732741146345)
                    ·
                      refine ⟨2056109018611299555859759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741478691481732741146345 2056109018611299555859759)
                      ·
                        rfl

theorem cell23_4004258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_4004258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004258 prefixEnd_4004258 := by exact prefixLift 4004258
  have htrace : WordTrace (prefixWord ++ tailWord_4004258) baseStart_4004258 baseEnd_4004258 := by
    simpa [prefixWord, tailWord_4004258, baseEnd_4004258] using wordTrace_append hprefix tailTrace_4004258
  have hstable : (prefixWord ++ tailWord_4004258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004258).length < 2 ^ (prefixWord ++ tailWord_4004258).sum := by decide
  have hdescent : baseEnd_4004258 < baseStart_4004258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004264 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 9]
def baseStart_4004264 : Nat := 118140960795 + 4004264 * 2 ^ 59
def prefixEnd_4004264 : Nat := 4983230072969 + 3 ^ 40 * 4004264 * 2
def baseEnd_4004264 : Nat := 228456899943914059153859

theorem tailTrace_4004264 : CollatzResearch.WordTrace tailWord_4004264 prefixEnd_4004264 228456899943914059153859 := by
  unfold tailWord_4004264
  simp only [CollatzResearch.WordTrace]
  refine ⟨73023753182621438345165923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97365004243495251126887897 73023753182621438345165923)
  ·
    refine ⟨109535629773932157517748885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73023753182621438345165923 109535629773932157517748885)
    ·
      refine ⟨5134482645653069883644479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109535629773932157517748885 5134482645653069883644479)
      ·
        refine ⟨7701723968479604825466719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134482645653069883644479 7701723968479604825466719)
        ·
          refine ⟨11552585952719407238200079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701723968479604825466719 11552585952719407238200079)
          ·
            refine ⟨17328878929079110857300119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552585952719407238200079 17328878929079110857300119)
            ·
              refine ⟨25993318393618666285950179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17328878929079110857300119 25993318393618666285950179)
              ·
                refine ⟨38989977590427999428925269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25993318393618666285950179 38989977590427999428925269)
                ·
                  refine ⟨228456899943914059153859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38989977590427999428925269 228456899943914059153859)
                  ·
                    rfl

theorem cell23_4004264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 9].length) (baseStart_4004264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004264 prefixEnd_4004264 := by exact prefixLift 4004264
  have htrace : WordTrace (prefixWord ++ tailWord_4004264) baseStart_4004264 baseEnd_4004264 := by
    simpa [prefixWord, tailWord_4004264, baseEnd_4004264] using wordTrace_append hprefix tailTrace_4004264
  have hstable : (prefixWord ++ tailWord_4004264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004264).length < 2 ^ (prefixWord ++ tailWord_4004264).sum := by decide
  have hdescent : baseEnd_4004264 < baseStart_4004264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004281 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 5]
def baseStart_4004281 : Nat := 118140960795 + 4004281 * 2 ^ 59
def prefixEnd_4004281 : Nat := 4983230072969 + 3 ^ 40 * 4004281 * 2
def baseEnd_4004281 : Nat := 228457869851816996208017

theorem tailTrace_4004281 : CollatzResearch.WordTrace tailWord_4004281 prefixEnd_4004281 228457869851816996208017 := by
  unfold tailWord_4004281
  simp only [CollatzResearch.WordTrace]
  refine ⟨146048126406181288593700697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97365417604120859062467131 146048126406181288593700697)
  ·
    refine ⟨109536094804635966445275523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146048126406181288593700697 109536094804635966445275523)
    ·
      refine ⟨164304142206953949667913285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109536094804635966445275523 164304142206953949667913285)
      ·
        refine ⟨30807026663803865562733741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164304142206953949667913285 30807026663803865562733741)
        ·
          refine ⟨11552634998926449586025153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30807026663803865562733741 11552634998926449586025153)
          ·
            refine ⟨8664476249194837189518865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11552634998926449586025153 8664476249194837189518865)
            ·
              refine ⟨6498357186896127892139149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8664476249194837189518865 6498357186896127892139149)
              ·
                refine ⟨2436883945086047959552181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6498357186896127892139149 2436883945086047959552181)
                ·
                  refine ⟨228457869851816996208017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2436883945086047959552181 228457869851816996208017)
                  ·
                    rfl

theorem cell23_4004281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 5].length) (baseStart_4004281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004281 prefixEnd_4004281 := by exact prefixLift 4004281
  have htrace : WordTrace (prefixWord ++ tailWord_4004281) baseStart_4004281 baseEnd_4004281 := by
    simpa [prefixWord, tailWord_4004281, baseEnd_4004281] using wordTrace_append hprefix tailTrace_4004281
  have hstable : (prefixWord ++ tailWord_4004281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004281).length < 2 ^ (prefixWord ++ tailWord_4004281).sum := by decide
  have hdescent : baseEnd_4004281 < baseStart_4004281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004292 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4004292 : Nat := 118140960795 + 4004292 * 2 ^ 59
def prefixEnd_4004292 : Nat := 4983230072969 + 3 ^ 40 * 4004292 * 2
def baseEnd_4004292 : Nat := 2056126476953552422834603

theorem tailTrace_4004292 : CollatzResearch.WordTrace tailWord_4004292 prefixEnd_4004292 2056126476953552422834603 := by
  unfold tailWord_4004292
  simp only [CollatzResearch.WordTrace]
  refine ⟨73024263804570718736175565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97365685072760958314900753 73024263804570718736175565)
  ·
    refine ⟨27384098926714019526065837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73024263804570718736175565 27384098926714019526065837)
    ·
      refine ⟨10269037097517757322274689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27384098926714019526065837 10269037097517757322274689)
      ·
        refine ⟨7701777823138317991706017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10269037097517757322274689 7701777823138317991706017)
        ·
          refine ⟨5776333367353738493779513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7701777823138317991706017 5776333367353738493779513)
          ·
            refine ⟨4332250025515303870334635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5776333367353738493779513 4332250025515303870334635)
            ·
              refine ⟨6498375038272955805501953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332250025515303870334635 6498375038272955805501953)
              ·
                refine ⟨4873781278704716854126465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498375038272955805501953 4873781278704716854126465)
                ·
                  refine ⟨3655335959028537640594849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4873781278704716854126465 3655335959028537640594849)
                  ·
                    refine ⟨2741501969271403230446137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655335959028537640594849 2741501969271403230446137)
                    ·
                      refine ⟨2056126476953552422834603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741501969271403230446137 2056126476953552422834603)
                      ·
                        rfl

theorem cell23_4004292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4004292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004292 prefixEnd_4004292 := by exact prefixLift 4004292
  have htrace : WordTrace (prefixWord ++ tailWord_4004292) baseStart_4004292 baseEnd_4004292 := by
    simpa [prefixWord, tailWord_4004292, baseEnd_4004292] using wordTrace_append hprefix tailTrace_4004292
  have hstable : (prefixWord ++ tailWord_4004292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004292).length < 2 ^ (prefixWord ++ tailWord_4004292).sum := by decide
  have hdescent : baseEnd_4004292 < baseStart_4004292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004337 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 10]
def baseStart_4004337 : Nat := 118140960795 + 4004337 * 2 ^ 59
def prefixEnd_4004337 : Nat := 4983230072969 + 3 ^ 40 * 4004337 * 2
def baseEnd_4004337 : Nat := 228461064842556082974655

theorem tailTrace_4004337 : CollatzResearch.WordTrace tailWord_4004337 prefixEnd_4004337 228461064842556082974655 := by
  unfold tailWord_4004337
  simp only [CollatzResearch.WordTrace]
  refine ⟨146050168893978410157739265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97366779262652273438492843 146050168893978410157739265)
  ·
    refine ⟨109537626670483807618304449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146050168893978410157739265 109537626670483807618304449)
    ·
      refine ⟨82153220002862855713728337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109537626670483807618304449 82153220002862855713728337)
      ·
        refine ⟨61614915002147141785296253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82153220002862855713728337 61614915002147141785296253)
        ·
          refine ⟨23105593125805178169486095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61614915002147141785296253 23105593125805178169486095)
          ·
            refine ⟨34658389688707767254229143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23105593125805178169486095 34658389688707767254229143)
            ·
              refine ⟨51987584533061650881343715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34658389688707767254229143 51987584533061650881343715)
              ·
                refine ⟨77981376799592476322015573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51987584533061650881343715 77981376799592476322015573)
                ·
                  refine ⟨228461064842556082974655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 77981376799592476322015573 228461064842556082974655)
                  ·
                    rfl

theorem cell23_4004337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_4004337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004337 prefixEnd_4004337 := by exact prefixLift 4004337
  have htrace : WordTrace (prefixWord ++ tailWord_4004337) baseStart_4004337 baseEnd_4004337 := by
    simpa [prefixWord, tailWord_4004337, baseEnd_4004337] using wordTrace_append hprefix tailTrace_4004337
  have hstable : (prefixWord ++ tailWord_4004337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004337).length < 2 ^ (prefixWord ++ tailWord_4004337).sum := by decide
  have hdescent : baseEnd_4004337 < baseStart_4004337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004357 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_4004357 : Nat := 118140960795 + 4004357 * 2 ^ 59
def prefixEnd_4004357 : Nat := 4983230072969 + 3 ^ 40 * 4004357 * 2
def baseEnd_4004357 : Nat := 2056159853196094668521803

theorem tailTrace_4004357 : CollatzResearch.WordTrace tailWord_4004357 prefixEnd_4004357 2056159853196094668521803 := by
  unfold tailWord_4004357
  simp only [CollatzResearch.WordTrace]
  refine ⟨146050898353905953573467325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97367265569270635715644883 146050898353905953573467325)
  ·
    refine ⟨54769086882714732590050247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146050898353905953573467325 54769086882714732590050247)
    ·
      refine ⟨82153630324072098885075371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54769086882714732590050247 82153630324072098885075371)
      ·
        refine ⟨123230445486108148327613057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82153630324072098885075371 123230445486108148327613057)
        ·
          refine ⟨92422834114581111245709793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123230445486108148327613057 92422834114581111245709793)
          ·
            refine ⟨69317125585935833434282345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92422834114581111245709793 69317125585935833434282345)
            ·
              refine ⟨51987844189451875075711759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69317125585935833434282345 51987844189451875075711759)
              ·
                refine ⟨77981766284177812613567639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51987844189451875075711759 77981766284177812613567639)
                ·
                  refine ⟨116972649426266718920351459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77981766284177812613567639 116972649426266718920351459)
                  ·
                    refine ⟨175458974139400078380527189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116972649426266718920351459 175458974139400078380527189)
                    ·
                      refine ⟨2056159853196094668521803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 175458974139400078380527189 2056159853196094668521803)
                      ·
                        rfl

theorem cell23_4004357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_4004357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004357 prefixEnd_4004357 := by exact prefixLift 4004357
  have htrace : WordTrace (prefixWord ++ tailWord_4004357) baseStart_4004357 baseEnd_4004357 := by
    simpa [prefixWord, tailWord_4004357, baseEnd_4004357] using wordTrace_append hprefix tailTrace_4004357
  have hstable : (prefixWord ++ tailWord_4004357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004357).length < 2 ^ (prefixWord ++ tailWord_4004357).sum := by decide
  have hdescent : baseEnd_4004357 < baseStart_4004357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004377 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_4004377 : Nat := 118140960795 + 4004377 * 2 ^ 59
def prefixEnd_4004377 : Nat := 4983230072969 + 3 ^ 40 * 4004377 * 2
def baseEnd_4004377 : Nat := 2056170122809184590271711

theorem tailTrace_4004377 : CollatzResearch.WordTrace tailWord_4004377 prefixEnd_4004377 2056170122809184590271711 := by
  unfold tailWord_4004377
  simp only [CollatzResearch.WordTrace]
  refine ⟨146051627813833496989195385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97367751875888997992796923 146051627813833496989195385)
  ·
    refine ⟨109538720860375122741896539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146051627813833496989195385 109538720860375122741896539)
    ·
      refine ⟨164308081290562684112844809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109538720860375122741896539 164308081290562684112844809)
      ·
        refine ⟨123231060967922013084633607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164308081290562684112844809 123231060967922013084633607)
        ·
          refine ⟨184846591451883019626950411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123231060967922013084633607 184846591451883019626950411)
          ·
            refine ⟨277269887177824529440425617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184846591451883019626950411 277269887177824529440425617)
            ·
              refine ⟨207952415383368397080319213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277269887177824529440425617 207952415383368397080319213)
              ·
                refine ⟨77982155768763148905119705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207952415383368397080319213 77982155768763148905119705)
                ·
                  refine ⟨58486616826572361678839779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77982155768763148905119705 58486616826572361678839779)
                  ·
                    refine ⟨87729925239858542518259669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58486616826572361678839779 87729925239858542518259669)
                    ·
                      refine ⟨2056170122809184590271711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87729925239858542518259669 2056170122809184590271711)
                      ·
                        rfl

theorem cell23_4004377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_4004377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004377 prefixEnd_4004377 := by exact prefixLift 4004377
  have htrace : WordTrace (prefixWord ++ tailWord_4004377) baseStart_4004377 baseEnd_4004377 := by
    simpa [prefixWord, tailWord_4004377, baseEnd_4004377] using wordTrace_append hprefix tailTrace_4004377
  have hstable : (prefixWord ++ tailWord_4004377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004377).length < 2 ^ (prefixWord ++ tailWord_4004377).sum := by decide
  have hdescent : baseEnd_4004377 < baseStart_4004377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004424 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_4004424 : Nat := 118140960795 + 4004424 * 2 ^ 59
def prefixEnd_4004424 : Nat := 4983230072969 + 3 ^ 40 * 4004424 * 2
def baseEnd_4004424 : Nat := 2056194256399945906383995

theorem tailTrace_4004424 : CollatzResearch.WordTrace tailWord_4004424 prefixEnd_4004424 2056194256399945906383995 := by
  unfold tailWord_4004424
  simp only [CollatzResearch.WordTrace]
  refine ⟨73026671022331612008078163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97368894696442149344104217 73026671022331612008078163)
  ·
    refine ⟨109540006533497418012117245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73026671022331612008078163 109540006533497418012117245)
    ·
      refine ⟨41077502450061531754543967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109540006533497418012117245 41077502450061531754543967)
      ·
        refine ⟨61616253675092297631815951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41077502450061531754543967 61616253675092297631815951)
        ·
          refine ⟨92424380512638446447723927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61616253675092297631815951 92424380512638446447723927)
          ·
            refine ⟨138636570768957669671585891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92424380512638446447723927 138636570768957669671585891)
            ·
              refine ⟨207954856153436504507378837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138636570768957669671585891 207954856153436504507378837)
              ·
                refine ⟨9747883882192336148783383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207954856153436504507378837 9747883882192336148783383)
                ·
                  refine ⟨14621825823288504223175075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9747883882192336148783383 14621825823288504223175075)
                  ·
                    refine ⟨21932738734932756334762613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14621825823288504223175075 21932738734932756334762613)
                    ·
                      refine ⟨2056194256399945906383995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21932738734932756334762613 2056194256399945906383995)
                      ·
                        rfl

theorem cell23_4004424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_4004424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004424 prefixEnd_4004424 := by exact prefixLift 4004424
  have htrace : WordTrace (prefixWord ++ tailWord_4004424) baseStart_4004424 baseEnd_4004424 := by
    simpa [prefixWord, tailWord_4004424, baseEnd_4004424] using wordTrace_append hprefix tailTrace_4004424
  have hstable : (prefixWord ++ tailWord_4004424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004424).length < 2 ^ (prefixWord ++ tailWord_4004424).sum := by decide
  have hdescent : baseEnd_4004424 < baseStart_4004424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004431 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 2, 4]
def baseStart_4004431 : Nat := 118140960795 + 4004431 * 2 ^ 59
def prefixEnd_4004431 : Nat := 4983230072969 + 3 ^ 40 * 4004431 * 2
def baseEnd_4004431 : Nat := 685399283588175792998821

theorem tailTrace_4004431 : CollatzResearch.WordTrace tailWord_4004431 prefixEnd_4004431 685399283588175792998821 := by
  unfold tailWord_4004431
  simp only [CollatzResearch.WordTrace]
  refine ⟨146053597355637864211661147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97369064903758576141107431 146053597355637864211661147)
  ·
    refine ⟨219080396033456796317491721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146053597355637864211661147 219080396033456796317491721)
    ·
      refine ⟨164310297025092597238118791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219080396033456796317491721 164310297025092597238118791)
      ·
        refine ⟨246465445537638895857178187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164310297025092597238118791 246465445537638895857178187)
        ·
          refine ⟨369698168306458343785767281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246465445537638895857178187 369698168306458343785767281)
          ·
            refine ⟨277273626229843757839325461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369698168306458343785767281 277273626229843757839325461)
            ·
              refine ⟨12997201229523926148718381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277273626229843757839325461 12997201229523926148718381)
              ·
                refine ⟨4873950461071472305769393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12997201229523926148718381 4873950461071472305769393)
                ·
                  refine ⟨3655462845803604229327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4873950461071472305769393 3655462845803604229327045)
                  ·
                    refine ⟨685399283588175792998821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655462845803604229327045 685399283588175792998821)
                    ·
                      rfl

theorem cell23_4004431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_4004431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004431 prefixEnd_4004431 := by exact prefixLift 4004431
  have htrace : WordTrace (prefixWord ++ tailWord_4004431) baseStart_4004431 baseEnd_4004431 := by
    simpa [prefixWord, tailWord_4004431, baseEnd_4004431] using wordTrace_append hprefix tailTrace_4004431
  have hstable : (prefixWord ++ tailWord_4004431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004431).length < 2 ^ (prefixWord ++ tailWord_4004431).sum := by decide
  have hdescent : baseEnd_4004431 < baseStart_4004431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004458 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_4004458 : Nat := 118140960795 + 4004458 * 2 ^ 59
def prefixEnd_4004458 : Nat := 4983230072969 + 3 ^ 40 * 4004458 * 2
def baseEnd_4004458 : Nat := 2056211714742198773358839

theorem tailTrace_4004458 : CollatzResearch.WordTrace tailWord_4004458 prefixEnd_4004458 2056211714742198773358839 := by
  unfold tailWord_4004458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36513645531635011955723507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97369721417693365215262685 36513645531635011955723507)
  ·
    refine ⟨54770468297452517933585261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36513645531635011955723507 54770468297452517933585261)
    ·
      refine ⟨20538925611544694225094473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54770468297452517933585261 20538925611544694225094473)
      ·
        refine ⟨15404194208658520668820855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20538925611544694225094473 15404194208658520668820855)
        ·
          refine ⟨23106291312987781003231283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15404194208658520668820855 23106291312987781003231283)
          ·
            refine ⟨34659436969481671504846925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23106291312987781003231283 34659436969481671504846925)
            ·
              refine ⟨12997288863555626814317597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34659436969481671504846925 12997288863555626814317597)
              ·
                refine ⟨4873983323833360055369099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12997288863555626814317597 4873983323833360055369099)
                ·
                  refine ⟨7310974985750040083053649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873983323833360055369099 7310974985750040083053649)
                  ·
                    refine ⟨5483231239312530062290237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7310974985750040083053649 5483231239312530062290237)
                    ·
                      refine ⟨2056211714742198773358839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5483231239312530062290237 2056211714742198773358839)
                      ·
                        rfl

theorem cell23_4004458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_4004458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004458 prefixEnd_4004458 := by exact prefixLift 4004458
  have htrace : WordTrace (prefixWord ++ tailWord_4004458) baseStart_4004458 baseEnd_4004458 := by
    simpa [prefixWord, tailWord_4004458, baseEnd_4004458] using wordTrace_append hprefix tailTrace_4004458
  have hstable : (prefixWord ++ tailWord_4004458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004458).length < 2 ^ (prefixWord ++ tailWord_4004458).sum := by decide
  have hdescent : baseEnd_4004458 < baseStart_4004458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004506 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4004506 : Nat := 118140960795 + 4004506 * 2 ^ 59
def prefixEnd_4004506 : Nat := 4983230072969 + 3 ^ 40 * 4004506 * 2
def baseEnd_4004506 : Nat := 2056236361813614585558619

theorem tailTrace_4004506 : CollatzResearch.WordTrace tailWord_4004506 prefixEnd_4004506 2056236361813614585558619 := by
  unfold tailWord_4004506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36514083207591538005160343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97370888553577434680427581 36514083207591538005160343)
  ·
    refine ⟨54771124811387307007740515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36514083207591538005160343 54771124811387307007740515)
    ·
      refine ⟨82156687217080960511610773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54771124811387307007740515 82156687217080960511610773)
      ·
        refine ⟨3851094713300670023981755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82156687217080960511610773 3851094713300670023981755)
        ·
          refine ⟨5776642069951005035972633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851094713300670023981755 5776642069951005035972633)
          ·
            refine ⟨4332481552463253776979475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5776642069951005035972633 4332481552463253776979475)
            ·
              refine ⟨6498722328694880665469213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332481552463253776979475 6498722328694880665469213)
              ·
                refine ⟨2437020873260580249550955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6498722328694880665469213 2437020873260580249550955)
                ·
                  refine ⟨3655531309890870374326433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437020873260580249550955 3655531309890870374326433)
                  ·
                    refine ⟨2741648482418152780744825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655531309890870374326433 2741648482418152780744825)
                    ·
                      refine ⟨2056236361813614585558619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741648482418152780744825 2056236361813614585558619)
                      ·
                        rfl

theorem cell23_4004506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4004506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004506 prefixEnd_4004506 := by exact prefixLift 4004506
  have htrace : WordTrace (prefixWord ++ tailWord_4004506) baseStart_4004506 baseEnd_4004506 := by
    simpa [prefixWord, tailWord_4004506, baseEnd_4004506] using wordTrace_append hprefix tailTrace_4004506
  have hstable : (prefixWord ++ tailWord_4004506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004506).length < 2 ^ (prefixWord ++ tailWord_4004506).sum := by decide
  have hdescent : baseEnd_4004506 < baseStart_4004506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004591 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_4004591 : Nat := 118140960795 + 4004591 * 2 ^ 59
def prefixEnd_4004591 : Nat := 4983230072969 + 3 ^ 40 * 4004591 * 2
def baseEnd_4004591 : Nat := 2056280007669246752995727

theorem tailTrace_4004591 : CollatzResearch.WordTrace tailWord_4004591 prefixEnd_4004591 2056280007669246752995727 := by
  unfold tailWord_4004591
  simp only [CollatzResearch.WordTrace]
  refine ⟨146059433035058211537485627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97372955356705474358323751 146059433035058211537485627)
  ·
    refine ⟨219089149552587317306228441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146059433035058211537485627 219089149552587317306228441)
    ·
      refine ⟨164316862164440487979671331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219089149552587317306228441 164316862164440487979671331)
      ·
        refine ⟨246475293246660731969506997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164316862164440487979671331 246475293246660731969506997)
        ·
          refine ⟨23107058741874443622141281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246475293246660731969506997 23107058741874443622141281)
          ·
            refine ⟨17330294056405832716605961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23107058741874443622141281 17330294056405832716605961)
            ·
              refine ⟨12997720542304374537454471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17330294056405832716605961 12997720542304374537454471)
              ·
                refine ⟨19496580813456561806181707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12997720542304374537454471 19496580813456561806181707)
                ·
                  refine ⟨29244871220184842709272561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19496580813456561806181707 29244871220184842709272561)
                  ·
                    refine ⟨21933653415138632031954421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29244871220184842709272561 21933653415138632031954421)
                    ·
                      refine ⟨2056280007669246752995727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21933653415138632031954421 2056280007669246752995727)
                      ·
                        rfl

theorem cell23_4004591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_4004591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004591 prefixEnd_4004591 := by exact prefixLift 4004591
  have htrace : WordTrace (prefixWord ++ tailWord_4004591) baseStart_4004591 baseEnd_4004591 := by
    simpa [prefixWord, tailWord_4004591, baseEnd_4004591] using wordTrace_append hprefix tailTrace_4004591
  have hstable : (prefixWord ++ tailWord_4004591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004591).length < 2 ^ (prefixWord ++ tailWord_4004591).sum := by decide
  have hdescent : baseEnd_4004591 < baseStart_4004591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004601 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_4004601 : Nat := 118140960795 + 4004601 * 2 ^ 59
def prefixEnd_4004601 : Nat := 4983230072969 + 3 ^ 40 * 4004601 * 2
def baseEnd_4004601 : Nat := 2056285142475791713870681

theorem tailTrace_4004601 : CollatzResearch.WordTrace tailWord_4004601 prefixEnd_4004601 2056285142475791713870681 := by
  unfold tailWord_4004601
  simp only [CollatzResearch.WordTrace]
  refine ⟨146059797765021983245349657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97373198510014655496899771 146059797765021983245349657)
  ·
    refine ⟨109544848323766487434012243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146059797765021983245349657 109544848323766487434012243)
    ·
      refine ⟨164317272485649731151018365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109544848323766487434012243 164317272485649731151018365)
      ·
        refine ⟨61618977182118649181631887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164317272485649731151018365 61618977182118649181631887)
        ·
          refine ⟨92428465773177973772447831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61618977182118649181631887 92428465773177973772447831)
          ·
            refine ⟨138642698659766960658671747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92428465773177973772447831 138642698659766960658671747)
            ·
              refine ⟨207964047989650440988007621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138642698659766960658671747 207964047989650440988007621)
              ·
                refine ⟨38993258998059457685251429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207964047989650440988007621 38993258998059457685251429)
                ·
                  refine ⟨7311236062136148315984643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38993258998059457685251429 7311236062136148315984643)
                  ·
                    refine ⟨10966854093204222473976965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7311236062136148315984643 10966854093204222473976965)
                    ·
                      refine ⟨2056285142475791713870681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10966854093204222473976965 2056285142475791713870681)
                      ·
                        rfl

theorem cell23_4004601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_4004601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004601 prefixEnd_4004601 := by exact prefixLift 4004601
  have htrace : WordTrace (prefixWord ++ tailWord_4004601) baseStart_4004601 baseEnd_4004601 := by
    simpa [prefixWord, tailWord_4004601, baseEnd_4004601] using wordTrace_append hprefix tailTrace_4004601
  have hstable : (prefixWord ++ tailWord_4004601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004601).length < 2 ^ (prefixWord ++ tailWord_4004601).sum := by decide
  have hdescent : baseEnd_4004601 < baseStart_4004601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004615 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 2, 5]
def baseStart_4004615 : Nat := 118140960795 + 4004615 * 2 ^ 59
def prefixEnd_4004615 : Nat := 4983230072969 + 3 ^ 40 * 4004615 * 2
def baseEnd_4004615 : Nat := 685430777068318219698539

theorem tailTrace_4004615 : CollatzResearch.WordTrace tailWord_4004615 prefixEnd_4004615 685430777068318219698539 := by
  unfold tailWord_4004615
  simp only [CollatzResearch.WordTrace]
  refine ⟨146060308386971263636359299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97373538924647509090906199 146060308386971263636359299)
  ·
    refine ⟨219090462580456895454538949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146060308386971263636359299 219090462580456895454538949)
    ·
      refine ⟨41079461733835667897726053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219090462580456895454538949 41079461733835667897726053)
      ·
        refine ⟨7702399075094187730823635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41079461733835667897726053 7702399075094187730823635)
        ·
          refine ⟨11553598612641281596235453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702399075094187730823635 11553598612641281596235453)
          ·
            refine ⟨4332599479740480598588295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11553598612641281596235453 4332599479740480598588295)
            ·
              refine ⟨6498899219610720897882443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332599479740480598588295 6498899219610720897882443)
              ·
                refine ⟨9748348829416081346823665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498899219610720897882443 9748348829416081346823665)
                ·
                  refine ⟨7311261622062061010117749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9748348829416081346823665 7311261622062061010117749)
                  ·
                    refine ⟨685430777068318219698539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7311261622062061010117749 685430777068318219698539)
                    ·
                      rfl

theorem cell23_4004615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_4004615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004615 prefixEnd_4004615 := by exact prefixLift 4004615
  have htrace : WordTrace (prefixWord ++ tailWord_4004615) baseStart_4004615 baseEnd_4004615 := by
    simpa [prefixWord, tailWord_4004615, baseEnd_4004615] using wordTrace_append hprefix tailTrace_4004615
  have hstable : (prefixWord ++ tailWord_4004615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004615).length < 2 ^ (prefixWord ++ tailWord_4004615).sum := by decide
  have hdescent : baseEnd_4004615 < baseStart_4004615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004618 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_4004618 : Nat := 118140960795 + 4004618 * 2 ^ 59
def prefixEnd_4004618 : Nat := 4983230072969 + 3 ^ 40 * 4004618 * 2
def baseEnd_4004618 : Nat := 2056293871646918147358103

theorem tailTrace_4004618 : CollatzResearch.WordTrace tailWord_4004618 prefixEnd_4004618 2056293871646918147358103 := by
  unfold tailWord_4004618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36515104451490098787179627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97373611870640263432479005 36515104451490098787179627)
  ·
    refine ⟨54772656677235148180769441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36515104451490098787179627 54772656677235148180769441)
    ·
      refine ⟨41079492507926361135577081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54772656677235148180769441 41079492507926361135577081)
      ·
        refine ⟨30809619380944770851682811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41079492507926361135577081 30809619380944770851682811)
        ·
          refine ⟨46214429071417156277524217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30809619380944770851682811 46214429071417156277524217)
          ·
            refine ⟨34660821803562867208143163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46214429071417156277524217 34660821803562867208143163)
            ·
              refine ⟨51991232705344300812214745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34660821803562867208143163 51991232705344300812214745)
              ·
                refine ⟨38993424529008225609161059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51991232705344300812214745 38993424529008225609161059)
                ·
                  refine ⟨58490136793512338413741589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38993424529008225609161059 58490136793512338413741589)
                  ·
                    refine ⟨2741725162195890863144137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58490136793512338413741589 2741725162195890863144137)
                    ·
                      refine ⟨2056293871646918147358103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741725162195890863144137 2056293871646918147358103)
                      ·
                        rfl

theorem cell23_4004618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_4004618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004618 prefixEnd_4004618 := by exact prefixLift 4004618
  have htrace : WordTrace (prefixWord ++ tailWord_4004618) baseStart_4004618 baseEnd_4004618 := by
    simpa [prefixWord, tailWord_4004618, baseEnd_4004618] using wordTrace_append hprefix tailTrace_4004618
  have hstable : (prefixWord ++ tailWord_4004618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004618).length < 2 ^ (prefixWord ++ tailWord_4004618).sum := by decide
  have hdescent : baseEnd_4004618 < baseStart_4004618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004641 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 8]
def baseStart_4004641 : Nat := 118140960795 + 4004641 * 2 ^ 59
def prefixEnd_4004641 : Nat := 4983230072969 + 3 ^ 40 * 4004641 * 2
def baseEnd_4004641 : Nat := 228478409077996839707833

theorem tailTrace_4004641 : CollatzResearch.WordTrace tailWord_4004641 prefixEnd_4004641 228478409077996839707833 := by
  unfold tailWord_4004641
  simp only [CollatzResearch.WordTrace]
  refine ⟨146061256684877070076805777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97374171123251380051203851 146061256684877070076805777)
  ·
    refine ⟨109545942513657802557604333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146061256684877070076805777 109545942513657802557604333)
    ·
      refine ⟨41079728442621675959101625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109545942513657802557604333 41079728442621675959101625)
      ·
        refine ⟨30809796331966256969326219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41079728442621675959101625 30809796331966256969326219)
        ·
          refine ⟨46214694497949385453989329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30809796331966256969326219 46214694497949385453989329)
          ·
            refine ⟨34661020873462039090491997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46214694497949385453989329 34661020873462039090491997)
            ·
              refine ⟨12997882827548264658934499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34661020873462039090491997 12997882827548264658934499)
              ·
                refine ⟨19496824241322396988401749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12997882827548264658934499 19496824241322396988401749)
                ·
                  refine ⟨228478409077996839707833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19496824241322396988401749 228478409077996839707833)
                  ·
                    rfl

theorem cell23_4004641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_4004641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004641 prefixEnd_4004641 := by exact prefixLift 4004641
  have htrace : WordTrace (prefixWord ++ tailWord_4004641) baseStart_4004641 baseEnd_4004641 := by
    simpa [prefixWord, tailWord_4004641, baseEnd_4004641] using wordTrace_append hprefix tailTrace_4004641
  have hstable : (prefixWord ++ tailWord_4004641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004641).length < 2 ^ (prefixWord ++ tailWord_4004641).sum := by decide
  have hdescent : baseEnd_4004641 < baseStart_4004641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004645 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_4004645 : Nat := 118140960795 + 4004645 * 2 ^ 59
def prefixEnd_4004645 : Nat := 4983230072969 + 3 ^ 40 * 4004645 * 2
def baseEnd_4004645 : Nat := 685435911874863180573493

theorem tailTrace_4004645 : CollatzResearch.WordTrace tailWord_4004645 prefixEnd_4004645 685435911874863180573493 := by
  unfold tailWord_4004645
  simp only [CollatzResearch.WordTrace]
  refine ⟨146061402576862578759951389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97374268384575052506634259 146061402576862578759951389)
  ·
    refine ⟨54773025966323467034981771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146061402576862578759951389 54773025966323467034981771)
    ·
      refine ⟨82159538949485200552472657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54773025966323467034981771 82159538949485200552472657)
      ·
        refine ⟨61619654212113900414354493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82159538949485200552472657 61619654212113900414354493)
        ·
          refine ⟨23107370329542712655382935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61619654212113900414354493 23107370329542712655382935)
          ·
            refine ⟨34661055494314068983074403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23107370329542712655382935 34661055494314068983074403)
            ·
              refine ⟨51991583241471103474611605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34661055494314068983074403 51991583241471103474611605)
              ·
                refine ⟨2437105464443957975372419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51991583241471103474611605 2437105464443957975372419)
                ·
                  refine ⟨3655658196665936963058629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437105464443957975372419 3655658196665936963058629)
                  ·
                    refine ⟨685435911874863180573493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655658196665936963058629 685435911874863180573493)
                    ·
                      rfl

theorem cell23_4004645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_4004645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004645 prefixEnd_4004645 := by exact prefixLift 4004645
  have htrace : WordTrace (prefixWord ++ tailWord_4004645) baseStart_4004645 baseEnd_4004645 := by
    simpa [prefixWord, tailWord_4004645, baseEnd_4004645] using wordTrace_append hprefix tailTrace_4004645
  have hstable : (prefixWord ++ tailWord_4004645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004645).length < 2 ^ (prefixWord ++ tailWord_4004645).sum := by decide
  have hdescent : baseEnd_4004645 < baseStart_4004645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004651 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 3]
def baseStart_4004651 : Nat := 118140960795 + 4004651 * 2 ^ 59
def prefixEnd_4004651 : Nat := 4983230072969 + 3 ^ 40 * 4004651 * 2
def baseEnd_4004651 : Nat := 2056310816508516518245451

theorem tailTrace_4004651 : CollatzResearch.WordTrace tailWord_4004651 prefixEnd_4004651 2056310816508516518245451 := by
  unfold tailWord_4004651
  simp only [CollatzResearch.WordTrace]
  refine ⟨146061621414840841784669807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97374414276560561189779871 146061621414840841784669807)
  ·
    refine ⟨219092432122261262677004711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146061621414840841784669807 219092432122261262677004711)
    ·
      refine ⟨328638648183391894015507067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219092432122261262677004711 328638648183391894015507067)
      ·
        refine ⟨492957972275087841023260601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328638648183391894015507067 492957972275087841023260601)
        ·
          refine ⟨369718479206315880767445451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492957972275087841023260601 369718479206315880767445451)
          ·
            refine ⟨554577718809473821151168177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369718479206315880767445451 554577718809473821151168177)
            ·
              refine ⟨415933289107105365863376133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554577718809473821151168177 415933289107105365863376133)
              ·
                refine ⟨77987491707582256099383025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415933289107105365863376133 77987491707582256099383025)
                ·
                  refine ⟨58490618780686692074537269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77987491707582256099383025 58490618780686692074537269)
                  ·
                    refine ⟨5483495510689377381987869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58490618780686692074537269 5483495510689377381987869)
                    ·
                      refine ⟨2056310816508516518245451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5483495510689377381987869 2056310816508516518245451)
                      ·
                        rfl

theorem cell23_4004651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 3].length) (baseStart_4004651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004651 prefixEnd_4004651 := by exact prefixLift 4004651
  have htrace : WordTrace (prefixWord ++ tailWord_4004651) baseStart_4004651 baseEnd_4004651 := by
    simpa [prefixWord, tailWord_4004651, baseEnd_4004651] using wordTrace_append hprefix tailTrace_4004651
  have hstable : (prefixWord ++ tailWord_4004651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004651).length < 2 ^ (prefixWord ++ tailWord_4004651).sum := by decide
  have hdescent : baseEnd_4004651 < baseStart_4004651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004688 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 1, 5]
def baseStart_4004688 : Nat := 118140960795 + 4004688 * 2 ^ 59
def prefixEnd_4004688 : Nat := 4983230072969 + 3 ^ 40 * 4004688 * 2
def baseEnd_4004688 : Nat := 685443271764244291160927

theorem tailTrace_4004688 : CollatzResearch.WordTrace tailWord_4004688 prefixEnd_4004688 685443271764244291160927 := by
  unfold tailWord_4004688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73031485457853398551883359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97375313943804531402511145 73031485457853398551883359)
  ·
    refine ⟨109547228186780097827825039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73031485457853398551883359 109547228186780097827825039)
    ·
      refine ⟨164320842280170146741737559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109547228186780097827825039 164320842280170146741737559)
      ·
        refine ⟨246481263420255220112606339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164320842280170146741737559 246481263420255220112606339)
        ·
          refine ⟨369721895130382830168909509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246481263420255220112606339 369721895130382830168909509)
          ·
            refine ⟨69322855336946780656670533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369721895130382830168909509 69322855336946780656670533)
            ·
              refine ⟨12998035375677521373125725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69322855336946780656670533 12998035375677521373125725)
              ·
                refine ⟨4874263265879070514922147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12998035375677521373125725 4874263265879070514922147)
                ·
                  refine ⟨7311394898818605772383221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874263265879070514922147 7311394898818605772383221)
                  ·
                    refine ⟨685443271764244291160927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7311394898818605772383221 685443271764244291160927)
                    ·
                      rfl

theorem cell23_4004688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_4004688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004688 prefixEnd_4004688 := by exact prefixLift 4004688
  have htrace : WordTrace (prefixWord ++ tailWord_4004688) baseStart_4004688 baseEnd_4004688 := by
    simpa [prefixWord, tailWord_4004688, baseEnd_4004688] using wordTrace_append hprefix tailTrace_4004688
  have hstable : (prefixWord ++ tailWord_4004688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004688).length < 2 ^ (prefixWord ++ tailWord_4004688).sum := by decide
  have hdescent : baseEnd_4004688 < baseStart_4004688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004695 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 4, 3, 2]
def baseStart_4004695 : Nat := 118140960795 + 4004695 * 2 ^ 59
def prefixEnd_4004695 : Nat := 4983230072969 + 3 ^ 40 * 4004695 * 2
def baseEnd_4004695 : Nat := 2056333409657314346095249

theorem tailTrace_4004695 : CollatzResearch.WordTrace tailWord_4004695 prefixEnd_4004695 2056333409657314346095249 := by
  unfold tailWord_4004695
  simp only [CollatzResearch.WordTrace]
  refine ⟨146063226226681437299271539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97375484151120958199514359 146063226226681437299271539)
  ·
    refine ⟨219094839340022155948907309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146063226226681437299271539 219094839340022155948907309)
    ·
      refine ⟨82160564752508308480840241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219094839340022155948907309 82160564752508308480840241)
      ·
        refine ⟨61620423564381231360630181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82160564752508308480840241 61620423564381231360630181)
        ·
          refine ⟨11553829418321480880118159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61620423564381231360630181 11553829418321480880118159)
          ·
            refine ⟨17330744127482221320177239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11553829418321480880118159 17330744127482221320177239)
            ·
              refine ⟨25996116191223331980265859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17330744127482221320177239 25996116191223331980265859)
              ·
                refine ⟨38994174286834997970398789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25996116191223331980265859 38994174286834997970398789)
                ·
                  refine ⟨7311407678781562119449773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38994174286834997970398789 7311407678781562119449773)
                  ·
                    refine ⟨2741777879543085794793665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7311407678781562119449773 2741777879543085794793665)
                    ·
                      refine ⟨2056333409657314346095249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741777879543085794793665 2056333409657314346095249)
                      ·
                        rfl

theorem cell23_4004695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_4004695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004695 prefixEnd_4004695 := by exact prefixLift 4004695
  have htrace : WordTrace (prefixWord ++ tailWord_4004695) baseStart_4004695 baseEnd_4004695 := by
    simpa [prefixWord, tailWord_4004695, baseEnd_4004695] using wordTrace_append hprefix tailTrace_4004695
  have hstable : (prefixWord ++ tailWord_4004695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004695).length < 2 ^ (prefixWord ++ tailWord_4004695).sum := by decide
  have hdescent : baseEnd_4004695 < baseStart_4004695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004725 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4004725 : Nat := 118140960795 + 4004725 * 2 ^ 59
def prefixEnd_4004725 : Nat := 4983230072969 + 3 ^ 40 * 4004725 * 2
def baseEnd_4004725 : Nat := 2056348814076949228720111

theorem tailTrace_4004725 : CollatzResearch.WordTrace tailWord_4004725 prefixEnd_4004725 2056348814076949228720111 := by
  unfold tailWord_4004725
  simp only [CollatzResearch.WordTrace]
  refine ⟨146064320416572752422863629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97376213611048501615242419 146064320416572752422863629)
  ·
    refine ⟨54774120156214782158573861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146064320416572752422863629 54774120156214782158573861)
    ·
      refine ⟨10270147529290271654732599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54774120156214782158573861 10270147529290271654732599)
      ·
        refine ⟨15405221293935407482098899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10270147529290271654732599 15405221293935407482098899)
        ·
          refine ⟨23107831940903111223148349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15405221293935407482098899 23107831940903111223148349)
          ·
            refine ⟨8665436977838666708680631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23107831940903111223148349 8665436977838666708680631)
            ·
              refine ⟨12998155466758000063020947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8665436977838666708680631 12998155466758000063020947)
              ·
                refine ⟨19497233200137000094531421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12998155466758000063020947 19497233200137000094531421)
                ·
                  refine ⟨7311462450051375035449283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19497233200137000094531421 7311462450051375035449283)
                  ·
                    refine ⟨10967193675077062553173925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7311462450051375035449283 10967193675077062553173925)
                    ·
                      refine ⟨2056348814076949228720111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10967193675077062553173925 2056348814076949228720111)
                      ·
                        rfl

theorem cell23_4004725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4004725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004725 prefixEnd_4004725 := by exact prefixLift 4004725
  have htrace : WordTrace (prefixWord ++ tailWord_4004725) baseStart_4004725 baseEnd_4004725 := by
    simpa [prefixWord, tailWord_4004725, baseEnd_4004725] using wordTrace_append hprefix tailTrace_4004725
  have hstable : (prefixWord ++ tailWord_4004725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004725).length < 2 ^ (prefixWord ++ tailWord_4004725).sum := by decide
  have hdescent : baseEnd_4004725 < baseStart_4004725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004731 : List Nat := [1, 1, 1, 1, 1, 5, 4, 9]
def baseStart_4004731 : Nat := 118140960795 + 4004731 * 2 ^ 59
def prefixEnd_4004731 : Nat := 4983230072969 + 3 ^ 40 * 4004731 * 2
def baseEnd_4004731 : Nat := 76161181294847266860929

theorem tailTrace_4004731 : CollatzResearch.WordTrace tailWord_4004731 prefixEnd_4004731 76161181294847266860929 := by
  unfold tailWord_4004731
  simp only [CollatzResearch.WordTrace]
  refine ⟨146064539254551015447582047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97376359503034010298388031 146064539254551015447582047)
  ·
    refine ⟨219096808881826523171373071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146064539254551015447582047 219096808881826523171373071)
    ·
      refine ⟨328645213322739784757059607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219096808881826523171373071 328645213322739784757059607)
      ·
        refine ⟨492967819984109677135589411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328645213322739784757059607 492967819984109677135589411)
        ·
          refine ⟨739451729976164515703384117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492967819984109677135589411 739451729976164515703384117)
          ·
            refine ⟨69323599685265423347192261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 739451729976164515703384117 69323599685265423347192261)
            ·
              refine ⟨12998174940987266877598549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69323599685265423347192261 12998174940987266877598549)
              ·
                refine ⟨76161181294847266860929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12998174940987266877598549 76161181294847266860929)
                ·
                  rfl

theorem cell23_4004731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 9].length) (baseStart_4004731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004731 prefixEnd_4004731 := by exact prefixLift 4004731
  have htrace : WordTrace (prefixWord ++ tailWord_4004731) baseStart_4004731 baseEnd_4004731 := by
    simpa [prefixWord, tailWord_4004731, baseEnd_4004731] using wordTrace_append hprefix tailTrace_4004731
  have hstable : (prefixWord ++ tailWord_4004731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004731).length < 2 ^ (prefixWord ++ tailWord_4004731).sum := by decide
  have hdescent : baseEnd_4004731 < baseStart_4004731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004745 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 5]
def baseStart_4004745 : Nat := 118140960795 + 4004745 * 2 ^ 59
def prefixEnd_4004745 : Nat := 4983230072969 + 3 ^ 40 * 4004745 * 2
def baseEnd_4004745 : Nat := 2056359083690039150470019

theorem tailTrace_4004745 : CollatzResearch.WordTrace tailWord_4004745 prefixEnd_4004745 2056359083690039150470019 := by
  unfold tailWord_4004745
  simp only [CollatzResearch.WordTrace]
  refine ⟨146065049876500295838591689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97376699917666863892394459 146065049876500295838591689)
  ·
    refine ⟨109548787407375221878943767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146065049876500295838591689 109548787407375221878943767)
    ·
      refine ⟨164323181111062832818415651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109548787407375221878943767 164323181111062832818415651)
      ·
        refine ⟨246484771666594249227623477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164323181111062832818415651 246484771666594249227623477)
        ·
          refine ⟨23107947343743210865089701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246484771666594249227623477 23107947343743210865089701)
          ·
            refine ⟨4332740126951852037204319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23107947343743210865089701 4332740126951852037204319)
            ·
              refine ⟨6499110190427778055806479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332740126951852037204319 6499110190427778055806479)
              ·
                refine ⟨9748665285641667083709719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499110190427778055806479 9748665285641667083709719)
                ·
                  refine ⟨14622997928462500625564579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748665285641667083709719 14622997928462500625564579)
                  ·
                    refine ⟨21934496892693750938346869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14622997928462500625564579 21934496892693750938346869)
                    ·
                      refine ⟨2056359083690039150470019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21934496892693750938346869 2056359083690039150470019)
                      ·
                        rfl

theorem cell23_4004745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_4004745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004745 prefixEnd_4004745 := by exact prefixLift 4004745
  have htrace : WordTrace (prefixWord ++ tailWord_4004745) baseStart_4004745 baseEnd_4004745 := by
    simpa [prefixWord, tailWord_4004745, baseEnd_4004745] using wordTrace_append hprefix tailTrace_4004745
  have hstable : (prefixWord ++ tailWord_4004745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004745).length < 2 ^ (prefixWord ++ tailWord_4004745).sum := by decide
  have hdescent : baseEnd_4004745 < baseStart_4004745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004759 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 1, 2, 2]
def baseStart_4004759 : Nat := 118140960795 + 4004759 * 2 ^ 59
def prefixEnd_4004759 : Nat := 4983230072969 + 3 ^ 40 * 4004759 * 2
def baseEnd_4004759 : Nat := 2056366272419202095694955

theorem tailTrace_4004759 : CollatzResearch.WordTrace tailWord_4004759 prefixEnd_4004759 2056366272419202095694955 := by
  unfold tailWord_4004759
  simp only [CollatzResearch.WordTrace]
  refine ⟨146065560498449576229601331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97377040332299717486400887 146065560498449576229601331)
  ·
    refine ⟨219098340747674364344401997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146065560498449576229601331 219098340747674364344401997)
    ·
      refine ⟨82161877780377886629150749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219098340747674364344401997 82161877780377886629150749)
      ·
        refine ⟨30810704167641707485931531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82161877780377886629150749 30810704167641707485931531)
        ·
          refine ⟨46216056251462561228897297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30810704167641707485931531 46216056251462561228897297)
          ·
            refine ⟨34662042188596920921672973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46216056251462561228897297 34662042188596920921672973)
            ·
              refine ⟨12998265820723845345627365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34662042188596920921672973 12998265820723845345627365)
              ·
                refine ⟨2437174841385721002305131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12998265820723845345627365 2437174841385721002305131)
                ·
                  refine ⟨3655762262078581503457697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437174841385721002305131 3655762262078581503457697)
                  ·
                    refine ⟨2741821696558936127593273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655762262078581503457697 2741821696558936127593273)
                    ·
                      refine ⟨2056366272419202095694955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2741821696558936127593273 2056366272419202095694955)
                      ·
                        rfl

theorem cell23_4004759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_4004759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004759 prefixEnd_4004759 := by exact prefixLift 4004759
  have htrace : WordTrace (prefixWord ++ tailWord_4004759) baseStart_4004759 baseEnd_4004759 := by
    simpa [prefixWord, tailWord_4004759, baseEnd_4004759] using wordTrace_append hprefix tailTrace_4004759
  have hstable : (prefixWord ++ tailWord_4004759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004759).length < 2 ^ (prefixWord ++ tailWord_4004759).sum := by decide
  have hdescent : baseEnd_4004759 < baseStart_4004759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004790 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4004790 : Nat := 118140960795 + 4004790 * 2 ^ 59
def prefixEnd_4004790 : Nat := 4983230072969 + 3 ^ 40 * 4004790 * 2
def baseEnd_4004790 : Nat := 685460730106497158135771

theorem tailTrace_4004790 : CollatzResearch.WordTrace tailWord_4004790 prefixEnd_4004790 685460730106497158135771 := by
  unfold tailWord_4004790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129168197583579282748739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97377794107558179015986549 9129168197583579282748739)
  ·
    refine ⟨13693752296375368924123109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9129168197583579282748739 13693752296375368924123109)
    ·
      refine ⟨2567578555570381673273083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13693752296375368924123109 2567578555570381673273083)
      ·
        refine ⟨3851367833355572509909625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567578555570381673273083 3851367833355572509909625)
        ·
          refine ⟨2888525875016679382432219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3851367833355572509909625 2888525875016679382432219)
          ·
            refine ⟨4332788812525019073648329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888525875016679382432219 4332788812525019073648329)
            ·
              refine ⟨3249591609393764305236247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332788812525019073648329 3249591609393764305236247)
              ·
                refine ⟨4874387414090646457854371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249591609393764305236247 4874387414090646457854371)
                ·
                  refine ⟨7311581121135969686781557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874387414090646457854371 7311581121135969686781557)
                  ·
                    refine ⟨685460730106497158135771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7311581121135969686781557 685460730106497158135771)
                    ·
                      rfl

theorem cell23_4004790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4004790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004790 prefixEnd_4004790 := by exact prefixLift 4004790
  have htrace : WordTrace (prefixWord ++ tailWord_4004790) baseStart_4004790 baseEnd_4004790 := by
    simpa [prefixWord, tailWord_4004790, baseEnd_4004790] using wordTrace_append hprefix tailTrace_4004790
  have hstable : (prefixWord ++ tailWord_4004790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004790).length < 2 ^ (prefixWord ++ tailWord_4004790).sum := by decide
  have hdescent : baseEnd_4004790 < baseStart_4004790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004945 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 6]
def baseStart_4004945 : Nat := 118140960795 + 4004945 * 2 ^ 59
def prefixEnd_4004945 : Nat := 4983230072969 + 3 ^ 40 * 4004945 * 2
def baseEnd_4004945 : Nat := 228495753313437596441011

theorem tailTrace_4004945 : CollatzResearch.WordTrace tailWord_4004945 prefixEnd_4004945 228495753313437596441011 := by
  unfold tailWord_4004945
  simp only [CollatzResearch.WordTrace]
  refine ⟨146072344475775729995872289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97381562983850486663914859 146072344475775729995872289)
  ·
    refine ⟨109554258356831797496904217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146072344475775729995872289 109554258356831797496904217)
    ·
      refine ⟨82165693767623848122678163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109554258356831797496904217 82165693767623848122678163)
      ·
        refine ⟨123248540651435772184017245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82165693767623848122678163 123248540651435772184017245)
        ·
          refine ⟨46218202744288414569006467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123248540651435772184017245 46218202744288414569006467)
          ·
            refine ⟨69327304116432621853509701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46218202744288414569006467 69327304116432621853509701)
            ·
              refine ⟨12998869521831116597533069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69327304116432621853509701 12998869521831116597533069)
              ·
                refine ⟨4874576070686668724074901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12998869521831116597533069 4874576070686668724074901)
                ·
                  refine ⟨228495753313437596441011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4874576070686668724074901 228495753313437596441011)
                  ·
                    rfl

theorem cell23_4004945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 6].length) (baseStart_4004945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004945 prefixEnd_4004945 := by exact prefixLift 4004945
  have htrace : WordTrace (prefixWord ++ tailWord_4004945) baseStart_4004945 baseEnd_4004945 := by
    simpa [prefixWord, tailWord_4004945, baseEnd_4004945] using wordTrace_append hprefix tailTrace_4004945
  have hstable : (prefixWord ++ tailWord_4004945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004945).length < 2 ^ (prefixWord ++ tailWord_4004945).sum := by decide
  have hdescent : baseEnd_4004945 < baseStart_4004945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004972 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_4004972 : Nat := 118140960795 + 4004972 * 2 ^ 59
def prefixEnd_4004972 : Nat := 4983230072969 + 3 ^ 40 * 4004972 * 2
def baseEnd_4004972 : Nat := 2056475643798609762331475

theorem tailTrace_4004972 : CollatzResearch.WordTrace tailWord_4004972 prefixEnd_4004972 2056475643798609762331475 := by
  unfold tailWord_4004972
  simp only [CollatzResearch.WordTrace]
  refine ⟨73036664623338956803552585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97382219497785275738070113 73036664623338956803552585)
  ·
    refine ⟨54777498467504217602664439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73036664623338956803552585 54777498467504217602664439)
    ·
      refine ⟨82166247701256326403996659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54777498467504217602664439 82166247701256326403996659)
      ·
        refine ⟨123249371551884489605994989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82166247701256326403996659 123249371551884489605994989)
        ·
          refine ⟨46218514331956683602248121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123249371551884489605994989 46218514331956683602248121)
          ·
            refine ⟨34663885748967512701686091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46218514331956683602248121 34663885748967512701686091)
            ·
              refine ⟨51995828623451269052529137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34663885748967512701686091 51995828623451269052529137)
              ·
                refine ⟨38996871467588451789396853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51995828623451269052529137 38996871467588451789396853)
                ·
                  refine ⟨3655956700086417355255955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38996871467588451789396853 3655956700086417355255955)
                  ·
                    refine ⟨5483935050129626032883933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3655956700086417355255955 5483935050129626032883933)
                    ·
                      refine ⟨2056475643798609762331475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5483935050129626032883933 2056475643798609762331475)
                      ·
                        rfl

theorem cell23_4004972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_4004972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004972 prefixEnd_4004972 := by exact prefixLift 4004972
  have htrace : WordTrace (prefixWord ++ tailWord_4004972) baseStart_4004972 baseEnd_4004972 := by
    simpa [prefixWord, tailWord_4004972, baseEnd_4004972] using wordTrace_append hprefix tailTrace_4004972
  have hstable : (prefixWord ++ tailWord_4004972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004972).length < 2 ^ (prefixWord ++ tailWord_4004972).sum := by decide
  have hdescent : baseEnd_4004972 < baseStart_4004972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4004989 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_4004989 : Nat := 118140960795 + 4004989 * 2 ^ 59
def prefixEnd_4004989 : Nat := 4983230072969 + 3 ^ 40 * 4004989 * 2
def baseEnd_4004989 : Nat := 2056484372969736195818897

theorem tailTrace_4004989 : CollatzResearch.WordTrace tailWord_4004989 prefixEnd_4004989 2056484372969736195818897 := by
  unfold tailWord_4004989
  simp only [CollatzResearch.WordTrace]
  refine ⟨146073949287616325510474021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97382632858410883673649347 146073949287616325510474021)
  ·
    refine ⟨27388865491428061033213879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146073949287616325510474021 27388865491428061033213879)
    ·
      refine ⟨41083298237142091549820819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27388865491428061033213879 41083298237142091549820819)
      ·
        refine ⟨61624947355713137324731229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41083298237142091549820819 61624947355713137324731229)
        ·
          refine ⟨23109355258392426496774211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61624947355713137324731229 23109355258392426496774211)
          ·
            refine ⟨34664032887588639745161317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23109355258392426496774211 34664032887588639745161317)
            ·
              refine ⟨6499506166422869952217747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34664032887588639745161317 6499506166422869952217747)
              ·
                refine ⟨9749259249634304928326621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499506166422869952217747 9749259249634304928326621)
                ·
                  refine ⟨3655972218612864348122483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9749259249634304928326621 3655972218612864348122483)
                  ·
                    refine ⟨5483958327919296522183725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3655972218612864348122483 5483958327919296522183725)
                    ·
                      refine ⟨2056484372969736195818897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5483958327919296522183725 2056484372969736195818897)
                      ·
                        rfl

theorem cell23_4004989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_4004989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4004989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4004989 prefixEnd_4004989 := by exact prefixLift 4004989
  have htrace : WordTrace (prefixWord ++ tailWord_4004989) baseStart_4004989 baseEnd_4004989 := by
    simpa [prefixWord, tailWord_4004989, baseEnd_4004989] using wordTrace_append hprefix tailTrace_4004989
  have hstable : (prefixWord ++ tailWord_4004989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4004989).length < 2 ^ (prefixWord ++ tailWord_4004989).sum := by decide
  have hdescent : baseEnd_4004989 < baseStart_4004989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4004989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005052 : List Nat := [2, 2, 2, 3, 2, 2, 2, 8]
def baseStart_4005052 : Nat := 118140960795 + 4005052 * 2 ^ 59
def prefixEnd_4005052 : Nat := 4983230072969 + 3 ^ 40 * 4005052 * 2
def baseEnd_4005052 : Nat := 76167286009295164790041

theorem tailTrace_4005052 : CollatzResearch.WordTrace tailWord_4005052 prefixEnd_4005052 76167286009295164790041 := by
  unfold tailWord_4005052
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038123543194043635008705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97384164724258724846678273 73038123543194043635008705)
  ·
    refine ⟨54778592657395532726256529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73038123543194043635008705 54778592657395532726256529)
    ·
      refine ⟨41083944493046649544692397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54778592657395532726256529 41083944493046649544692397)
      ·
        refine ⟨15406479184892493579259649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41083944493046649544692397 15406479184892493579259649)
        ·
          refine ⟨11554859388669370184444737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15406479184892493579259649 11554859388669370184444737)
          ·
            refine ⟨8666144541502027638333553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11554859388669370184444737 8666144541502027638333553)
            ·
              refine ⟨6499608406126520728750165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8666144541502027638333553 6499608406126520728750165)
              ·
                refine ⟨76167286009295164790041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6499608406126520728750165 76167286009295164790041)
                ·
                  rfl

theorem cell23_4005052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 8].length) (baseStart_4005052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005052 prefixEnd_4005052 := by exact prefixLift 4005052
  have htrace : WordTrace (prefixWord ++ tailWord_4005052) baseStart_4005052 baseEnd_4005052 := by
    simpa [prefixWord, tailWord_4005052, baseEnd_4005052] using wordTrace_append hprefix tailTrace_4005052
  have hstable : (prefixWord ++ tailWord_4005052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005052).length < 2 ^ (prefixWord ++ tailWord_4005052).sum := by decide
  have hdescent : baseEnd_4005052 < baseStart_4005052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005066 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_4005066 : Nat := 118140960795 + 4005066 * 2 ^ 59
def prefixEnd_4005066 : Nat := 4983230072969 + 3 ^ 40 * 4005066 * 2
def baseEnd_4005066 : Nat := 2056523910980132394556043

theorem tailTrace_4005066 : CollatzResearch.WordTrace tailWord_4005066 prefixEnd_4005066 2056523910980132394556043 := by
  unfold tailWord_4005066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36519189427084341915256763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97384505138891578440684701 36519189427084341915256763)
  ·
    refine ⟨54778784140626512872885145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36519189427084341915256763 54778784140626512872885145)
    ·
      refine ⟨41084088105469884654663859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54778784140626512872885145 41084088105469884654663859)
      ·
        refine ⟨61626132158204826981995789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41084088105469884654663859 61626132158204826981995789)
        ·
          refine ⟨23109799559326810118248421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61626132158204826981995789 23109799559326810118248421)
          ·
            refine ⟨4333087417373776897171579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23109799559326810118248421 4333087417373776897171579)
            ·
              refine ⟨6499631126060665345757369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333087417373776897171579 6499631126060665345757369)
              ·
                refine ⟨4874723344545499009318027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499631126060665345757369 4874723344545499009318027)
                ·
                  refine ⟨7312085016818248513977041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874723344545499009318027 7312085016818248513977041)
                  ·
                    refine ⟨5484063762613686385482781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7312085016818248513977041 5484063762613686385482781)
                    ·
                      refine ⟨2056523910980132394556043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484063762613686385482781 2056523910980132394556043)
                      ·
                        rfl

theorem cell23_4005066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_4005066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005066 prefixEnd_4005066 := by exact prefixLift 4005066
  have htrace : WordTrace (prefixWord ++ tailWord_4005066) baseStart_4005066 baseEnd_4005066 := by
    simpa [prefixWord, tailWord_4005066, baseEnd_4005066] using wordTrace_append hprefix tailTrace_4005066
  have hstable : (prefixWord ++ tailWord_4005066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005066).length < 2 ^ (prefixWord ++ tailWord_4005066).sum := by decide
  have hdescent : baseEnd_4005066 < baseStart_4005066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005076 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4005076 : Nat := 118140960795 + 4005076 * 2 ^ 59
def prefixEnd_4005076 : Nat := 4983230072969 + 3 ^ 40 * 4005076 * 2
def baseEnd_4005076 : Nat := 2056529045786677355430997

theorem tailTrace_4005076 : CollatzResearch.WordTrace tailWord_4005076 prefixEnd_4005076 2056529045786677355430997 := by
  unfold tailWord_4005076
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038561219150569684445541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97384748292200759579260721 73038561219150569684445541)
  ·
    refine ⟨13694730228590731815833539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73038561219150569684445541 13694730228590731815833539)
    ·
      refine ⟨20542095342886097723750309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13694730228590731815833539 20542095342886097723750309)
      ·
        refine ⟨3851642876791143323203183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20542095342886097723750309 3851642876791143323203183)
        ·
          refine ⟨5777464315186714984804775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851642876791143323203183 5777464315186714984804775)
          ·
            refine ⟨8666196472780072477207163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777464315186714984804775 8666196472780072477207163)
            ·
              refine ⟨12999294709170108715810745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8666196472780072477207163 12999294709170108715810745)
              ·
                refine ⟨9749471031877581536858059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12999294709170108715810745 9749471031877581536858059)
                ·
                  refine ⟨14624206547816372305287089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9749471031877581536858059 14624206547816372305287089)
                  ·
                    refine ⟨10968154910862279228965317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14624206547816372305287089 10968154910862279228965317)
                    ·
                      refine ⟨2056529045786677355430997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10968154910862279228965317 2056529045786677355430997)
                      ·
                        rfl

theorem cell23_4005076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4005076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005076 prefixEnd_4005076 := by exact prefixLift 4005076
  have htrace : WordTrace (prefixWord ++ tailWord_4005076) baseStart_4005076 baseEnd_4005076 := by
    simpa [prefixWord, tailWord_4005076, baseEnd_4005076] using wordTrace_append hprefix tailTrace_4005076
  have hstable : (prefixWord ++ tailWord_4005076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005076).length < 2 ^ (prefixWord ++ tailWord_4005076).sum := by decide
  have hdescent : baseEnd_4005076 < baseStart_4005076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005096 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_4005096 : Nat := 118140960795 + 4005096 * 2 ^ 59
def prefixEnd_4005096 : Nat := 4983230072969 + 3 ^ 40 * 4005096 * 2
def baseEnd_4005096 : Nat := 2056539315399767277180905

theorem tailTrace_4005096 : CollatzResearch.WordTrace tailWord_4005096 prefixEnd_4005096 2056539315399767277180905 := by
  unfold tailWord_4005096
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038925949114341392309571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97385234598819121856412761 73038925949114341392309571)
  ·
    refine ⟨109558388923671512088464357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73038925949114341392309571 109558388923671512088464357)
    ·
      refine ⟨20542197923188408516587067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109558388923671512088464357 20542197923188408516587067)
      ·
        refine ⟨30813296884782612774880601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20542197923188408516587067 30813296884782612774880601)
        ·
          refine ⟨23109972663586959581160451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30813296884782612774880601 23109972663586959581160451)
          ·
            refine ⟨34664958995380439371740677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23109972663586959581160451 34664958995380439371740677)
            ·
              refine ⟨6499679811633832382201377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34664958995380439371740677 6499679811633832382201377)
              ·
                refine ⟨4874759858725374286651033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499679811633832382201377 4874759858725374286651033)
                ·
                  refine ⟨3656069894044030714988275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874759858725374286651033 3656069894044030714988275)
                  ·
                    refine ⟨5484104841066046072482413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656069894044030714988275 5484104841066046072482413)
                    ·
                      refine ⟨2056539315399767277180905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484104841066046072482413 2056539315399767277180905)
                      ·
                        rfl

theorem cell23_4005096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_4005096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005096 prefixEnd_4005096 := by exact prefixLift 4005096
  have htrace : WordTrace (prefixWord ++ tailWord_4005096) baseStart_4005096 baseEnd_4005096 := by
    simpa [prefixWord, tailWord_4005096, baseEnd_4005096] using wordTrace_append hprefix tailTrace_4005096
  have hstable : (prefixWord ++ tailWord_4005096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005096).length < 2 ^ (prefixWord ++ tailWord_4005096).sum := by decide
  have hdescent : baseEnd_4005096 < baseStart_4005096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005102 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4005102 : Nat := 118140960795 + 4005102 * 2 ^ 59
def prefixEnd_4005102 : Nat := 4983230072969 + 3 ^ 40 * 4005102 * 2
def baseEnd_4005102 : Nat := 2056542396283694253705877

theorem tailTrace_4005102 : CollatzResearch.WordTrace tailWord_4005102 prefixEnd_4005102 2056542396283694253705877 := by
  unfold tailWord_4005102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259758842025868226167195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97385380490804630539558373 18259758842025868226167195)
  ·
    refine ⟨27389638263038802339250793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18259758842025868226167195 27389638263038802339250793)
    ·
      refine ⟨20542228697279101754438095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27389638263038802339250793 20542228697279101754438095)
      ·
        refine ⟨30813343045918652631657143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20542228697279101754438095 30813343045918652631657143)
        ·
          refine ⟨46220014568877978947485715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30813343045918652631657143 46220014568877978947485715)
          ·
            refine ⟨69330021853316968421228573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46220014568877978947485715 69330021853316968421228573)
            ·
              refine ⟨25998758194993863157960715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69330021853316968421228573 25998758194993863157960715)
              ·
                refine ⟨38998137292490794736941073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25998758194993863157960715 38998137292490794736941073)
                ·
                  refine ⟨29248602969368096052705805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38998137292490794736941073 29248602969368096052705805)
                  ·
                    refine ⟨10968226113513036019764677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29248602969368096052705805 10968226113513036019764677)
                    ·
                      refine ⟨2056542396283694253705877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10968226113513036019764677 2056542396283694253705877)
                      ·
                        rfl

theorem cell23_4005102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4005102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005102 prefixEnd_4005102 := by exact prefixLift 4005102
  have htrace : WordTrace (prefixWord ++ tailWord_4005102) baseStart_4005102 baseEnd_4005102 := by
    simpa [prefixWord, tailWord_4005102, baseEnd_4005102] using wordTrace_append hprefix tailTrace_4005102
  have hstable : (prefixWord ++ tailWord_4005102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005102).length < 2 ^ (prefixWord ++ tailWord_4005102).sum := by decide
  have hdescent : baseEnd_4005102 < baseStart_4005102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005119 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 1, 4, 2]
def baseStart_4005119 : Nat := 118140960795 + 4005119 * 2 ^ 59
def prefixEnd_4005119 : Nat := 4983230072969 + 3 ^ 40 * 4005119 * 2
def baseEnd_4005119 : Nat := 2056551125454820687193299

theorem tailTrace_4005119 : CollatzResearch.WordTrace tailWord_4005119 prefixEnd_4005119 2056551125454820687193299 := by
  unfold tailWord_4005119
  simp only [CollatzResearch.WordTrace]
  refine ⟨146078690777145357712706411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97385793851430238475137607 146078690777145357712706411)
  ·
    refine ⟨219118036165718036569059617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146078690777145357712706411 219118036165718036569059617)
    ·
      refine ⟨164338527124288527426794713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219118036165718036569059617 164338527124288527426794713)
      ·
        refine ⟨123253895343216395570096035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164338527124288527426794713 123253895343216395570096035)
        ·
          refine ⟨184880843014824593355144053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123253895343216395570096035 184880843014824593355144053)
          ·
            refine ⟨17332579032639805627044755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184880843014824593355144053 17332579032639805627044755)
            ·
              refine ⟨25998868548959708440567133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17332579032639805627044755 25998868548959708440567133)
              ·
                refine ⟨9749575705859890665212675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25998868548959708440567133 9749575705859890665212675)
                ·
                  refine ⟨14624363558789835997819013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9749575705859890665212675 14624363558789835997819013)
                  ·
                    refine ⟨2742068167273094249591065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14624363558789835997819013 2742068167273094249591065)
                    ·
                      refine ⟨2056551125454820687193299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742068167273094249591065 2056551125454820687193299)
                      ·
                        rfl

theorem cell23_4005119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_4005119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005119 prefixEnd_4005119 := by exact prefixLift 4005119
  have htrace : WordTrace (prefixWord ++ tailWord_4005119) baseStart_4005119 baseEnd_4005119 := by
    simpa [prefixWord, tailWord_4005119, baseEnd_4005119] using wordTrace_append hprefix tailTrace_4005119
  have hstable : (prefixWord ++ tailWord_4005119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005119).length < 2 ^ (prefixWord ++ tailWord_4005119).sum := by decide
  have hdescent : baseEnd_4005119 < baseStart_4005119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005135 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_4005135 : Nat := 118140960795 + 4005135 * 2 ^ 59
def prefixEnd_4005135 : Nat := 4983230072969 + 3 ^ 40 * 4005135 * 2
def baseEnd_4005135 : Nat := 2056559341145292624593225

theorem tailTrace_4005135 : CollatzResearch.WordTrace tailWord_4005135 prefixEnd_4005135 2056559341145292624593225 := by
  unfold tailWord_4005135
  simp only [CollatzResearch.WordTrace]
  refine ⟨146079274345087392445288859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97386182896724928296859239 146079274345087392445288859)
  ·
    refine ⟨219118911517631088667933289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146079274345087392445288859 219118911517631088667933289)
    ·
      refine ⟨164339183638223316500949967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219118911517631088667933289 164339183638223316500949967)
      ·
        refine ⟨246508775457334974751424951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164339183638223316500949967 246508775457334974751424951)
        ·
          refine ⟨369763163186002462127137427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246508775457334974751424951 369763163186002462127137427)
          ·
            refine ⟨554644744779003693190706141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369763163186002462127137427 554644744779003693190706141)
            ·
              refine ⟨207991779292126384946514803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554644744779003693190706141 207991779292126384946514803)
              ·
                refine ⟨311987668938189577419772205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207991779292126384946514803 311987668938189577419772205)
                ·
                  refine ⟨116995375851821091532414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311987668938189577419772205 116995375851821091532414577)
                  ·
                    refine ⟨87746531888865818649310933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116995375851821091532414577 87746531888865818649310933)
                    ·
                      refine ⟨2056559341145292624593225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87746531888865818649310933 2056559341145292624593225)
                      ·
                        rfl

theorem cell23_4005135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_4005135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005135 prefixEnd_4005135 := by exact prefixLift 4005135
  have htrace : WordTrace (prefixWord ++ tailWord_4005135) baseStart_4005135 baseEnd_4005135 := by
    simpa [prefixWord, tailWord_4005135, baseEnd_4005135] using wordTrace_append hprefix tailTrace_4005135
  have hstable : (prefixWord ++ tailWord_4005135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005135).length < 2 ^ (prefixWord ++ tailWord_4005135).sum := by decide
  have hdescent : baseEnd_4005135 < baseStart_4005135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005149 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4005149 : Nat := 118140960795 + 4005149 * 2 ^ 59
def prefixEnd_4005149 : Nat := 4983230072969 + 3 ^ 40 * 4005149 * 2
def baseEnd_4005149 : Nat := 2056566529874455569818161

theorem tailTrace_4005149 : CollatzResearch.WordTrace tailWord_4005149 prefixEnd_4005149 2056566529874455569818161 := by
  unfold tailWord_4005149
  simp only [CollatzResearch.WordTrace]
  refine ⟨146079784967036672836298501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97386523311357781890865667 146079784967036672836298501)
  ·
    refine ⟨27389959681319376156805969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146079784967036672836298501 27389959681319376156805969)
    ·
      refine ⟨20542469760989532117604477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27389959681319376156805969 20542469760989532117604477)
      ·
        refine ⟨7703426160371074544101679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20542469760989532117604477 7703426160371074544101679)
        ·
          refine ⟨11555139240556611816152519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703426160371074544101679 11555139240556611816152519)
          ·
            refine ⟨17332708860834917724228779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11555139240556611816152519 17332708860834917724228779)
            ·
              refine ⟨25999063291252376586343169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17332708860834917724228779 25999063291252376586343169)
              ·
                refine ⟨19499297468439282439757377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25999063291252376586343169 19499297468439282439757377)
                ·
                  refine ⟨14624473101329461829818033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19499297468439282439757377 14624473101329461829818033)
                  ·
                    refine ⟨10968354825997096372363525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14624473101329461829818033 10968354825997096372363525)
                    ·
                      refine ⟨2056566529874455569818161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10968354825997096372363525 2056566529874455569818161)
                      ·
                        rfl

theorem cell23_4005149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4005149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005149 prefixEnd_4005149 := by exact prefixLift 4005149
  have htrace : WordTrace (prefixWord ++ tailWord_4005149) baseStart_4005149 baseEnd_4005149 := by
    simpa [prefixWord, tailWord_4005149, baseEnd_4005149] using wordTrace_append hprefix tailTrace_4005149
  have hstable : (prefixWord ++ tailWord_4005149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005149).length < 2 ^ (prefixWord ++ tailWord_4005149).sum := by decide
  have hdescent : baseEnd_4005149 < baseStart_4005149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005169 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4005169 : Nat := 118140960795 + 4005169 * 2 ^ 59
def prefixEnd_4005169 : Nat := 4983230072969 + 3 ^ 40 * 4005169 * 2
def baseEnd_4005169 : Nat := 2056576799487545491568069

theorem tailTrace_4005169 : CollatzResearch.WordTrace tailWord_4005169 prefixEnd_4005169 2056576799487545491568069 := by
  unfold tailWord_4005169
  simp only [CollatzResearch.WordTrace]
  refine ⟨146080514426964216252026561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97387009617976144168017707 146080514426964216252026561)
  ·
    refine ⟨109560385820223162189019921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146080514426964216252026561 109560385820223162189019921)
    ·
      refine ⟨82170289365167371641764941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109560385820223162189019921 82170289365167371641764941)
      ·
        refine ⟨30813858511937764365661853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82170289365167371641764941 30813858511937764365661853)
        ·
          refine ⟨11555196941976661637123195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30813858511937764365661853 11555196941976661637123195)
          ·
            refine ⟨17332795412964992455684793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11555196941976661637123195 17332795412964992455684793)
            ·
              refine ⟨12999596559723744341763595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17332795412964992455684793 12999596559723744341763595)
              ·
                refine ⟨19499394839585616512645393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12999596559723744341763595 19499394839585616512645393)
                ·
                  refine ⟨14624546129689212384484045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19499394839585616512645393 14624546129689212384484045)
                  ·
                    refine ⟨5484204798633454644181517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14624546129689212384484045 5484204798633454644181517)
                    ·
                      refine ⟨2056576799487545491568069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484204798633454644181517 2056576799487545491568069)
                      ·
                        rfl

theorem cell23_4005169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4005169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005169 prefixEnd_4005169 := by exact prefixLift 4005169
  have htrace : WordTrace (prefixWord ++ tailWord_4005169) baseStart_4005169 baseEnd_4005169 := by
    simpa [prefixWord, tailWord_4005169, baseEnd_4005169] using wordTrace_append hprefix tailTrace_4005169
  have hstable : (prefixWord ++ tailWord_4005169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005169).length < 2 ^ (prefixWord ++ tailWord_4005169).sum := by decide
  have hdescent : baseEnd_4005169 < baseStart_4005169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005170 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_4005170 : Nat := 118140960795 + 4005170 * 2 ^ 59
def prefixEnd_4005170 : Nat := 4983230072969 + 3 ^ 40 * 4005170 * 2
def baseEnd_4005170 : Nat := 2056577312968199987655565

theorem tailTrace_4005170 : CollatzResearch.WordTrace tailWord_4005170 prefixEnd_4005170 2056577312968199987655565 := by
  unfold tailWord_4005170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36520137724990148355703241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97387033933307062281875309 36520137724990148355703241)
  ·
    refine ⟨27390103293742611266777431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36520137724990148355703241 27390103293742611266777431)
    ·
      refine ⟨41085154940613916900166147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27390103293742611266777431 41085154940613916900166147)
      ·
        refine ⟨61627732410920875350249221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41085154940613916900166147 61627732410920875350249221)
        ·
          refine ⟨11555199827047664128171729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61627732410920875350249221 11555199827047664128171729)
          ·
            refine ⟨8666399870285748096128797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11555199827047664128171729 8666399870285748096128797)
            ·
              refine ⟨3249899951357155536048299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8666399870285748096128797 3249899951357155536048299)
              ·
                refine ⟨4874849927035733304072449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249899951357155536048299 4874849927035733304072449)
                ·
                  refine ⟨3656137445276799978054337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874849927035733304072449 3656137445276799978054337)
                  ·
                    refine ⟨2742103083957599983540753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3656137445276799978054337 2742103083957599983540753)
                    ·
                      refine ⟨2056577312968199987655565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742103083957599983540753 2056577312968199987655565)
                      ·
                        rfl

theorem cell23_4005170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_4005170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005170 prefixEnd_4005170 := by exact prefixLift 4005170
  have htrace : WordTrace (prefixWord ++ tailWord_4005170) baseStart_4005170 baseEnd_4005170 := by
    simpa [prefixWord, tailWord_4005170, baseEnd_4005170] using wordTrace_append hprefix tailTrace_4005170
  have hstable : (prefixWord ++ tailWord_4005170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005170).length < 2 ^ (prefixWord ++ tailWord_4005170).sum := by decide
  have hdescent : baseEnd_4005170 < baseStart_4005170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005209 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 4, 4, 2]
def baseStart_4005209 : Nat := 118140960795 + 4005209 * 2 ^ 59
def prefixEnd_4005209 : Nat := 4983230072969 + 3 ^ 40 * 4005209 * 2
def baseEnd_4005209 : Nat := 2056597338713725335067885

theorem tailTrace_4005209 : CollatzResearch.WordTrace tailWord_4005209 prefixEnd_4005209 2056597338713725335067885 := by
  unfold tailWord_4005209
  simp only [CollatzResearch.WordTrace]
  refine ⟨146081973346819303083482681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97387982231212868722321787 146081973346819303083482681)
  ·
    refine ⟨109561480010114477312612011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146081973346819303083482681 109561480010114477312612011)
    ·
      refine ⟨164342220015171715968918017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109561480010114477312612011 164342220015171715968918017)
      ·
        refine ⟨123256665011378786976688513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164342220015171715968918017 123256665011378786976688513)
        ·
          refine ⟨92442498758534090232516385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123256665011378786976688513 92442498758534090232516385)
          ·
            refine ⟨69331874068900567674387289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92442498758534090232516385 69331874068900567674387289)
            ·
              refine ⟨51998905551675425755790467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69331874068900567674387289 51998905551675425755790467)
              ·
                refine ⟨77998358327513138633685701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51998905551675425755790467 77998358327513138633685701)
                ·
                  refine ⟨14624692186408713493816069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77998358327513138633685701 14624692186408713493816069)
                  ·
                    refine ⟨2742129784951633780090513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14624692186408713493816069 2742129784951633780090513)
                    ·
                      refine ⟨2056597338713725335067885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742129784951633780090513 2056597338713725335067885)
                      ·
                        rfl

theorem cell23_4005209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_4005209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005209 prefixEnd_4005209 := by exact prefixLift 4005209
  have htrace : WordTrace (prefixWord ++ tailWord_4005209) baseStart_4005209 baseEnd_4005209 := by
    simpa [prefixWord, tailWord_4005209, baseEnd_4005209] using wordTrace_append hprefix tailTrace_4005209
  have hstable : (prefixWord ++ tailWord_4005209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005209).length < 2 ^ (prefixWord ++ tailWord_4005209).sum := by decide
  have hdescent : baseEnd_4005209 < baseStart_4005209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005279 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 3, 5]
def baseStart_4005279 : Nat := 118140960795 + 4005279 * 2 ^ 59
def prefixEnd_4005279 : Nat := 4983230072969 + 3 ^ 40 * 4005279 * 2
def baseEnd_4005279 : Nat := 685544427453180020397521

theorem tailTrace_4005279 : CollatzResearch.WordTrace tailWord_4005279 prefixEnd_4005279 685544427453180020397521 := by
  unfold tailWord_4005279
  simp only [CollatzResearch.WordTrace]
  refine ⟨146084526456565705038530891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97389684304377136692353927 146084526456565705038530891)
  ·
    refine ⟨219126789684848557557796337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146084526456565705038530891 219126789684848557557796337)
    ·
      refine ⟨164345092263636418168347253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219126789684848557557796337 164345092263636418168347253)
      ·
        refine ⟨15407352399715914203282555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164345092263636418168347253 15407352399715914203282555)
        ·
          refine ⟨23111028599573871304923833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15407352399715914203282555 23111028599573871304923833)
          ·
            refine ⟨17333271449680403478692875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23111028599573871304923833 17333271449680403478692875)
            ·
              refine ⟨25999907174520605218039313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17333271449680403478692875 25999907174520605218039313)
              ·
                refine ⟨19499930380890453913529485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25999907174520605218039313 19499930380890453913529485)
                ·
                  refine ⟨7312473892833920217573557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19499930380890453913529485 7312473892833920217573557)
                  ·
                    refine ⟨685544427453180020397521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7312473892833920217573557 685544427453180020397521)
                    ·
                      rfl

theorem cell23_4005279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_4005279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005279 prefixEnd_4005279 := by exact prefixLift 4005279
  have htrace : WordTrace (prefixWord ++ tailWord_4005279) baseStart_4005279 baseEnd_4005279 := by
    simpa [prefixWord, tailWord_4005279, baseEnd_4005279] using wordTrace_append hprefix tailTrace_4005279
  have hstable : (prefixWord ++ tailWord_4005279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005279).length < 2 ^ (prefixWord ++ tailWord_4005279).sum := by decide
  have hdescent : baseEnd_4005279 < baseStart_4005279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005293 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4005293 : Nat := 118140960795 + 4005293 * 2 ^ 59
def prefixEnd_4005293 : Nat := 4983230072969 + 3 ^ 40 * 4005293 * 2
def baseEnd_4005293 : Nat := 2056640471088703006417499

theorem tailTrace_4005293 : CollatzResearch.WordTrace tailWord_4005293 prefixEnd_4005293 2056640471088703006417499 := by
  unfold tailWord_4005293
  simp only [CollatzResearch.WordTrace]
  refine ⟨146085037078514985429540533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97390024719009990286360355 146085037078514985429540533)
  ·
    refine ⟨13695472226110779884019425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146085037078514985429540533 13695472226110779884019425)
    ·
      refine ⟨10271604169583084913014569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13695472226110779884019425 10271604169583084913014569)
      ·
        refine ⟨7703703127187313684760927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10271604169583084913014569 7703703127187313684760927)
        ·
          refine ⟨11555554690780970527141391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703703127187313684760927 11555554690780970527141391)
          ·
            refine ⟨17333332036171455790712087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11555554690780970527141391 17333332036171455790712087)
            ·
              refine ⟨25999998054257183686068131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17333332036171455790712087 25999998054257183686068131)
              ·
                refine ⟨38999997081385775529102197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25999998054257183686068131 38999997081385775529102197)
                ·
                  refine ⟨3656249726379916455853331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38999997081385775529102197 3656249726379916455853331)
                  ·
                    refine ⟨5484374589569874683779997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656249726379916455853331 5484374589569874683779997)
                    ·
                      refine ⟨2056640471088703006417499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484374589569874683779997 2056640471088703006417499)
                      ·
                        rfl

theorem cell23_4005293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4005293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005293 prefixEnd_4005293 := by exact prefixLift 4005293
  have htrace : WordTrace (prefixWord ++ tailWord_4005293) baseStart_4005293 baseEnd_4005293 := by
    simpa [prefixWord, tailWord_4005293, baseEnd_4005293] using wordTrace_append hprefix tailTrace_4005293
  have hstable : (prefixWord ++ tailWord_4005293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005293).length < 2 ^ (prefixWord ++ tailWord_4005293).sum := by decide
  have hdescent : baseEnd_4005293 < baseStart_4005293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005309 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_4005309 : Nat := 118140960795 + 4005309 * 2 ^ 59
def prefixEnd_4005309 : Nat := 4983230072969 + 3 ^ 40 * 4005309 * 2
def baseEnd_4005309 : Nat := 685549562259724981272475

theorem tailTrace_4005309 : CollatzResearch.WordTrace tailWord_4005309 prefixEnd_4005309 685549562259724981272475 := by
  unfold tailWord_4005309
  simp only [CollatzResearch.WordTrace]
  refine ⟨146085620646457020162122981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97390413764304680108081987 146085620646457020162122981)
  ·
    refine ⟨27391053871210691280398059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146085620646457020162122981 27391053871210691280398059)
    ·
      refine ⟨41086580806816036920597089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27391053871210691280398059 41086580806816036920597089)
      ·
        refine ⟨30814935605112027690447817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41086580806816036920597089 30814935605112027690447817)
        ·
          refine ⟨23111201703834020767835863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30814935605112027690447817 23111201703834020767835863)
          ·
            refine ⟨34666802555751031151753795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23111201703834020767835863 34666802555751031151753795)
            ·
              refine ⟨52000203833626546727630693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34666802555751031151753795 52000203833626546727630693)
              ·
                refine ⟨9750038218804977511430755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52000203833626546727630693 9750038218804977511430755)
                ·
                  refine ⟨14625057328207466267146133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9750038218804977511430755 14625057328207466267146133)
                  ·
                    refine ⟨685549562259724981272475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14625057328207466267146133 685549562259724981272475)
                    ·
                      rfl

theorem cell23_4005309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_4005309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005309 prefixEnd_4005309 := by exact prefixLift 4005309
  have htrace : WordTrace (prefixWord ++ tailWord_4005309) baseStart_4005309 baseEnd_4005309 := by
    simpa [prefixWord, tailWord_4005309, baseEnd_4005309] using wordTrace_append hprefix tailTrace_4005309
  have hstable : (prefixWord ++ tailWord_4005309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005309).length < 2 ^ (prefixWord ++ tailWord_4005309).sum := by decide
  have hdescent : baseEnd_4005309 < baseStart_4005309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005319 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_4005319 : Nat := 118140960795 + 4005319 * 2 ^ 59
def prefixEnd_4005319 : Nat := 4983230072969 + 3 ^ 40 * 4005319 * 2
def baseEnd_4005319 : Nat := 2056653821585719904692379

theorem tailTrace_4005319 : CollatzResearch.WordTrace tailWord_4005319 prefixEnd_4005319 2056653821585719904692379 := by
  unfold tailWord_4005319
  simp only [CollatzResearch.WordTrace]
  refine ⟨146085985376420791869987011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97390656917613861246658007 146085985376420791869987011)
  ·
    refine ⟨219128978064631187804980517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146085985376420791869987011 219128978064631187804980517)
    ·
      refine ⟨41086683387118347713433847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219128978064631187804980517 41086683387118347713433847)
      ·
        refine ⟨61630025080677521570150771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41086683387118347713433847 61630025080677521570150771)
        ·
          refine ⟨92445037621016282355226157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61630025080677521570150771 92445037621016282355226157)
          ·
            refine ⟨34666889107881105883209809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92445037621016282355226157 34666889107881105883209809)
            ·
              refine ⟨26000166830910829412407357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34666889107881105883209809 26000166830910829412407357)
              ·
                refine ⟨9750062561591561029652759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26000166830910829412407357 9750062561591561029652759)
                ·
                  refine ⟨14625093842387341544479139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9750062561591561029652759 14625093842387341544479139)
                  ·
                    refine ⟨21937640763581012316718709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14625093842387341544479139 21937640763581012316718709)
                    ·
                      refine ⟨2056653821585719904692379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21937640763581012316718709 2056653821585719904692379)
                      ·
                        rfl

theorem cell23_4005319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_4005319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005319 prefixEnd_4005319 := by exact prefixLift 4005319
  have htrace : WordTrace (prefixWord ++ tailWord_4005319) baseStart_4005319 baseEnd_4005319 := by
    simpa [prefixWord, tailWord_4005319, baseEnd_4005319] using wordTrace_append hprefix tailTrace_4005319
  have hstable : (prefixWord ++ tailWord_4005319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005319).length < 2 ^ (prefixWord ++ tailWord_4005319).sum := by decide
  have hdescent : baseEnd_4005319 < baseStart_4005319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005343 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 2, 4]
def baseStart_4005343 : Nat := 118140960795 + 4005343 * 2 ^ 59
def prefixEnd_4005343 : Nat := 4983230072969 + 3 ^ 40 * 4005343 * 2
def baseEnd_4005343 : Nat := 685555381707142603597423

theorem tailTrace_4005343 : CollatzResearch.WordTrace tailWord_4005343 prefixEnd_4005343 685555381707142603597423 := by
  unfold tailWord_4005343
  simp only [CollatzResearch.WordTrace]
  refine ⟨146086860728333843968860683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97391240485555895979240455 146086860728333843968860683)
  ·
    refine ⟨219130291092500765953291025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146086860728333843968860683 219130291092500765953291025)
    ·
      refine ⟨164347718319375574464968269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219130291092500765953291025 164347718319375574464968269)
      ·
        refine ⟨61630394369765840424363101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164347718319375574464968269 61630394369765840424363101)
        ·
          refine ⟨23111397888662190159136163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61630394369765840424363101 23111397888662190159136163)
          ·
            refine ⟨34667096832993285238704245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23111397888662190159136163 34667096832993285238704245)
            ·
              refine ⟨3250040328093120491128523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34667096832993285238704245 3250040328093120491128523)
              ·
                refine ⟨4875060492139680736692785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250040328093120491128523 4875060492139680736692785)
                ·
                  refine ⟨3656295369104760552519589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875060492139680736692785 3656295369104760552519589)
                  ·
                    refine ⟨685555381707142603597423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656295369104760552519589 685555381707142603597423)
                    ·
                      rfl

theorem cell23_4005343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 4].length) (baseStart_4005343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005343 prefixEnd_4005343 := by exact prefixLift 4005343
  have htrace : WordTrace (prefixWord ++ tailWord_4005343) baseStart_4005343 baseEnd_4005343 := by
    simpa [prefixWord, tailWord_4005343, baseEnd_4005343] using wordTrace_append hprefix tailTrace_4005343
  have hstable : (prefixWord ++ tailWord_4005343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005343).length < 2 ^ (prefixWord ++ tailWord_4005343).sum := by decide
  have hdescent : baseEnd_4005343 < baseStart_4005343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005383 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_4005383 : Nat := 118140960795 + 4005383 * 2 ^ 59
def prefixEnd_4005383 : Nat := 4983230072969 + 3 ^ 40 * 4005383 * 2
def baseEnd_4005383 : Nat := 2056686684347607654292085

theorem tailTrace_4005383 : CollatzResearch.WordTrace tailWord_4005383 prefixEnd_4005383 2056686684347607654292085 := by
  unfold tailWord_4005383
  simp only [CollatzResearch.WordTrace]
  refine ⟨146088319648188930800316803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97392213098792620533544535 146088319648188930800316803)
  ·
    refine ⟨219132479472283396200475205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146088319648188930800316803 219132479472283396200475205)
    ·
      refine ⟨41087339901053136787589101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219132479472283396200475205 41087339901053136787589101)
      ·
        refine ⟨15407752462894926295345913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41087339901053136787589101 15407752462894926295345913)
        ·
          refine ⟨11555814347171194721509435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15407752462894926295345913 11555814347171194721509435)
          ·
            refine ⟨17333721520756792082264153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11555814347171194721509435 17333721520756792082264153)
            ·
              refine ⟨13000291140567594061698115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17333721520756792082264153 13000291140567594061698115)
              ·
                refine ⟨19500436710851391092547173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13000291140567594061698115 19500436710851391092547173)
                ·
                  refine ⟨3656331883284635829852595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19500436710851391092547173 3656331883284635829852595)
                  ·
                    refine ⟨5484497824926953744778893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656331883284635829852595 5484497824926953744778893)
                    ·
                      refine ⟨2056686684347607654292085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484497824926953744778893 2056686684347607654292085)
                      ·
                        rfl

theorem cell23_4005383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_4005383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005383 prefixEnd_4005383 := by exact prefixLift 4005383
  have htrace : WordTrace (prefixWord ++ tailWord_4005383) baseStart_4005383 baseEnd_4005383 := by
    simpa [prefixWord, tailWord_4005383, baseEnd_4005383] using wordTrace_append hprefix tailTrace_4005383
  have hstable : (prefixWord ++ tailWord_4005383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005383).length < 2 ^ (prefixWord ++ tailWord_4005383).sum := by decide
  have hdescent : baseEnd_4005383 < baseStart_4005383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005400 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4005400 : Nat := 118140960795 + 4005400 * 2 ^ 59
def prefixEnd_4005400 : Nat := 4983230072969 + 3 ^ 40 * 4005400 * 2
def baseEnd_4005400 : Nat := 2056695413518734087779507

theorem tailTrace_4005400 : CollatzResearch.WordTrace tailWord_4005400 prefixEnd_4005400 2056695413518734087779507 := by
  unfold tailWord_4005400
  simp only [CollatzResearch.WordTrace]
  refine ⟨73044469844563671351842827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97392626459418228469123769 73044469844563671351842827)
  ·
    refine ⟨109566704766845507027764241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73044469844563671351842827 109566704766845507027764241)
    ·
      refine ⟨82175028575134130270823181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109566704766845507027764241 82175028575134130270823181)
      ·
        refine ⟨30815635715675298851558693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82175028575134130270823181 30815635715675298851558693)
        ·
          refine ⟨5777931696689118534667255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30815635715675298851558693 5777931696689118534667255)
          ·
            refine ⟨8666897545033677802000883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777931696689118534667255 8666897545033677802000883)
            ·
              refine ⟨13000346317550516703001325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8666897545033677802000883 13000346317550516703001325)
              ·
                refine ⟨4875129869081443763625497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13000346317550516703001325 4875129869081443763625497)
                ·
                  refine ⟨3656347401811082822719123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875129869081443763625497 3656347401811082822719123)
                  ·
                    refine ⟨5484521102716624234078685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656347401811082822719123 5484521102716624234078685)
                    ·
                      refine ⟨2056695413518734087779507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484521102716624234078685 2056695413518734087779507)
                      ·
                        rfl

theorem cell23_4005400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4005400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005400 prefixEnd_4005400 := by exact prefixLift 4005400
  have htrace : WordTrace (prefixWord ++ tailWord_4005400) baseStart_4005400 baseEnd_4005400 := by
    simpa [prefixWord, tailWord_4005400, baseEnd_4005400] using wordTrace_append hprefix tailTrace_4005400
  have hstable : (prefixWord ++ tailWord_4005400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005400).length < 2 ^ (prefixWord ++ tailWord_4005400).sum := by decide
  have hdescent : baseEnd_4005400 < baseStart_4005400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005410 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_4005410 : Nat := 118140960795 + 4005410 * 2 ^ 59
def prefixEnd_4005410 : Nat := 4983230072969 + 3 ^ 40 * 4005410 * 2
def baseEnd_4005410 : Nat := 2056700548325279048654461

theorem tailTrace_4005410 : CollatzResearch.WordTrace tailWord_4005410 prefixEnd_4005410 2056700548325279048654461 := by
  unfold tailWord_4005410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36522326104772778602887421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97392869612727409607699789 36522326104772778602887421)
  ·
    refine ⟨13695872289289791976082783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36522326104772778602887421 13695872289289791976082783)
    ·
      refine ⟨20543808433934687964124175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13695872289289791976082783 20543808433934687964124175)
      ·
        refine ⟨30815712650902031946186263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20543808433934687964124175 30815712650902031946186263)
        ·
          refine ⟨46223568976353047919279395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30815712650902031946186263 46223568976353047919279395)
          ·
            refine ⟨69335353464529571878919093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46223568976353047919279395 69335353464529571878919093)
            ·
              refine ⟨6500189387299647363648665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69335353464529571878919093 6500189387299647363648665)
              ·
                refine ⟨4875142040474735522736499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6500189387299647363648665 4875142040474735522736499)
                ·
                  refine ⟨7312713060712103284104749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4875142040474735522736499 7312713060712103284104749)
                  ·
                    refine ⟨2742267397767038731539281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7312713060712103284104749 2742267397767038731539281)
                    ·
                      refine ⟨2056700548325279048654461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742267397767038731539281 2056700548325279048654461)
                      ·
                        rfl

theorem cell23_4005410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_4005410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005410 prefixEnd_4005410 := by exact prefixLift 4005410
  have htrace : WordTrace (prefixWord ++ tailWord_4005410) baseStart_4005410 baseEnd_4005410 := by
    simpa [prefixWord, tailWord_4005410, baseEnd_4005410] using wordTrace_append hprefix tailTrace_4005410
  have hstable : (prefixWord ++ tailWord_4005410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005410).length < 2 ^ (prefixWord ++ tailWord_4005410).sum := by decide
  have hdescent : baseEnd_4005410 < baseStart_4005410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005419 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4]
def baseStart_4005419 : Nat := 118140960795 + 4005419 * 2 ^ 59
def prefixEnd_4005419 : Nat := 4983230072969 + 3 ^ 40 * 4005419 * 2
def baseEnd_4005419 : Nat := 2056705169651169513441919

theorem tailTrace_4005419 : CollatzResearch.WordTrace tailWord_4005419 prefixEnd_4005419 2056705169651169513441919 := by
  unfold tailWord_4005419
  simp only [CollatzResearch.WordTrace]
  refine ⟨146089632676058508948627311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97393088450705672632418207 146089632676058508948627311)
  ·
    refine ⟨219134449014087763422940967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146089632676058508948627311 219134449014087763422940967)
    ·
      refine ⟨328701673521131645134411451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219134449014087763422940967 328701673521131645134411451)
      ·
        refine ⟨493052510281697467701617177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328701673521131645134411451 493052510281697467701617177)
        ·
          refine ⟨369789382711273100776212883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493052510281697467701617177 369789382711273100776212883)
          ·
            refine ⟨554684074066909651164319325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369789382711273100776212883 554684074066909651164319325)
            ·
              refine ⟨208006527775091119186619747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554684074066909651164319325 208006527775091119186619747)
              ·
                refine ⟨312009791662636678779929621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208006527775091119186619747 312009791662636678779929621)
                ·
                  refine ⟨14625458984186094317809201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312009791662636678779929621 14625458984186094317809201)
                  ·
                    refine ⟨10969094238139570738356901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14625458984186094317809201 10969094238139570738356901)
                    ·
                      refine ⟨2056705169651169513441919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10969094238139570738356901 2056705169651169513441919)
                      ·
                        rfl

theorem cell23_4005419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_4005419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005419 prefixEnd_4005419 := by exact prefixLift 4005419
  have htrace : WordTrace (prefixWord ++ tailWord_4005419) baseStart_4005419 baseEnd_4005419 := by
    simpa [prefixWord, tailWord_4005419, baseEnd_4005419] using wordTrace_append hprefix tailTrace_4005419
  have hstable : (prefixWord ++ tailWord_4005419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005419).length < 2 ^ (prefixWord ++ tailWord_4005419).sum := by decide
  have hdescent : baseEnd_4005419 < baseStart_4005419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005456 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_4005456 : Nat := 118140960795 + 4005456 * 2 ^ 59
def prefixEnd_4005456 : Nat := 4983230072969 + 3 ^ 40 * 4005456 * 2
def baseEnd_4005456 : Nat := 2056724168435385868679249

theorem tailTrace_4005456 : CollatzResearch.WordTrace tailWord_4005456 prefixEnd_4005456 2056724168435385868679249 := by
  unfold tailWord_4005456
  simp only [CollatzResearch.WordTrace]
  refine ⟨73045491088462232133862111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97393988117949642845149481 73045491088462232133862111)
  ·
    refine ⟨109568236632693348200793167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73045491088462232133862111 109568236632693348200793167)
    ·
      refine ⟨164352354949040022301189751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109568236632693348200793167 164352354949040022301189751)
      ·
        refine ⟨246528532423560033451784627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164352354949040022301189751 246528532423560033451784627)
        ·
          refine ⟨369792798635340050177676941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246528532423560033451784627 369792798635340050177676941)
          ·
            refine ⟨138672299488252518816628853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369792798635340050177676941 138672299488252518816628853)
            ·
              refine ⟨13000528077023673639058955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138672299488252518816628853 13000528077023673639058955)
              ·
                refine ⟨19500792115535510458588433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13000528077023673639058955 19500792115535510458588433)
                ·
                  refine ⟨14625594086651632843941325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19500792115535510458588433 14625594086651632843941325)
                  ·
                    refine ⟨5484597782494362316477997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14625594086651632843941325 5484597782494362316477997)
                    ·
                      refine ⟨2056724168435385868679249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484597782494362316477997 2056724168435385868679249)
                      ·
                        rfl

theorem cell23_4005456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_4005456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005456 prefixEnd_4005456 := by exact prefixLift 4005456
  have htrace : WordTrace (prefixWord ++ tailWord_4005456) baseStart_4005456 baseEnd_4005456 := by
    simpa [prefixWord, tailWord_4005456, baseEnd_4005456] using wordTrace_append hprefix tailTrace_4005456
  have hstable : (prefixWord ++ tailWord_4005456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005456).length < 2 ^ (prefixWord ++ tailWord_4005456).sum := by decide
  have hdescent : baseEnd_4005456 < baseStart_4005456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005476 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_4005476 : Nat := 118140960795 + 4005476 * 2 ^ 59
def prefixEnd_4005476 : Nat := 4983230072969 + 3 ^ 40 * 4005476 * 2
def baseEnd_4005476 : Nat := 685578146016158596809719

theorem tailTrace_4005476 : CollatzResearch.WordTrace tailWord_4005476 prefixEnd_4005476 685578146016158596809719 := by
  unfold tailWord_4005476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73045855818426003841726141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97394474424568005122301521 73045855818426003841726141)
  ·
    refine ⟨27392195931909751440647303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73045855818426003841726141 27392195931909751440647303)
    ·
      refine ⟨41088293897864627160970955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27392195931909751440647303 41088293897864627160970955)
      ·
        refine ⟨61632440846796940741456433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41088293897864627160970955 61632440846796940741456433)
        ·
          refine ⟨46224330635097705556092325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61632440846796940741456433 46224330635097705556092325)
          ·
            refine ⟨8667061994080819791767311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46224330635097705556092325 8667061994080819791767311)
            ·
              refine ⟨13000592991121229687650967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667061994080819791767311 13000592991121229687650967)
              ·
                refine ⟨19500889486681844531476451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13000592991121229687650967 19500889486681844531476451)
                ·
                  refine ⟨29251334230022766797214677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19500889486681844531476451 29251334230022766797214677)
                  ·
                    refine ⟨685578146016158596809719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29251334230022766797214677 685578146016158596809719)
                    ·
                      rfl

theorem cell23_4005476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_4005476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005476 prefixEnd_4005476 := by exact prefixLift 4005476
  have htrace : WordTrace (prefixWord ++ tailWord_4005476) baseStart_4005476 baseEnd_4005476 := by
    simpa [prefixWord, tailWord_4005476, baseEnd_4005476] using wordTrace_append hprefix tailTrace_4005476
  have hstable : (prefixWord ++ tailWord_4005476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005476).length < 2 ^ (prefixWord ++ tailWord_4005476).sum := by decide
  have hdescent : baseEnd_4005476 < baseStart_4005476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005480 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 5]
def baseStart_4005480 : Nat := 118140960795 + 4005480 * 2 ^ 59
def prefixEnd_4005480 : Nat := 4983230072969 + 3 ^ 40 * 4005480 * 2
def baseEnd_4005480 : Nat := 228526276885677086086571

theorem tailTrace_4005480 : CollatzResearch.WordTrace tailWord_4005480 prefixEnd_4005480 228526276885677086086571 := by
  unfold tailWord_4005480
  simp only [CollatzResearch.WordTrace]
  refine ⟨73045928764418758183298947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97394571685891677577731929 73045928764418758183298947)
  ·
    refine ⟨109568893146628137274948421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73045928764418758183298947 109568893146628137274948421)
    ·
      refine ⟨20544167464992775739052829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109568893146628137274948421 20544167464992775739052829)
      ·
        refine ⟨7704062799372290902144811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20544167464992775739052829 7704062799372290902144811)
        ·
          refine ⟨11556094199058436353217217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7704062799372290902144811 11556094199058436353217217)
          ·
            refine ⟨8667070649293827264912913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11556094199058436353217217 8667070649293827264912913)
            ·
              refine ⟨6500302986970370448684685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8667070649293827264912913 6500302986970370448684685)
              ·
                refine ⟨2437613620113888918256757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6500302986970370448684685 2437613620113888918256757)
                ·
                  refine ⟨228526276885677086086571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2437613620113888918256757 228526276885677086086571)
                  ·
                    rfl

theorem cell23_4005480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 5].length) (baseStart_4005480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005480 prefixEnd_4005480 := by exact prefixLift 4005480
  have htrace : WordTrace (prefixWord ++ tailWord_4005480) baseStart_4005480 baseEnd_4005480 := by
    simpa [prefixWord, tailWord_4005480, baseEnd_4005480] using wordTrace_append hprefix tailTrace_4005480
  have hstable : (prefixWord ++ tailWord_4005480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005480).length < 2 ^ (prefixWord ++ tailWord_4005480).sum := by decide
  have hdescent : baseEnd_4005480 < baseStart_4005480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005489 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_4005489 : Nat := 118140960795 + 4005489 * 2 ^ 59
def prefixEnd_4005489 : Nat := 4983230072969 + 3 ^ 40 * 4005489 * 2
def baseEnd_4005489 : Nat := 685580371098994746522199

theorem tailTrace_4005489 : CollatzResearch.WordTrace tailWord_4005489 prefixEnd_4005489 685580371098994746522199 := by
  unfold tailWord_4005489
  simp only [CollatzResearch.WordTrace]
  refine ⟨146092185785804910903675521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97394790523869940602450347 146092185785804910903675521)
  ·
    refine ⟨109569139339353683177756641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146092185785804910903675521 109569139339353683177756641)
    ·
      refine ⟨82176854504515262383317481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109569139339353683177756641 82176854504515262383317481)
      ·
        refine ⟨61632640878386446787488111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82176854504515262383317481 61632640878386446787488111)
        ·
          refine ⟨92448961317579670181232167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61632640878386446787488111 92448961317579670181232167)
          ·
            refine ⟨138673441976369505271848251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92448961317579670181232167 138673441976369505271848251)
            ·
              refine ⟨208010162964554257907772377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138673441976369505271848251 208010162964554257907772377)
              ·
                refine ⟨156007622223415693430829283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208010162964554257907772377 156007622223415693430829283)
                ·
                  refine ⟨234011433335123540146243925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156007622223415693430829283 234011433335123540146243925)
                  ·
                    refine ⟨685580371098994746522199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 234011433335123540146243925 685580371098994746522199)
                    ·
                      rfl

theorem cell23_4005489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_4005489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005489 prefixEnd_4005489 := by exact prefixLift 4005489
  have htrace : WordTrace (prefixWord ++ tailWord_4005489) baseStart_4005489 baseEnd_4005489 := by
    simpa [prefixWord, tailWord_4005489, baseEnd_4005489] using wordTrace_append hprefix tailTrace_4005489
  have hstable : (prefixWord ++ tailWord_4005489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005489).length < 2 ^ (prefixWord ++ tailWord_4005489).sum := by decide
  have hdescent : baseEnd_4005489 < baseStart_4005489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005513 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 2, 4, 2]
def baseStart_4005513 : Nat := 118140960795 + 4005513 * 2 ^ 59
def prefixEnd_4005513 : Nat := 4983230072969 + 3 ^ 40 * 4005513 * 2
def baseEnd_4005513 : Nat := 2056753436832692145666487

theorem tailTrace_4005513 : CollatzResearch.WordTrace tailWord_4005513 prefixEnd_4005513 2056753436832692145666487 := by
  unfold tailWord_4005513
  simp only [CollatzResearch.WordTrace]
  refine ⟨146093061137717963002549193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97395374091811975335032795 146093061137717963002549193)
  ·
    refine ⟨109569795853288472251911895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146093061137717963002549193 109569795853288472251911895)
    ·
      refine ⟨164354693779932708377867843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109569795853288472251911895 164354693779932708377867843)
      ·
        refine ⟨246532040669899062566801765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164354693779932708377867843 246532040669899062566801765)
        ·
          refine ⟨46224757625606074231275331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246532040669899062566801765 46224757625606074231275331)
          ·
            refine ⟨69337136438409111346912997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46224757625606074231275331 69337136438409111346912997)
            ·
              refine ⟨13000713082201708377546187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69337136438409111346912997 13000713082201708377546187)
              ·
                refine ⟨19501069623302562566319281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13000713082201708377546187 19501069623302562566319281)
                ·
                  refine ⟨14625802217476921924739461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19501069623302562566319281 14625802217476921924739461)
                  ·
                    refine ⟨2742337915776922860888649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14625802217476921924739461 2742337915776922860888649)
                    ·
                      refine ⟨2056753436832692145666487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742337915776922860888649 2056753436832692145666487)
                      ·
                        rfl

theorem cell23_4005513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 4, 2].length) (baseStart_4005513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005513 prefixEnd_4005513 := by exact prefixLift 4005513
  have htrace : WordTrace (prefixWord ++ tailWord_4005513) baseStart_4005513 baseEnd_4005513 := by
    simpa [prefixWord, tailWord_4005513, baseEnd_4005513] using wordTrace_append hprefix tailTrace_4005513
  have hstable : (prefixWord ++ tailWord_4005513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005513).length < 2 ^ (prefixWord ++ tailWord_4005513).sum := by decide
  have hdescent : baseEnd_4005513 < baseStart_4005513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005516 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_4005516 : Nat := 118140960795 + 4005516 * 2 ^ 59
def prefixEnd_4005516 : Nat := 4983230072969 + 3 ^ 40 * 4005516 * 2
def baseEnd_4005516 : Nat := 2056754977274655633928973

theorem tailTrace_4005516 : CollatzResearch.WordTrace tailWord_4005516 prefixEnd_4005516 2056754977274655633928973 := by
  unfold tailWord_4005516
  simp only [CollatzResearch.WordTrace]
  refine ⟨73046585278353547257454201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97395447037804729676605601 73046585278353547257454201)
  ·
    refine ⟨54784938958765160443090651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73046585278353547257454201 54784938958765160443090651)
    ·
      refine ⟨82177408438147740664635977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54784938958765160443090651 82177408438147740664635977)
      ·
        refine ⟨61633056328610805498476983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82177408438147740664635977 61633056328610805498476983)
        ·
          refine ⟨92449584492916208247715475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61633056328610805498476983 92449584492916208247715475)
          ·
            refine ⟨138674376739374312371573213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92449584492916208247715475 138674376739374312371573213)
            ·
              refine ⟨52002891277265367139339955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138674376739374312371573213 52002891277265367139339955)
              ·
                refine ⟨78004336915898050709009933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52002891277265367139339955 78004336915898050709009933)
                ·
                  refine ⟨29251626343461769015878725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78004336915898050709009933 29251626343461769015878725)
                  ·
                    refine ⟨5484679939399081690477261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29251626343461769015878725 5484679939399081690477261)
                    ·
                      refine ⟨2056754977274655633928973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484679939399081690477261 2056754977274655633928973)
                      ·
                        rfl

theorem cell23_4005516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_4005516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005516 prefixEnd_4005516 := by exact prefixLift 4005516
  have htrace : WordTrace (prefixWord ++ tailWord_4005516) baseStart_4005516 baseEnd_4005516 := by
    simpa [prefixWord, tailWord_4005516, baseEnd_4005516] using wordTrace_append hprefix tailTrace_4005516
  have hstable : (prefixWord ++ tailWord_4005516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005516).length < 2 ^ (prefixWord ++ tailWord_4005516).sum := by decide
  have hdescent : baseEnd_4005516 < baseStart_4005516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005519 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 12]
def baseStart_4005519 : Nat := 118140960795 + 4005519 * 2 ^ 59
def prefixEnd_4005519 : Nat := 4983230072969 + 3 ^ 40 * 4005519 * 2
def baseEnd_4005519 : Nat := 228528501968513235799051

theorem tailTrace_4005519 : CollatzResearch.WordTrace tailWord_4005519 prefixEnd_4005519 228528501968513235799051 := by
  unfold tailWord_4005519
  simp only [CollatzResearch.WordTrace]
  refine ⟨146093279975696226027267611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97395519983797484018178407 146093279975696226027267611)
  ·
    refine ⟨219139919963544339040901417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146093279975696226027267611 219139919963544339040901417)
    ·
      refine ⟨164354939972658254280676063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219139919963544339040901417 164354939972658254280676063)
      ·
        refine ⟨246532409958987381421014095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164354939972658254280676063 246532409958987381421014095)
        ·
          refine ⟨369798614938481072131521143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246532409958987381421014095 369798614938481072131521143)
          ·
            refine ⟨554697922407721608197281715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369798614938481072131521143 554697922407721608197281715)
            ·
              refine ⟨832046883611582412295922573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554697922407721608197281715 832046883611582412295922573)
              ·
                refine ⟨312017581354343404610970965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 832046883611582412295922573 312017581354343404610970965)
                ·
                  refine ⟨228528501968513235799051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 312017581354343404610970965 228528501968513235799051)
                  ·
                    rfl

theorem cell23_4005519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 12].length) (baseStart_4005519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005519 prefixEnd_4005519 := by exact prefixLift 4005519
  have htrace : WordTrace (prefixWord ++ tailWord_4005519) baseStart_4005519 baseEnd_4005519 := by
    simpa [prefixWord, tailWord_4005519, baseEnd_4005519] using wordTrace_append hprefix tailTrace_4005519
  have hstable : (prefixWord ++ tailWord_4005519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005519).length < 2 ^ (prefixWord ++ tailWord_4005519).sum := by decide
  have hdescent : baseEnd_4005519 < baseStart_4005519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005533 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_4005533 : Nat := 118140960795 + 4005533 * 2 ^ 59
def prefixEnd_4005533 : Nat := 4983230072969 + 3 ^ 40 * 4005533 * 2
def baseEnd_4005533 : Nat := 2056763706445782067416395

theorem tailTrace_4005533 : CollatzResearch.WordTrace tailWord_4005533 prefixEnd_4005533 2056763706445782067416395 := by
  unfold tailWord_4005533
  simp only [CollatzResearch.WordTrace]
  refine ⟨146093790597645506418277253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97395860398430337612184835 146093790597645506418277253)
  ·
    refine ⟨27392585737058532453426985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146093790597645506418277253 27392585737058532453426985)
    ·
      refine ⟨20544439302793899340070239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27392585737058532453426985 20544439302793899340070239)
      ·
        refine ⟨30816658954190849010105359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20544439302793899340070239 30816658954190849010105359)
        ·
          refine ⟨46224988431286273515158039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30816658954190849010105359 46224988431286273515158039)
          ·
            refine ⟨69337482646929410272737059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46224988431286273515158039 69337482646929410272737059)
            ·
              refine ⟨104006223970394115409105589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69337482646929410272737059 104006223970394115409105589)
              ·
                refine ⟨9750583497224448319603649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104006223970394115409105589 9750583497224448319603649)
                ·
                  refine ⟨7312937622918336239702737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9750583497224448319603649 7312937622918336239702737)
                  ·
                    refine ⟨5484703217188752179777053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7312937622918336239702737 5484703217188752179777053)
                    ·
                      refine ⟨2056763706445782067416395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484703217188752179777053 2056763706445782067416395)
                      ·
                        rfl

theorem cell23_4005533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_4005533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005533 prefixEnd_4005533 := by exact prefixLift 4005533
  have htrace : WordTrace (prefixWord ++ tailWord_4005533) baseStart_4005533 baseEnd_4005533 := by
    simpa [prefixWord, tailWord_4005533, baseEnd_4005533] using wordTrace_append hprefix tailTrace_4005533
  have hstable : (prefixWord ++ tailWord_4005533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005533).length < 2 ^ (prefixWord ++ tailWord_4005533).sum := by decide
  have hdescent : baseEnd_4005533 < baseStart_4005533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005536 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 8]
def baseStart_4005536 : Nat := 118140960795 + 4005536 * 2 ^ 59
def prefixEnd_4005536 : Nat := 4983230072969 + 3 ^ 40 * 4005536 * 2
def baseEnd_4005536 : Nat := 228529471876416172853209

theorem tailTrace_4005536 : CollatzResearch.WordTrace tailWord_4005536 prefixEnd_4005536 228529471876416172853209 := by
  unfold tailWord_4005536
  simp only [CollatzResearch.WordTrace]
  refine ⟨73046950008317318965318231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97395933344423091953757641 73046950008317318965318231)
  ·
    refine ⟨109570425012475978447977347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73046950008317318965318231 109570425012475978447977347)
    ·
      refine ⟨164355637518713967671966021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109570425012475978447977347 164355637518713967671966021)
      ·
        refine ⟨30816682034758868938493629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164355637518713967671966021 30816682034758868938493629)
        ·
          refine ⟨11556255763034575851935111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30816682034758868938493629 11556255763034575851935111)
          ·
            refine ⟨17334383644551863777902667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11556255763034575851935111 17334383644551863777902667)
            ·
              refine ⟨26001575466827795666854001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17334383644551863777902667 26001575466827795666854001)
              ·
                refine ⟨19501181600120846750140501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26001575466827795666854001 19501181600120846750140501)
                ·
                  refine ⟨228529471876416172853209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19501181600120846750140501 228529471876416172853209)
                  ·
                    rfl

theorem cell23_4005536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_4005536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005536 prefixEnd_4005536 := by exact prefixLift 4005536
  have htrace : WordTrace (prefixWord ++ tailWord_4005536) baseStart_4005536 baseEnd_4005536 := by
    simpa [prefixWord, tailWord_4005536, baseEnd_4005536] using wordTrace_append hprefix tailTrace_4005536
  have hstable : (prefixWord ++ tailWord_4005536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005536).length < 2 ^ (prefixWord ++ tailWord_4005536).sum := by decide
  have hdescent : baseEnd_4005536 < baseStart_4005536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005557 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_4005557 : Nat := 118140960795 + 4005557 * 2 ^ 59
def prefixEnd_4005557 : Nat := 4983230072969 + 3 ^ 40 * 4005557 * 2
def baseEnd_4005557 : Nat := 685592009993829991172095

theorem tailTrace_4005557 : CollatzResearch.WordTrace tailWord_4005557 prefixEnd_4005557 685592009993829991172095 := by
  unfold tailWord_4005557
  simp only [CollatzResearch.WordTrace]
  refine ⟨146094665949558558517150925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97396443966372372344767283 146094665949558558517150925)
  ·
    refine ⟨54785499731084459443931597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146094665949558558517150925 54785499731084459443931597)
    ·
      refine ⟨20544562399156672291474349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54785499731084459443931597 20544562399156672291474349)
      ·
        refine ⟨7704210899683752109302881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20544562399156672291474349 7704210899683752109302881)
        ·
          refine ⟨5778158174762814081977161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704210899683752109302881 5778158174762814081977161)
          ·
            refine ⟨4333618631072110561482871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778158174762814081977161 4333618631072110561482871)
            ·
              refine ⟨6500427946608165842224307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333618631072110561482871 6500427946608165842224307)
              ·
                refine ⟨9750641919912248763336461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6500427946608165842224307 9750641919912248763336461)
                ·
                  refine ⟨3656490719967093286251173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9750641919912248763336461 3656490719967093286251173)
                  ·
                    refine ⟨685592009993829991172095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656490719967093286251173 685592009993829991172095)
                    ·
                      rfl

theorem cell23_4005557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_4005557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005557 prefixEnd_4005557 := by exact prefixLift 4005557
  have htrace : WordTrace (prefixWord ++ tailWord_4005557) baseStart_4005557 baseEnd_4005557 := by
    simpa [prefixWord, tailWord_4005557, baseEnd_4005557] using wordTrace_append hprefix tailTrace_4005557
  have hstable : (prefixWord ++ tailWord_4005557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005557).length < 2 ^ (prefixWord ++ tailWord_4005557).sum := by decide
  have hdescent : baseEnd_4005557 < baseStart_4005557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005616 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_4005616 : Nat := 118140960795 + 4005616 * 2 ^ 59
def prefixEnd_4005616 : Nat := 4983230072969 + 3 ^ 40 * 4005616 * 2
def baseEnd_4005616 : Nat := 2056806325340105242678513

theorem tailTrace_4005616 : CollatzResearch.WordTrace tailWord_4005616 prefixEnd_4005616 2056806325340105242678513 := by
  unfold tailWord_4005616
  simp only [CollatzResearch.WordTrace]
  refine ⟨73048408928172405796774351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97397878570896541062365801 73048408928172405796774351)
  ·
    refine ⟨109572613392258608695161527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73048408928172405796774351 109572613392258608695161527)
    ·
      refine ⟨164358920088387913042742291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109572613392258608695161527 164358920088387913042742291)
      ·
        refine ⟨246538380132581869564113437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164358920088387913042742291 246538380132581869564113437)
        ·
          refine ⟨92451892549718201086542539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246538380132581869564113437 92451892549718201086542539)
          ·
            refine ⟨138677838824577301629813809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92451892549718201086542539 138677838824577301629813809)
            ·
              refine ⟨104008379118432976222360357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138677838824577301629813809 104008379118432976222360357)
              ·
                refine ⟨19501571084706183041692567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104008379118432976222360357 19501571084706183041692567)
                ·
                  refine ⟨29252356627059274562538851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19501571084706183041692567 29252356627059274562538851)
                  ·
                    refine ⟨43878534940588911843808277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29252356627059274562538851 43878534940588911843808277)
                    ·
                      refine ⟨2056806325340105242678513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43878534940588911843808277 2056806325340105242678513)
                      ·
                        rfl

theorem cell23_4005616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_4005616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005616 prefixEnd_4005616 := by exact prefixLift 4005616
  have htrace : WordTrace (prefixWord ++ tailWord_4005616) baseStart_4005616 baseEnd_4005616 := by
    simpa [prefixWord, tailWord_4005616, baseEnd_4005616] using wordTrace_append hprefix tailTrace_4005616
  have hstable : (prefixWord ++ tailWord_4005616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005616).length < 2 ^ (prefixWord ++ tailWord_4005616).sum := by decide
  have hdescent : baseEnd_4005616 < baseStart_4005616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005623 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_4005623 : Nat := 118140960795 + 4005623 * 2 ^ 59
def prefixEnd_4005623 : Nat := 4983230072969 + 3 ^ 40 * 4005623 * 2
def baseEnd_4005623 : Nat := 2056809919704686715290981

theorem tailTrace_4005623 : CollatzResearch.WordTrace tailWord_4005623 prefixEnd_4005623 2056809919704686715290981 := by
  unfold tailWord_4005623
  simp only [CollatzResearch.WordTrace]
  refine ⟨146097073167319451789053523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97398048778212967859369015 146097073167319451789053523)
  ·
    refine ⟨219145609750979177683580285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146097073167319451789053523 219145609750979177683580285)
    ·
      refine ⟨82179603656617191631342607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219145609750979177683580285 82179603656617191631342607)
      ·
        refine ⟨123269405484925787447013911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82179603656617191631342607 123269405484925787447013911)
        ·
          refine ⟨184904108227388681170520867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123269405484925787447013911 184904108227388681170520867)
          ·
            refine ⟨277356162341083021755781301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184904108227388681170520867 277356162341083021755781301)
            ·
              refine ⟨26002140219476533289604497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277356162341083021755781301 26002140219476533289604497)
              ·
                refine ⟨19501605164607399967203373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26002140219476533289604497 19501605164607399967203373)
                ·
                  refine ⟨7313101936727774987701265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19501605164607399967203373 7313101936727774987701265)
                  ·
                    refine ⟨5484826452545831240775949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7313101936727774987701265 5484826452545831240775949)
                    ·
                      refine ⟨2056809919704686715290981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484826452545831240775949 2056809919704686715290981)
                      ·
                        rfl

theorem cell23_4005623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_4005623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005623 prefixEnd_4005623 := by exact prefixLift 4005623
  have htrace : WordTrace (prefixWord ++ tailWord_4005623) baseStart_4005623 baseEnd_4005623 := by
    simpa [prefixWord, tailWord_4005623, baseEnd_4005623] using wordTrace_append hprefix tailTrace_4005623
  have hstable : (prefixWord ++ tailWord_4005623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005623).length < 2 ^ (prefixWord ++ tailWord_4005623).sum := by decide
  have hdescent : baseEnd_4005623 < baseStart_4005623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005633 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4005633 : Nat := 118140960795 + 4005633 * 2 ^ 59
def prefixEnd_4005633 : Nat := 4983230072969 + 3 ^ 40 * 4005633 * 2
def baseEnd_4005633 : Nat := 2056815054511231676165935

theorem tailTrace_4005633 : CollatzResearch.WordTrace tailWord_4005633 prefixEnd_4005633 2056815054511231676165935 := by
  unfold tailWord_4005633
  simp only [CollatzResearch.WordTrace]
  refine ⟨146097437897283223496917553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97398291931522148997945035 146097437897283223496917553)
  ·
    refine ⟨109573078422962417622688165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146097437897283223496917553 109573078422962417622688165)
    ·
      refine ⟨20544952204305453304254031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109573078422962417622688165 20544952204305453304254031)
      ·
        refine ⟨30817428306458179956381047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20544952204305453304254031 30817428306458179956381047)
        ·
          refine ⟨46226142459687269934571571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30817428306458179956381047 46226142459687269934571571)
          ·
            refine ⟨69339213689530904901857357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46226142459687269934571571 69339213689530904901857357)
            ·
              refine ⟨26002205133574089338196509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69339213689530904901857357 26002205133574089338196509)
              ·
                refine ⟨9750826925090283501823691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26002205133574089338196509 9750826925090283501823691)
                ·
                  refine ⟨14626240387635425252735537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9750826925090283501823691 14626240387635425252735537)
                  ·
                    refine ⟨10969680290726568939551653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14626240387635425252735537 10969680290726568939551653)
                    ·
                      refine ⟨2056815054511231676165935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10969680290726568939551653 2056815054511231676165935)
                      ·
                        rfl

theorem cell23_4005633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4005633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005633 prefixEnd_4005633 := by exact prefixLift 4005633
  have htrace : WordTrace (prefixWord ++ tailWord_4005633) baseStart_4005633 baseEnd_4005633 := by
    simpa [prefixWord, tailWord_4005633, baseEnd_4005633] using wordTrace_append hprefix tailTrace_4005633
  have hstable : (prefixWord ++ tailWord_4005633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005633).length < 2 ^ (prefixWord ++ tailWord_4005633).sum := by decide
  have hdescent : baseEnd_4005633 < baseStart_4005633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005640 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_4005640 : Nat := 118140960795 + 4005640 * 2 ^ 59
def prefixEnd_4005640 : Nat := 4983230072969 + 3 ^ 40 * 4005640 * 2
def baseEnd_4005640 : Nat := 2056818648875813148778403

theorem tailTrace_4005640 : CollatzResearch.WordTrace tailWord_4005640 prefixEnd_4005640 2056818648875813148778403 := by
  unfold tailWord_4005640
  simp only [CollatzResearch.WordTrace]
  refine ⟨73048846604128931846211187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97398462138838575794948249 73048846604128931846211187)
  ·
    refine ⟨109573269906193397769316781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73048846604128931846211187 109573269906193397769316781)
    ·
      refine ⟨41089976214822524163493793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109573269906193397769316781 41089976214822524163493793)
      ·
        refine ⟨30817482161116893122620345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41089976214822524163493793 30817482161116893122620345)
        ·
          refine ⟨23113111620837669841965259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30817482161116893122620345 23113111620837669841965259)
          ·
            refine ⟨34669667431256504762947889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23113111620837669841965259 34669667431256504762947889)
            ·
              refine ⟨26002250573442378572210917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34669667431256504762947889 26002250573442378572210917)
              ·
                refine ⟨4875421982520445982289547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26002250573442378572210917 4875421982520445982289547)
                ·
                  refine ⟨7313132973780668973434321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4875421982520445982289547 7313132973780668973434321)
                  ·
                    refine ⟨5484849730335501730075741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7313132973780668973434321 5484849730335501730075741)
                    ·
                      refine ⟨2056818648875813148778403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484849730335501730075741 2056818648875813148778403)
                      ·
                        rfl

theorem cell23_4005640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_4005640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005640 prefixEnd_4005640 := by exact prefixLift 4005640
  have htrace : WordTrace (prefixWord ++ tailWord_4005640) baseStart_4005640 baseEnd_4005640 := by
    simpa [prefixWord, tailWord_4005640, baseEnd_4005640] using wordTrace_append hprefix tailTrace_4005640
  have hstable : (prefixWord ++ tailWord_4005640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005640).length < 2 ^ (prefixWord ++ tailWord_4005640).sum := by decide
  have hdescent : baseEnd_4005640 < baseStart_4005640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005713 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_4005713 : Nat := 118140960795 + 4005713 * 2 ^ 59
def prefixEnd_4005713 : Nat := 4983230072969 + 3 ^ 40 * 4005713 * 2
def baseEnd_4005713 : Nat := 2056856132963591363165567

theorem tailTrace_4005713 : CollatzResearch.WordTrace tailWord_4005713 prefixEnd_4005713 2056856132963591363165567 := by
  unfold tailWord_4005713
  simp only [CollatzResearch.WordTrace]
  refine ⟨146100355736993397159829793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97400237157995598106553195 146100355736993397159829793)
  ·
    refine ⟨109575266802745047869872345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146100355736993397159829793 109575266802745047869872345)
    ·
      refine ⟨82181450102058785902404259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109575266802745047869872345 82181450102058785902404259)
      ·
        refine ⟨123272175153088178853606389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82181450102058785902404259 123272175153088178853606389)
        ·
          refine ⟨11556766420602016767525599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123272175153088178853606389 11556766420602016767525599)
          ·
            refine ⟨17335149630903025151288399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11556766420602016767525599 17335149630903025151288399)
            ·
              refine ⟨26002724446354537726932599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17335149630903025151288399 26002724446354537726932599)
              ·
                refine ⟨39004086669531806590398899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26002724446354537726932599 39004086669531806590398899)
                ·
                  refine ⟨58506130004297709885598349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39004086669531806590398899 58506130004297709885598349)
                  ·
                    refine ⟨21939798751611641207099381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58506130004297709885598349 21939798751611641207099381)
                    ·
                      refine ⟨2056856132963591363165567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21939798751611641207099381 2056856132963591363165567)
                      ·
                        rfl

theorem cell23_4005713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_4005713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005713 prefixEnd_4005713 := by exact prefixLift 4005713
  have htrace : WordTrace (prefixWord ++ tailWord_4005713) baseStart_4005713 baseEnd_4005713 := by
    simpa [prefixWord, tailWord_4005713, baseEnd_4005713] using wordTrace_append hprefix tailTrace_4005713
  have hstable : (prefixWord ++ tailWord_4005713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005713).length < 2 ^ (prefixWord ++ tailWord_4005713).sum := by decide
  have hdescent : baseEnd_4005713 < baseStart_4005713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005727 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 4, 2, 2]
def baseStart_4005727 : Nat := 118140960795 + 4005727 * 2 ^ 59
def prefixEnd_4005727 : Nat := 4983230072969 + 3 ^ 40 * 4005727 * 2
def baseEnd_4005727 : Nat := 2056863321692754308390503

theorem tailTrace_4005727 : CollatzResearch.WordTrace tailWord_4005727 prefixEnd_4005727 2056863321692754308390503 := by
  unfold tailWord_4005727
  simp only [CollatzResearch.WordTrace]
  refine ⟨146100866358942677550839435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97400577572628451700559623 146100866358942677550839435)
  ·
    refine ⟨219151299538414016326259153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146100866358942677550839435 219151299538414016326259153)
    ·
      refine ⟨164363474653810512244694365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219151299538414016326259153 164363474653810512244694365)
      ·
        refine ⟨61636302995178942091760387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164363474653810512244694365 61636302995178942091760387)
        ·
          refine ⟨92454454492768413137640581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61636302995178942091760387 92454454492768413137640581)
          ·
            refine ⟨17335210217394077463307609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92454454492768413137640581 17335210217394077463307609)
            ·
              refine ⟨13001407663045558097480707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17335210217394077463307609 13001407663045558097480707)
              ·
                refine ⟨19502111494568337146221061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13001407663045558097480707 19502111494568337146221061)
                ·
                  refine ⟨3656645905231563214916449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19502111494568337146221061 3656645905231563214916449)
                  ·
                    refine ⟨2742484428923672411187337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3656645905231563214916449 2742484428923672411187337)
                    ·
                      refine ⟨2056863321692754308390503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742484428923672411187337 2056863321692754308390503)
                      ·
                        rfl

theorem cell23_4005727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_4005727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005727 prefixEnd_4005727 := by exact prefixLift 4005727
  have htrace : WordTrace (prefixWord ++ tailWord_4005727) baseStart_4005727 baseEnd_4005727 := by
    simpa [prefixWord, tailWord_4005727, baseEnd_4005727] using wordTrace_append hprefix tailTrace_4005727
  have hstable : (prefixWord ++ tailWord_4005727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005727).length < 2 ^ (prefixWord ++ tailWord_4005727).sum := by decide
  have hdescent : baseEnd_4005727 < baseStart_4005727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005738 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4005738 : Nat := 118140960795 + 4005738 * 2 ^ 59
def prefixEnd_4005738 : Nat := 4983230072969 + 3 ^ 40 * 4005738 * 2
def baseEnd_4005738 : Nat := 2056868969979953765352953

theorem tailTrace_4005738 : CollatzResearch.WordTrace tailWord_4005738 prefixEnd_4005738 2056868969979953765352953 := by
  unfold tailWord_4005738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36525316890475706607372467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97400845041268550952993245 36525316890475706607372467)
  ·
    refine ⟨54787975335713559911058701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36525316890475706607372467 54787975335713559911058701)
    ·
      refine ⟨20545490750892584966647013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54787975335713559911058701 20545490750892584966647013)
      ·
        refine ⟨3852279515792359681246315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20545490750892584966647013 3852279515792359681246315)
        ·
          refine ⟨5778419273688539521869473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852279515792359681246315 5778419273688539521869473)
          ·
            refine ⟨4333814455266404641402105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778419273688539521869473 4333814455266404641402105)
            ·
              refine ⟨3250360841449803481051579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4333814455266404641402105 3250360841449803481051579)
              ·
                refine ⟨4875541262174705221577369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250360841449803481051579 4875541262174705221577369)
                ·
                  refine ⟨3656655946631028916183027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875541262174705221577369 3656655946631028916183027)
                  ·
                    refine ⟨5484983919946543374274541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656655946631028916183027 5484983919946543374274541)
                    ·
                      refine ⟨2056868969979953765352953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5484983919946543374274541 2056868969979953765352953)
                      ·
                        rfl

theorem cell23_4005738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4005738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005738 prefixEnd_4005738 := by exact prefixLift 4005738
  have htrace : WordTrace (prefixWord ++ tailWord_4005738) baseStart_4005738 baseEnd_4005738 := by
    simpa [prefixWord, tailWord_4005738, baseEnd_4005738] using wordTrace_append hprefix tailTrace_4005738
  have hstable : (prefixWord ++ tailWord_4005738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005738).length < 2 ^ (prefixWord ++ tailWord_4005738).sum := by decide
  have hdescent : baseEnd_4005738 < baseStart_4005738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005784 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 5]
def baseStart_4005784 : Nat := 118140960795 + 4005784 * 2 ^ 59
def prefixEnd_4005784 : Nat := 4983230072969 + 3 ^ 40 * 4005784 * 2
def baseEnd_4005784 : Nat := 228543621121117842819749

theorem tailTrace_4005784 : CollatzResearch.WordTrace tailWord_4005784 prefixEnd_4005784 228543621121117842819749 := by
  unfold tailWord_4005784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73051472659868088142832203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97401963546490784190442937 73051472659868088142832203)
  ·
    refine ⟨109577208989802132214248305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73051472659868088142832203 109577208989802132214248305)
    ·
      refine ⟨82182906742351599160686229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109577208989802132214248305 82182906742351599160686229)
      ·
        refine ⟨3852323753547731210657167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82182906742351599160686229 3852323753547731210657167)
        ·
          refine ⟨5778485630321596815985751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852323753547731210657167 5778485630321596815985751)
          ·
            refine ⟨8667728445482395223978627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778485630321596815985751 8667728445482395223978627)
            ·
              refine ⟨13001592668223592835967941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667728445482395223978627 13001592668223592835967941)
              ·
                refine ⟨2437798625291923656743989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13001592668223592835967941 2437798625291923656743989)
                ·
                  refine ⟨228543621121117842819749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2437798625291923656743989 228543621121117842819749)
                  ·
                    rfl

theorem cell23_4005784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 5].length) (baseStart_4005784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005784 prefixEnd_4005784 := by exact prefixLift 4005784
  have htrace : WordTrace (prefixWord ++ tailWord_4005784) baseStart_4005784 baseEnd_4005784 := by
    simpa [prefixWord, tailWord_4005784, baseEnd_4005784] using wordTrace_append hprefix tailTrace_4005784
  have hstable : (prefixWord ++ tailWord_4005784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005784).length < 2 ^ (prefixWord ++ tailWord_4005784).sum := by decide
  have hdescent : baseEnd_4005784 < baseStart_4005784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005823 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 8]
def baseStart_4005823 : Nat := 118140960795 + 4005823 * 2 ^ 59
def prefixEnd_4005823 : Nat := 4983230072969 + 3 ^ 40 * 4005823 * 2
def baseEnd_4005823 : Nat := 228545846203953992532229

theorem tailTrace_4005823 : CollatzResearch.WordTrace tailWord_4005823 prefixEnd_4005823 228545846203953992532229 := by
  unfold tailWord_4005823
  simp only [CollatzResearch.WordTrace]
  refine ⟨146104367766594885946334123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97402911844396590630889415 146104367766594885946334123)
  ·
    refine ⟨219156551649892328919501185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146104367766594885946334123 219156551649892328919501185)
    ·
      refine ⟨164367413737419246689625889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219156551649892328919501185 164367413737419246689625889)
      ·
        refine ⟨123275560303064435017219417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164367413737419246689625889 123275560303064435017219417)
        ·
          refine ⟨92456670227298326262914563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123275560303064435017219417 92456670227298326262914563)
          ·
            refine ⟨138685005340947489394371845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92456670227298326262914563 138685005340947489394371845)
            ·
              refine ⟨26003438501427654261444721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138685005340947489394371845 26003438501427654261444721)
              ·
                refine ⟨19502578876070740696083541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26003438501427654261444721 19502578876070740696083541)
                ·
                  refine ⟨228545846203953992532229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19502578876070740696083541 228545846203953992532229)
                  ·
                    rfl

theorem cell23_4005823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 8].length) (baseStart_4005823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005823 prefixEnd_4005823 := by exact prefixLift 4005823
  have htrace : WordTrace (prefixWord ++ tailWord_4005823) baseStart_4005823 baseEnd_4005823 := by
    simpa [prefixWord, tailWord_4005823, baseEnd_4005823] using wordTrace_append hprefix tailTrace_4005823
  have hstable : (prefixWord ++ tailWord_4005823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005823).length < 2 ^ (prefixWord ++ tailWord_4005823).sum := by decide
  have hdescent : baseEnd_4005823 < baseStart_4005823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005840 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 6]
def baseStart_4005840 : Nat := 118140960795 + 4005840 * 2 ^ 59
def prefixEnd_4005840 : Nat := 4983230072969 + 3 ^ 40 * 4005840 * 2
def baseEnd_4005840 : Nat := 228546816111856929586387

theorem tailTrace_4005840 : CollatzResearch.WordTrace tailWord_4005840 prefixEnd_4005840 228546816111856929586387 := by
  unfold tailWord_4005840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73052493903766648924851487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97403325205022198566468649 73052493903766648924851487)
  ·
    refine ⟨109578740855649973387277231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73052493903766648924851487 109578740855649973387277231)
    ·
      refine ⟨164368111283474960080915847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109578740855649973387277231 164368111283474960080915847)
      ·
        refine ⟨246552166925212440121373771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164368111283474960080915847 246552166925212440121373771)
        ·
          refine ⟨369828250387818660182060657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246552166925212440121373771 369828250387818660182060657)
          ·
            refine ⟨277371187790863995136545493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369828250387818660182060657 277371187790863995136545493)
            ·
              refine ⟨6500887213848374886012785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 277371187790863995136545493 6500887213848374886012785)
              ·
                refine ⟨4875665410386281164509589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6500887213848374886012785 4875665410386281164509589)
                ·
                  refine ⟨228546816111856929586387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4875665410386281164509589 228546816111856929586387)
                  ·
                    rfl

theorem cell23_4005840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_4005840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005840 prefixEnd_4005840 := by exact prefixLift 4005840
  have htrace : WordTrace (prefixWord ++ tailWord_4005840) baseStart_4005840 baseEnd_4005840 := by
    simpa [prefixWord, tailWord_4005840, baseEnd_4005840] using wordTrace_append hprefix tailTrace_4005840
  have hstable : (prefixWord ++ tailWord_4005840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005840).length < 2 ^ (prefixWord ++ tailWord_4005840).sum := by decide
  have hdescent : baseEnd_4005840 < baseStart_4005840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005844 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_4005844 : Nat := 118140960795 + 4005844 * 2 ^ 59
def prefixEnd_4005844 : Nat := 4983230072969 + 3 ^ 40 * 4005844 * 2
def baseEnd_4005844 : Nat := 685641132976443450209155

theorem tailTrace_4005844 : CollatzResearch.WordTrace tailWord_4005844 prefixEnd_4005844 685641132976443450209155 := by
  unfold tailWord_4005844
  simp only [CollatzResearch.WordTrace]
  refine ⟨73052566849759403266424293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97403422466345871021899057 73052566849759403266424293)
  ·
    refine ⟨13697356284329888112454555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73052566849759403266424293 13697356284329888112454555)
    ·
      refine ⟨20546034426494832168681833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697356284329888112454555 20546034426494832168681833)
      ·
        refine ⟨15409525819871124126511375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20546034426494832168681833 15409525819871124126511375)
        ·
          refine ⟨23114288729806686189767063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15409525819871124126511375 23114288729806686189767063)
          ·
            refine ⟨34671433094710029284650595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23114288729806686189767063 34671433094710029284650595)
            ·
              refine ⟨52007149642065043926975893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34671433094710029284650595 52007149642065043926975893)
              ·
                refine ⟨2437835139471798934076995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52007149642065043926975893 2437835139471798934076995)
                ·
                  refine ⟨3656752709207698401115493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437835139471798934076995 3656752709207698401115493)
                  ·
                    refine ⟨685641132976443450209155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656752709207698401115493 685641132976443450209155)
                    ·
                      rfl

theorem cell23_4005844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_4005844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005844 prefixEnd_4005844 := by exact prefixLift 4005844
  have htrace : WordTrace (prefixWord ++ tailWord_4005844) baseStart_4005844 baseEnd_4005844 := by
    simpa [prefixWord, tailWord_4005844, baseEnd_4005844] using wordTrace_append hprefix tailTrace_4005844
  have hstable : (prefixWord ++ tailWord_4005844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005844).length < 2 ^ (prefixWord ++ tailWord_4005844).sum := by decide
  have hdescent : baseEnd_4005844 < baseStart_4005844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005878 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_4005878 : Nat := 118140960795 + 4005878 * 2 ^ 59
def prefixEnd_4005878 : Nat := 4983230072969 + 3 ^ 40 * 4005878 * 2
def baseEnd_4005878 : Nat := 685646952423861072534103

theorem tailTrace_4005878 : CollatzResearch.WordTrace tailWord_4005878 prefixEnd_4005878 685646952423861072534103 := by
  unfold tailWord_4005878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131648361337226896224143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97404249187597086893057525 9131648361337226896224143)
  ·
    refine ⟨13697472542005840344336215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9131648361337226896224143 13697472542005840344336215)
    ·
      refine ⟨20546208813008760516504323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697472542005840344336215 20546208813008760516504323)
      ·
        refine ⟨30819313219513140774756485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20546208813008760516504323 30819313219513140774756485)
        ·
          refine ⟨5778621228658713895266841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30819313219513140774756485 5778621228658713895266841)
          ·
            refine ⟨4333965921494035421450131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778621228658713895266841 4333965921494035421450131)
            ·
              refine ⟨6500948882241053132175197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333965921494035421450131 6500948882241053132175197)
              ·
                refine ⟨2437855830840394924565699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6500948882241053132175197 2437855830840394924565699)
                ·
                  refine ⟨3656783746260592386848549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437855830840394924565699 3656783746260592386848549)
                  ·
                    refine ⟨685646952423861072534103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656783746260592386848549 685646952423861072534103)
                    ·
                      rfl

theorem cell23_4005878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_4005878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005878 prefixEnd_4005878 := by exact prefixLift 4005878
  have htrace : WordTrace (prefixWord ++ tailWord_4005878) baseStart_4005878 baseEnd_4005878 := by
    simpa [prefixWord, tailWord_4005878, baseEnd_4005878] using wordTrace_append hprefix tailTrace_4005878
  have hstable : (prefixWord ++ tailWord_4005878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005878).length < 2 ^ (prefixWord ++ tailWord_4005878).sum := by decide
  have hdescent : baseEnd_4005878 < baseStart_4005878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005908 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 6]
def baseStart_4005908 : Nat := 118140960795 + 4005908 * 2 ^ 59
def prefixEnd_4005908 : Nat := 4983230072969 + 3 ^ 40 * 4005908 * 2
def baseEnd_4005908 : Nat := 228550695743468677803019

theorem tailTrace_4005908 : CollatzResearch.WordTrace tailWord_4005908 prefixEnd_4005908 228550695743468677803019 := by
  unfold tailWord_4005908
  simp only [CollatzResearch.WordTrace]
  refine ⟨73053733985643472731589189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97404978647524630308785585 73053733985643472731589189)
  ·
    refine ⟨13697575122308151137172973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73053733985643472731589189 13697575122308151137172973)
    ·
      refine ⟨5136590670865556676439865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13697575122308151137172973 5136590670865556676439865)
      ·
        refine ⟨3852443003149167507329899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5136590670865556676439865 3852443003149167507329899)
        ·
          refine ⟨5778664504723751260994849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852443003149167507329899 5778664504723751260994849)
          ·
            refine ⟨4333998378542813445746137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778664504723751260994849 4333998378542813445746137)
            ·
              refine ⟨3250498783907110084309603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4333998378542813445746137 3250498783907110084309603)
              ·
                refine ⟨4875748175860665126464405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250498783907110084309603 4875748175860665126464405)
                ·
                  refine ⟨228550695743468677803019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4875748175860665126464405 228550695743468677803019)
                  ·
                    rfl

theorem cell23_4005908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_4005908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005908 prefixEnd_4005908 := by exact prefixLift 4005908
  have htrace : WordTrace (prefixWord ++ tailWord_4005908) baseStart_4005908 baseEnd_4005908 := by
    simpa [prefixWord, tailWord_4005908, baseEnd_4005908] using wordTrace_append hprefix tailTrace_4005908
  have hstable : (prefixWord ++ tailWord_4005908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005908).length < 2 ^ (prefixWord ++ tailWord_4005908).sum := by decide
  have hdescent : baseEnd_4005908 < baseStart_4005908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005921 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 1, 5]
def baseStart_4005921 : Nat := 118140960795 + 4005921 * 2 ^ 59
def prefixEnd_4005921 : Nat := 4983230072969 + 3 ^ 40 * 4005921 * 2
def baseEnd_4005921 : Nat := 685654312313242183121537

theorem tailTrace_4005921 : CollatzResearch.WordTrace tailWord_4005921 prefixEnd_4005921 685654312313242183121537 := by
  unfold tailWord_4005921
  simp only [CollatzResearch.WordTrace]
  refine ⟨146107942120239848683401617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97405294746826565788934411 146107942120239848683401617)
  ·
    refine ⟨109580956590179886512551213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146107942120239848683401617 109580956590179886512551213)
    ·
      refine ⟨41092858721317457442206705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109580956590179886512551213 41092858721317457442206705)
      ·
        refine ⟨30819644040988093081655029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41092858721317457442206705 30819644040988093081655029)
        ·
          refine ⟨2889341628842633726405159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30819644040988093081655029 2889341628842633726405159)
          ·
            refine ⟨4334012443263950589607739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889341628842633726405159 4334012443263950589607739)
            ·
              refine ⟨6501018664895925884411609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334012443263950589607739 6501018664895925884411609)
              ·
                refine ⟨4875763998671944413308707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501018664895925884411609 4875763998671944413308707)
                ·
                  refine ⟨7313645998007916619963061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4875763998671944413308707 7313645998007916619963061)
                  ·
                    refine ⟨685654312313242183121537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7313645998007916619963061 685654312313242183121537)
                    ·
                      rfl

theorem cell23_4005921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_4005921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005921 prefixEnd_4005921 := by exact prefixLift 4005921
  have htrace : WordTrace (prefixWord ++ tailWord_4005921) baseStart_4005921 baseEnd_4005921 := by
    simpa [prefixWord, tailWord_4005921, baseEnd_4005921] using wordTrace_append hprefix tailTrace_4005921
  have hstable : (prefixWord ++ tailWord_4005921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005921).length < 2 ^ (prefixWord ++ tailWord_4005921).sum := by decide
  have hdescent : baseEnd_4005921 < baseStart_4005921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005924 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4005924 : Nat := 118140960795 + 4005924 * 2 ^ 59
def prefixEnd_4005924 : Nat := 4983230072969 + 3 ^ 40 * 4005924 * 2
def baseEnd_4005924 : Nat := 2056964477381690037627097

theorem tailTrace_4005924 : CollatzResearch.WordTrace tailWord_4005924 prefixEnd_4005924 2056964477381690037627097 := by
  unfold tailWord_4005924
  simp only [CollatzResearch.WordTrace]
  refine ⟨73054025769614490097880413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97405367692819320130507217 73054025769614490097880413)
  ·
    refine ⟨27395259663605433786705155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73054025769614490097880413 27395259663605433786705155)
    ·
      refine ⟨41092889495408150680057733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27395259663605433786705155 41092889495408150680057733)
      ·
        refine ⟨7704916780389028252510825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41092889495408150680057733 7704916780389028252510825)
        ·
          refine ⟨5778687585291771189383119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704916780389028252510825 5778687585291771189383119)
          ·
            refine ⟨8668031377937656784074679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778687585291771189383119 8668031377937656784074679)
            ·
              refine ⟨13002047066906485176112019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668031377937656784074679 13002047066906485176112019)
              ·
                refine ⟨19503070600359727764168029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13002047066906485176112019 19503070600359727764168029)
                ·
                  refine ⟨7313651475134897911563011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19503070600359727764168029 7313651475134897911563011)
                  ·
                    refine ⟨10970477212702346867344517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7313651475134897911563011 10970477212702346867344517)
                    ·
                      refine ⟨2056964477381690037627097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10970477212702346867344517 2056964477381690037627097)
                      ·
                        rfl

theorem cell23_4005924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4005924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005924 prefixEnd_4005924 := by exact prefixLift 4005924
  have htrace : WordTrace (prefixWord ++ tailWord_4005924) baseStart_4005924 baseEnd_4005924 := by
    simpa [prefixWord, tailWord_4005924, baseEnd_4005924] using wordTrace_append hprefix tailTrace_4005924
  have hstable : (prefixWord ++ tailWord_4005924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005924).length < 2 ^ (prefixWord ++ tailWord_4005924).sum := by decide
  have hdescent : baseEnd_4005924 < baseStart_4005924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005928 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4005928 : Nat := 118140960795 + 4005928 * 2 ^ 59
def prefixEnd_4005928 : Nat := 4983230072969 + 3 ^ 40 * 4005928 * 2
def baseEnd_4005928 : Nat := 2056966531304308021977079

theorem tailTrace_4005928 : CollatzResearch.WordTrace tailWord_4005928 prefixEnd_4005928 2056966531304308021977079 := by
  unfold tailWord_4005928
  simp only [CollatzResearch.WordTrace]
  refine ⟨73054098715607244439453219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97405464954142992585937625 73054098715607244439453219)
  ·
    refine ⟨109581148073410866659179829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73054098715607244439453219 109581148073410866659179829)
    ·
      refine ⟨10273232631882268749298109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109581148073410866659179829 10273232631882268749298109)
      ·
        refine ⟨3852462236955850780986791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10273232631882268749298109 3852462236955850780986791)
        ·
          refine ⟨5778693355433776171480187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852462236955850780986791 5778693355433776171480187)
          ·
            refine ⟨8668040033150664257220281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778693355433776171480187 8668040033150664257220281)
            ·
              refine ⟨6501030024862998192915211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8668040033150664257220281 6501030024862998192915211)
              ·
                refine ⟨9751545037294497289372817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501030024862998192915211 9751545037294497289372817)
                ·
                  refine ⟨7313658777970872967029613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9751545037294497289372817 7313658777970872967029613)
                  ·
                    refine ⟨2742622041739077362636105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7313658777970872967029613 2742622041739077362636105)
                    ·
                      refine ⟨2056966531304308021977079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742622041739077362636105 2056966531304308021977079)
                      ·
                        rfl

theorem cell23_4005928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4005928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005928 prefixEnd_4005928 := by exact prefixLift 4005928
  have htrace : WordTrace (prefixWord ++ tailWord_4005928) baseStart_4005928 baseEnd_4005928 := by
    simpa [prefixWord, tailWord_4005928, baseEnd_4005928] using wordTrace_append hprefix tailTrace_4005928
  have hstable : (prefixWord ++ tailWord_4005928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005928).length < 2 ^ (prefixWord ++ tailWord_4005928).sum := by decide
  have hdescent : baseEnd_4005928 < baseStart_4005928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005937 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4005937 : Nat := 118140960795 + 4005937 * 2 ^ 59
def prefixEnd_4005937 : Nat := 4983230072969 + 3 ^ 40 * 4005937 * 2
def baseEnd_4005937 : Nat := 2056971152630198486764537

theorem tailTrace_4005937 : CollatzResearch.WordTrace tailWord_4005937 prefixEnd_4005937 2056971152630198486764537 := by
  unfold tailWord_4005937
  simp only [CollatzResearch.WordTrace]
  refine ⟨146108525688181883415984065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97405683792121255610656043 146108525688181883415984065)
  ·
    refine ⟨109581394266136412561988049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146108525688181883415984065 109581394266136412561988049)
    ·
      refine ⟨82186045699602309421491037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109581394266136412561988049 82186045699602309421491037)
      ·
        refine ⟨30819767137350866033059139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82186045699602309421491037 30819767137350866033059139)
        ·
          refine ⟨46229650706026299049588709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30819767137350866033059139 46229650706026299049588709)
          ·
            refine ⟨8668059507379931071797883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46229650706026299049588709 8668059507379931071797883)
            ·
              refine ⟨13002089261069896607696825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668059507379931071797883 13002089261069896607696825)
              ·
                refine ⟨9751566945802422455772619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13002089261069896607696825 9751566945802422455772619)
                ·
                  refine ⟨14627350418703633683658929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9751566945802422455772619 14627350418703633683658929)
                  ·
                    refine ⟨10970512814027725262744197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14627350418703633683658929 10970512814027725262744197)
                    ·
                      refine ⟨2056971152630198486764537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10970512814027725262744197 2056971152630198486764537)
                      ·
                        rfl

theorem cell23_4005937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4005937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005937 prefixEnd_4005937 := by exact prefixLift 4005937
  have htrace : WordTrace (prefixWord ++ tailWord_4005937) baseStart_4005937 baseEnd_4005937 := by
    simpa [prefixWord, tailWord_4005937, baseEnd_4005937] using wordTrace_append hprefix tailTrace_4005937
  have hstable : (prefixWord ++ tailWord_4005937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005937).length < 2 ^ (prefixWord ++ tailWord_4005937).sum := by decide
  have hdescent : baseEnd_4005937 < baseStart_4005937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005944 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_4005944 : Nat := 118140960795 + 4005944 * 2 ^ 59
def prefixEnd_4005944 : Nat := 4983230072969 + 3 ^ 40 * 4005944 * 2
def baseEnd_4005944 : Nat := 2056974746994779959377005

theorem tailTrace_4005944 : CollatzResearch.WordTrace tailWord_4005944 prefixEnd_4005944 2056974746994779959377005 := by
  unfold tailWord_4005944
  simp only [CollatzResearch.WordTrace]
  refine ⟨73054390499578261805744443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97405853999437682407659257 73054390499578261805744443)
  ·
    refine ⟨109581585749367392708616665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73054390499578261805744443 109581585749367392708616665)
    ·
      refine ⟨82186189312025544531462499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109581585749367392708616665 82186189312025544531462499)
      ·
        refine ⟨123279283968038316797193749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82186189312025544531462499 123279283968038316797193749)
        ·
          refine ⟨5778716436001796099868457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123279283968038316797193749 5778716436001796099868457)
          ·
            refine ⟨4334037327001347074901343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778716436001796099868457 4334037327001347074901343)
            ·
              refine ⟨6501055990502020612352015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334037327001347074901343 6501055990502020612352015)
              ·
                refine ⟨9751583985753030918528023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501055990502020612352015 9751583985753030918528023)
                ·
                  refine ⟨14627375978629546377792035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9751583985753030918528023 14627375978629546377792035)
                  ·
                    refine ⟨21941063967944319566688053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14627375978629546377792035 21941063967944319566688053)
                    ·
                      refine ⟨2056974746994779959377005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21941063967944319566688053 2056974746994779959377005)
                      ·
                        rfl

theorem cell23_4005944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_4005944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005944 prefixEnd_4005944 := by exact prefixLift 4005944
  have htrace : WordTrace (prefixWord ++ tailWord_4005944) baseStart_4005944 baseEnd_4005944 := by
    simpa [prefixWord, tailWord_4005944, baseEnd_4005944] using wordTrace_append hprefix tailTrace_4005944
  have hstable : (prefixWord ++ tailWord_4005944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005944).length < 2 ^ (prefixWord ++ tailWord_4005944).sum := by decide
  have hdescent : baseEnd_4005944 < baseStart_4005944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005958 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4005958 : Nat := 118140960795 + 4005958 * 2 ^ 59
def prefixEnd_4005958 : Nat := 4983230072969 + 3 ^ 40 * 4005958 * 2
def baseEnd_4005958 : Nat := 2056981935723942904601941

theorem tailTrace_4005958 : CollatzResearch.WordTrace tailWord_4005958 prefixEnd_4005958 2056981935723942904601941 := by
  unfold tailWord_4005958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565915363159556375078079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97406194414070536001665685 4565915363159556375078079)
  ·
    refine ⟨6848873044739334562617119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4565915363159556375078079 6848873044739334562617119)
    ·
      refine ⟨10273309567109001843925679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6848873044739334562617119 10273309567109001843925679)
      ·
        refine ⟨15409964350663502765888519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10273309567109001843925679 15409964350663502765888519)
        ·
          refine ⟨23114946525995254148832779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15409964350663502765888519 23114946525995254148832779)
          ·
            refine ⟨34672419788992881223249169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23114946525995254148832779 34672419788992881223249169)
            ·
              refine ⟨26004314841744660917436877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34672419788992881223249169 26004314841744660917436877)
              ·
                refine ⟨9751618065654247844038829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26004314841744660917436877 9751618065654247844038829)
                ·
                  refine ⟨3656856774620342941514561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9751618065654247844038829 3656856774620342941514561)
                  ·
                    refine ⟨2742642580965257206135921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3656856774620342941514561 2742642580965257206135921)
                    ·
                      refine ⟨2056981935723942904601941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742642580965257206135921 2056981935723942904601941)
                      ·
                        rfl

theorem cell23_4005958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4005958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005958 prefixEnd_4005958 := by exact prefixLift 4005958
  have htrace : WordTrace (prefixWord ++ tailWord_4005958) baseStart_4005958 baseEnd_4005958 := by
    simpa [prefixWord, tailWord_4005958, baseEnd_4005958] using wordTrace_append hprefix tailTrace_4005958
  have hstable : (prefixWord ++ tailWord_4005958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005958).length < 2 ^ (prefixWord ++ tailWord_4005958).sum := by decide
  have hdescent : baseEnd_4005958 < baseStart_4005958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4005984 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 3, 3, 2]
def baseStart_4005984 : Nat := 118140960795 + 4005984 * 2 ^ 59
def prefixEnd_4005984 : Nat := 4983230072969 + 3 ^ 40 * 4005984 * 2
def baseEnd_4005984 : Nat := 2056995286220959802876821

theorem tailTrace_4005984 : CollatzResearch.WordTrace tailWord_4005984 prefixEnd_4005984 2056995286220959802876821 := by
  unfold tailWord_4005984
  simp only [CollatzResearch.WordTrace]
  refine ⟨73055119959505805221472503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97406826612674406961963337 73055119959505805221472503)
  ·
    refine ⟨109582679939258707832208755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73055119959505805221472503 109582679939258707832208755)
    ·
      refine ⟨164374019908888061748313133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109582679939258707832208755 164374019908888061748313133)
      ·
        refine ⟨61640257465833023155617425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164374019908888061748313133 61640257465833023155617425)
        ·
          refine ⟨46230193099374767366713069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61640257465833023155617425 46230193099374767366713069)
          ·
            refine ⟨17336322412265537762517401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46230193099374767366713069 17336322412265537762517401)
            ·
              refine ⟨13002241809199153321888051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17336322412265537762517401 13002241809199153321888051)
              ·
                refine ⟨19503362713798729982832077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13002241809199153321888051 19503362713798729982832077)
                ·
                  refine ⟨7313761017674523743562029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19503362713798729982832077 7313761017674523743562029)
                  ·
                    refine ⟨2742660381627946403835761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7313761017674523743562029 2742660381627946403835761)
                    ·
                      refine ⟨2056995286220959802876821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742660381627946403835761 2056995286220959802876821)
                      ·
                        rfl

theorem cell23_4005984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_4005984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4005984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4005984 prefixEnd_4005984 := by exact prefixLift 4005984
  have htrace : WordTrace (prefixWord ++ tailWord_4005984) baseStart_4005984 baseEnd_4005984 := by
    simpa [prefixWord, tailWord_4005984, baseEnd_4005984] using wordTrace_append hprefix tailTrace_4005984
  have hstable : (prefixWord ++ tailWord_4005984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4005984).length < 2 ^ (prefixWord ++ tailWord_4005984).sum := by decide
  have hdescent : baseEnd_4005984 < baseStart_4005984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4005984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006071 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 5]
def baseStart_4006071 : Nat := 118140960795 + 4006071 * 2 ^ 59
def prefixEnd_4006071 : Nat := 4983230072969 + 3 ^ 40 * 4006071 * 2
def baseEnd_4006071 : Nat := 228559995448655662498769

theorem tailTrace_4006071 : CollatzResearch.WordTrace tailWord_4006071 prefixEnd_4006071 228559995448655662498769 := by
  unfold tailWord_4006071
  simp only [CollatzResearch.WordTrace]
  refine ⟨146113413069696424301362067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97408942046464282867574711 146113413069696424301362067)
  ·
    refine ⟨219170119604544636452043101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146113413069696424301362067 219170119604544636452043101)
    ·
      refine ⟨82188794851704238669516163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219170119604544636452043101 82188794851704238669516163)
      ·
        refine ⟨123283192277556358004274245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82188794851704238669516163 123283192277556358004274245)
        ·
          refine ⟨23115598552041817125801421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123283192277556358004274245 23115598552041817125801421)
          ·
            refine ⟨8668349457015681422175533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23115598552041817125801421 8668349457015681422175533)
            ·
              refine ⟨3250631046380880533315825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8668349457015681422175533 3250631046380880533315825)
              ·
                refine ⟨2437973284785660399986869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250631046380880533315825 2437973284785660399986869)
                ·
                  refine ⟨228559995448655662498769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2437973284785660399986869 228559995448655662498769)
                  ·
                    rfl

theorem cell23_4006071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 5].length) (baseStart_4006071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006071 prefixEnd_4006071 := by exact prefixLift 4006071
  have htrace : WordTrace (prefixWord ++ tailWord_4006071) baseStart_4006071 baseEnd_4006071 := by
    simpa [prefixWord, tailWord_4006071, baseEnd_4006071] using wordTrace_append hprefix tailTrace_4006071
  have hstable : (prefixWord ++ tailWord_4006071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006071).length < 2 ^ (prefixWord ++ tailWord_4006071).sum := by decide
  have hdescent : baseEnd_4006071 < baseStart_4006071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006082 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4006082 : Nat := 118140960795 + 4006082 * 2 ^ 59
def prefixEnd_4006082 : Nat := 4983230072969 + 3 ^ 40 * 4006082 * 2
def baseEnd_4006082 : Nat := 2057045607325100419451371

theorem tailTrace_4006082 : CollatzResearch.WordTrace tailWord_4006082 prefixEnd_4006082 2057045607325100419451371 := by
  unfold tailWord_4006082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36528453568164143295003125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97409209515104382120008333 36528453568164143295003125)
  ·
    refine ⟨3424542522015388433906543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36528453568164143295003125 3424542522015388433906543)
    ·
      refine ⟨5136813783023082650859815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424542522015388433906543 5136813783023082650859815)
      ·
        refine ⟨7705220674534623976289723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5136813783023082650859815 7705220674534623976289723)
        ·
          refine ⟨11557831011801935964434585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705220674534623976289723 11557831011801935964434585)
          ·
            refine ⟨8668373258851451973325939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11557831011801935964434585 8668373258851451973325939)
            ·
              refine ⟨13002559888277177959988909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668373258851451973325939 13002559888277177959988909)
              ·
                refine ⟨4875959958103941734995841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13002559888277177959988909 4875959958103941734995841)
                ·
                  refine ⟨3656969968577956301246881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875959958103941734995841 3656969968577956301246881)
                  ·
                    refine ⟨2742727476433467225935161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3656969968577956301246881 2742727476433467225935161)
                    ·
                      refine ⟨2057045607325100419451371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742727476433467225935161 2057045607325100419451371)
                      ·
                        rfl

theorem cell23_4006082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4006082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006082 prefixEnd_4006082 := by exact prefixLift 4006082
  have htrace : WordTrace (prefixWord ++ tailWord_4006082) baseStart_4006082 baseEnd_4006082 := by
    simpa [prefixWord, tailWord_4006082, baseEnd_4006082] using wordTrace_append hprefix tailTrace_4006082
  have hstable : (prefixWord ++ tailWord_4006082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006082).length < 2 ^ (prefixWord ++ tailWord_4006082).sum := by decide
  have hdescent : baseEnd_4006082 < baseStart_4006082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006101 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_4006101 : Nat := 118140960795 + 4006101 * 2 ^ 59
def prefixEnd_4006101 : Nat := 4983230072969 + 3 ^ 40 * 4006101 * 2
def baseEnd_4006101 : Nat := 685685121152511948371261

theorem tailTrace_4006101 : CollatzResearch.WordTrace tailWord_4006101 prefixEnd_4006101 685685121152511948371261 := by
  unfold tailWord_4006101
  simp only [CollatzResearch.WordTrace]
  refine ⟨146114507259587739424954157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97409671506391826283302771 146114507259587739424954157)
  ·
    refine ⟨54792940222345402284357809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146114507259587739424954157 54792940222345402284357809)
    ·
      refine ⟨41094705166759051713268357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54792940222345402284357809 41094705166759051713268357)
      ·
        refine ⟨7705257218767322196237817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41094705166759051713268357 7705257218767322196237817)
        ·
          refine ⟨5778942914075491647178363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7705257218767322196237817 5778942914075491647178363)
          ·
            refine ⟨8668414371113237470767545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778942914075491647178363 8668414371113237470767545)
            ·
              refine ⟨6501310778334928103075659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8668414371113237470767545 6501310778334928103075659)
              ·
                refine ⟨9751966167502392154613489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501310778334928103075659 9751966167502392154613489)
                ·
                  refine ⟨7313974625626794115960117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9751966167502392154613489 7313974625626794115960117)
                  ·
                    refine ⟨685685121152511948371261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7313974625626794115960117 685685121152511948371261)
                    ·
                      rfl

theorem cell23_4006101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_4006101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006101 prefixEnd_4006101 := by exact prefixLift 4006101
  have htrace : WordTrace (prefixWord ++ tailWord_4006101) baseStart_4006101 baseEnd_4006101 := by
    simpa [prefixWord, tailWord_4006101, baseEnd_4006101] using wordTrace_append hprefix tailTrace_4006101
  have hstable : (prefixWord ++ tailWord_4006101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006101).length < 2 ^ (prefixWord ++ tailWord_4006101).sum := by decide
  have hdescent : baseEnd_4006101 < baseStart_4006101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006104 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_4006104 : Nat := 118140960795 + 4006104 * 2 ^ 59
def prefixEnd_4006104 : Nat := 4983230072969 + 3 ^ 40 * 4006104 * 2
def baseEnd_4006104 : Nat := 2057056903899499333376269

theorem tailTrace_4006104 : CollatzResearch.WordTrace tailWord_4006104 prefixEnd_4006104 2057056903899499333376269 := by
  unfold tailWord_4006104
  simp only [CollatzResearch.WordTrace]
  refine ⟨73057308339288435468656683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97409744452384580624875577 73057308339288435468656683)
  ·
    refine ⟨109585962508932653202985025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73057308339288435468656683 109585962508932653202985025)
    ·
      refine ⟨82189471881699489902238769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109585962508932653202985025 82189471881699489902238769)
      ·
        refine ⟨61642103911274617426679077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82189471881699489902238769 61642103911274617426679077)
        ·
          refine ⟨11557894483363990767502327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61642103911274617426679077 11557894483363990767502327)
          ·
            refine ⟨17336841725045986151253491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11557894483363990767502327 17336841725045986151253491)
            ·
              refine ⟨26005262587568979226880237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17336841725045986151253491 26005262587568979226880237)
              ·
                refine ⟨9751973470338367210080089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26005262587568979226880237 9751973470338367210080089)
                ·
                  refine ⟨7313980102753775407560067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9751973470338367210080089 7313980102753775407560067)
                  ·
                    refine ⟨10970970154130663111340101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7313980102753775407560067 10970970154130663111340101)
                    ·
                      refine ⟨2057056903899499333376269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10970970154130663111340101 2057056903899499333376269)
                      ·
                        rfl

theorem cell23_4006104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_4006104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006104 prefixEnd_4006104 := by exact prefixLift 4006104
  have htrace : WordTrace (prefixWord ++ tailWord_4006104) baseStart_4006104 baseEnd_4006104 := by
    simpa [prefixWord, tailWord_4006104, baseEnd_4006104] using wordTrace_append hprefix tailTrace_4006104
  have hstable : (prefixWord ++ tailWord_4006104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006104).length < 2 ^ (prefixWord ++ tailWord_4006104).sum := by decide
  have hdescent : baseEnd_4006104 < baseStart_4006104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006124 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_4006124 : Nat := 118140960795 + 4006124 * 2 ^ 59
def prefixEnd_4006124 : Nat := 4983230072969 + 3 ^ 40 * 4006124 * 2
def baseEnd_4006124 : Nat := 2057067173512589255126177

theorem tailTrace_4006124 : CollatzResearch.WordTrace tailWord_4006124 prefixEnd_4006124 2057067173512589255126177 := by
  unfold tailWord_4006124
  simp only [CollatzResearch.WordTrace]
  refine ⟨73057673069252207176520713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97410230759002942902027617 73057673069252207176520713)
  ·
    refine ⟨54793254801939155382390535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73057673069252207176520713 54793254801939155382390535)
    ·
      refine ⟨82189882202908733073585803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54793254801939155382390535 82189882202908733073585803)
      ·
        refine ⟨123284823304363099610378705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82189882202908733073585803 123284823304363099610378705)
        ·
          refine ⟨92463617478272324707784029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123284823304363099610378705 92463617478272324707784029)
          ·
            refine ⟨34673856554352121765419011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92463617478272324707784029 34673856554352121765419011)
            ·
              refine ⟨52010784831528182648128517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34673856554352121765419011 52010784831528182648128517)
              ·
                refine ⟨9752022155911534246524097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52010784831528182648128517 9752022155911534246524097)
                ·
                  refine ⟨7314016616933650684893073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9752022155911534246524097 7314016616933650684893073)
                  ·
                    refine ⟨5485512462700238013669805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7314016616933650684893073 5485512462700238013669805)
                    ·
                      refine ⟨2057067173512589255126177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5485512462700238013669805 2057067173512589255126177)
                      ·
                        rfl

theorem cell23_4006124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_4006124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006124 prefixEnd_4006124 := by exact prefixLift 4006124
  have htrace : WordTrace (prefixWord ++ tailWord_4006124) baseStart_4006124 baseEnd_4006124 := by
    simpa [prefixWord, tailWord_4006124, baseEnd_4006124] using wordTrace_append hprefix tailTrace_4006124
  have hstable : (prefixWord ++ tailWord_4006124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006124).length < 2 ^ (prefixWord ++ tailWord_4006124).sum := by decide
  have hdescent : baseEnd_4006124 < baseStart_4006124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006131 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 1, 4]
def baseStart_4006131 : Nat := 118140960795 + 4006131 * 2 ^ 59
def prefixEnd_4006131 : Nat := 4983230072969 + 3 ^ 40 * 4006131 * 2
def baseEnd_4006131 : Nat := 685690255959056909246215

theorem tailTrace_4006131 : CollatzResearch.WordTrace tailWord_4006131 prefixEnd_4006131 685690255959056909246215 := by
  unfold tailWord_4006131
  simp only [CollatzResearch.WordTrace]
  refine ⟨146115601449479054548546247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97410400966319369699030831 146115601449479054548546247)
  ·
    refine ⟨219173402174218581822819371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146115601449479054548546247 219173402174218581822819371)
    ·
      refine ⟨328760103261327872734229057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219173402174218581822819371 328760103261327872734229057)
      ·
        refine ⟨246570077445995904550671793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328760103261327872734229057 246570077445995904550671793)
        ·
          refine ⟨184927558084496928413003845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246570077445995904550671793 184927558084496928413003845)
          ·
            refine ⟨34673917140843174077438221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184927558084496928413003845 34673917140843174077438221)
            ·
              refine ⟨13002718927816190279039333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34673917140843174077438221 13002718927816190279039333)
              ·
                refine ⟨2438009798965535677319875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13002718927816190279039333 2438009798965535677319875)
                ·
                  refine ⟨3657014698448303515979813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438009798965535677319875 3657014698448303515979813)
                  ·
                    refine ⟨685690255959056909246215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657014698448303515979813 685690255959056909246215)
                    ·
                      rfl

theorem cell23_4006131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 4].length) (baseStart_4006131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006131 prefixEnd_4006131 := by exact prefixLift 4006131
  have htrace : WordTrace (prefixWord ++ tailWord_4006131) baseStart_4006131 baseEnd_4006131 := by
    simpa [prefixWord, tailWord_4006131, baseEnd_4006131] using wordTrace_append hprefix tailTrace_4006131
  have hstable : (prefixWord ++ tailWord_4006131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006131).length < 2 ^ (prefixWord ++ tailWord_4006131).sum := by decide
  have hdescent : baseEnd_4006131 < baseStart_4006131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006188 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 1, 1, 3]
def baseStart_4006188 : Nat := 118140960795 + 4006188 * 2 ^ 59
def prefixEnd_4006188 : Nat := 4983230072969 + 3 ^ 40 * 4006188 * 2
def baseEnd_4006188 : Nat := 2057100036274477004725883

theorem tailTrace_4006188 : CollatzResearch.WordTrace tailWord_4006188 prefixEnd_4006188 2057100036274477004725883 := by
  unfold tailWord_4006188
  simp only [CollatzResearch.WordTrace]
  refine ⟨73058840205136276641685609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97411786940181702188914145 73058840205136276641685609)
  ·
    refine ⟨54794130153852207481264207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73058840205136276641685609 54794130153852207481264207)
    ·
      refine ⟨82191195230778311221896311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54794130153852207481264207 82191195230778311221896311)
      ·
        refine ⟨123286792846167466832844467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82191195230778311221896311 123286792846167466832844467)
        ·
          refine ⟨184930189269251200249266701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123286792846167466832844467 184930189269251200249266701)
          ·
            refine ⟨69348820975969200093475013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184930189269251200249266701 69348820975969200093475013)
            ·
              refine ⟨13002903932994225017526565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69348820975969200093475013 13002903932994225017526565)
              ·
                refine ⟨2438044487436417190786231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13002903932994225017526565 2438044487436417190786231)
                ·
                  refine ⟨3657066731154625786179347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438044487436417190786231 3657066731154625786179347)
                  ·
                    refine ⟨5485600096731938679269021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3657066731154625786179347 5485600096731938679269021)
                    ·
                      refine ⟨2057100036274477004725883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5485600096731938679269021 2057100036274477004725883)
                      ·
                        rfl

theorem cell23_4006188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_4006188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006188 prefixEnd_4006188 := by exact prefixLift 4006188
  have htrace : WordTrace (prefixWord ++ tailWord_4006188) baseStart_4006188 baseEnd_4006188 := by
    simpa [prefixWord, tailWord_4006188, baseEnd_4006188] using wordTrace_append hprefix tailTrace_4006188
  have hstable : (prefixWord ++ tailWord_4006188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006188).length < 2 ^ (prefixWord ++ tailWord_4006188).sum := by decide
  have hdescent : baseEnd_4006188 < baseStart_4006188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006231 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_4006231 : Nat := 118140960795 + 4006231 * 2 ^ 59
def prefixEnd_4006231 : Nat := 4983230072969 + 3 ^ 40 * 4006231 * 2
def baseEnd_4006231 : Nat := 2057122115942620336488185

theorem tailTrace_4006231 : CollatzResearch.WordTrace tailWord_4006231 prefixEnd_4006231 2057122115942620336488185 := by
  unfold tailWord_4006231
  simp only [CollatzResearch.WordTrace]
  refine ⟨146119248749116771627186547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97412832499411181084791031 146119248749116771627186547)
  ·
    refine ⟨219178873123675157440779821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146119248749116771627186547 219178873123675157440779821)
    ·
      refine ⟨82192077421378184040292433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219178873123675157440779821 82192077421378184040292433)
      ·
        refine ⟨61644058066033638030219325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82192077421378184040292433 61644058066033638030219325)
        ·
          refine ⟨23116521774762614261332247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61644058066033638030219325 23116521774762614261332247)
          ·
            refine ⟨34674782662143921391998371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23116521774762614261332247 34674782662143921391998371)
            ·
              refine ⟨52012173993215882087997557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34674782662143921391998371 52012173993215882087997557)
              ·
                refine ⟨4876141311863988945749771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52012173993215882087997557 4876141311863988945749771)
                ·
                  refine ⟨7314211967795983418624657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876141311863988945749771 7314211967795983418624657)
                  ·
                    refine ⟨5485658975846987563968493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7314211967795983418624657 5485658975846987563968493)
                    ·
                      refine ⟨2057122115942620336488185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5485658975846987563968493 2057122115942620336488185)
                      ·
                        rfl

theorem cell23_4006231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_4006231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006231 prefixEnd_4006231 := by exact prefixLift 4006231
  have htrace : WordTrace (prefixWord ++ tailWord_4006231) baseStart_4006231 baseEnd_4006231 := by
    simpa [prefixWord, tailWord_4006231, baseEnd_4006231] using wordTrace_append hprefix tailTrace_4006231
  have hstable : (prefixWord ++ tailWord_4006231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006231).length < 2 ^ (prefixWord ++ tailWord_4006231).sum := by decide
  have hdescent : baseEnd_4006231 < baseStart_4006231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006245 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 3, 2, 2]
def baseStart_4006245 : Nat := 118140960795 + 4006245 * 2 ^ 59
def prefixEnd_4006245 : Nat := 4983230072969 + 3 ^ 40 * 4006245 * 2
def baseEnd_4006245 : Nat := 2057129304671783281713121

theorem tailTrace_4006245 : CollatzResearch.WordTrace tailWord_4006245 prefixEnd_4006245 2057129304671783281713121 := by
  unfold tailWord_4006245
  simp only [CollatzResearch.WordTrace]
  refine ⟨146119759371066052018196189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97413172914044034678797459 146119759371066052018196189)
  ·
    refine ⟨54794909764149769506823571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146119759371066052018196189 54794909764149769506823571)
    ·
      refine ⟨82192364646224654260235357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54794909764149769506823571 82192364646224654260235357)
      ·
        refine ⟨30822136742334245347588259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82192364646224654260235357 30822136742334245347588259)
        ·
          refine ⟨46233205113501368021382389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30822136742334245347588259 46233205113501368021382389)
          ·
            refine ⟨4334362979390753252004599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46233205113501368021382389 4334362979390753252004599)
            ·
              refine ⟨6501544469086129878006899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334362979390753252004599 6501544469086129878006899)
              ·
                refine ⟨9752316703629194817010349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501544469086129878006899 9752316703629194817010349)
                ·
                  refine ⟨3657118763860948056378881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9752316703629194817010349 3657118763860948056378881)
                  ·
                    refine ⟨2742839072895711042284161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657118763860948056378881 2742839072895711042284161)
                    ·
                      refine ⟨2057129304671783281713121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742839072895711042284161 2057129304671783281713121)
                      ·
                        rfl

theorem cell23_4006245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_4006245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006245 prefixEnd_4006245 := by exact prefixLift 4006245
  have htrace : WordTrace (prefixWord ++ tailWord_4006245) baseStart_4006245 baseEnd_4006245 := by
    simpa [prefixWord, tailWord_4006245, baseEnd_4006245] using wordTrace_append hprefix tailTrace_4006245
  have hstable : (prefixWord ++ tailWord_4006245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006245).length < 2 ^ (prefixWord ++ tailWord_4006245).sum := by decide
  have hdescent : baseEnd_4006245 < baseStart_4006245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006262 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4006262 : Nat := 118140960795 + 4006262 * 2 ^ 59
def prefixEnd_4006262 : Nat := 4983230072969 + 3 ^ 40 * 4006262 * 2
def baseEnd_4006262 : Nat := 2057138033842909715200543

theorem tailTrace_4006262 : CollatzResearch.WordTrace tailWord_4006262 prefixEnd_4006262 2057138033842909715200543 := by
  unfold tailWord_4006262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132523713250278995097815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97413586274669642614376693 9132523713250278995097815)
  ·
    refine ⟨13698785569875418492646723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9132523713250278995097815 13698785569875418492646723)
    ·
      refine ⟨20548178354813127738970085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13698785569875418492646723 20548178354813127738970085)
      ·
        refine ⟨3852783441527461451056891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20548178354813127738970085 3852783441527461451056891)
        ·
          refine ⟨5779175162291192176585337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852783441527461451056891 5779175162291192176585337)
          ·
            refine ⟨4334381371718394132439003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779175162291192176585337 4334381371718394132439003)
            ·
              refine ⟨6501572057577591198658505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334381371718394132439003 6501572057577591198658505)
              ·
                refine ⟨4876179043183193398993879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501572057577591198658505 4876179043183193398993879)
                ·
                  refine ⟨7314268564774790098490819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876179043183193398993879 7314268564774790098490819)
                  ·
                    refine ⟨10971402847162185147736229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7314268564774790098490819 10971402847162185147736229)
                    ·
                      refine ⟨2057138033842909715200543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10971402847162185147736229 2057138033842909715200543)
                      ·
                        rfl

theorem cell23_4006262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4006262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006262 prefixEnd_4006262 := by exact prefixLift 4006262
  have htrace : WordTrace (prefixWord ++ tailWord_4006262) baseStart_4006262 baseEnd_4006262 := by
    simpa [prefixWord, tailWord_4006262, baseEnd_4006262] using wordTrace_append hprefix tailTrace_4006262
  have hstable : (prefixWord ++ tailWord_4006262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006262).length < 2 ^ (prefixWord ++ tailWord_4006262).sum := by decide
  have hdescent : baseEnd_4006262 < baseStart_4006262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006271 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 3, 3, 2]
def baseStart_4006271 : Nat := 118140960795 + 4006271 * 2 ^ 59
def prefixEnd_4006271 : Nat := 4983230072969 + 3 ^ 40 * 4006271 * 2
def baseEnd_4006271 : Nat := 2057142655168800179988001

theorem tailTrace_4006271 : CollatzResearch.WordTrace tailWord_4006271 prefixEnd_4006271 2057142655168800179988001 := by
  unfold tailWord_4006271
  simp only [CollatzResearch.WordTrace]
  refine ⟨146120707668971858458642667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97413805112647905639095111 146120707668971858458642667)
  ·
    refine ⟨219181061503457787687964001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146120707668971858458642667 219181061503457787687964001)
    ·
      refine ⟨164385796127593340765973001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219181061503457787687964001 164385796127593340765973001)
      ·
        refine ⟨123289347095695005574479751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164385796127593340765973001 123289347095695005574479751)
        ·
          refine ⟨184934020643542508361719627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123289347095695005574479751 184934020643542508361719627)
          ·
            refine ⟨277401030965313762542579441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184934020643542508361719627 277401030965313762542579441)
            ·
              refine ⟨208050773223985321906934581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277401030965313762542579441 208050773223985321906934581)
              ·
                refine ⟨19504759989748623928775117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208050773223985321906934581 19504759989748623928775117)
                ·
                  refine ⟨7314284996155733973290669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19504759989748623928775117 7314284996155733973290669)
                  ·
                    refine ⟨2742856873558400239984001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7314284996155733973290669 2742856873558400239984001)
                    ·
                      refine ⟨2057142655168800179988001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2742856873558400239984001 2057142655168800179988001)
                      ·
                        rfl

theorem cell23_4006271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_4006271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006271 prefixEnd_4006271 := by exact prefixLift 4006271
  have htrace : WordTrace (prefixWord ++ tailWord_4006271) baseStart_4006271 baseEnd_4006271 := by
    simpa [prefixWord, tailWord_4006271, baseEnd_4006271] using wordTrace_append hprefix tailTrace_4006271
  have hstable : (prefixWord ++ tailWord_4006271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006271).length < 2 ^ (prefixWord ++ tailWord_4006271).sum := by decide
  have hdescent : baseEnd_4006271 < baseStart_4006271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006282 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4006282 : Nat := 118140960795 + 4006282 * 2 ^ 59
def prefixEnd_4006282 : Nat := 4983230072969 + 3 ^ 40 * 4006282 * 2
def baseEnd_4006282 : Nat := 2057148303455999636950451

theorem tailTrace_4006282 : CollatzResearch.WordTrace tailWord_4006282 prefixEnd_4006282 2057148303455999636950451 := by
  unfold tailWord_4006282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36530277217983001834323275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97414072581288004891528733 36530277217983001834323275)
  ·
    refine ⟨54795415826974502751484913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36530277217983001834323275 54795415826974502751484913)
    ·
      refine ⟨41096561870230877063613685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54795415826974502751484913 41096561870230877063613685)
      ·
        refine ⟨3852802675334144724713783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41096561870230877063613685 3852802675334144724713783)
        ·
          refine ⟨5779204013001217087070675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852802675334144724713783 5779204013001217087070675)
          ·
            refine ⟨8668806019501825630606013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779204013001217087070675 8668806019501825630606013)
            ·
              refine ⟨3250802257313184611477255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8668806019501825630606013 3250802257313184611477255)
              ·
                refine ⟨4876203385969776917215883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250802257313184611477255 4876203385969776917215883)
                ·
                  refine ⟨7314305078954665375823825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876203385969776917215883 7314305078954665375823825)
                  ·
                    refine ⟨5485728809215999031867869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7314305078954665375823825 5485728809215999031867869)
                    ·
                      refine ⟨2057148303455999636950451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5485728809215999031867869 2057148303455999636950451)
                      ·
                        rfl

theorem cell23_4006282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4006282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006282 prefixEnd_4006282 := by exact prefixLift 4006282
  have htrace : WordTrace (prefixWord ++ tailWord_4006282) baseStart_4006282 baseEnd_4006282 := by
    simpa [prefixWord, tailWord_4006282, baseEnd_4006282] using wordTrace_append hprefix tailTrace_4006282
  have hstable : (prefixWord ++ tailWord_4006282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006282).length < 2 ^ (prefixWord ++ tailWord_4006282).sum := by decide
  have hdescent : baseEnd_4006282 < baseStart_4006282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006311 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 2, 6]
def baseStart_4006311 : Nat := 118140960795 + 4006311 * 2 ^ 59
def prefixEnd_4006311 : Nat := 4983230072969 + 3 ^ 40 * 4006311 * 2
def baseEnd_4006311 : Nat := 685721064798326674495939

theorem tailTrace_4006311 : CollatzResearch.WordTrace tailWord_4006311 prefixEnd_4006311 685721064798326674495939 := by
  unfold tailWord_4006311
  simp only [CollatzResearch.WordTrace]
  refine ⟨146122166588826945290098787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97414777725884630193399191 146122166588826945290098787)
  ·
    refine ⟨219183249883240417935148181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146122166588826945290098787 219183249883240417935148181)
    ·
      refine ⟨10274214838276894590710071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219183249883240417935148181 10274214838276894590710071)
      ·
        refine ⟨15411322257415341886065107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10274214838276894590710071 15411322257415341886065107)
        ·
          refine ⟨23116983386123012829097661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15411322257415341886065107 23116983386123012829097661)
          ·
            refine ⟨8668868769796129810911623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23116983386123012829097661 8668868769796129810911623)
            ·
              refine ⟨13003303154694194716367435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668868769796129810911623 13003303154694194716367435)
              ·
                refine ⟨19504954732041292074551153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13003303154694194716367435 19504954732041292074551153)
                ·
                  refine ⟨14628716049030969055913365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19504954732041292074551153 14628716049030969055913365)
                  ·
                    refine ⟨685721064798326674495939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14628716049030969055913365 685721064798326674495939)
                    ·
                      rfl

theorem cell23_4006311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_4006311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006311 prefixEnd_4006311 := by exact prefixLift 4006311
  have htrace : WordTrace (prefixWord ++ tailWord_4006311) baseStart_4006311 baseEnd_4006311 := by
    simpa [prefixWord, tailWord_4006311, baseEnd_4006311] using wordTrace_append hprefix tailTrace_4006311
  have hstable : (prefixWord ++ tailWord_4006311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006311).length < 2 ^ (prefixWord ++ tailWord_4006311).sum := by decide
  have hdescent : baseEnd_4006311 < baseStart_4006311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006358 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_4006358 : Nat := 118140960795 + 4006358 * 2 ^ 59
def prefixEnd_4006358 : Nat := 4983230072969 + 3 ^ 40 * 4006358 * 2
def baseEnd_4006358 : Nat := 228576369776193482177789

theorem tailTrace_4006358 : CollatzResearch.WordTrace tailWord_4006358 prefixEnd_4006358 228576369776193482177789 := by
  unfold tailWord_4006358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132742551228542019816233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97415920546437781544706485 9132742551228542019816233)
  ·
    refine ⟨6849556913421406514862175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9132742551228542019816233 6849556913421406514862175)
    ·
      refine ⟨10274335370132109772293263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6849556913421406514862175 10274335370132109772293263)
      ·
        refine ⟨15411503055198164658439895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10274335370132109772293263 15411503055198164658439895)
        ·
          refine ⟨23117254582797246987659843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15411503055198164658439895 23117254582797246987659843)
          ·
            refine ⟨34675881874195870481489765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23117254582797246987659843 34675881874195870481489765)
            ·
              refine ⟨6501727851411725715279331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34675881874195870481489765 6501727851411725715279331)
              ·
                refine ⟨9752591777117588572918997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501727851411725715279331 9752591777117588572918997)
                ·
                  refine ⟨228576369776193482177789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9752591777117588572918997 228576369776193482177789)
                  ·
                    rfl

theorem cell23_4006358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_4006358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006358 prefixEnd_4006358 := by exact prefixLift 4006358
  have htrace : WordTrace (prefixWord ++ tailWord_4006358) baseStart_4006358 baseEnd_4006358 := by
    simpa [prefixWord, tailWord_4006358, baseEnd_4006358] using wordTrace_append hprefix tailTrace_4006358
  have hstable : (prefixWord ++ tailWord_4006358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006358).length < 2 ^ (prefixWord ++ tailWord_4006358).sum := by decide
  have hdescent : baseEnd_4006358 < baseStart_4006358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006384 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_4006384 : Nat := 118140960795 + 4006384 * 2 ^ 59
def prefixEnd_4006384 : Nat := 4983230072969 + 3 ^ 40 * 4006384 * 2
def baseEnd_4006384 : Nat := 685733559494252745958327

theorem tailTrace_4006384 : CollatzResearch.WordTrace tailWord_4006384 prefixEnd_4006384 685733559494252745958327 := by
  unfold tailWord_4006384
  simp only [CollatzResearch.WordTrace]
  refine ⟨73062414558781239378753103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97416552745041652505004137 73062414558781239378753103)
  ·
    refine ⟨109593621838171859068129655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73062414558781239378753103 109593621838171859068129655)
    ·
      refine ⟨164390432757257788602194483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109593621838171859068129655 164390432757257788602194483)
      ·
        refine ⟨246585649135886682903291725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164390432757257788602194483 246585649135886682903291725)
        ·
          refine ⟨92469618425957506088734397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246585649135886682903291725 92469618425957506088734397)
          ·
            refine ⟨34676106909734064783275399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92469618425957506088734397 34676106909734064783275399)
            ·
              refine ⟨52014160364601097174913099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34676106909734064783275399 52014160364601097174913099)
              ·
                refine ⟨78021240546901645762369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52014160364601097174913099 78021240546901645762369649)
                ·
                  refine ⟨58515930410176234321777237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78021240546901645762369649 58515930410176234321777237)
                  ·
                    refine ⟨685733559494252745958327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58515930410176234321777237 685733559494252745958327)
                    ·
                      rfl

theorem cell23_4006384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_4006384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006384 prefixEnd_4006384 := by exact prefixLift 4006384
  have htrace : WordTrace (prefixWord ++ tailWord_4006384) baseStart_4006384 baseEnd_4006384 := by
    simpa [prefixWord, tailWord_4006384, baseEnd_4006384] using wordTrace_append hprefix tailTrace_4006384
  have hstable : (prefixWord ++ tailWord_4006384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006384).length < 2 ^ (prefixWord ++ tailWord_4006384).sum := by decide
  have hdescent : baseEnd_4006384 < baseStart_4006384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006492 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_4006492 : Nat := 118140960795 + 4006492 * 2 ^ 59
def prefixEnd_4006492 : Nat := 4983230072969 + 3 ^ 40 * 4006492 * 2
def baseEnd_4006492 : Nat := 2057256134393443815324485

theorem tailTrace_4006492 : CollatzResearch.WordTrace tailWord_4006492 prefixEnd_4006492 2057256134393443815324485 := by
  unfold tailWord_4006492
  simp only [CollatzResearch.WordTrace]
  refine ⟨73064384100585606601218865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97419178800780808801625153 73064384100585606601218865)
  ·
    refine ⟨54798288075439204950914149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73064384100585606601218865 54798288075439204950914149)
    ·
      refine ⟨10274679014144850928296403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54798288075439204950914149 10274679014144850928296403)
      ·
        refine ⟨15412018521217276392444605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10274679014144850928296403 15412018521217276392444605)
        ·
          refine ⟨5779506945456478647166727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15412018521217276392444605 5779506945456478647166727)
          ·
            refine ⟨8669260418184717970750091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779506945456478647166727 8669260418184717970750091)
            ·
              refine ⟨13003890627277076956125137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669260418184717970750091 13003890627277076956125137)
              ·
                refine ⟨9752917970457807717093853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13003890627277076956125137 9752917970457807717093853)
                ·
                  refine ⟨3657344238921677893910195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9752917970457807717093853 3657344238921677893910195)
                  ·
                    refine ⟨5486016358382516840865293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3657344238921677893910195 5486016358382516840865293)
                    ·
                      refine ⟨2057256134393443815324485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5486016358382516840865293 2057256134393443815324485)
                      ·
                        rfl

theorem cell23_4006492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_4006492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006492 prefixEnd_4006492 := by exact prefixLift 4006492
  have htrace : WordTrace (prefixWord ++ tailWord_4006492) baseStart_4006492 baseEnd_4006492 := by
    simpa [prefixWord, tailWord_4006492, baseEnd_4006492] using wordTrace_append hprefix tailTrace_4006492
  have hstable : (prefixWord ++ tailWord_4006492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006492).length < 2 ^ (prefixWord ++ tailWord_4006492).sum := by decide
  have hdescent : baseEnd_4006492 < baseStart_4006492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006509 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4006509 : Nat := 118140960795 + 4006509 * 2 ^ 59
def prefixEnd_4006509 : Nat := 4983230072969 + 3 ^ 40 * 4006509 * 2
def baseEnd_4006509 : Nat := 2057264863564570248811907

theorem tailTrace_4006509 : CollatzResearch.WordTrace tailWord_4006509 prefixEnd_4006509 2057264863564570248811907 := by
  unfold tailWord_4006509
  simp only [CollatzResearch.WordTrace]
  refine ⟨146129388242109625105806581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97419592161406416737204387 146129388242109625105806581)
  ·
    refine ⟨13699630147697777353669367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146129388242109625105806581 13699630147697777353669367)
    ·
      refine ⟨20549445221546666030504051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699630147697777353669367 20549445221546666030504051)
      ·
        refine ⟨30824167832319999045756077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20549445221546666030504051 30824167832319999045756077)
        ·
          refine ⟨11559062937119999642158529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30824167832319999045756077 11559062937119999642158529)
          ·
            refine ⟨8669297202839999731618897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11559062937119999642158529 8669297202839999731618897)
            ·
              refine ⟨6501972902129999798714173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8669297202839999731618897 6501972902129999798714173)
              ·
                refine ⟨2438239838298749924517815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6501972902129999798714173 2438239838298749924517815)
                ·
                  refine ⟨3657359757448124886776723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438239838298749924517815 3657359757448124886776723)
                  ·
                    refine ⟨5486039636172187330165085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3657359757448124886776723 5486039636172187330165085)
                    ·
                      refine ⟨2057264863564570248811907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5486039636172187330165085 2057264863564570248811907)
                      ·
                        rfl

theorem cell23_4006509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4006509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006509 prefixEnd_4006509 := by exact prefixLift 4006509
  have htrace : WordTrace (prefixWord ++ tailWord_4006509) baseStart_4006509 baseEnd_4006509 := by
    simpa [prefixWord, tailWord_4006509, baseEnd_4006509] using wordTrace_append hprefix tailTrace_4006509
  have hstable : (prefixWord ++ tailWord_4006509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006509).length < 2 ^ (prefixWord ++ tailWord_4006509).sum := by decide
  have hdescent : baseEnd_4006509 < baseStart_4006509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006512 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 1, 5]
def baseStart_4006512 : Nat := 118140960795 + 4006512 * 2 ^ 59
def prefixEnd_4006512 : Nat := 4983230072969 + 3 ^ 40 * 4006512 * 2
def baseEnd_4006512 : Nat := 685755468002177912358131

theorem tailTrace_4006512 : CollatzResearch.WordTrace tailWord_4006512 prefixEnd_4006512 685755468002177912358131 := by
  unfold tailWord_4006512
  simp only [CollatzResearch.WordTrace]
  refine ⟨73064748830549378309082895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97419665107399171078777193 73064748830549378309082895)
  ·
    refine ⟨109597123245824067463624343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73064748830549378309082895 109597123245824067463624343)
    ·
      refine ⟨164395684868736101195436515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109597123245824067463624343 164395684868736101195436515)
      ·
        refine ⟨246593527303104151793154773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164395684868736101195436515 246593527303104151793154773)
        ·
          refine ⟨5779535796166503557652065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 246593527303104151793154773 5779535796166503557652065)
          ·
            refine ⟨4334651847124877668239049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779535796166503557652065 4334651847124877668239049)
            ·
              refine ⟨3250988885343658251179287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334651847124877668239049 3250988885343658251179287)
              ·
                refine ⟨4876483328015487376768931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250988885343658251179287 4876483328015487376768931)
                ·
                  refine ⟨7314724992023231065153397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876483328015487376768931 7314724992023231065153397)
                  ·
                    refine ⟨685755468002177912358131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7314724992023231065153397 685755468002177912358131)
                    ·
                      rfl

theorem cell23_4006512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 5].length) (baseStart_4006512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006512 prefixEnd_4006512 := by exact prefixLift 4006512
  have htrace : WordTrace (prefixWord ++ tailWord_4006512) baseStart_4006512 baseEnd_4006512 := by
    simpa [prefixWord, tailWord_4006512, baseEnd_4006512] using wordTrace_append hprefix tailTrace_4006512
  have hstable : (prefixWord ++ tailWord_4006512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006512).length < 2 ^ (prefixWord ++ tailWord_4006512).sum := by decide
  have hdescent : baseEnd_4006512 < baseStart_4006512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006521 : List Nat := [1, 2, 1, 3, 3, 3, 10]
def baseStart_4006521 : Nat := 118140960795 + 4006521 * 2 ^ 59
def prefixEnd_4006521 : Nat := 4983230072969 + 3 ^ 40 * 4006521 * 2
def baseEnd_4006521 : Nat := 25398407720153385208171

theorem tailTrace_4006521 : CollatzResearch.WordTrace tailWord_4006521 prefixEnd_4006521 25398407720153385208171 := by
  unfold tailWord_4006521
  simp only [CollatzResearch.WordTrace]
  refine ⟨146129825918066151155243417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97419883945377434103495611 146129825918066151155243417)
  ·
    refine ⟨109597369438549613366432563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146129825918066151155243417 109597369438549613366432563)
    ·
      refine ⟨164396054157824420049648845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109597369438549613366432563 164396054157824420049648845)
      ·
        refine ⟨61648520309184157518618317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164396054157824420049648845 61648520309184157518618317)
        ·
          refine ⟨23118195115944059069481869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61648520309184157518618317 23118195115944059069481869)
          ·
            refine ⟨8669323168479022151055701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23118195115944059069481869 8669323168479022151055701)
            ·
              refine ⟨25398407720153385208171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8669323168479022151055701 25398407720153385208171)
              ·
                rfl

theorem cell23_4006521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 10].length) (baseStart_4006521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006521 prefixEnd_4006521 := by exact prefixLift 4006521
  have htrace : WordTrace (prefixWord ++ tailWord_4006521) baseStart_4006521 baseEnd_4006521 := by
    simpa [prefixWord, tailWord_4006521, baseEnd_4006521] using wordTrace_append hprefix tailTrace_4006521
  have hstable : (prefixWord ++ tailWord_4006521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006521).length < 2 ^ (prefixWord ++ tailWord_4006521).sum := by decide
  have hdescent : baseEnd_4006521 < baseStart_4006521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006525 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_4006525 : Nat := 118140960795 + 4006525 * 2 ^ 59
def prefixEnd_4006525 : Nat := 4983230072969 + 3 ^ 40 * 4006525 * 2
def baseEnd_4006525 : Nat := 685757693085014062070611

theorem tailTrace_4006525 : CollatzResearch.WordTrace tailWord_4006525 prefixEnd_4006525 685757693085014062070611 := by
  unfold tailWord_4006525
  simp only [CollatzResearch.WordTrace]
  refine ⟨146129971810051659838389029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97419981206701106558926019 146129971810051659838389029)
  ·
    refine ⟨27399369714384686219697943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146129971810051659838389029 27399369714384686219697943)
    ·
      refine ⟨41099054571577029329546915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27399369714384686219697943 41099054571577029329546915)
      ·
        refine ⟨61648581857365543994320373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41099054571577029329546915 61648581857365543994320373)
        ·
          refine ⟨5779554549128019749467535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61648581857365543994320373 5779554549128019749467535)
          ·
            refine ⟨8669331823692029624201303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779554549128019749467535 8669331823692029624201303)
            ·
              refine ⟨13003997735538044436301955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669331823692029624201303 13003997735538044436301955)
              ·
                refine ⟨19505996603307066654452933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13003997735538044436301955 19505996603307066654452933)
                ·
                  refine ⟨3657374363120074997709925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19505996603307066654452933 3657374363120074997709925)
                  ·
                    refine ⟨685757693085014062070611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657374363120074997709925 685757693085014062070611)
                    ·
                      rfl

theorem cell23_4006525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_4006525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006525 prefixEnd_4006525 := by exact prefixLift 4006525
  have htrace : WordTrace (prefixWord ++ tailWord_4006525) baseStart_4006525 baseEnd_4006525 := by
    simpa [prefixWord, tailWord_4006525, baseEnd_4006525] using wordTrace_append hprefix tailTrace_4006525
  have hstable : (prefixWord ++ tailWord_4006525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006525).length < 2 ^ (prefixWord ++ tailWord_4006525).sum := by decide
  have hdescent : baseEnd_4006525 < baseStart_4006525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006532 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_4006532 : Nat := 118140960795 + 4006532 * 2 ^ 59
def prefixEnd_4006532 : Nat := 4983230072969 + 3 ^ 40 * 4006532 * 2
def baseEnd_4006532 : Nat := 2057276673619623658824301

theorem tailTrace_4006532 : CollatzResearch.WordTrace tailWord_4006532 prefixEnd_4006532 2057276673619623658824301 := by
  unfold tailWord_4006532
  simp only [CollatzResearch.WordTrace]
  refine ⟨73065113560513150016946925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97420151414017533355929233 73065113560513150016946925)
  ·
    refine ⟨27399417585192431256355097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73065113560513150016946925 27399417585192431256355097)
    ·
      refine ⟨20549563188894323442266323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27399417585192431256355097 20549563188894323442266323)
      ·
        refine ⟨30824344783341485163399485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20549563188894323442266323 30824344783341485163399485)
        ·
          refine ⟨11559129293753056936274807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30824344783341485163399485 11559129293753056936274807)
          ·
            refine ⟨17338693940629585404412211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11559129293753056936274807 17338693940629585404412211)
            ·
              refine ⟨26008040910944378106618317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17338693940629585404412211 26008040910944378106618317)
              ·
                refine ⟨9753015341604141789981869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26008040910944378106618317 9753015341604141789981869)
                ·
                  refine ⟨3657380753101553171243201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9753015341604141789981869 3657380753101553171243201)
                  ·
                    refine ⟨2743035564826164878432401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657380753101553171243201 2743035564826164878432401)
                    ·
                      refine ⟨2057276673619623658824301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743035564826164878432401 2057276673619623658824301)
                      ·
                        rfl

theorem cell23_4006532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_4006532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006532 prefixEnd_4006532 := by exact prefixLift 4006532
  have htrace : WordTrace (prefixWord ++ tailWord_4006532) baseStart_4006532 baseEnd_4006532 := by
    simpa [prefixWord, tailWord_4006532, baseEnd_4006532] using wordTrace_append hprefix tailTrace_4006532
  have hstable : (prefixWord ++ tailWord_4006532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006532).length < 2 ^ (prefixWord ++ tailWord_4006532).sum := by decide
  have hdescent : baseEnd_4006532 < baseStart_4006532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006542 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_4006542 : Nat := 118140960795 + 4006542 * 2 ^ 59
def prefixEnd_4006542 : Nat := 4983230072969 + 3 ^ 40 * 4006542 * 2
def baseEnd_4006542 : Nat := 685760602808722873233085

theorem tailTrace_4006542 : CollatzResearch.WordTrace tailWord_4006542 prefixEnd_4006542 685760602808722873233085 := by
  unfold tailWord_4006542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18266323981373758967719735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97420394567326714494505253 18266323981373758967719735)
  ·
    refine ⟨27399485972060638451579603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18266323981373758967719735 27399485972060638451579603)
    ·
      refine ⟨41099228958090957677369405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27399485972060638451579603 41099228958090957677369405)
      ·
        refine ⟨15412210859284109129013527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41099228958090957677369405 15412210859284109129013527)
        ·
          refine ⟨23118316288926163693520291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15412210859284109129013527 23118316288926163693520291)
          ·
            refine ⟨34677474433389245540280437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23118316288926163693520291 34677474433389245540280437)
            ·
              refine ⟨3251013228130241769401291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34677474433389245540280437 3251013228130241769401291)
              ·
                refine ⟨4876519842195362654101937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251013228130241769401291 4876519842195362654101937)
                ·
                  refine ⟨3657389881646521990576453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876519842195362654101937 3657389881646521990576453)
                  ·
                    refine ⟨685760602808722873233085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657389881646521990576453 685760602808722873233085)
                    ·
                      rfl

theorem cell23_4006542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_4006542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006542 prefixEnd_4006542 := by exact prefixLift 4006542
  have htrace : WordTrace (prefixWord ++ tailWord_4006542) baseStart_4006542 baseEnd_4006542 := by
    simpa [prefixWord, tailWord_4006542, baseEnd_4006542] using wordTrace_append hprefix tailTrace_4006542
  have hstable : (prefixWord ++ tailWord_4006542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006542).length < 2 ^ (prefixWord ++ tailWord_4006542).sum := by decide
  have hdescent : baseEnd_4006542 < baseStart_4006542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006588 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4006588 : Nat := 118140960795 + 4006588 * 2 ^ 59
def prefixEnd_4006588 : Nat := 4983230072969 + 3 ^ 40 * 4006588 * 2
def baseEnd_4006588 : Nat := 2057305428536275439724043

theorem tailTrace_4006588 : CollatzResearch.WordTrace tailWord_4006588 prefixEnd_4006588 2057305428536275439724043 := by
  unfold tailWord_4006588
  simp only [CollatzResearch.WordTrace]
  refine ⟨73066134804411710798966209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97421513072548947731954945 73066134804411710798966209)
  ·
    refine ⟨54799601103308783099224657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73066134804411710798966209 54799601103308783099224657)
    ·
      refine ⟨41099700827481587324418493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54799601103308783099224657 41099700827481587324418493)
      ·
        refine ⟨15412387810305595246656935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41099700827481587324418493 15412387810305595246656935)
        ·
          refine ⟨23118581715458392869985403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15412387810305595246656935 23118581715458392869985403)
          ·
            refine ⟨34677872573187589304978105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23118581715458392869985403 34677872573187589304978105)
            ·
              refine ⟨26008404429890691978733579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34677872573187589304978105 26008404429890691978733579)
              ·
                refine ⟨39012606644836037968100369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26008404429890691978733579 39012606644836037968100369)
                ·
                  refine ⟨29259454983627028476075277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39012606644836037968100369 29259454983627028476075277)
                  ·
                    refine ⟨10972295618860135678528229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29259454983627028476075277 10972295618860135678528229)
                    ·
                      refine ⟨2057305428536275439724043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10972295618860135678528229 2057305428536275439724043)
                      ·
                        rfl

theorem cell23_4006588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4006588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006588 prefixEnd_4006588 := by exact prefixLift 4006588
  have htrace : WordTrace (prefixWord ++ tailWord_4006588) baseStart_4006588 baseEnd_4006588 := by
    simpa [prefixWord, tailWord_4006588, baseEnd_4006588] using wordTrace_append hprefix tailTrace_4006588
  have hstable : (prefixWord ++ tailWord_4006588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006588).length < 2 ^ (prefixWord ++ tailWord_4006588).sum := by decide
  have hdescent : baseEnd_4006588 < baseStart_4006588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006593 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4006593 : Nat := 118140960795 + 4006593 * 2 ^ 59
def prefixEnd_4006593 : Nat := 4983230072969 + 3 ^ 40 * 4006593 * 2
def baseEnd_4006593 : Nat := 685769331979849306720507

theorem tailTrace_4006593 : CollatzResearch.WordTrace tailWord_4006593 prefixEnd_4006593 685769331979849306720507 := by
  unfold tailWord_4006593
  simp only [CollatzResearch.WordTrace]
  refine ⟨146132451973805307451864433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97421634649203538301242955 146132451973805307451864433)
  ·
    refine ⟨109599338980353980588898325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146132451973805307451864433 109599338980353980588898325)
    ·
      refine ⟨5137469014704092840104609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109599338980353980588898325 5137469014704092840104609)
      ·
        refine ⟨3853101761028069630078457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5137469014704092840104609 3853101761028069630078457)
        ·
          refine ⟨2889826320771052222558843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853101761028069630078457 2889826320771052222558843)
          ·
            refine ⟨4334739481156578333838265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889826320771052222558843 4334739481156578333838265)
            ·
              refine ⟨3251054610867433750378699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334739481156578333838265 3251054610867433750378699)
              ·
                refine ⟨4876581916301150625568049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251054610867433750378699 4876581916301150625568049)
                ·
                  refine ⟨3657436437225862969176037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876581916301150625568049 3657436437225862969176037)
                  ·
                    refine ⟨685769331979849306720507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657436437225862969176037 685769331979849306720507)
                    ·
                      rfl

theorem cell23_4006593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4006593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006593 prefixEnd_4006593 := by exact prefixLift 4006593
  have htrace : WordTrace (prefixWord ++ tailWord_4006593) baseStart_4006593 baseEnd_4006593 := by
    simpa [prefixWord, tailWord_4006593, baseEnd_4006593] using wordTrace_append hprefix tailTrace_4006593
  have hstable : (prefixWord ++ tailWord_4006593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006593).length < 2 ^ (prefixWord ++ tailWord_4006593).sum := by decide
  have hdescent : baseEnd_4006593 < baseStart_4006593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006601 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_4006601 : Nat := 118140960795 + 4006601 * 2 ^ 59
def prefixEnd_4006601 : Nat := 4983230072969 + 3 ^ 40 * 4006601 * 2
def baseEnd_4006601 : Nat := 2057312103784783888861483

theorem tailTrace_4006601 : CollatzResearch.WordTrace tailWord_4006601 prefixEnd_4006601 2057312103784783888861483 := by
  unfold tailWord_4006601
  simp only [CollatzResearch.WordTrace]
  refine ⟨146132743757776324818155657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97421829171850883212103771 146132743757776324818155657)
  ·
    refine ⟨109599557818332243613616743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146132743757776324818155657 109599557818332243613616743)
    ·
      refine ⟨164399336727498365420425115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109599557818332243613616743 164399336727498365420425115)
      ·
        refine ⟨246599005091247548130637673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164399336727498365420425115 246599005091247548130637673)
        ·
          refine ⟨184949253818435661097978255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246599005091247548130637673 184949253818435661097978255)
          ·
            refine ⟨277423880727653491646967383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184949253818435661097978255 277423880727653491646967383)
            ·
              refine ⟨416135821091480237470451075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277423880727653491646967383 416135821091480237470451075)
              ·
                refine ⟨624203731637220356205676613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416135821091480237470451075 624203731637220356205676613)
                ·
                  refine ⟨117038199681978816788564365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624203731637220356205676613 117038199681978816788564365)
                  ·
                    refine ⟨43889324880742056295711637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117038199681978816788564365 43889324880742056295711637)
                    ·
                      refine ⟨2057312103784783888861483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43889324880742056295711637 2057312103784783888861483)
                      ·
                        rfl

theorem cell23_4006601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_4006601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006601 prefixEnd_4006601 := by exact prefixLift 4006601
  have htrace : WordTrace (prefixWord ++ tailWord_4006601) baseStart_4006601 baseEnd_4006601 := by
    simpa [prefixWord, tailWord_4006601, baseEnd_4006601] using wordTrace_append hprefix tailTrace_4006601
  have hstable : (prefixWord ++ tailWord_4006601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006601).length < 2 ^ (prefixWord ++ tailWord_4006601).sum := by decide
  have hdescent : baseEnd_4006601 < baseStart_4006601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006639 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 2, 2, 2]
def baseStart_4006639 : Nat := 118140960795 + 4006639 * 2 ^ 59
def prefixEnd_4006639 : Nat := 4983230072969 + 3 ^ 40 * 4006639 * 2
def baseEnd_4006639 : Nat := 2057331616049654740186309

theorem tailTrace_4006639 : CollatzResearch.WordTrace tailWord_4006639 prefixEnd_4006639 2057331616049654740186309 := by
  unfold tailWord_4006639
  simp only [CollatzResearch.WordTrace]
  refine ⟨146134129731638657308038971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97422753154425771538692647 146134129731638657308038971)
  ·
    refine ⟨219201194597457985962058457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146134129731638657308038971 219201194597457985962058457)
    ·
      refine ⟨164400895948093489471543843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219201194597457985962058457 164400895948093489471543843)
      ·
        refine ⟨246601343922140234207315765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164400895948093489471543843 246601343922140234207315765)
        ·
          refine ⟨23118875992700646956935853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246601343922140234207315765 23118875992700646956935853)
          ·
            refine ⟨8669578497262742608850945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23118875992700646956935853 8669578497262742608850945)
            ·
              refine ⟨6502183872947056956638209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8669578497262742608850945 6502183872947056956638209)
              ·
                refine ⟨4876637904710292717478657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502183872947056956638209 4876637904710292717478657)
                ·
                  refine ⟨3657478428532719538108993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876637904710292717478657 3657478428532719538108993)
                  ·
                    refine ⟨2743108821399539653581745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657478428532719538108993 2743108821399539653581745)
                    ·
                      refine ⟨2057331616049654740186309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743108821399539653581745 2057331616049654740186309)
                      ·
                        rfl

theorem cell23_4006639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 2, 2].length) (baseStart_4006639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006639 prefixEnd_4006639 := by exact prefixLift 4006639
  have htrace : WordTrace (prefixWord ++ tailWord_4006639) baseStart_4006639 baseEnd_4006639 := by
    simpa [prefixWord, tailWord_4006639, baseEnd_4006639] using wordTrace_append hprefix tailTrace_4006639
  have hstable : (prefixWord ++ tailWord_4006639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006639).length < 2 ^ (prefixWord ++ tailWord_4006639).sum := by decide
  have hdescent : baseEnd_4006639 < baseStart_4006639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006756 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_4006756 : Nat := 118140960795 + 4006756 * 2 ^ 59
def prefixEnd_4006756 : Nat := 4983230072969 + 3 ^ 40 * 4006756 * 2
def baseEnd_4006756 : Nat := 685797231095410260807757

theorem tailTrace_4006756 : CollatzResearch.WordTrace tailWord_4006756 prefixEnd_4006756 685797231095410260807757 := by
  unfold tailWord_4006756
  simp only [CollatzResearch.WordTrace]
  refine ⟨73069198536107393145024061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97425598048143190860032081 73069198536107393145024061)
  ·
    refine ⟨27400949451040272429384023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73069198536107393145024061 27400949451040272429384023)
    ·
      refine ⟨41101424176560408644076035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27400949451040272429384023 41101424176560408644076035)
      ·
        refine ⟨61652136264840612966114053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41101424176560408644076035 61652136264840612966114053)
        ·
          refine ⟨11559775549657614931146385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61652136264840612966114053 11559775549657614931146385)
          ·
            refine ⟨8669831662243211198359789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11559775549657614931146385 8669831662243211198359789)
            ·
              refine ⟨3251186873341204199384921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8669831662243211198359789 3251186873341204199384921)
              ·
                refine ⟨2438390155005903149538691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251186873341204199384921 2438390155005903149538691)
                ·
                  refine ⟨3657585232508854724308037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438390155005903149538691 3657585232508854724308037)
                  ·
                    refine ⟨685797231095410260807757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657585232508854724308037 685797231095410260807757)
                    ·
                      rfl

theorem cell23_4006756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_4006756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006756 prefixEnd_4006756 := by exact prefixLift 4006756
  have htrace : WordTrace (prefixWord ++ tailWord_4006756) baseStart_4006756 baseEnd_4006756 := by
    simpa [prefixWord, tailWord_4006756, baseEnd_4006756] using wordTrace_append hprefix tailTrace_4006756
  have hstable : (prefixWord ++ tailWord_4006756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006756).length < 2 ^ (prefixWord ++ tailWord_4006756).sum := by decide
  have hdescent : baseEnd_4006756 < baseStart_4006756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006765 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_4006765 : Nat := 118140960795 + 4006765 * 2 ^ 59
def prefixEnd_4006765 : Nat := 4983230072969 + 3 ^ 40 * 4006765 * 2
def baseEnd_4006765 : Nat := 685798771537373749070243

theorem tailTrace_4006765 : CollatzResearch.WordTrace tailWord_4006765 prefixEnd_4006765 685798771537373749070243 := by
  unfold tailWord_4006765
  simp only [CollatzResearch.WordTrace]
  refine ⟨146138725329182180827125749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97425816886121453884750499 146138725329182180827125749)
  ·
    refine ⟨13700505499610829452543039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146138725329182180827125749 13700505499610829452543039)
    ·
      refine ⟨20550758249416244178814559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13700505499610829452543039 20550758249416244178814559)
      ·
        refine ⟨30826137374124366268221839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20550758249416244178814559 30826137374124366268221839)
        ·
          refine ⟨46239206061186549402332759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30826137374124366268221839 46239206061186549402332759)
          ·
            refine ⟨69358809091779824103499139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46239206061186549402332759 69358809091779824103499139)
            ·
              refine ⟨104038213637669736155248709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69358809091779824103499139 104038213637669736155248709)
              ·
                refine ⟨19507165057063075529109133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104038213637669736155248709 19507165057063075529109133)
                ·
                  refine ⟨7315186896398653323415925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19507165057063075529109133 7315186896398653323415925)
                  ·
                    refine ⟨685798771537373749070243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7315186896398653323415925 685798771537373749070243)
                    ·
                      rfl

theorem cell23_4006765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_4006765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006765 prefixEnd_4006765 := by exact prefixLift 4006765
  have htrace : WordTrace (prefixWord ++ tailWord_4006765) baseStart_4006765 baseEnd_4006765 := by
    simpa [prefixWord, tailWord_4006765, baseEnd_4006765] using wordTrace_append hprefix tailTrace_4006765
  have hstable : (prefixWord ++ tailWord_4006765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006765).length < 2 ^ (prefixWord ++ tailWord_4006765).sum := by decide
  have hdescent : baseEnd_4006765 < baseStart_4006765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006789 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 2, 3, 2]
def baseStart_4006789 : Nat := 118140960795 + 4006789 * 2 ^ 59
def prefixEnd_4006789 : Nat := 4983230072969 + 3 ^ 40 * 4006789 * 2
def baseEnd_4006789 : Nat := 2057408638147829153310619

theorem tailTrace_4006789 : CollatzResearch.WordTrace tailWord_4006789 prefixEnd_4006789 2057408638147829153310619 := by
  unfold tailWord_4006789
  simp only [CollatzResearch.WordTrace]
  refine ⟨146139600681095232925999421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97426400454063488617332947 146139600681095232925999421)
  ·
    refine ⟨54802350255410712347249783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146139600681095232925999421 54802350255410712347249783)
    ·
      refine ⟨82203525383116068520874675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54802350255410712347249783 82203525383116068520874675)
      ·
        refine ⟨123305288074674102781312013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82203525383116068520874675 123305288074674102781312013)
        ·
          refine ⟨46239483028002788542992005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123305288074674102781312013 46239483028002788542992005)
          ·
            refine ⟨8669903067750522851811001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46239483028002788542992005 8669903067750522851811001)
            ·
              refine ⟨6502427300812892138858251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8669903067750522851811001 6502427300812892138858251)
              ·
                refine ⟨9753640951219338208287377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6502427300812892138858251 9753640951219338208287377)
                ·
                  refine ⟨7315230713414503656215533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9753640951219338208287377 7315230713414503656215533)
                  ·
                    refine ⟨2743211517530438871080825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7315230713414503656215533 2743211517530438871080825)
                    ·
                      refine ⟨2057408638147829153310619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743211517530438871080825 2057408638147829153310619)
                      ·
                        rfl

theorem cell23_4006789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_4006789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006789 prefixEnd_4006789 := by exact prefixLift 4006789
  have htrace : WordTrace (prefixWord ++ tailWord_4006789) baseStart_4006789 baseEnd_4006789 := by
    simpa [prefixWord, tailWord_4006789, baseEnd_4006789] using wordTrace_append hprefix tailTrace_4006789
  have hstable : (prefixWord ++ tailWord_4006789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006789).length < 2 ^ (prefixWord ++ tailWord_4006789).sum := by decide
  have hdescent : baseEnd_4006789 < baseStart_4006789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006795 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 6, 4]
def baseStart_4006795 : Nat := 118140960795 + 4006795 * 2 ^ 59
def prefixEnd_4006795 : Nat := 4983230072969 + 3 ^ 40 * 4006795 * 2
def baseEnd_4006795 : Nat := 685803906343918709945197

theorem tailTrace_4006795 : CollatzResearch.WordTrace tailWord_4006795 prefixEnd_4006795 685803906343918709945197 := by
  unfold tailWord_4006795
  simp only [CollatzResearch.WordTrace]
  refine ⟨146139819519073495950717839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97426546346048997300478559 146139819519073495950717839)
  ·
    refine ⟨219209729278610243926076759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146139819519073495950717839 219209729278610243926076759)
    ·
      refine ⟨328814593917915365889115139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219209729278610243926076759 328814593917915365889115139)
      ·
        refine ⟨493221890876873048833672709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328814593917915365889115139 493221890876873048833672709)
        ·
          refine ⟨92479104539413696656313633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493221890876873048833672709 92479104539413696656313633)
          ·
            refine ⟨69359328404560272492235225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92479104539413696656313633 69359328404560272492235225)
            ·
              refine ⟨52019496303420204369176419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69359328404560272492235225 52019496303420204369176419)
              ·
                refine ⟨78029244455130306553764629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52019496303420204369176419 78029244455130306553764629)
                ·
                  refine ⟨3657620833834233119707717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78029244455130306553764629 3657620833834233119707717)
                  ·
                    refine ⟨685803906343918709945197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657620833834233119707717 685803906343918709945197)
                    ·
                      rfl

theorem cell23_4006795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 4].length) (baseStart_4006795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006795 prefixEnd_4006795 := by exact prefixLift 4006795
  have htrace : WordTrace (prefixWord ++ tailWord_4006795) baseStart_4006795 baseEnd_4006795 := by
    simpa [prefixWord, tailWord_4006795, baseEnd_4006795] using wordTrace_append hprefix tailTrace_4006795
  have hstable : (prefixWord ++ tailWord_4006795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006795).length < 2 ^ (prefixWord ++ tailWord_4006795).sum := by decide
  have hdescent : baseEnd_4006795 < baseStart_4006795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006808 : List Nat := [2, 1, 2, 18]
def baseStart_4006808 : Nat := 118140960795 + 4006808 * 2 ^ 59
def prefixEnd_4006808 : Nat := 4983230072969 + 3 ^ 40 * 4006808 * 2
def baseEnd_4006808 : Nat := 940749151477029985813

theorem tailTrace_4006808 : CollatzResearch.WordTrace tailWord_4006808 prefixEnd_4006808 940749151477029985813 := by
  unfold tailWord_4006808
  simp only [CollatzResearch.WordTrace]
  refine ⟨73070146834013199585470539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97426862445350932780627385 73070146834013199585470539)
  ·
    refine ⟨109605220251019799378205809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73070146834013199585470539 109605220251019799378205809)
    ·
      refine ⟨82203915188264849533654357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109605220251019799378205809 82203915188264849533654357)
      ·
        refine ⟨940749151477029985813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 82203915188264849533654357 940749151477029985813)
        ·
          rfl

theorem cell23_4006808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 18].length) (baseStart_4006808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006808 prefixEnd_4006808 := by exact prefixLift 4006808
  have htrace : WordTrace (prefixWord ++ tailWord_4006808) baseStart_4006808 baseEnd_4006808 := by
    simpa [prefixWord, tailWord_4006808, baseEnd_4006808] using wordTrace_append hprefix tailTrace_4006808
  have hstable : (prefixWord ++ tailWord_4006808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006808).length < 2 ^ (prefixWord ++ tailWord_4006808).sum := by decide
  have hdescent : baseEnd_4006808 < baseStart_4006808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006870 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_4006870 : Nat := 118140960795 + 4006870 * 2 ^ 59
def prefixEnd_4006870 : Nat := 4983230072969 + 3 ^ 40 * 4006870 * 2
def baseEnd_4006870 : Nat := 2057450230080843336397747

theorem tailTrace_4006870 : CollatzResearch.WordTrace tailWord_4006870 prefixEnd_4006870 2057450230080843336397747 := by
  unfold tailWord_4006870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133909687112611484981129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97428369995867855839798709 9133909687112611484981129)
  ·
    refine ⟨6850432265334458613735847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9133909687112611484981129 6850432265334458613735847)
    ·
      refine ⟨10275648398001687920603771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850432265334458613735847 10275648398001687920603771)
      ·
        refine ⟨15413472597002531880905657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275648398001687920603771 15413472597002531880905657)
        ·
          refine ⟨11560104447751898910679243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15413472597002531880905657 11560104447751898910679243)
          ·
            refine ⟨17340156671627848366018865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560104447751898910679243 17340156671627848366018865)
            ·
              refine ⟨13005117503720886274514149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17340156671627848366018865 13005117503720886274514149)
              ·
                refine ⟨2438459531947666176471403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13005117503720886274514149 2438459531947666176471403)
                ·
                  refine ⟨3657689297921499264707105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438459531947666176471403 3657689297921499264707105)
                  ·
                    refine ⟨2743266973441124448530329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657689297921499264707105 2743266973441124448530329)
                    ·
                      refine ⟨2057450230080843336397747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743266973441124448530329 2057450230080843336397747)
                      ·
                        rfl

theorem cell23_4006870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_4006870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006870 prefixEnd_4006870 := by exact prefixLift 4006870
  have htrace : WordTrace (prefixWord ++ tailWord_4006870) baseStart_4006870 baseEnd_4006870 := by
    simpa [prefixWord, tailWord_4006870, baseEnd_4006870] using wordTrace_append hprefix tailTrace_4006870
  have hstable : (prefixWord ++ tailWord_4006870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006870).length < 2 ^ (prefixWord ++ tailWord_4006870).sum := by decide
  have hdescent : baseEnd_4006870 < baseStart_4006870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006926 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_4006926 : Nat := 118140960795 + 4006926 * 2 ^ 59
def prefixEnd_4006926 : Nat := 4983230072969 + 3 ^ 40 * 4006926 * 2
def baseEnd_4006926 : Nat := 2057478984997495117297489

theorem tailTrace_4006926 : CollatzResearch.WordTrace tailWord_4006926 prefixEnd_4006926 2057478984997495117297489 := by
  unfold tailWord_4006926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268074685199863165467079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97429731654399270215824421 18268074685199863165467079)
  ·
    refine ⟨27402112027799794748200619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18268074685199863165467079 27402112027799794748200619)
    ·
      refine ⟨41103168041699692122300929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27402112027799794748200619 41103168041699692122300929)
      ·
        refine ⟨30827376031274769091725697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41103168041699692122300929 30827376031274769091725697)
        ·
          refine ⟨23120532023456076818794273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30827376031274769091725697 23120532023456076818794273)
          ·
            refine ⟨17340399017592057614095705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23120532023456076818794273 17340399017592057614095705)
            ·
              refine ⟨13005299263194043210571779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17340399017592057614095705 13005299263194043210571779)
              ·
                refine ⟨19507948894791064815857669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005299263194043210571779 19507948894791064815857669)
                ·
                  refine ⟨3657740417773324652973313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19507948894791064815857669 3657740417773324652973313)
                  ·
                    refine ⟨2743305313329993489729985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657740417773324652973313 2743305313329993489729985)
                    ·
                      refine ⟨2057478984997495117297489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743305313329993489729985 2057478984997495117297489)
                      ·
                        rfl

theorem cell23_4006926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_4006926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006926 prefixEnd_4006926 := by exact prefixLift 4006926
  have htrace : WordTrace (prefixWord ++ tailWord_4006926) baseStart_4006926 baseEnd_4006926 := by
    simpa [prefixWord, tailWord_4006926, baseEnd_4006926] using wordTrace_append hprefix tailTrace_4006926
  have hstable : (prefixWord ++ tailWord_4006926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006926).length < 2 ^ (prefixWord ++ tailWord_4006926).sum := by decide
  have hdescent : baseEnd_4006926 < baseStart_4006926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006943 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 2, 2, 2]
def baseStart_4006943 : Nat := 118140960795 + 4006943 * 2 ^ 59
def prefixEnd_4006943 : Nat := 4983230072969 + 3 ^ 40 * 4006943 * 2
def baseEnd_4006943 : Nat := 2057487714168621550784911

theorem tailTrace_4006943 : CollatzResearch.WordTrace tailWord_4006943 prefixEnd_4006943 2057487714168621550784911 := by
  unfold tailWord_4006943
  simp only [CollatzResearch.WordTrace]
  refine ⟨146145217522537317227105483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97430145015024878151403655 146145217522537317227105483)
  ·
    refine ⟨219217826283805975840658225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146145217522537317227105483 219217826283805975840658225)
    ·
      refine ⟨164413369712854481880493669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219217826283805975840658225 164413369712854481880493669)
      ·
        refine ⟨30827506821160215352592563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164413369712854481880493669 30827506821160215352592563)
        ·
          refine ⟨46241260231740323028888845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30827506821160215352592563 46241260231740323028888845)
          ·
            refine ⟨17340472586902621135833317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46241260231740323028888845 17340472586902621135833317)
            ·
              refine ⟨3251338610044241462968747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17340472586902621135833317 3251338610044241462968747)
              ·
                refine ⟨4877007915066362194453121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251338610044241462968747 4877007915066362194453121)
                ·
                  refine ⟨3657755936299771645839841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4877007915066362194453121 3657755936299771645839841)
                  ·
                    refine ⟨2743316952224828734379881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657755936299771645839841 2743316952224828734379881)
                    ·
                      refine ⟨2057487714168621550784911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743316952224828734379881 2057487714168621550784911)
                      ·
                        rfl

theorem cell23_4006943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_4006943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006943 prefixEnd_4006943 := by exact prefixLift 4006943
  have htrace : WordTrace (prefixWord ++ tailWord_4006943) baseStart_4006943 baseEnd_4006943 := by
    simpa [prefixWord, tailWord_4006943, baseEnd_4006943] using wordTrace_append hprefix tailTrace_4006943
  have hstable : (prefixWord ++ tailWord_4006943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006943).length < 2 ^ (prefixWord ++ tailWord_4006943).sum := by decide
  have hdescent : baseEnd_4006943 < baseStart_4006943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006955 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_4006955 : Nat := 118140960795 + 4006955 * 2 ^ 59
def prefixEnd_4006955 : Nat := 4983230072969 + 3 ^ 40 * 4006955 * 2
def baseEnd_4006955 : Nat := 2057493875936475503834855

theorem tailTrace_4006955 : CollatzResearch.WordTrace tailWord_4006955 prefixEnd_4006955 2057493875936475503834855 := by
  unfold tailWord_4006955
  simp only [CollatzResearch.WordTrace]
  refine ⟨146145655198493843276542319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97430436798995895517694879 146145655198493843276542319)
  ·
    refine ⟨219218482797740764914813479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146145655198493843276542319 219218482797740764914813479)
    ·
      refine ⟨328827724196611147372220219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219218482797740764914813479 328827724196611147372220219)
      ·
        refine ⟨493241586294916721058330329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328827724196611147372220219 493241586294916721058330329)
        ·
          refine ⟨369931189721187540793747747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493241586294916721058330329 369931189721187540793747747)
          ·
            refine ⟨554896784581781311190621621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369931189721187540793747747 554896784581781311190621621)
            ·
              refine ⟨52021573554541997924120777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 554896784581781311190621621 52021573554541997924120777)
              ·
                refine ⟨39016180165906498443090583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52021573554541997924120777 39016180165906498443090583)
                ·
                  refine ⟨58524270248859747664635875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39016180165906498443090583 58524270248859747664635875)
                  ·
                    refine ⟨87786405373289621496953813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58524270248859747664635875 87786405373289621496953813)
                    ·
                      refine ⟨2057493875936475503834855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87786405373289621496953813 2057493875936475503834855)
                      ·
                        rfl

theorem cell23_4006955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_4006955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006955 prefixEnd_4006955 := by exact prefixLift 4006955
  have htrace : WordTrace (prefixWord ++ tailWord_4006955) baseStart_4006955 baseEnd_4006955 := by
    simpa [prefixWord, tailWord_4006955, baseEnd_4006955] using wordTrace_append hprefix tailTrace_4006955
  have hstable : (prefixWord ++ tailWord_4006955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006955).length < 2 ^ (prefixWord ++ tailWord_4006955).sum := by decide
  have hdescent : baseEnd_4006955 < baseStart_4006955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006972 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_4006972 : Nat := 118140960795 + 4006972 * 2 ^ 59
def prefixEnd_4006972 : Nat := 4983230072969 + 3 ^ 40 * 4006972 * 2
def baseEnd_4006972 : Nat := 2057502605107601937322277

theorem tailTrace_4006972 : CollatzResearch.WordTrace tailWord_4006972 prefixEnd_4006972 2057502605107601937322277 := by
  unfold tailWord_4006972
  simp only [CollatzResearch.WordTrace]
  refine ⟨73073137619716127589955585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97430850159621503453274113 73073137619716127589955585)
  ·
    refine ⟨54804853214787095692466689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73073137619716127589955585 54804853214787095692466689)
    ·
      refine ⟨41103639911090321769350017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54804853214787095692466689 41103639911090321769350017)
      ·
        refine ⟨30827729933317741327012513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41103639911090321769350017 30827729933317741327012513)
        ·
          refine ⟨23120797449988305995259385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30827729933317741327012513 23120797449988305995259385)
          ·
            refine ⟨17340598087491229496444539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23120797449988305995259385 17340598087491229496444539)
            ·
              refine ⟨26010897131236844244666809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17340598087491229496444539 26010897131236844244666809)
              ·
                refine ⟨19508172848427633183500107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26010897131236844244666809 19508172848427633183500107)
                ·
                  refine ⟨29262259272641449775250161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508172848427633183500107 29262259272641449775250161)
                  ·
                    refine ⟨21946694454481087331437621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29262259272641449775250161 21946694454481087331437621)
                    ·
                      refine ⟨2057502605107601937322277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21946694454481087331437621 2057502605107601937322277)
                      ·
                        rfl

theorem cell23_4006972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_4006972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006972 prefixEnd_4006972 := by exact prefixLift 4006972
  have htrace : WordTrace (prefixWord ++ tailWord_4006972) baseStart_4006972 baseEnd_4006972 := by
    simpa [prefixWord, tailWord_4006972, baseEnd_4006972] using wordTrace_append hprefix tailTrace_4006972
  have hstable : (prefixWord ++ tailWord_4006972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006972).length < 2 ^ (prefixWord ++ tailWord_4006972).sum := by decide
  have hdescent : baseEnd_4006972 < baseStart_4006972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006989 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4006989 : Nat := 118140960795 + 4006989 * 2 ^ 59
def prefixEnd_4006989 : Nat := 4983230072969 + 3 ^ 40 * 4006989 * 2
def baseEnd_4006989 : Nat := 2057511334278728370809699

theorem tailTrace_4006989 : CollatzResearch.WordTrace tailWord_4006989 prefixEnd_4006989 2057511334278728370809699 := by
  unfold tailWord_4006989
  simp only [CollatzResearch.WordTrace]
  refine ⟨146146895280370667083280021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97431263520247111388853347 146146895280370667083280021)
  ·
    refine ⟨6850635716267375019528751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146146895280370667083280021 6850635716267375019528751)
    ·
      refine ⟨10275953574401062529293127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850635716267375019528751 10275953574401062529293127)
      ·
        refine ⟨15413930361601593793939691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275953574401062529293127 15413930361601593793939691)
        ·
          refine ⟨23120895542402390690909537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15413930361601593793939691 23120895542402390690909537)
          ·
            refine ⟨17340671656801793018182153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23120895542402390690909537 17340671656801793018182153)
            ·
              refine ⟨13005503742601344763636615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17340671656801793018182153 13005503742601344763636615)
              ·
                refine ⟨19508255613902017145454923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005503742601344763636615 19508255613902017145454923)
                ·
                  refine ⟨29262383420853025718182385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508255613902017145454923 29262383420853025718182385)
                  ·
                    refine ⟨21946787565639769288636789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29262383420853025718182385 21946787565639769288636789)
                    ·
                      refine ⟨2057511334278728370809699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21946787565639769288636789 2057511334278728370809699)
                      ·
                        rfl

theorem cell23_4006989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4006989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006989 prefixEnd_4006989 := by exact prefixLift 4006989
  have htrace : WordTrace (prefixWord ++ tailWord_4006989) baseStart_4006989 baseEnd_4006989 := by
    simpa [prefixWord, tailWord_4006989, baseEnd_4006989] using wordTrace_append hprefix tailTrace_4006989
  have hstable : (prefixWord ++ tailWord_4006989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006989).length < 2 ^ (prefixWord ++ tailWord_4006989).sum := by decide
  have hdescent : baseEnd_4006989 < baseStart_4006989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006992 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 7, 4]
def baseStart_4006992 : Nat := 118140960795 + 4006992 * 2 ^ 59
def prefixEnd_4006992 : Nat := 4983230072969 + 3 ^ 40 * 4006992 * 2
def baseEnd_4006992 : Nat := 685837624906897286357395

theorem tailTrace_4006992 : CollatzResearch.WordTrace tailWord_4006992 prefixEnd_4006992 685837624906897286357395 := by
  unfold tailWord_4006992
  simp only [CollatzResearch.WordTrace]
  refine ⟨73073502349679899297819615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97431336466239865730426153 73073502349679899297819615)
  ·
    refine ⟨109610253524519848946729423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73073502349679899297819615 109610253524519848946729423)
    ·
      refine ⟨164415380286779773420094135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109610253524519848946729423 164415380286779773420094135)
      ·
        refine ⟨246623070430169660130141203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164415380286779773420094135 246623070430169660130141203)
        ·
          refine ⟨369934605645254490195211805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246623070430169660130141203 369934605645254490195211805)
          ·
            refine ⟨138725477116970433823204427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369934605645254490195211805 138725477116970433823204427)
            ·
              refine ⟨208088215675455650734806641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138725477116970433823204427 208088215675455650734806641)
              ·
                refine ⟨156066161756591738051104981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208088215675455650734806641 156066161756591738051104981)
                ·
                  refine ⟨3657800666170118860572773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 156066161756591738051104981 3657800666170118860572773)
                  ·
                    refine ⟨685837624906897286357395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657800666170118860572773 685837624906897286357395)
                    ·
                      rfl

theorem cell23_4006992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_4006992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4006992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4006992 prefixEnd_4006992 := by exact prefixLift 4006992
  have htrace : WordTrace (prefixWord ++ tailWord_4006992) baseStart_4006992 baseEnd_4006992 := by
    simpa [prefixWord, tailWord_4006992, baseEnd_4006992] using wordTrace_append hprefix tailTrace_4006992
  have hstable : (prefixWord ++ tailWord_4006992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006992).length < 2 ^ (prefixWord ++ tailWord_4006992).sum := by decide
  have hdescent : baseEnd_4006992 < baseStart_4006992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007016 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4007016 : Nat := 118140960795 + 4007016 * 2 ^ 59
def prefixEnd_4007016 : Nat := 4983230072969 + 3 ^ 40 * 4007016 * 2
def baseEnd_4007016 : Nat := 2057525198256399765172075

theorem tailTrace_4007016 : CollatzResearch.WordTrace tailWord_4007016 prefixEnd_4007016 2057525198256399765172075 := by
  unfold tailWord_4007016
  simp only [CollatzResearch.WordTrace]
  refine ⟨73073940025636425347256451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97431920034181900463008601 73073940025636425347256451)
  ·
    refine ⟨109610910038454638020884677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73073940025636425347256451 109610910038454638020884677)
    ·
      refine ⟨20552045632210244628915877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109610910038454638020884677 20552045632210244628915877)
      ·
        refine ⟨3853508556039420867921727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20552045632210244628915877 3853508556039420867921727)
        ·
          refine ⟨5780262834059131301882591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853508556039420867921727 5780262834059131301882591)
          ·
            refine ⟨8670394251088696952823887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780262834059131301882591 8670394251088696952823887)
            ·
              refine ⟨13005591376633045429235831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670394251088696952823887 13005591376633045429235831)
              ·
                refine ⟨19508387064949568143853747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005591376633045429235831 19508387064949568143853747)
                ·
                  refine ⟨29262580597424352215780621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508387064949568143853747 29262580597424352215780621)
                  ·
                    refine ⟨10973467724034132080917733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29262580597424352215780621 10973467724034132080917733)
                    ·
                      refine ⟨2057525198256399765172075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10973467724034132080917733 2057525198256399765172075)
                      ·
                        rfl

theorem cell23_4007016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4007016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007016 prefixEnd_4007016 := by exact prefixLift 4007016
  have htrace : WordTrace (prefixWord ++ tailWord_4007016) baseStart_4007016 baseEnd_4007016 := by
    simpa [prefixWord, tailWord_4007016, baseEnd_4007016] using wordTrace_append hprefix tailTrace_4007016
  have hstable : (prefixWord ++ tailWord_4007016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007016).length < 2 ^ (prefixWord ++ tailWord_4007016).sum := by decide
  have hdescent : baseEnd_4007016 < baseStart_4007016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007052 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_4007052 : Nat := 118140960795 + 4007052 * 2 ^ 59
def prefixEnd_4007052 : Nat := 4983230072969 + 3 ^ 40 * 4007052 * 2
def baseEnd_4007052 : Nat := 685847894519987208107303

theorem tailTrace_4007052 : CollatzResearch.WordTrace tailWord_4007052 prefixEnd_4007052 685847894519987208107303 := by
  unfold tailWord_4007052
  simp only [CollatzResearch.WordTrace]
  refine ⟨73074596539571214421411705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97432795386094952561882273 73074596539571214421411705)
  ·
    refine ⟨54805947404678410816058779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73074596539571214421411705 54805947404678410816058779)
    ·
      refine ⟨82208921107017616224088169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54805947404678410816058779 82208921107017616224088169)
      ·
        refine ⟨61656690830263212168066127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82208921107017616224088169 61656690830263212168066127)
        ·
          refine ⟨92485036245394818252099191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61656690830263212168066127 92485036245394818252099191)
          ·
            refine ⟨138727554368092227378148787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92485036245394818252099191 138727554368092227378148787)
            ·
              refine ⟨208091331552138341067223181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138727554368092227378148787 208091331552138341067223181)
              ·
                refine ⟨78034249332051877900208693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208091331552138341067223181 78034249332051877900208693)
                ·
                  refine ⟨7315710874879863553144565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78034249332051877900208693 7315710874879863553144565)
                  ·
                    refine ⟨685847894519987208107303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7315710874879863553144565 685847894519987208107303)
                    ·
                      rfl

theorem cell23_4007052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_4007052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007052 prefixEnd_4007052 := by exact prefixLift 4007052
  have htrace : WordTrace (prefixWord ++ tailWord_4007052) baseStart_4007052 baseEnd_4007052 := by
    simpa [prefixWord, tailWord_4007052, baseEnd_4007052] using wordTrace_append hprefix tailTrace_4007052
  have hstable : (prefixWord ++ tailWord_4007052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007052).length < 2 ^ (prefixWord ++ tailWord_4007052).sum := by decide
  have hdescent : baseEnd_4007052 < baseStart_4007052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007059 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 1, 5, 2]
def baseStart_4007059 : Nat := 118140960795 + 4007059 * 2 ^ 59
def prefixEnd_4007059 : Nat := 4983230072969 + 3 ^ 40 * 4007059 * 2
def baseEnd_4007059 : Nat := 2057547277924543096934377

theorem tailTrace_4007059 : CollatzResearch.WordTrace tailWord_4007059 prefixEnd_4007059 2057547277924543096934377 := by
  unfold tailWord_4007059
  simp only [CollatzResearch.WordTrace]
  refine ⟨146149448390117069038328231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97432965593411379358885487 146149448390117069038328231)
  ·
    refine ⟨219224172585175603557492347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146149448390117069038328231 219224172585175603557492347)
    ·
      refine ⟨328836258877763405336238521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219224172585175603557492347 328836258877763405336238521)
      ·
        refine ⟨246627194158322554002178891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328836258877763405336238521 246627194158322554002178891)
        ·
          refine ⟨369940791237483831003268337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246627194158322554002178891 369940791237483831003268337)
          ·
            refine ⟨277455593428112873252451253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369940791237483831003268337 277455593428112873252451253)
            ·
              refine ⟨26011461883885581867417305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277455593428112873252451253 26011461883885581867417305)
              ·
                refine ⟨19508596412914186400562979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26011461883885581867417305 19508596412914186400562979)
                ·
                  refine ⟨29262894619371279600844469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508596412914186400562979 29262894619371279600844469)
                  ·
                    refine ⟨2743396370566057462579169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29262894619371279600844469 2743396370566057462579169)
                    ·
                      refine ⟨2057547277924543096934377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743396370566057462579169 2057547277924543096934377)
                      ·
                        rfl

theorem cell23_4007059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5, 2].length) (baseStart_4007059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007059 prefixEnd_4007059 := by exact prefixLift 4007059
  have htrace : WordTrace (prefixWord ++ tailWord_4007059) baseStart_4007059 baseEnd_4007059 := by
    simpa [prefixWord, tailWord_4007059, baseEnd_4007059] using wordTrace_append hprefix tailTrace_4007059
  have hstable : (prefixWord ++ tailWord_4007059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007059).length < 2 ^ (prefixWord ++ tailWord_4007059).sum := by decide
  have hdescent : baseEnd_4007059 < baseStart_4007059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007076 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_4007076 : Nat := 118140960795 + 4007076 * 2 ^ 59
def prefixEnd_4007076 : Nat := 4983230072969 + 3 ^ 40 * 4007076 * 2
def baseEnd_4007076 : Nat := 2057556007095669530421799

theorem tailTrace_4007076 : CollatzResearch.WordTrace tailWord_4007076 prefixEnd_4007076 2057556007095669530421799 := by
  unfold tailWord_4007076
  simp only [CollatzResearch.WordTrace]
  refine ⟨73075034215527740470848541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97433378954036987294464721 73075034215527740470848541)
  ·
    refine ⟨27403137830822902676568203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73075034215527740470848541 27403137830822902676568203)
    ·
      refine ⟨41104706746234354014852305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27403137830822902676568203 41104706746234354014852305)
      ·
        refine ⟨30828530059675765511139229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41104706746234354014852305 30828530059675765511139229)
        ·
          refine ⟨11560698772378412066677211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30828530059675765511139229 11560698772378412066677211)
          ·
            refine ⟨17341048158567618100015817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560698772378412066677211 17341048158567618100015817)
            ·
              refine ⟨13005786118925713575011863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17341048158567618100015817 13005786118925713575011863)
              ·
                refine ⟨19508679178388570362517795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005786118925713575011863 19508679178388570362517795)
                ·
                  refine ⟨29263018767582855543776693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508679178388570362517795 29263018767582855543776693)
                  ·
                    refine ⟨2743408009460892707229065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29263018767582855543776693 2743408009460892707229065)
                    ·
                      refine ⟨2057556007095669530421799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743408009460892707229065 2057556007095669530421799)
                      ·
                        rfl

theorem cell23_4007076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_4007076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007076 prefixEnd_4007076 := by exact prefixLift 4007076
  have htrace : WordTrace (prefixWord ++ tailWord_4007076) baseStart_4007076 baseEnd_4007076 := by
    simpa [prefixWord, tailWord_4007076, baseEnd_4007076] using wordTrace_append hprefix tailTrace_4007076
  have hstable : (prefixWord ++ tailWord_4007076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007076).length < 2 ^ (prefixWord ++ tailWord_4007076).sum := by decide
  have hdescent : baseEnd_4007076 < baseStart_4007076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007094 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4007094 : Nat := 118140960795 + 4007094 * 2 ^ 59
def prefixEnd_4007094 : Nat := 4983230072969 + 3 ^ 40 * 4007094 * 2
def baseEnd_4007094 : Nat := 685855083249150153332239

theorem tailTrace_4007094 : CollatzResearch.WordTrace tailWord_4007094 prefixEnd_4007094 685855083249150153332239 := by
  unfold tailWord_4007094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134420309061891875990771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97433816629993513343901557 9134420309061891875990771)
  ·
    refine ⟨13701630463592837813986157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9134420309061891875990771 13701630463592837813986157)
    ·
      refine ⟨5138111423847314180244809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13701630463592837813986157 5138111423847314180244809)
      ·
        refine ⟨3853583567885485635183607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5138111423847314180244809 3853583567885485635183607)
        ·
          refine ⟨5780375351828228452775411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853583567885485635183607 5780375351828228452775411)
          ·
            refine ⟨8670563027742342679163117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780375351828228452775411 8670563027742342679163117)
            ·
              refine ⟨3251461135403378504686169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8670563027742342679163117 3251461135403378504686169)
              ·
                refine ⟨2438595851552533878514627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251461135403378504686169 2438595851552533878514627)
                ·
                  refine ⟨3657893777328800817771941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438595851552533878514627 3657893777328800817771941)
                  ·
                    refine ⟨685855083249150153332239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657893777328800817771941 685855083249150153332239)
                    ·
                      rfl

theorem cell23_4007094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4007094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007094 prefixEnd_4007094 := by exact prefixLift 4007094
  have htrace : WordTrace (prefixWord ++ tailWord_4007094) baseStart_4007094 baseEnd_4007094 := by
    simpa [prefixWord, tailWord_4007094, baseEnd_4007094] using wordTrace_append hprefix tailTrace_4007094
  have hstable : (prefixWord ++ tailWord_4007094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007094).length < 2 ^ (prefixWord ++ tailWord_4007094).sum := by decide
  have hdescent : baseEnd_4007094 < baseStart_4007094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007109 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_4007109 : Nat := 118140960795 + 4007109 * 2 ^ 59
def prefixEnd_4007109 : Nat := 4983230072969 + 3 ^ 40 * 4007109 * 2
def baseEnd_4007109 : Nat := 2057572951957267901309147

theorem tailTrace_4007109 : CollatzResearch.WordTrace tailWord_4007109 prefixEnd_4007109 2057572951957267901309147 := by
  unfold tailWord_4007109
  simp only [CollatzResearch.WordTrace]
  refine ⟨146151272039935927577648381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97434181359957285051765587 146151272039935927577648381)
  ·
    refine ⟨54806727014975972841618143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146151272039935927577648381 54806727014975972841618143)
    ·
      refine ⟨82210090522463959262427215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54806727014975972841618143 82210090522463959262427215)
      ·
        refine ⟨123315135783695938893640823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82210090522463959262427215 123315135783695938893640823)
        ·
          refine ⟨184972703675543908340461235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123315135783695938893640823 184972703675543908340461235)
          ·
            refine ⟨277459055513315862510691853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184972703675543908340461235 277459055513315862510691853)
            ·
              refine ⟨104047145817493448441509445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277459055513315862510691853 104047145817493448441509445)
              ·
                refine ⟨19508839840780021582783021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104047145817493448441509445 19508839840780021582783021)
                ·
                  refine ⟨7315814940292508093543633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19508839840780021582783021 7315814940292508093543633)
                  ·
                    refine ⟨5486861205219381070157725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315814940292508093543633 5486861205219381070157725)
                    ·
                      refine ⟨2057572951957267901309147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5486861205219381070157725 2057572951957267901309147)
                      ·
                        rfl

theorem cell23_4007109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_4007109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007109 prefixEnd_4007109 := by exact prefixLift 4007109
  have htrace : WordTrace (prefixWord ++ tailWord_4007109) baseStart_4007109 baseEnd_4007109 := by
    simpa [prefixWord, tailWord_4007109, baseEnd_4007109] using wordTrace_append hprefix tailTrace_4007109
  have hstable : (prefixWord ++ tailWord_4007109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007109).length < 2 ^ (prefixWord ++ tailWord_4007109).sum := by decide
  have hdescent : baseEnd_4007109 < baseStart_4007109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007112 : List Nat := [2, 1, 3, 1, 2, 1, 3, 10]
def baseStart_4007112 : Nat := 118140960795 + 4007112 * 2 ^ 59
def prefixEnd_4007112 : Nat := 4983230072969 + 3 ^ 40 * 4007112 * 2
def baseEnd_4007112 : Nat := 76206462681453014428579

theorem tailTrace_4007112 : CollatzResearch.WordTrace tailWord_4007112 prefixEnd_4007112 76206462681453014428579 := by
  unfold tailWord_4007112
  simp only [CollatzResearch.WordTrace]
  refine ⟨73075690729462529545003795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97434254305950039393338393 73075690729462529545003795)
  ·
    refine ⟨109613536094193794317505693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73075690729462529545003795 109613536094193794317505693)
    ·
      refine ⟨41105076035322672869064635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109613536094193794317505693 41105076035322672869064635)
      ·
        refine ⟨61657614052984009303596953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41105076035322672869064635 61657614052984009303596953)
        ·
          refine ⟨46243210539738006977697715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61657614052984009303596953 46243210539738006977697715)
          ·
            refine ⟨69364815809607010466546573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46243210539738006977697715 69364815809607010466546573)
            ·
              refine ⟨26011805928602628924954965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69364815809607010466546573 26011805928602628924954965)
              ·
                refine ⟨76206462681453014428579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26011805928602628924954965 76206462681453014428579)
                ·
                  rfl

theorem cell23_4007112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 10].length) (baseStart_4007112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007112 prefixEnd_4007112 := by exact prefixLift 4007112
  have htrace : WordTrace (prefixWord ++ tailWord_4007112) baseStart_4007112 baseEnd_4007112 := by
    simpa [prefixWord, tailWord_4007112, baseEnd_4007112] using wordTrace_append hprefix tailTrace_4007112
  have hstable : (prefixWord ++ tailWord_4007112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007112).length < 2 ^ (prefixWord ++ tailWord_4007112).sum := by decide
  have hdescent : baseEnd_4007112 < baseStart_4007112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007143 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4007143 : Nat := 118140960795 + 4007143 * 2 ^ 59
def prefixEnd_4007143 : Nat := 4983230072969 + 3 ^ 40 * 4007143 * 2
def baseEnd_4007143 : Nat := 2057590410299520768283991

theorem tailTrace_4007143 : CollatzResearch.WordTrace tailWord_4007143 prefixEnd_4007143 2057590410299520768283991 := by
  unfold tailWord_4007143
  simp only [CollatzResearch.WordTrace]
  refine ⟨146152512121812751384386083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97435008081208500922924055 146152512121812751384386083)
  ·
    refine ⟨219228768182719127076579125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146152512121812751384386083 219228768182719127076579125)
    ·
      refine ⟨20552697017129918163429293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219228768182719127076579125 20552697017129918163429293)
      ·
        refine ⟨7707261381423719311285985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20552697017129918163429293 7707261381423719311285985)
        ·
          refine ⟨5780446036067789483464489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7707261381423719311285985 5780446036067789483464489)
          ·
            refine ⟨4335334527050842112598367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5780446036067789483464489 4335334527050842112598367)
            ·
              refine ⟨6503001790576263168897551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335334527050842112598367 6503001790576263168897551)
              ·
                refine ⟨9754502685864394753346327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503001790576263168897551 9754502685864394753346327)
                ·
                  refine ⟨14631754028796592130019491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9754502685864394753346327 14631754028796592130019491)
                  ·
                    refine ⟨21947631043194888195029237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14631754028796592130019491 21947631043194888195029237)
                    ·
                      refine ⟨2057590410299520768283991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21947631043194888195029237 2057590410299520768283991)
                      ·
                        rfl

theorem cell23_4007143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4007143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007143 prefixEnd_4007143 := by exact prefixLift 4007143
  have htrace : WordTrace (prefixWord ++ tailWord_4007143) baseStart_4007143 baseEnd_4007143 := by
    simpa [prefixWord, tailWord_4007143, baseEnd_4007143] using wordTrace_append hprefix tailTrace_4007143
  have hstable : (prefixWord ++ tailWord_4007143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007143).length < 2 ^ (prefixWord ++ tailWord_4007143).sum := by decide
  have hdescent : baseEnd_4007143 < baseStart_4007143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007152 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_4007152 : Nat := 118140960795 + 4007152 * 2 ^ 59
def prefixEnd_4007152 : Nat := 4983230072969 + 3 ^ 40 * 4007152 * 2
def baseEnd_4007152 : Nat := 2057595031625411233071449

theorem tailTrace_4007152 : CollatzResearch.WordTrace tailWord_4007152 prefixEnd_4007152 2057595031625411233071449 := by
  unfold tailWord_4007152
  simp only [CollatzResearch.WordTrace]
  refine ⟨73076420189390072960731855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97435226919186763947642473 73076420189390072960731855)
  ·
    refine ⟨109614630284085109441097783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73076420189390072960731855 109614630284085109441097783)
    ·
      refine ⟨164421945426127664161646675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109614630284085109441097783 164421945426127664161646675)
      ·
        refine ⟨246632918139191496242470013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164421945426127664161646675 246632918139191496242470013)
        ·
          refine ⟨92487344302196811090926255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246632918139191496242470013 92487344302196811090926255)
          ·
            refine ⟨138731016453295216636389383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92487344302196811090926255 138731016453295216636389383)
            ·
              refine ⟨208096524679942824954584075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138731016453295216636389383 208096524679942824954584075)
              ·
                refine ⟨312144787019914237431876113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208096524679942824954584075 312144787019914237431876113)
                ·
                  refine ⟨234108590264935678073907085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312144787019914237431876113 234108590264935678073907085)
                  ·
                    refine ⟨87790721349350879277715157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234108590264935678073907085 87790721349350879277715157)
                    ·
                      refine ⟨2057595031625411233071449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87790721349350879277715157 2057595031625411233071449)
                      ·
                        rfl

theorem cell23_4007152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_4007152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007152 prefixEnd_4007152 := by exact prefixLift 4007152
  have htrace : WordTrace (prefixWord ++ tailWord_4007152) baseStart_4007152 baseEnd_4007152 := by
    simpa [prefixWord, tailWord_4007152, baseEnd_4007152] using wordTrace_append hprefix tailTrace_4007152
  have hstable : (prefixWord ++ tailWord_4007152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007152).length < 2 ^ (prefixWord ++ tailWord_4007152).sum := by decide
  have hdescent : baseEnd_4007152 < baseStart_4007152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007200 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 1, 3, 2]
def baseStart_4007200 : Nat := 118140960795 + 4007200 * 2 ^ 59
def prefixEnd_4007200 : Nat := 4983230072969 + 3 ^ 40 * 4007200 * 2
def baseEnd_4007200 : Nat := 2057619678696827045271229

theorem tailTrace_4007200 : CollatzResearch.WordTrace tailWord_4007200 prefixEnd_4007200 2057619678696827045271229 := by
  unfold tailWord_4007200
  simp only [CollatzResearch.WordTrace]
  refine ⟨73077295541303125059605527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97436394055070833412807369 73077295541303125059605527)
  ·
    refine ⟨109615943311954687589408291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73077295541303125059605527 109615943311954687589408291)
    ·
      refine ⟨164423914967932031384112437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109615943311954687589408291 164423914967932031384112437)
      ·
        refine ⟨15414742028243627942260541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164423914967932031384112437 15414742028243627942260541)
        ·
          refine ⟨5780528260591360478347703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15414742028243627942260541 5780528260591360478347703)
          ·
            refine ⟨8670792390887040717521555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780528260591360478347703 8670792390887040717521555)
            ·
              refine ⟨13006188586330561076282333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670792390887040717521555 13006188586330561076282333)
              ·
                refine ⟨4877320719873960403605875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13006188586330561076282333 4877320719873960403605875)
                ·
                  refine ⟨7315981079810940605408813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877320719873960403605875 7315981079810940605408813)
                  ·
                    refine ⟨2743492904929102727028305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7315981079810940605408813 2743492904929102727028305)
                    ·
                      refine ⟨2057619678696827045271229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743492904929102727028305 2057619678696827045271229)
                      ·
                        rfl

theorem cell23_4007200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_4007200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007200 prefixEnd_4007200 := by exact prefixLift 4007200
  have htrace : WordTrace (prefixWord ++ tailWord_4007200) baseStart_4007200 baseEnd_4007200 := by
    simpa [prefixWord, tailWord_4007200, baseEnd_4007200] using wordTrace_append hprefix tailTrace_4007200
  have hstable : (prefixWord ++ tailWord_4007200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007200).length < 2 ^ (prefixWord ++ tailWord_4007200).sum := by decide
  have hdescent : baseEnd_4007200 < baseStart_4007200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007219 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 7]
def baseStart_4007219 : Nat := 118140960795 + 4007219 * 2 ^ 59
def prefixEnd_4007219 : Nat := 4983230072969 + 3 ^ 40 * 4007219 * 2
def baseEnd_4007219 : Nat := 228625492758806941214849

theorem tailTrace_4007219 : CollatzResearch.WordTrace tailWord_4007219 prefixEnd_4007219 228625492758806941214849 := by
  unfold tailWord_4007219
  simp only [CollatzResearch.WordTrace]
  refine ⟨146155284069537416364152711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97436856046358277576101807 146155284069537416364152711)
  ·
    refine ⟨219232926104306124546229067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146155284069537416364152711 219232926104306124546229067)
    ·
      refine ⟨328849389156459186819343601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219232926104306124546229067 328849389156459186819343601)
      ·
        refine ⟨246637041867344390114507701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328849389156459186819343601 246637041867344390114507701)
        ·
          refine ⟨23122222675063536573235097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246637041867344390114507701 23122222675063536573235097)
          ·
            refine ⟨17341667006297652429926323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23122222675063536573235097 17341667006297652429926323)
            ·
              refine ⟨26012500509446478644889485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17341667006297652429926323 26012500509446478644889485)
              ·
                refine ⟨9754687691042429491833557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26012500509446478644889485 9754687691042429491833557)
                ·
                  refine ⟨228625492758806941214849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9754687691042429491833557 228625492758806941214849)
                  ·
                    rfl

theorem cell23_4007219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 7].length) (baseStart_4007219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007219 prefixEnd_4007219 := by exact prefixLift 4007219
  have htrace : WordTrace (prefixWord ++ tailWord_4007219) baseStart_4007219 baseEnd_4007219 := by
    simpa [prefixWord, tailWord_4007219, baseEnd_4007219] using wordTrace_append hprefix tailTrace_4007219
  have hstable : (prefixWord ++ tailWord_4007219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007219).length < 2 ^ (prefixWord ++ tailWord_4007219).sum := by decide
  have hdescent : baseEnd_4007219 < baseStart_4007219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007249 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_4007249 : Nat := 118140960795 + 4007249 * 2 ^ 59
def prefixEnd_4007249 : Nat := 4983230072969 + 3 ^ 40 * 4007249 * 2
def baseEnd_4007249 : Nat := 685881613082965784519501

theorem tailTrace_4007249 : CollatzResearch.WordTrace tailWord_4007249 prefixEnd_4007249 685881613082965784519501 := by
  unfold tailWord_4007249
  simp only [CollatzResearch.WordTrace]
  refine ⟨146156378259428731487744801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97437585506285820991829867 146156378259428731487744801)
  ·
    refine ⟨109617283694571548615808601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146156378259428731487744801 109617283694571548615808601)
    ·
      refine ⟨82212962770928661461856451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109617283694571548615808601 82212962770928661461856451)
      ·
        refine ⟨123319444156392992192784677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82212962770928661461856451 123319444156392992192784677)
        ·
          refine ⟨23122395779323686036147127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123319444156392992192784677 23122395779323686036147127)
          ·
            refine ⟨34683593668985529054220691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23122395779323686036147127 34683593668985529054220691)
            ·
              refine ⟨52025390503478293581331037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34683593668985529054220691 52025390503478293581331037)
              ·
                refine ⟨19509521438804360092999139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52025390503478293581331037 19509521438804360092999139)
                ·
                  refine ⟨29264282158206540139498709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19509521438804360092999139 29264282158206540139498709)
                  ·
                    refine ⟨685881613082965784519501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29264282158206540139498709 685881613082965784519501)
                    ·
                      rfl

theorem cell23_4007249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_4007249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007249 prefixEnd_4007249 := by exact prefixLift 4007249
  have htrace : WordTrace (prefixWord ++ tailWord_4007249) baseStart_4007249 baseEnd_4007249 := by
    simpa [prefixWord, tailWord_4007249, baseEnd_4007249] using wordTrace_append hprefix tailTrace_4007249
  have hstable : (prefixWord ++ tailWord_4007249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007249).length < 2 ^ (prefixWord ++ tailWord_4007249).sum := by decide
  have hdescent : baseEnd_4007249 < baseStart_4007249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007253 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 5]
def baseStart_4007253 : Nat := 118140960795 + 4007253 * 2 ^ 59
def prefixEnd_4007253 : Nat := 4983230072969 + 3 ^ 40 * 4007253 * 2
def baseEnd_4007253 : Nat := 228627432574612815323165

theorem tailTrace_4007253 : CollatzResearch.WordTrace tailWord_4007253 prefixEnd_4007253 228627432574612815323165 := by
  unfold tailWord_4007253
  simp only [CollatzResearch.WordTrace]
  refine ⟨146156524151414240170890413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97437682767609493447260275 146156524151414240170890413)
  ·
    refine ⟨54808696556780340064083905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146156524151414240170890413 54808696556780340064083905)
    ·
      refine ⟨41106522417585255048062929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54808696556780340064083905 41106522417585255048062929)
      ·
        refine ⟨30829891813188941286047197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41106522417585255048062929 30829891813188941286047197)
        ·
          refine ⟨11561209429945852982267699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30829891813188941286047197 11561209429945852982267699)
          ·
            refine ⟨17341814144918779473401549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561209429945852982267699 17341814144918779473401549)
            ·
              refine ⟨6503180304344542302525581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17341814144918779473401549 6503180304344542302525581)
              ·
                refine ⟨2438692614129203363447093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6503180304344542302525581 2438692614129203363447093)
                ·
                  refine ⟨228627432574612815323165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2438692614129203363447093 228627432574612815323165)
                  ·
                    rfl

theorem cell23_4007253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_4007253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007253 prefixEnd_4007253 := by exact prefixLift 4007253
  have htrace : WordTrace (prefixWord ++ tailWord_4007253) baseStart_4007253 baseEnd_4007253 := by
    simpa [prefixWord, tailWord_4007253, baseEnd_4007253] using wordTrace_append hprefix tailTrace_4007253
  have hstable : (prefixWord ++ tailWord_4007253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007253).length < 2 ^ (prefixWord ++ tailWord_4007253).sum := by decide
  have hdescent : baseEnd_4007253 < baseStart_4007253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007276 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_4007276 : Nat := 118140960795 + 4007276 * 2 ^ 59
def prefixEnd_4007276 : Nat := 4983230072969 + 3 ^ 40 * 4007276 * 2
def baseEnd_4007276 : Nat := 2057658703226568747920879

theorem tailTrace_4007276 : CollatzResearch.WordTrace tailWord_4007276 prefixEnd_4007276 2057658703226568747920879 := by
  unfold tailWord_4007276
  simp only [CollatzResearch.WordTrace]
  refine ⟨73078681515165457549488841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97438242020220610065985121 73078681515165457549488841)
  ·
    refine ⟨54809011136374093162116631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73078681515165457549488841 54809011136374093162116631)
    ·
      refine ⟨82213516704561139743174947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54809011136374093162116631 82213516704561139743174947)
      ·
        refine ⟨123320275056841709614762421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82213516704561139743174947 123320275056841709614762421)
        ·
          refine ⟨11561275786578910276383977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123320275056841709614762421 11561275786578910276383977)
          ·
            refine ⟨8670956839934182707287983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11561275786578910276383977 8670956839934182707287983)
            ·
              refine ⟨13006435259901274060931975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670956839934182707287983 13006435259901274060931975)
              ·
                refine ⟨19509652889851911091397963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13006435259901274060931975 19509652889851911091397963)
                ·
                  refine ⟨29264479334777866637096945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19509652889851911091397963 29264479334777866637096945)
                  ·
                    refine ⟨21948359501083399977822709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29264479334777866637096945 21948359501083399977822709)
                    ·
                      refine ⟨2057658703226568747920879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21948359501083399977822709 2057658703226568747920879)
                      ·
                        rfl

theorem cell23_4007276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_4007276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007276 prefixEnd_4007276 := by exact prefixLift 4007276
  have htrace : WordTrace (prefixWord ++ tailWord_4007276) baseStart_4007276 baseEnd_4007276 := by
    simpa [prefixWord, tailWord_4007276, baseEnd_4007276] using wordTrace_append hprefix tailTrace_4007276
  have hstable : (prefixWord ++ tailWord_4007276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007276).length < 2 ^ (prefixWord ++ tailWord_4007276).sum := by decide
  have hdescent : baseEnd_4007276 < baseStart_4007276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007296 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 3, 4]
def baseStart_4007296 : Nat := 118140960795 + 4007296 * 2 ^ 59
def prefixEnd_4007296 : Nat := 4983230072969 + 3 ^ 40 * 4007296 * 2
def baseEnd_4007296 : Nat := 685889657613219556556929

theorem tailTrace_4007296 : CollatzResearch.WordTrace tailWord_4007296 prefixEnd_4007296 685889657613219556556929 := by
  unfold tailWord_4007296
  simp only [CollatzResearch.WordTrace]
  refine ⟨73079046245129229257352871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97438728326838972343137161 73079046245129229257352871)
  ·
    refine ⟨109618569367693843886029307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73079046245129229257352871 109618569367693843886029307)
    ·
      refine ⟨164427854051540765829043961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109618569367693843886029307 164427854051540765829043961)
      ·
        refine ⟨123320890538655574371782971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164427854051540765829043961 123320890538655574371782971)
        ·
          refine ⟨184981335807983361557674457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123320890538655574371782971 184981335807983361557674457)
          ·
            refine ⟨138736001855987521168255843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184981335807983361557674457 138736001855987521168255843)
            ·
              refine ⟨208104002783981281752383765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138736001855987521168255843 208104002783981281752383765)
              ·
                refine ⟨9754875130499122582142989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208104002783981281752383765 9754875130499122582142989)
                ·
                  refine ⟨3658078173937170968303621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9754875130499122582142989 3658078173937170968303621)
                  ·
                    refine ⟨685889657613219556556929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658078173937170968303621 685889657613219556556929)
                    ·
                      rfl

theorem cell23_4007296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_4007296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007296 prefixEnd_4007296 := by exact prefixLift 4007296
  have htrace : WordTrace (prefixWord ++ tailWord_4007296) baseStart_4007296 baseEnd_4007296 := by
    simpa [prefixWord, tailWord_4007296, baseEnd_4007296] using wordTrace_append hprefix tailTrace_4007296
  have hstable : (prefixWord ++ tailWord_4007296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007296).length < 2 ^ (prefixWord ++ tailWord_4007296).sum := by decide
  have hdescent : baseEnd_4007296 < baseStart_4007296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007303 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_4007303 : Nat := 118140960795 + 4007303 * 2 ^ 59
def prefixEnd_4007303 : Nat := 4983230072969 + 3 ^ 40 * 4007303 * 2
def baseEnd_4007303 : Nat := 2057672567204240142283255

theorem tailTrace_4007303 : CollatzResearch.WordTrace tailWord_4007303 prefixEnd_4007303 2057672567204240142283255 := by
  unfold tailWord_4007303
  simp only [CollatzResearch.WordTrace]
  refine ⟨146158347801233098710210563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97438898534155399140140375 146158347801233098710210563)
  ·
    refine ⟨219237521701849648065315845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146158347801233098710210563 219237521701849648065315845)
    ·
      refine ⟨41107035319096809012246721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219237521701849648065315845 41107035319096809012246721)
      ·
        refine ⟨30830276489322606759185041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41107035319096809012246721 30830276489322606759185041)
        ·
          refine ⟨23122707366991955069388781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30830276489322606759185041 23122707366991955069388781)
          ·
            refine ⟨8671015262621983151020793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23122707366991955069388781 8671015262621983151020793)
            ·
              refine ⟨6503261446966487363265595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671015262621983151020793 6503261446966487363265595)
              ·
                refine ⟨9754892170449731044898393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503261446966487363265595 9754892170449731044898393)
                ·
                  refine ⟨7316169127837298283673795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9754892170449731044898393 7316169127837298283673795)
                  ·
                    refine ⟨10974253691755947425510693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7316169127837298283673795 10974253691755947425510693)
                    ·
                      refine ⟨2057672567204240142283255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10974253691755947425510693 2057672567204240142283255)
                      ·
                        rfl

theorem cell23_4007303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_4007303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007303 prefixEnd_4007303 := by exact prefixLift 4007303
  have htrace : WordTrace (prefixWord ++ tailWord_4007303) baseStart_4007303 baseEnd_4007303 := by
    simpa [prefixWord, tailWord_4007303, baseEnd_4007303] using wordTrace_append hprefix tailTrace_4007303
  have hstable : (prefixWord ++ tailWord_4007303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007303).length < 2 ^ (prefixWord ++ tailWord_4007303).sum := by decide
  have hdescent : baseEnd_4007303 < baseStart_4007303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007410 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4007410 : Nat := 118140960795 + 4007410 * 2 ^ 59
def prefixEnd_4007410 : Nat := 4983230072969 + 3 ^ 40 * 4007410 * 2
def baseEnd_4007410 : Nat := 2057727509634271223645263

theorem tailTrace_4007410 : CollatzResearch.WordTrace tailWord_4007410 prefixEnd_4007410 2057727509634271223645263 := by
  unfold tailWord_4007410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36540562602961363996088921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97441500274563637322903789 36540562602961363996088921)
  ·
    refine ⟨27405421952221022997066691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36540562602961363996088921 27405421952221022997066691)
    ·
      refine ⟨41108132928331534495600037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27405421952221022997066691 41108132928331534495600037)
      ·
        refine ⟨7707774924062162717925007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41108132928331534495600037 7707774924062162717925007)
        ·
          refine ⟨11561662386093244076887511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707774924062162717925007 11561662386093244076887511)
          ·
            refine ⟨17342493579139866115331267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561662386093244076887511 17342493579139866115331267)
            ·
              refine ⟨26013740368709799172996901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342493579139866115331267 26013740368709799172996901)
              ·
                refine ⟨4877576319133087344936919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26013740368709799172996901 4877576319133087344936919)
                ·
                  refine ⟨7316364478699631017405379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877576319133087344936919 7316364478699631017405379)
                  ·
                    refine ⟨10974546718049446526108069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7316364478699631017405379 10974546718049446526108069)
                    ·
                      refine ⟨2057727509634271223645263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10974546718049446526108069 2057727509634271223645263)
                      ·
                        rfl

theorem cell23_4007410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4007410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007410 prefixEnd_4007410 := by exact prefixLift 4007410
  have htrace : WordTrace (prefixWord ++ tailWord_4007410) baseStart_4007410 baseEnd_4007410 := by
    simpa [prefixWord, tailWord_4007410, baseEnd_4007410] using wordTrace_append hprefix tailTrace_4007410
  have hstable : (prefixWord ++ tailWord_4007410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007410).length < 2 ^ (prefixWord ++ tailWord_4007410).sum := by decide
  have hdescent : baseEnd_4007410 < baseStart_4007410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007416 : List Nat := [2, 1, 2, 1, 1, 6, 1, 9]
def baseStart_4007416 : Nat := 118140960795 + 4007416 * 2 ^ 59
def prefixEnd_4007416 : Nat := 4983230072969 + 3 ^ 40 * 4007416 * 2
def baseEnd_4007416 : Nat := 76212244093266600006305

theorem tailTrace_4007416 : CollatzResearch.WordTrace tailWord_4007416 prefixEnd_4007416 76212244093266600006305 := by
  unfold tailWord_4007416
  simp only [CollatzResearch.WordTrace]
  refine ⟨73081234624911859504537051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97441646166549146006049401 73081234624911859504537051)
  ·
    refine ⟨109621851937367789256805577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73081234624911859504537051 109621851937367789256805577)
    ·
      refine ⟨82216388953025841942604183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109621851937367789256805577 82216388953025841942604183)
      ·
        refine ⟨123324583429538762913906275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82216388953025841942604183 123324583429538762913906275)
        ·
          refine ⟨184986875144308144370859413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123324583429538762913906275 184986875144308144370859413)
          ·
            refine ⟨8671259772389444267384035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184986875144308144370859413 8671259772389444267384035)
            ·
              refine ⟨13006889658584166401076053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671259772389444267384035 13006889658584166401076053)
              ·
                refine ⟨76212244093266600006305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13006889658584166401076053 76212244093266600006305)
                ·
                  rfl

theorem cell23_4007416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 9].length) (baseStart_4007416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007416 prefixEnd_4007416 := by exact prefixLift 4007416
  have htrace : WordTrace (prefixWord ++ tailWord_4007416) baseStart_4007416 baseEnd_4007416 := by
    simpa [prefixWord, tailWord_4007416, baseEnd_4007416] using wordTrace_append hprefix tailTrace_4007416
  have hstable : (prefixWord ++ tailWord_4007416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007416).length < 2 ^ (prefixWord ++ tailWord_4007416).sum := by decide
  have hdescent : baseEnd_4007416 < baseStart_4007416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007427 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 1, 2, 2]
def baseStart_4007427 : Nat := 118140960795 + 4007427 * 2 ^ 59
def prefixEnd_4007427 : Nat := 4983230072969 + 3 ^ 40 * 4007427 * 2
def baseEnd_4007427 : Nat := 2057736238805397657132685

theorem tailTrace_4007427 : CollatzResearch.WordTrace tailWord_4007427 prefixEnd_4007427 2057736238805397657132685 := by
  unfold tailWord_4007427
  simp only [CollatzResearch.WordTrace]
  refine ⟨146162870452783867887724535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97441913635189245258483023 146162870452783867887724535)
  ·
    refine ⟨219244305679175801831586803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146162870452783867887724535 219244305679175801831586803)
    ·
      refine ⟨328866458518763702747380205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219244305679175801831586803 328866458518763702747380205)
      ·
        refine ⟨123324921944536388530267577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328866458518763702747380205 123324921944536388530267577)
        ·
          refine ⟨92493691458402291397700683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123324921944536388530267577 92493691458402291397700683)
          ·
            refine ⟨138740537187603437096551025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92493691458402291397700683 138740537187603437096551025)
            ·
              refine ⟨104055402890702577822413269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138740537187603437096551025 104055402890702577822413269)
              ·
                refine ⟨2438798505250841667712811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104055402890702577822413269 2438798505250841667712811)
                ·
                  refine ⟨3658197757876262501569217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438798505250841667712811 3658197757876262501569217)
                  ·
                    refine ⟨2743648318407196876176913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3658197757876262501569217 2743648318407196876176913)
                    ·
                      refine ⟨2057736238805397657132685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743648318407196876176913 2057736238805397657132685)
                      ·
                        rfl

theorem cell23_4007427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_4007427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007427 prefixEnd_4007427 := by exact prefixLift 4007427
  have htrace : WordTrace (prefixWord ++ tailWord_4007427) baseStart_4007427 baseEnd_4007427 := by
    simpa [prefixWord, tailWord_4007427, baseEnd_4007427] using wordTrace_append hprefix tailTrace_4007427
  have hstable : (prefixWord ++ tailWord_4007427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007427).length < 2 ^ (prefixWord ++ tailWord_4007427).sum := by decide
  have hdescent : baseEnd_4007427 < baseStart_4007427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007464 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4007464 : Nat := 118140960795 + 4007464 * 2 ^ 59
def prefixEnd_4007464 : Nat := 4983230072969 + 3 ^ 40 * 4007464 * 2
def baseEnd_4007464 : Nat := 2057755237589614012370015

theorem tailTrace_4007464 : CollatzResearch.WordTrace tailWord_4007464 prefixEnd_4007464 2057755237589614012370015 := by
  unfold tailWord_4007464
  simp only [CollatzResearch.WordTrace]
  refine ⟨73082109976824911603410723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97442813302433215471214297 73082109976824911603410723)
  ·
    refine ⟨109623164965237367405116085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73082109976824911603410723 109623164965237367405116085)
    ·
      refine ⟨10277171715491003194229633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109623164965237367405116085 10277171715491003194229633)
      ·
        refine ⟨7707878786618252395672225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10277171715491003194229633 7707878786618252395672225)
        ·
          refine ⟨5780909089963689296754169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7707878786618252395672225 5780909089963689296754169)
          ·
            refine ⟨4335681817472766972565627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5780909089963689296754169 4335681817472766972565627)
            ·
              refine ⟨6503522726209150458848441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335681817472766972565627 6503522726209150458848441)
              ·
                refine ⟨4877642044656862844136331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503522726209150458848441 4877642044656862844136331)
                ·
                  refine ⟨7316463066985294266204497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877642044656862844136331 7316463066985294266204497)
                  ·
                    refine ⟨5487347300238970699653373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7316463066985294266204497 5487347300238970699653373)
                    ·
                      refine ⟨2057755237589614012370015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5487347300238970699653373 2057755237589614012370015)
                      ·
                        rfl

theorem cell23_4007464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4007464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007464 prefixEnd_4007464 := by exact prefixLift 4007464
  have htrace : WordTrace (prefixWord ++ tailWord_4007464) baseStart_4007464 baseEnd_4007464 := by
    simpa [prefixWord, tailWord_4007464, baseEnd_4007464] using wordTrace_append hprefix tailTrace_4007464
  have hstable : (prefixWord ++ tailWord_4007464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007464).length < 2 ^ (prefixWord ++ tailWord_4007464).sum := by decide
  have hdescent : baseEnd_4007464 < baseStart_4007464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007496 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_4007496 : Nat := 118140960795 + 4007496 * 2 ^ 59
def prefixEnd_4007496 : Nat := 4983230072969 + 3 ^ 40 * 4007496 * 2
def baseEnd_4007496 : Nat := 2057771668970557887169867

theorem tailTrace_4007496 : CollatzResearch.WordTrace tailWord_4007496 prefixEnd_4007496 2057771668970557887169867 := by
  unfold tailWord_4007496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73082693544766946335993171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97443591393022595114657561 73082693544766946335993171)
  ·
    refine ⟨109624040317150419503989757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73082693544766946335993171 109624040317150419503989757)
    ·
      refine ⟨41109015118931407313996159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109624040317150419503989757 41109015118931407313996159)
      ·
        refine ⟨61663522678397110970994239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41109015118931407313996159 61663522678397110970994239)
        ·
          refine ⟨92495284017595666456491359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61663522678397110970994239 92495284017595666456491359)
          ·
            refine ⟨138742926026393499684737039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92495284017595666456491359 138742926026393499684737039)
            ·
              refine ⟨208114389039590249527105559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138742926026393499684737039 208114389039590249527105559)
              ·
                refine ⟨312171583559385374290658339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208114389039590249527105559 312171583559385374290658339)
                ·
                  refine ⟨468257375339078061435987509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312171583559385374290658339 468257375339078061435987509)
                  ·
                    refine ⟨43899128938038568259623829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 468257375339078061435987509 43899128938038568259623829)
                    ·
                      refine ⟨2057771668970557887169867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43899128938038568259623829 2057771668970557887169867)
                      ·
                        rfl

theorem cell23_4007496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_4007496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007496 prefixEnd_4007496 := by exact prefixLift 4007496
  have htrace : WordTrace (prefixWord ++ tailWord_4007496) baseStart_4007496 baseEnd_4007496 := by
    simpa [prefixWord, tailWord_4007496, baseEnd_4007496] using wordTrace_append hprefix tailTrace_4007496
  have hstable : (prefixWord ++ tailWord_4007496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007496).length < 2 ^ (prefixWord ++ tailWord_4007496).sum := by decide
  have hdescent : baseEnd_4007496 < baseStart_4007496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007523 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 7]
def baseStart_4007523 : Nat := 118140960795 + 4007523 * 2 ^ 59
def prefixEnd_4007523 : Nat := 4983230072969 + 3 ^ 40 * 4007523 * 2
def baseEnd_4007523 : Nat := 228642836994247697948027

theorem tailTrace_4007523 : CollatzResearch.WordTrace tailWord_4007523 prefixEnd_4007523 228642836994247697948027 := by
  unfold tailWord_4007523
  simp only [CollatzResearch.WordTrace]
  refine ⟨146166371860436076283219223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97444247906957384188812815 146166371860436076283219223)
  ·
    refine ⟨219249557790654114424828835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146166371860436076283219223 219249557790654114424828835)
    ·
      refine ⟨328874336685981171637243253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219249557790654114424828835 328874336685981171637243253)
      ·
        refine ⟨30831969064310734840991555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328874336685981171637243253 30831969064310734840991555)
        ·
          refine ⟨46247953596466102261487333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30831969064310734840991555 46247953596466102261487333)
          ·
            refine ⟨8671491299337394174028875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46247953596466102261487333 8671491299337394174028875)
            ·
              refine ⟨13007236949006091261043313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671491299337394174028875 13007236949006091261043313)
              ·
                refine ⟨9755427711754568445782485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13007236949006091261043313 9755427711754568445782485)
                ·
                  refine ⟨228642836994247697948027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9755427711754568445782485 228642836994247697948027)
                  ·
                    rfl

theorem cell23_4007523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 7].length) (baseStart_4007523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007523 prefixEnd_4007523 := by exact prefixLift 4007523
  have htrace : WordTrace (prefixWord ++ tailWord_4007523) baseStart_4007523 baseEnd_4007523 := by
    simpa [prefixWord, tailWord_4007523, baseEnd_4007523] using wordTrace_append hprefix tailTrace_4007523
  have hstable : (prefixWord ++ tailWord_4007523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007523).length < 2 ^ (prefixWord ++ tailWord_4007523).sum := by decide
  have hdescent : baseEnd_4007523 < baseStart_4007523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007593 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_4007593 : Nat := 118140960795 + 4007593 * 2 ^ 59
def prefixEnd_4007593 : Nat := 4983230072969 + 3 ^ 40 * 4007593 * 2
def baseEnd_4007593 : Nat := 2057821476594044007656921

theorem tailTrace_4007593 : CollatzResearch.WordTrace tailWord_4007593 prefixEnd_4007593 2057821476594044007656921 := by
  unfold tailWord_4007593
  simp only [CollatzResearch.WordTrace]
  refine ⟨146168924970182478238267433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97445949980121652158844955 146168924970182478238267433)
  ·
    refine ⟨109626693727636858678700575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146168924970182478238267433 109626693727636858678700575)
    ·
      refine ⟨164440040591455288018050863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109626693727636858678700575 164440040591455288018050863)
      ·
        refine ⟨246660060887182932027076295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164440040591455288018050863 246660060887182932027076295)
        ·
          refine ⟨369990091330774398040614443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246660060887182932027076295 369990091330774398040614443)
          ·
            refine ⟨554985136996161597060921665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369990091330774398040614443 554985136996161597060921665)
            ·
              refine ⟨416238852747121197795691249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554985136996161597060921665 416238852747121197795691249)
              ·
                refine ⟨312179139560340898346768437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416238852747121197795691249 312179139560340898346768437)
                ·
                  refine ⟨29266794333781959220009541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312179139560340898346768437 29266794333781959220009541)
                  ·
                    refine ⟨5487523937584117353751789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29266794333781959220009541 5487523937584117353751789)
                    ·
                      refine ⟨2057821476594044007656921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5487523937584117353751789 2057821476594044007656921)
                      ·
                        rfl

theorem cell23_4007593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_4007593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007593 prefixEnd_4007593 := by exact prefixLift 4007593
  have htrace : WordTrace (prefixWord ++ tailWord_4007593) baseStart_4007593 baseEnd_4007593 := by
    simpa [prefixWord, tailWord_4007593, baseEnd_4007593] using wordTrace_append hprefix tailTrace_4007593
  have hstable : (prefixWord ++ tailWord_4007593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007593).length < 2 ^ (prefixWord ++ tailWord_4007593).sum := by decide
  have hdescent : baseEnd_4007593 < baseStart_4007593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007610 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_4007610 : Nat := 118140960795 + 4007610 * 2 ^ 59
def prefixEnd_4007610 : Nat := 4983230072969 + 3 ^ 40 * 4007610 * 2
def baseEnd_4007610 : Nat := 2057830205765170441144343

theorem tailTrace_4007610 : CollatzResearch.WordTrace tailWord_4007610 prefixEnd_4007610 2057830205765170441144343 := by
  unfold tailWord_4007610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36542386252780222535409071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97446363340747260094424189 36542386252780222535409071)
  ·
    refine ⟨54813579379170333803113607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36542386252780222535409071 54813579379170333803113607)
    ·
      refine ⟨82220369068755500704670411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54813579379170333803113607 82220369068755500704670411)
      ·
        refine ⟨123330553603133251057005617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82220369068755500704670411 123330553603133251057005617)
        ·
          refine ⟨92497915202349938292754213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123330553603133251057005617 92497915202349938292754213)
          ·
            refine ⟨17343359100440613429891415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92497915202349938292754213 17343359100440613429891415)
            ·
              refine ⟨26015038650660920144837123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17343359100440613429891415 26015038650660920144837123)
              ·
                refine ⟨39022557975991380217255685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26015038650660920144837123 39022557975991380217255685)
                ·
                  refine ⟨7316729620498383790735441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39022557975991380217255685 7316729620498383790735441)
                  ·
                    refine ⟨5487547215373787843051581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7316729620498383790735441 5487547215373787843051581)
                    ·
                      refine ⟨2057830205765170441144343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5487547215373787843051581 2057830205765170441144343)
                      ·
                        rfl

theorem cell23_4007610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_4007610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007610 prefixEnd_4007610 := by exact prefixLift 4007610
  have htrace : WordTrace (prefixWord ++ tailWord_4007610) baseStart_4007610 baseEnd_4007610 := by
    simpa [prefixWord, tailWord_4007610, baseEnd_4007610] using wordTrace_append hprefix tailTrace_4007610
  have hstable : (prefixWord ++ tailWord_4007610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007610).length < 2 ^ (prefixWord ++ tailWord_4007610).sum := by decide
  have hdescent : baseEnd_4007610 < baseStart_4007610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007613 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 8]
def baseStart_4007613 : Nat := 118140960795 + 4007613 * 2 ^ 59
def prefixEnd_4007613 : Nat := 4983230072969 + 3 ^ 40 * 4007613 * 2
def baseEnd_4007613 : Nat := 228647971800792658822981

theorem tailTrace_4007613 : CollatzResearch.WordTrace tailWord_4007613 prefixEnd_4007613 228647971800792658822981 := by
  unfold tailWord_4007613
  simp only [CollatzResearch.WordTrace]
  refine ⟨146169654430110021653995493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97446436286740014435996995 146169654430110021653995493)
  ·
    refine ⟨27406810205645629060124155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146169654430110021653995493 27406810205645629060124155)
    ·
      refine ⟨41110215308468443590186233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27406810205645629060124155 41110215308468443590186233)
      ·
        refine ⟨30832661481351332692639675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41110215308468443590186233 30832661481351332692639675)
        ·
          refine ⟨46248992222026999038959513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30832661481351332692639675 46248992222026999038959513)
          ·
            refine ⟨34686744166520249279219635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46248992222026999038959513 34686744166520249279219635)
            ·
              refine ⟨52030116249780373918829453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34686744166520249279219635 52030116249780373918829453)
              ·
                refine ⟨19511293593667640219561045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52030116249780373918829453 19511293593667640219561045)
                ·
                  refine ⟨228647971800792658822981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19511293593667640219561045 228647971800792658822981)
                  ·
                    rfl

theorem cell23_4007613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_4007613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007613 prefixEnd_4007613 := by exact prefixLift 4007613
  have htrace : WordTrace (prefixWord ++ tailWord_4007613) baseStart_4007613 baseEnd_4007613 := by
    simpa [prefixWord, tailWord_4007613, baseEnd_4007613] using wordTrace_append hprefix tailTrace_4007613
  have hstable : (prefixWord ++ tailWord_4007613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007613).length < 2 ^ (prefixWord ++ tailWord_4007613).sum := by decide
  have hdescent : baseEnd_4007613 < baseStart_4007613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007630 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_4007630 : Nat := 118140960795 + 4007630 * 2 ^ 59
def prefixEnd_4007630 : Nat := 4983230072969 + 3 ^ 40 * 4007630 * 2
def baseEnd_4007630 : Nat := 228648941708695595877139

theorem tailTrace_4007630 : CollatzResearch.WordTrace tailWord_4007630 prefixEnd_4007630 228648941708695595877139 := by
  unfold tailWord_4007630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18271284308881054194670543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97446849647365622371576229 18271284308881054194670543)
  ·
    refine ⟨27406926463321581292005815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18271284308881054194670543 27406926463321581292005815)
    ·
      refine ⟨41110389694982371938008723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27406926463321581292005815 41110389694982371938008723)
      ·
        refine ⟨61665584542473557907013085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41110389694982371938008723 61665584542473557907013085)
        ·
          refine ⟨23124594203427584215129907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61665584542473557907013085 23124594203427584215129907)
          ·
            refine ⟨34686891305141376322694861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23124594203427584215129907 34686891305141376322694861)
            ·
              refine ⟨13007584239428016121010573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34686891305141376322694861 13007584239428016121010573)
              ·
                refine ⟨4877844089785506045378965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13007584239428016121010573 4877844089785506045378965)
                ·
                  refine ⟨228648941708695595877139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4877844089785506045378965 228648941708695595877139)
                  ·
                    rfl

theorem cell23_4007630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_4007630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007630 prefixEnd_4007630 := by exact prefixLift 4007630
  have htrace : WordTrace (prefixWord ++ tailWord_4007630) baseStart_4007630 baseEnd_4007630 := by
    simpa [prefixWord, tailWord_4007630, baseEnd_4007630] using wordTrace_append hprefix tailTrace_4007630
  have hstable : (prefixWord ++ tailWord_4007630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007630).length < 2 ^ (prefixWord ++ tailWord_4007630).sum := by decide
  have hdescent : baseEnd_4007630 < baseStart_4007630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007660 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_4007660 : Nat := 118140960795 + 4007660 * 2 ^ 59
def prefixEnd_4007660 : Nat := 4983230072969 + 3 ^ 40 * 4007660 * 2
def baseEnd_4007660 : Nat := 685951959932631748506371

theorem tailTrace_4007660 : CollatzResearch.WordTrace tailWord_4007660 prefixEnd_4007660 685951959932631748506371 := by
  unfold tailWord_4007660
  simp only [CollatzResearch.WordTrace]
  refine ⟨73085684330469874340478217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97447579107293165787304289 73085684330469874340478217)
  ·
    refine ⟨54814263247852405755358663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73085684330469874340478217 54814263247852405755358663)
    ·
      refine ⟨82221394871778608633037995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54814263247852405755358663 82221394871778608633037995)
      ·
        refine ⟨123332092307667912949556993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82221394871778608633037995 123332092307667912949556993)
        ·
          refine ⟨92499069230750934712167745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123332092307667912949556993 92499069230750934712167745)
          ·
            refine ⟨69374301923063201034125809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92499069230750934712167745 69374301923063201034125809)
            ·
              refine ⟨52030726442297400775594357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69374301923063201034125809 52030726442297400775594357)
              ·
                refine ⟨4877880603965381322711971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52030726442297400775594357 4877880603965381322711971)
                ·
                  refine ⟨7316820905948071984067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877880603965381322711971 7316820905948071984067957)
                  ·
                    refine ⟨685951959932631748506371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7316820905948071984067957 685951959932631748506371)
                    ·
                      rfl

theorem cell23_4007660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_4007660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007660 prefixEnd_4007660 := by exact prefixLift 4007660
  have htrace : WordTrace (prefixWord ++ tailWord_4007660) baseStart_4007660 baseEnd_4007660 := by
    simpa [prefixWord, tailWord_4007660, baseEnd_4007660] using wordTrace_append hprefix tailTrace_4007660
  have hstable : (prefixWord ++ tailWord_4007660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007660).length < 2 ^ (prefixWord ++ tailWord_4007660).sum := by decide
  have hdescent : baseEnd_4007660 < baseStart_4007660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007667 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 2, 3, 2]
def baseStart_4007667 : Nat := 118140960795 + 4007667 * 2 ^ 59
def prefixEnd_4007667 : Nat := 4983230072969 + 3 ^ 40 * 4007667 * 2
def baseEnd_4007667 : Nat := 2057859474162476718131581

theorem tailTrace_4007667 : CollatzResearch.WordTrace tailWord_4007667 prefixEnd_4007667 2057859474162476718131581 := by
  unfold tailWord_4007667
  simp only [CollatzResearch.WordTrace]
  refine ⟨146171623971914388876461255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97447749314609592584307503 146171623971914388876461255)
  ·
    refine ⟨219257435957871583314691883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146171623971914388876461255 219257435957871583314691883)
    ·
      refine ⟨328886153936807374972037825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219257435957871583314691883 328886153936807374972037825)
      ·
        refine ⟨246664615452605531229028369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328886153936807374972037825 246664615452605531229028369)
        ·
          refine ⟨184998461589454148421771277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246664615452605531229028369 184998461589454148421771277)
          ·
            refine ⟨69374423096045305658164229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184998461589454148421771277 69374423096045305658164229)
            ·
              refine ⟨13007704330508494810905793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69374423096045305658164229 13007704330508494810905793)
              ·
                refine ⟨9755778247881371108179345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13007704330508494810905793 9755778247881371108179345)
                ·
                  refine ⟨7316833685911028331134509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9755778247881371108179345 7316833685911028331134509)
                  ·
                    refine ⟨2743812632216635624175441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7316833685911028331134509 2743812632216635624175441)
                    ·
                      refine ⟨2057859474162476718131581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743812632216635624175441 2057859474162476718131581)
                      ·
                        rfl

theorem cell23_4007667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3, 2].length) (baseStart_4007667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007667 prefixEnd_4007667 := by exact prefixLift 4007667
  have htrace : WordTrace (prefixWord ++ tailWord_4007667) baseStart_4007667 baseEnd_4007667 := by
    simpa [prefixWord, tailWord_4007667, baseEnd_4007667] using wordTrace_append hprefix tailTrace_4007667
  have hstable : (prefixWord ++ tailWord_4007667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007667).length < 2 ^ (prefixWord ++ tailWord_4007667).sum := by decide
  have hdescent : baseEnd_4007667 < baseStart_4007667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007668 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4007668 : Nat := 118140960795 + 4007668 * 2 ^ 59
def prefixEnd_4007668 : Nat := 4983230072969 + 3 ^ 40 * 4007668 * 2
def baseEnd_4007668 : Nat := 685953329214377071406359

theorem tailTrace_4007668 : CollatzResearch.WordTrace tailWord_4007668 prefixEnd_4007668 685953329214377071406359 := by
  unfold tailWord_4007668
  simp only [CollatzResearch.WordTrace]
  refine ⟨73085830222455383023623829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97447773629940510698165105 73085830222455383023623829)
  ·
    refine ⟨3425898291677596079232367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73085830222455383023623829 3425898291677596079232367)
    ·
      refine ⟨5138847437516394118848551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425898291677596079232367 5138847437516394118848551)
      ·
        refine ⟨7708271156274591178272827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138847437516394118848551 7708271156274591178272827)
        ·
          refine ⟨11562406734411886767409241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708271156274591178272827 11562406734411886767409241)
          ·
            refine ⟨8671805050808915075556931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11562406734411886767409241 8671805050808915075556931)
            ·
              refine ⟨13007707576213372613335397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671805050808915075556931 13007707576213372613335397)
              ·
                refine ⟨2438945170540007365000387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13007707576213372613335397 2438945170540007365000387)
                ·
                  refine ⟨3658417755810011047500581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438945170540007365000387 3658417755810011047500581)
                  ·
                    refine ⟨685953329214377071406359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658417755810011047500581 685953329214377071406359)
                    ·
                      rfl

theorem cell23_4007668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4007668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007668 prefixEnd_4007668 := by exact prefixLift 4007668
  have htrace : WordTrace (prefixWord ++ tailWord_4007668) baseStart_4007668 baseEnd_4007668 := by
    simpa [prefixWord, tailWord_4007668, baseEnd_4007668] using wordTrace_append hprefix tailTrace_4007668
  have hstable : (prefixWord ++ tailWord_4007668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007668).length < 2 ^ (prefixWord ++ tailWord_4007668).sum := by decide
  have hdescent : baseEnd_4007668 < baseStart_4007668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007690 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_4007690 : Nat := 118140960795 + 4007690 * 2 ^ 59
def prefixEnd_4007690 : Nat := 4983230072969 + 3 ^ 40 * 4007690 * 2
def baseEnd_4007690 : Nat := 685957094739176709381325

theorem tailTrace_4007690 : CollatzResearch.WordTrace tailWord_4007690 prefixEnd_4007690 685957094739176709381325 := by
  unfold tailWord_4007690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36543115712707765951137131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97448308567220709203032349 36543115712707765951137131)
  ·
    refine ⟨54814673569061648926705697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36543115712707765951137131 54814673569061648926705697)
    ·
      refine ⟨41111005176796236695029273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54814673569061648926705697 41111005176796236695029273)
      ·
        refine ⟨30833253882597177521271955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41111005176796236695029273 30833253882597177521271955)
        ·
          refine ⟨46249880823895766281907933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30833253882597177521271955 46249880823895766281907933)
          ·
            refine ⟨17343705308960912355715475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46249880823895766281907933 17343705308960912355715475)
            ·
              refine ⟨26015557963441368533573213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17343705308960912355715475 26015557963441368533573213)
              ·
                refine ⟨9755834236290513200089955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26015557963441368533573213 9755834236290513200089955)
                ·
                  refine ⟨14633751354435769800134933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755834236290513200089955 14633751354435769800134933)
                  ·
                    refine ⟨685957094739176709381325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14633751354435769800134933 685957094739176709381325)
                    ·
                      rfl

theorem cell23_4007690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_4007690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007690 prefixEnd_4007690 := by exact prefixLift 4007690
  have htrace : WordTrace (prefixWord ++ tailWord_4007690) baseStart_4007690 baseEnd_4007690 := by
    simpa [prefixWord, tailWord_4007690, baseEnd_4007690] using wordTrace_append hprefix tailTrace_4007690
  have hstable : (prefixWord ++ tailWord_4007690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007690).length < 2 ^ (prefixWord ++ tailWord_4007690).sum := by decide
  have hdescent : baseEnd_4007690 < baseStart_4007690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007714 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_4007714 : Nat := 118140960795 + 4007714 * 2 ^ 59
def prefixEnd_4007714 : Nat := 4983230072969 + 3 ^ 40 * 4007714 * 2
def baseEnd_4007714 : Nat := 2057883607753238034243865

theorem tailTrace_4007714 : CollatzResearch.WordTrace tailWord_4007714 prefixEnd_4007714 2057883607753238034243865 := by
  unfold tailWord_4007714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36543334550686028975855549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97448892135162743935614797 36543334550686028975855549)
  ·
    refine ⟨13703750456507260865945831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36543334550686028975855549 13703750456507260865945831)
    ·
      refine ⟨20555625684760891298918747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13703750456507260865945831 20555625684760891298918747)
      ·
        refine ⟨30833438527141336948378121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20555625684760891298918747 30833438527141336948378121)
        ·
          refine ⟨23125078895356002711283591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30833438527141336948378121 23125078895356002711283591)
          ·
            refine ⟨34687618343034004066925387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23125078895356002711283591 34687618343034004066925387)
            ·
              refine ⟨52031427514551006100388081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34687618343034004066925387 52031427514551006100388081)
              ·
                refine ⟨39023570635913254575291061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52031427514551006100388081 39023570635913254575291061)
                ·
                  refine ⟨3658459747116867616433537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39023570635913254575291061 3658459747116867616433537)
                  ·
                    refine ⟨2743844810337650712325153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3658459747116867616433537 2743844810337650712325153)
                    ·
                      refine ⟨2057883607753238034243865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743844810337650712325153 2057883607753238034243865)
                      ·
                        rfl

theorem cell23_4007714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_4007714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007714 prefixEnd_4007714 := by exact prefixLift 4007714
  have htrace : WordTrace (prefixWord ++ tailWord_4007714) baseStart_4007714 baseEnd_4007714 := by
    simpa [prefixWord, tailWord_4007714, baseEnd_4007714] using wordTrace_append hprefix tailTrace_4007714
  have hstable : (prefixWord ++ tailWord_4007714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007714).length < 2 ^ (prefixWord ++ tailWord_4007714).sum := by decide
  have hdescent : baseEnd_4007714 < baseStart_4007714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007720 : List Nat := [2, 1, 5, 1, 1, 3, 10]
def baseStart_4007720 : Nat := 118140960795 + 4007720 * 2 ^ 59
def prefixEnd_4007720 : Nat := 4983230072969 + 3 ^ 40 * 4007720 * 2
def baseEnd_4007720 : Nat := 25406008501693395194677

theorem tailTrace_4007720 : CollatzResearch.WordTrace tailWord_4007720 prefixEnd_4007720 25406008501693395194677 := by
  unfold tailWord_4007720
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086778520361189464070307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97449038027148252618760409 73086778520361189464070307)
  ·
    refine ⟨109630167780541784196105461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73086778520361189464070307 109630167780541784196105461)
    ·
      refine ⟨10277828229425792268384887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109630167780541784196105461 10277828229425792268384887)
      ·
        refine ⟨15416742344138688402577331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10277828229425792268384887 15416742344138688402577331)
        ·
          refine ⟨23125113516208032603865997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15416742344138688402577331 23125113516208032603865997)
          ·
            refine ⟨8671917568578012226449749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23125113516208032603865997 8671917568578012226449749)
            ·
              refine ⟨25406008501693395194677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8671917568578012226449749 25406008501693395194677)
              ·
                rfl

theorem cell23_4007720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 10].length) (baseStart_4007720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007720 prefixEnd_4007720 := by exact prefixLift 4007720
  have htrace : WordTrace (prefixWord ++ tailWord_4007720) baseStart_4007720 baseEnd_4007720 := by
    simpa [prefixWord, tailWord_4007720, baseEnd_4007720] using wordTrace_append hprefix tailTrace_4007720
  have hstable : (prefixWord ++ tailWord_4007720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007720).length < 2 ^ (prefixWord ++ tailWord_4007720).sum := by decide
  have hdescent : baseEnd_4007720 < baseStart_4007720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007724 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_4007724 : Nat := 118140960795 + 4007724 * 2 ^ 59
def prefixEnd_4007724 : Nat := 4983230072969 + 3 ^ 40 * 4007724 * 2
def baseEnd_4007724 : Nat := 685962914186594331706273

theorem tailTrace_4007724 : CollatzResearch.WordTrace tailWord_4007724 prefixEnd_4007724 685962914186594331706273 := by
  unfold tailWord_4007724
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086851466353943805643113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97449135288471925074190817 73086851466353943805643113)
  ·
    refine ⟨54815138599765457854232335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73086851466353943805643113 54815138599765457854232335)
    ·
      refine ⟨82222707899648186781348503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54815138599765457854232335 82222707899648186781348503)
      ·
        refine ⟨123334061849472280172022755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82222707899648186781348503 123334061849472280172022755)
        ·
          refine ⟨185001092774208420258034133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123334061849472280172022755 185001092774208420258034133)
          ·
            refine ⟨4335963111895509849797675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 185001092774208420258034133 4335963111895509849797675)
            ·
              refine ⟨6503944667843264774696513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335963111895509849797675 6503944667843264774696513)
              ·
                refine ⟨4877958500882448581022385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503944667843264774696513 4877958500882448581022385)
                ·
                  refine ⟨3658468875661836435766789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4877958500882448581022385 3658468875661836435766789)
                  ·
                    refine ⟨685962914186594331706273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658468875661836435766789 685962914186594331706273)
                    ·
                      rfl

theorem cell23_4007724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_4007724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007724 prefixEnd_4007724 := by exact prefixLift 4007724
  have htrace : WordTrace (prefixWord ++ tailWord_4007724) baseStart_4007724 baseEnd_4007724 := by
    simpa [prefixWord, tailWord_4007724, baseEnd_4007724] using wordTrace_append hprefix tailTrace_4007724
  have hstable : (prefixWord ++ tailWord_4007724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007724).length < 2 ^ (prefixWord ++ tailWord_4007724).sum := by decide
  have hdescent : baseEnd_4007724 < baseStart_4007724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007731 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 3, 2, 2]
def baseStart_4007731 : Nat := 118140960795 + 4007731 * 2 ^ 59
def prefixEnd_4007731 : Nat := 4983230072969 + 3 ^ 40 * 4007731 * 2
def baseEnd_4007731 : Nat := 2057892336924364467731287

theorem tailTrace_4007731 : CollatzResearch.WordTrace tailWord_4007731 prefixEnd_4007731 2057892336924364467731287 := by
  unfold tailWord_4007731
  simp only [CollatzResearch.WordTrace]
  refine ⟨146173958243682527806791047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97449305495788351871194031 146173958243682527806791047)
  ·
    refine ⟨219260937365523791710186571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146173958243682527806791047 219260937365523791710186571)
    ·
      refine ⟨328891406048285687565279857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219260937365523791710186571 328891406048285687565279857)
      ·
        refine ⟨246668554536214265673959893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328891406048285687565279857 246668554536214265673959893)
        ·
          refine ⟨5781294246942521851733435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 246668554536214265673959893 5781294246942521851733435)
          ·
            refine ⟨8671941370413782777600153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781294246942521851733435 8671941370413782777600153)
            ·
              refine ⟨6503956027810337083200115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671941370413782777600153 6503956027810337083200115)
              ·
                refine ⟨9755934041715505624800173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503956027810337083200115 9755934041715505624800173)
                ·
                  refine ⟨3658475265643314609300065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9755934041715505624800173 3658475265643314609300065)
                  ·
                    refine ⟨2743856449232485956975049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3658475265643314609300065 2743856449232485956975049)
                    ·
                      refine ⟨2057892336924364467731287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2743856449232485956975049 2057892336924364467731287)
                      ·
                        rfl

theorem cell23_4007731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 2, 2].length) (baseStart_4007731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007731 prefixEnd_4007731 := by exact prefixLift 4007731
  have htrace : WordTrace (prefixWord ++ tailWord_4007731) baseStart_4007731 baseEnd_4007731 := by
    simpa [prefixWord, tailWord_4007731, baseEnd_4007731] using wordTrace_append hprefix tailTrace_4007731
  have hstable : (prefixWord ++ tailWord_4007731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007731).length < 2 ^ (prefixWord ++ tailWord_4007731).sum := by decide
  have hdescent : baseEnd_4007731 < baseStart_4007731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007734 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4007734 : Nat := 118140960795 + 4007734 * 2 ^ 59
def prefixEnd_4007734 : Nat := 4983230072969 + 3 ^ 40 * 4007734 * 2
def baseEnd_4007734 : Nat := 2057893877366327955993773

theorem tailTrace_4007734 : CollatzResearch.WordTrace tailWord_4007734 prefixEnd_4007734 2057893877366327955993773 := by
  unfold tailWord_4007734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9135879228916978707446891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97449378441781106212766837 9135879228916978707446891)
  ·
    refine ⟨13703818843375468061170337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9135879228916978707446891 13703818843375468061170337)
    ·
      refine ⟨10277864132531601045877753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13703818843375468061170337 10277864132531601045877753)
      ·
        refine ⟨7708398099398700784408315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10277864132531601045877753 7708398099398700784408315)
        ·
          refine ⟨11562597149098051176612473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708398099398700784408315 11562597149098051176612473)
          ·
            refine ⟨8671947861823538382459355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11562597149098051176612473 8671947861823538382459355)
            ·
              refine ⟨13007921792735307573689033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671947861823538382459355 13007921792735307573689033)
              ·
                refine ⟨9755941344551480680266775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13007921792735307573689033 9755941344551480680266775)
                ·
                  refine ⟨14633912016827221020400163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755941344551480680266775 14633912016827221020400163)
                  ·
                    refine ⟨21950868025240831530600245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14633912016827221020400163 21950868025240831530600245)
                    ·
                      refine ⟨2057893877366327955993773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21950868025240831530600245 2057893877366327955993773)
                      ·
                        rfl

theorem cell23_4007734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4007734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007734 prefixEnd_4007734 := by exact prefixLift 4007734
  have htrace : WordTrace (prefixWord ++ tailWord_4007734) baseStart_4007734 baseEnd_4007734 := by
    simpa [prefixWord, tailWord_4007734, baseEnd_4007734] using wordTrace_append hprefix tailTrace_4007734
  have hstable : (prefixWord ++ tailWord_4007734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007734).length < 2 ^ (prefixWord ++ tailWord_4007734).sum := by decide
  have hdescent : baseEnd_4007734 < baseStart_4007734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007741 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_4007741 : Nat := 118140960795 + 4007741 * 2 ^ 59
def prefixEnd_4007741 : Nat := 4983230072969 + 3 ^ 40 * 4007741 * 2
def baseEnd_4007741 : Nat := 685965823910303142868747

theorem tailTrace_4007741 : CollatzResearch.WordTrace tailWord_4007741 prefixEnd_4007741 685965823910303142868747 := by
  unfold tailWord_4007741
  simp only [CollatzResearch.WordTrace]
  refine ⟨146174322973646299514655077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97449548649097533009770051 146174322973646299514655077)
  ·
    refine ⟨27407685557558681158997827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146174322973646299514655077 27407685557558681158997827)
    ·
      refine ⟨41111528336338021738496741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27407685557558681158997827 41111528336338021738496741)
      ·
        refine ⟨7708411563063379075968139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41111528336338021738496741 7708411563063379075968139)
        ·
          refine ⟨11562617344595068613952209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708411563063379075968139 11562617344595068613952209)
          ·
            refine ⟨8671963008446301460464157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11562617344595068613952209 8671963008446301460464157)
            ·
              refine ⟨3251986128167363047674059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8671963008446301460464157 3251986128167363047674059)
              ·
                refine ⟨4877979192251044571511089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251986128167363047674059 4877979192251044571511089)
                ·
                  refine ⟨3658484394188283428633317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4877979192251044571511089 3658484394188283428633317)
                  ·
                    refine ⟨685965823910303142868747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658484394188283428633317 685965823910303142868747)
                    ·
                      rfl

theorem cell23_4007741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_4007741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007741 prefixEnd_4007741 := by exact prefixLift 4007741
  have htrace : WordTrace (prefixWord ++ tailWord_4007741) baseStart_4007741 baseEnd_4007741 := by
    simpa [prefixWord, tailWord_4007741, baseEnd_4007741] using wordTrace_append hprefix tailTrace_4007741
  have hstable : (prefixWord ++ tailWord_4007741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007741).length < 2 ^ (prefixWord ++ tailWord_4007741).sum := by decide
  have hdescent : baseEnd_4007741 < baseStart_4007741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007747 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 3]
def baseStart_4007747 : Nat := 118140960795 + 4007747 * 2 ^ 59
def prefixEnd_4007747 : Nat := 4983230072969 + 3 ^ 40 * 4007747 * 2
def baseEnd_4007747 : Nat := 2057900552614836405131213

theorem tailTrace_4007747 : CollatzResearch.WordTrace tailWord_4007747 prefixEnd_4007747 2057900552614836405131213 := by
  unfold tailWord_4007747
  simp only [CollatzResearch.WordTrace]
  refine ⟨146174541811624562539373495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97449694541083041692915663 146174541811624562539373495)
  ·
    refine ⟨219261812717436843809060243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146174541811624562539373495 219261812717436843809060243)
    ·
      refine ⟨328892719076155265713590365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219261812717436843809060243 328892719076155265713590365)
      ·
        refine ⟨123334769653558224642596387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328892719076155265713590365 123334769653558224642596387)
        ·
          refine ⟨185002154480337336963894581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123334769653558224642596387 185002154480337336963894581)
          ·
            refine ⟨17343951982531625340365117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185002154480337336963894581 17343951982531625340365117)
            ·
              refine ⟨6503981993449359502636919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17343951982531625340365117 6503981993449359502636919)
              ·
                refine ⟨9755972990174039253955379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503981993449359502636919 9755972990174039253955379)
                ·
                  refine ⟨14633959485261058880933069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755972990174039253955379 14633959485261058880933069)
                  ·
                    refine ⟨5487734806972897080349901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14633959485261058880933069 5487734806972897080349901)
                    ·
                      refine ⟨2057900552614836405131213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5487734806972897080349901 2057900552614836405131213)
                      ·
                        rfl

theorem cell23_4007747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_4007747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007747 prefixEnd_4007747 := by exact prefixLift 4007747
  have htrace : WordTrace (prefixWord ++ tailWord_4007747) baseStart_4007747 baseEnd_4007747 := by
    simpa [prefixWord, tailWord_4007747, baseEnd_4007747] using wordTrace_append hprefix tailTrace_4007747
  have hstable : (prefixWord ++ tailWord_4007747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007747).length < 2 ^ (prefixWord ++ tailWord_4007747).sum := by decide
  have hdescent : baseEnd_4007747 < baseStart_4007747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007764 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_4007764 : Nat := 118140960795 + 4007764 * 2 ^ 59
def prefixEnd_4007764 : Nat := 4983230072969 + 3 ^ 40 * 4007764 * 2
def baseEnd_4007764 : Nat := 2057909281785962838618635

theorem tailTrace_4007764 : CollatzResearch.WordTrace tailWord_4007764 prefixEnd_4007764 2057909281785962838618635 := by
  unfold tailWord_4007764
  simp only [CollatzResearch.WordTrace]
  refine ⟨73087580926281487221371173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97450107901708649628494897 73087580926281487221371173)
  ·
    refine ⟨13703921423677778854007095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73087580926281487221371173 13703921423677778854007095)
    ·
      refine ⟨20555882135516668281010643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13703921423677778854007095 20555882135516668281010643)
      ·
        refine ⟨30833823203275002421515965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20555882135516668281010643 30833823203275002421515965)
        ·
          refine ⟨11562683701228125908068487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30833823203275002421515965 11562683701228125908068487)
          ·
            refine ⟨17344025551842188862102731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11562683701228125908068487 17344025551842188862102731)
            ·
              refine ⟨26016038327763283293154097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17344025551842188862102731 26016038327763283293154097)
              ·
                refine ⟨19512028745822462469865573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26016038327763283293154097 19512028745822462469865573)
                ·
                  refine ⟨3658505389841711713099795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19512028745822462469865573 3658505389841711713099795)
                  ·
                    refine ⟨5487758084762567569649693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3658505389841711713099795 5487758084762567569649693)
                    ·
                      refine ⟨2057909281785962838618635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5487758084762567569649693 2057909281785962838618635)
                      ·
                        rfl

theorem cell23_4007764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_4007764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007764 prefixEnd_4007764 := by exact prefixLift 4007764
  have htrace : WordTrace (prefixWord ++ tailWord_4007764) baseStart_4007764 baseEnd_4007764 := by
    simpa [prefixWord, tailWord_4007764, baseEnd_4007764] using wordTrace_append hprefix tailTrace_4007764
  have hstable : (prefixWord ++ tailWord_4007764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007764).length < 2 ^ (prefixWord ++ tailWord_4007764).sum := by decide
  have hdescent : baseEnd_4007764 < baseStart_4007764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007798 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4007798 : Nat := 118140960795 + 4007798 * 2 ^ 59
def prefixEnd_4007798 : Nat := 4983230072969 + 3 ^ 40 * 4007798 * 2
def baseEnd_4007798 : Nat := 2057926740128215705593479

theorem tailTrace_4007798 : CollatzResearch.WordTrace tailWord_4007798 prefixEnd_4007798 2057926740128215705593479 := by
  unfold tailWord_4007798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136025120902487390592503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97450934622959865499653365 9136025120902487390592503)
  ·
    refine ⟨13704037681353731085888755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9136025120902487390592503 13704037681353731085888755)
    ·
      refine ⟨20556056522030596628833133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13704037681353731085888755 20556056522030596628833133)
      ·
        refine ⟨7708521195761473735812425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20556056522030596628833133 7708521195761473735812425)
        ·
          refine ⟨5781390896821105301859319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7708521195761473735812425 5781390896821105301859319)
          ·
            refine ⟨8672086345231657952788979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781390896821105301859319 8672086345231657952788979)
            ·
              refine ⟨13008129517847486929183469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672086345231657952788979 13008129517847486929183469)
              ·
                refine ⟨4878048569192807598443801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13008129517847486929183469 4878048569192807598443801)
                ·
                  refine ⟨3658536426894605698832851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878048569192807598443801 3658536426894605698832851)
                  ·
                    refine ⟨5487804640341908548249277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3658536426894605698832851 5487804640341908548249277)
                    ·
                      refine ⟨2057926740128215705593479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5487804640341908548249277 2057926740128215705593479)
                      ·
                        rfl

theorem cell23_4007798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4007798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007798 prefixEnd_4007798 := by exact prefixLift 4007798
  have htrace : WordTrace (prefixWord ++ tailWord_4007798) baseStart_4007798 baseEnd_4007798 := by
    simpa [prefixWord, tailWord_4007798, baseEnd_4007798] using wordTrace_append hprefix tailTrace_4007798
  have hstable : (prefixWord ++ tailWord_4007798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007798).length < 2 ^ (prefixWord ++ tailWord_4007798).sum := by decide
  have hdescent : baseEnd_4007798 < baseStart_4007798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007800 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_4007800 : Nat := 118140960795 + 4007800 * 2 ^ 59
def prefixEnd_4007800 : Nat := 4983230072969 + 3 ^ 40 * 4007800 * 2
def baseEnd_4007800 : Nat := 2057927767089524697768469

theorem tailTrace_4007800 : CollatzResearch.WordTrace tailWord_4007800 prefixEnd_4007800 2057927767089524697768469 := by
  unfold tailWord_4007800
  simp only [CollatzResearch.WordTrace]
  refine ⟨73088237440216276295526427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97450983253621701727368569 73088237440216276295526427)
  ·
    refine ⟨109632356160324414443289641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73088237440216276295526427 109632356160324414443289641)
    ·
      refine ⟨82224267120243310832467231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109632356160324414443289641 82224267120243310832467231)
      ·
        refine ⟨123336400680364966248700847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82224267120243310832467231 123336400680364966248700847)
        ·
          refine ⟨185004601020547449373051271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123336400680364966248700847 185004601020547449373051271)
          ·
            refine ⟨277506901530821174059576907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185004601020547449373051271 277506901530821174059576907)
            ·
              refine ⟨416260352296231761089365361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277506901530821174059576907 416260352296231761089365361)
              ·
                refine ⟨312195264222173820817024021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416260352296231761089365361 312195264222173820817024021)
                ·
                  refine ⟨14634153010414397850798001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312195264222173820817024021 14634153010414397850798001)
                  ·
                    refine ⟨10975614757810798388098501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14634153010414397850798001 10975614757810798388098501)
                    ·
                      refine ⟨2057927767089524697768469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10975614757810798388098501 2057927767089524697768469)
                      ·
                        rfl

theorem cell23_4007800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_4007800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007800 prefixEnd_4007800 := by exact prefixLift 4007800
  have htrace : WordTrace (prefixWord ++ tailWord_4007800) baseStart_4007800 baseEnd_4007800 := by
    simpa [prefixWord, tailWord_4007800, baseEnd_4007800] using wordTrace_append hprefix tailTrace_4007800
  have hstable : (prefixWord ++ tailWord_4007800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007800).length < 2 ^ (prefixWord ++ tailWord_4007800).sum := by decide
  have hdescent : baseEnd_4007800 < baseStart_4007800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007840 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_4007840 : Nat := 118140960795 + 4007840 * 2 ^ 59
def prefixEnd_4007840 : Nat := 4983230072969 + 3 ^ 40 * 4007840 * 2
def baseEnd_4007840 : Nat := 685982768771901513756095

theorem tailTrace_4007840 : CollatzResearch.WordTrace tailWord_4007840 prefixEnd_4007840 685982768771901513756095 := by
  unfold tailWord_4007840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73088966900143819711254487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97451955866858426281672649 73088966900143819711254487)
  ·
    refine ⟨109633450350215729566881731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73088966900143819711254487 109633450350215729566881731)
    ·
      refine ⟨164450175525323594350322597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109633450350215729566881731 164450175525323594350322597)
      ·
        refine ⟨30834407910998173940685487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164450175525323594350322597 30834407910998173940685487)
        ·
          refine ⟨46251611866497260911028231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30834407910998173940685487 46251611866497260911028231)
          ·
            refine ⟨69377417799745891366542347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46251611866497260911028231 69377417799745891366542347)
            ·
              refine ⟨104066126699618837049813521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69377417799745891366542347 104066126699618837049813521)
              ·
                refine ⟨78049595024714127787360141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104066126699618837049813521 78049595024714127787360141)
                ·
                  refine ⟨29268598134267797920260053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78049595024714127787360141 29268598134267797920260053)
                  ·
                    refine ⟨685982768771901513756095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29268598134267797920260053 685982768771901513756095)
                    ·
                      rfl

theorem cell23_4007840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_4007840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007840 prefixEnd_4007840 := by exact prefixLift 4007840
  have htrace : WordTrace (prefixWord ++ tailWord_4007840) baseStart_4007840 baseEnd_4007840 := by
    simpa [prefixWord, tailWord_4007840, baseEnd_4007840] using wordTrace_append hprefix tailTrace_4007840
  have hstable : (prefixWord ++ tailWord_4007840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007840).length < 2 ^ (prefixWord ++ tailWord_4007840).sum := by decide
  have hdescent : baseEnd_4007840 < baseStart_4007840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007844 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 5]
def baseStart_4007844 : Nat := 118140960795 + 4007844 * 2 ^ 59
def prefixEnd_4007844 : Nat := 4983230072969 + 3 ^ 40 * 4007844 * 2
def baseEnd_4007844 : Nat := 228661151137591391735363

theorem tailTrace_4007844 : CollatzResearch.WordTrace tailWord_4007844 prefixEnd_4007844 228661151137591391735363 := by
  unfold tailWord_4007844
  simp only [CollatzResearch.WordTrace]
  refine ⟨73089039846136574052827293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97452053128182098737103057 73089039846136574052827293)
  ·
    refine ⟨27408389942301215269810235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73089039846136574052827293 27408389942301215269810235)
    ·
      refine ⟨41112584913451822904715353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27408389942301215269810235 41112584913451822904715353)
      ·
        refine ⟨30834438685088867178536515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41112584913451822904715353 30834438685088867178536515)
        ·
          refine ⟨46251658027633300767804773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30834438685088867178536515 46251658027633300767804773)
          ·
            refine ⟨8672185880181243893963395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46251658027633300767804773 8672185880181243893963395)
            ·
              refine ⟨13008278820271865840945093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672185880181243893963395 13008278820271865840945093)
              ·
                refine ⟨2439052278800974845177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13008278820271865840945093 2439052278800974845177205)
                ·
                  refine ⟨228661151137591391735363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2439052278800974845177205 228661151137591391735363)
                  ·
                    rfl

theorem cell23_4007844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_4007844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007844 prefixEnd_4007844 := by exact prefixLift 4007844
  have htrace : WordTrace (prefixWord ++ tailWord_4007844) baseStart_4007844 baseEnd_4007844 := by
    simpa [prefixWord, tailWord_4007844, baseEnd_4007844] using wordTrace_append hprefix tailTrace_4007844
  have hstable : (prefixWord ++ tailWord_4007844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007844).length < 2 ^ (prefixWord ++ tailWord_4007844).sum := by decide
  have hdescent : baseEnd_4007844 < baseStart_4007844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007877 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_4007877 : Nat := 118140960795 + 4007877 * 2 ^ 59
def prefixEnd_4007877 : Nat := 4983230072969 + 3 ^ 40 * 4007877 * 2
def baseEnd_4007877 : Nat := 2057967305099920896505615

theorem tailTrace_4007877 : CollatzResearch.WordTrace tailWord_4007877 prefixEnd_4007877 2057967305099920896505615 := by
  unfold tailWord_4007877
  simp only [CollatzResearch.WordTrace]
  refine ⟨146179283301153594741605885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97452855534102396494403923 146179283301153594741605885)
  ·
    refine ⟨54817231237932598028102207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146179283301153594741605885 54817231237932598028102207)
    ·
      refine ⟨82225846856898897042153311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54817231237932598028102207 82225846856898897042153311)
      ·
        refine ⟨123338770285348345563229967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82225846856898897042153311 123338770285348345563229967)
        ·
          refine ⟨185008155428022518344844951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123338770285348345563229967 185008155428022518344844951)
          ·
            refine ⟨277512233142033777517267427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185008155428022518344844951 277512233142033777517267427)
            ·
              refine ⟨416268349713050666275901141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277512233142033777517267427 416268349713050666275901141)
              ·
                refine ⟨9756289446399624990841433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 416268349713050666275901141 9756289446399624990841433)
                ·
                  refine ⟨7317217084799718743131075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9756289446399624990841433 7317217084799718743131075)
                  ·
                    refine ⟨10975825627199578114696613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7317217084799718743131075 10975825627199578114696613)
                    ·
                      refine ⟨2057967305099920896505615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10975825627199578114696613 2057967305099920896505615)
                      ·
                        rfl

theorem cell23_4007877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_4007877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007877 prefixEnd_4007877 := by exact prefixLift 4007877
  have htrace : WordTrace (prefixWord ++ tailWord_4007877) baseStart_4007877 baseEnd_4007877 := by
    simpa [prefixWord, tailWord_4007877, baseEnd_4007877] using wordTrace_append hprefix tailTrace_4007877
  have hstable : (prefixWord ++ tailWord_4007877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007877).length < 2 ^ (prefixWord ++ tailWord_4007877).sum := by decide
  have hdescent : baseEnd_4007877 < baseStart_4007877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007887 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 5, 4]
def baseStart_4007887 : Nat := 118140960795 + 4007887 * 2 ^ 59
def prefixEnd_4007887 : Nat := 4983230072969 + 3 ^ 40 * 4007887 * 2
def baseEnd_4007887 : Nat := 685990813302155285793523

theorem tailTrace_4007887 : CollatzResearch.WordTrace tailWord_4007887 prefixEnd_4007887 685990813302155285793523 := by
  unfold tailWord_4007887
  simp only [CollatzResearch.WordTrace]
  refine ⟨146179648031117366449469915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97453098687411577632979943 146179648031117366449469915)
  ·
    refine ⟨219269472046676049674204873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146179648031117366449469915 219269472046676049674204873)
    ·
      refine ⟨164452104035007037255653655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219269472046676049674204873 164452104035007037255653655)
      ·
        refine ⟨246678156052510555883480483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164452104035007037255653655 246678156052510555883480483)
        ·
          refine ⟨370017234078765833825220725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246678156052510555883480483 370017234078765833825220725)
          ·
            refine ⟨34689115694884296921114443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370017234078765833825220725 34689115694884296921114443)
            ·
              refine ⟨52033673542326445381671665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34689115694884296921114443 52033673542326445381671665)
              ·
                refine ⟨39025255156744834036253749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52033673542326445381671665 39025255156744834036253749)
                ·
                  refine ⟨3658617670944828190898789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39025255156744834036253749 3658617670944828190898789)
                  ·
                    refine ⟨685990813302155285793523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658617670944828190898789 685990813302155285793523)
                    ·
                      rfl

theorem cell23_4007887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_4007887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007887 prefixEnd_4007887 := by exact prefixLift 4007887
  have htrace : WordTrace (prefixWord ++ tailWord_4007887) baseStart_4007887 baseEnd_4007887 := by
    simpa [prefixWord, tailWord_4007887, baseEnd_4007887] using wordTrace_append hprefix tailTrace_4007887
  have hstable : (prefixWord ++ tailWord_4007887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007887).length < 2 ^ (prefixWord ++ tailWord_4007887).sum := by decide
  have hdescent : baseEnd_4007887 < baseStart_4007887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007934 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_4007934 : Nat := 118140960795 + 4007934 * 2 ^ 59
def prefixEnd_4007934 : Nat := 4983230072969 + 3 ^ 40 * 4007934 * 2
def baseEnd_4007934 : Nat := 228666285944136352610317

theorem tailTrace_4007934 : CollatzResearch.WordTrace tailWord_4007934 prefixEnd_4007934 228666285944136352610317 := by
  unfold tailWord_4007934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272670282743386684553857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97454241507964728984287237 18272670282743386684553857)
  ·
    refine ⟨13704502712057540013415393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18272670282743386684553857 13704502712057540013415393)
    ·
      refine ⟨10278377034043155010061545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13704502712057540013415393 10278377034043155010061545)
      ·
        refine ⟨7708782775532366257546159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10278377034043155010061545 7708782775532366257546159)
        ·
          refine ⟨11563174163298549386319239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708782775532366257546159 11563174163298549386319239)
          ·
            refine ⟨17344761244947824079478859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563174163298549386319239 17344761244947824079478859)
            ·
              refine ⟨26017141867421736119218289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17344761244947824079478859 26017141867421736119218289)
              ·
                refine ⟨19512856400566302089413717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26017141867421736119218289 19512856400566302089413717)
                ·
                  refine ⟨228666285944136352610317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19512856400566302089413717 228666285944136352610317)
                  ·
                    rfl

theorem cell23_4007934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_4007934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007934 prefixEnd_4007934 := by exact prefixLift 4007934
  have htrace : WordTrace (prefixWord ++ tailWord_4007934) baseStart_4007934 baseEnd_4007934 := by
    simpa [prefixWord, tailWord_4007934, baseEnd_4007934] using wordTrace_append hprefix tailTrace_4007934
  have hstable : (prefixWord ++ tailWord_4007934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007934).length < 2 ^ (prefixWord ++ tailWord_4007934).sum := by decide
  have hdescent : baseEnd_4007934 < baseStart_4007934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007984 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_4007984 : Nat := 118140960795 + 4007984 * 2 ^ 59
def prefixEnd_4007984 : Nat := 4983230072969 + 3 ^ 40 * 4007984 * 2
def baseEnd_4007984 : Nat := 2058022247529951977867623

theorem tailTrace_4007984 : CollatzResearch.WordTrace tailWord_4007984 prefixEnd_4007984 2058022247529951977867623 := by
  unfold tailWord_4007984
  simp only [CollatzResearch.WordTrace]
  refine ⟨73091592955882976007875503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97455457274510634677167337 73091592955882976007875503)
  ·
    refine ⟨109637389433824464011813255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73091592955882976007875503 109637389433824464011813255)
    ·
      refine ⟨164456084150736696017719883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109637389433824464011813255 164456084150736696017719883)
      ·
        refine ⟨246684126226105044026579825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164456084150736696017719883 246684126226105044026579825)
        ·
          refine ⟨185013094669578783019934869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246684126226105044026579825 185013094669578783019934869)
          ·
            refine ⟨8672488812636505454059447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185013094669578783019934869 8672488812636505454059447)
            ·
              refine ⟨13008733218954758181089171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672488812636505454059447 13008733218954758181089171)
              ·
                refine ⟨19513099828432137271633757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13008733218954758181089171 19513099828432137271633757)
                ·
                  refine ⟨7317412435662051476862659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19513099828432137271633757 7317412435662051476862659)
                  ·
                    refine ⟨10976118653493077215293989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7317412435662051476862659 10976118653493077215293989)
                    ·
                      refine ⟨2058022247529951977867623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10976118653493077215293989 2058022247529951977867623)
                      ·
                        rfl

theorem cell23_4007984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_4007984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007984 prefixEnd_4007984 := by exact prefixLift 4007984
  have htrace : WordTrace (prefixWord ++ tailWord_4007984) baseStart_4007984 baseEnd_4007984 := by
    simpa [prefixWord, tailWord_4007984, baseEnd_4007984] using wordTrace_append hprefix tailTrace_4007984
  have hstable : (prefixWord ++ tailWord_4007984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007984).length < 2 ^ (prefixWord ++ tailWord_4007984).sum := by decide
  have hdescent : baseEnd_4007984 < baseStart_4007984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4007987 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5]
def baseStart_4007987 : Nat := 118140960795 + 4007987 * 2 ^ 59
def prefixEnd_4007987 : Nat := 4983230072969 + 3 ^ 40 * 4007987 * 2
def baseEnd_4007987 : Nat := 2058023787971915466130109

theorem tailTrace_4007987 : CollatzResearch.WordTrace tailWord_4007987 prefixEnd_4007987 2058023787971915466130109 := by
  unfold tailWord_4007987
  simp only [CollatzResearch.WordTrace]
  refine ⟨146183295330755083528110215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97455530220503389018740143 146183295330755083528110215)
  ·
    refine ⟨219274942996132625292165323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146183295330755083528110215 219274942996132625292165323)
    ·
      refine ⟨328912414494198937938247985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219274942996132625292165323 328912414494198937938247985)
      ·
        refine ⟨246684310870649203453685989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328912414494198937938247985 246684310870649203453685989)
        ·
          refine ⟨46253308288246725647566123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246684310870649203453685989 46253308288246725647566123)
          ·
            refine ⟨69379962432370088471349185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46253308288246725647566123 69379962432370088471349185)
            ·
              refine ⟨52034971824277566353511889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69379962432370088471349185 52034971824277566353511889)
              ·
                refine ⟨39026228868208174765133917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52034971824277566353511889 39026228868208174765133917)
                ·
                  refine ⟨14634835825578065536925219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39026228868208174765133917 14634835825578065536925219)
                  ·
                    refine ⟨21952253738367098305387829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14634835825578065536925219 21952253738367098305387829)
                    ·
                      refine ⟨2058023787971915466130109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21952253738367098305387829 2058023787971915466130109)
                      ·
                        rfl

theorem cell23_4007987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_4007987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4007987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4007987 prefixEnd_4007987 := by exact prefixLift 4007987
  have htrace : WordTrace (prefixWord ++ tailWord_4007987) baseStart_4007987 baseEnd_4007987 := by
    simpa [prefixWord, tailWord_4007987, baseEnd_4007987] using wordTrace_append hprefix tailTrace_4007987
  have hstable : (prefixWord ++ tailWord_4007987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4007987).length < 2 ^ (prefixWord ++ tailWord_4007987).sum := by decide
  have hdescent : baseEnd_4007987 < baseStart_4007987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4007987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008024 : List Nat := [2, 1, 2, 2, 1, 6, 1, 8]
def baseStart_4008024 : Nat := 118140960795 + 4008024 * 2 ^ 59
def prefixEnd_4008024 : Nat := 4983230072969 + 3 ^ 40 * 4008024 * 2
def baseEnd_4008024 : Nat := 76223806916893771161757

theorem tailTrace_4008024 : CollatzResearch.WordTrace tailWord_4008024 prefixEnd_4008024 76223806916893771161757 := by
  unfold tailWord_4008024
  simp only [CollatzResearch.WordTrace]
  refine ⟨73092322415810519423603563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97456429887747359231471417 73092322415810519423603563)
  ·
    refine ⟨109638483623715779135405345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73092322415810519423603563 109638483623715779135405345)
    ·
      refine ⟨82228862717786834351554009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109638483623715779135405345 82228862717786834351554009)
      ·
        refine ⟨61671647038340125763665507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82228862717786834351554009 61671647038340125763665507)
        ·
          refine ⟨92507470557510188645498261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61671647038340125763665507 92507470557510188645498261)
          ·
            refine ⟨4336287682383290092757731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92507470557510188645498261 4336287682383290092757731)
            ·
              refine ⟨6504431523574935139136597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336287682383290092757731 6504431523574935139136597)
              ·
                refine ⟨76223806916893771161757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6504431523574935139136597 76223806916893771161757)
                ·
                  rfl

theorem cell23_4008024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 8].length) (baseStart_4008024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008024 prefixEnd_4008024 := by exact prefixLift 4008024
  have htrace : WordTrace (prefixWord ++ tailWord_4008024) baseStart_4008024 baseEnd_4008024 := by
    simpa [prefixWord, tailWord_4008024, baseEnd_4008024] using wordTrace_append hprefix tailTrace_4008024
  have hstable : (prefixWord ++ tailWord_4008024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008024).length < 2 ^ (prefixWord ++ tailWord_4008024).sum := by decide
  have hdescent : baseEnd_4008024 < baseStart_4008024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008095 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4008095 : Nat := 118140960795 + 4008095 * 2 ^ 59
def prefixEnd_4008095 : Nat := 4983230072969 + 3 ^ 40 * 4008095 * 2
def baseEnd_4008095 : Nat := 2058079243882601043579613

theorem tailTrace_4008095 : CollatzResearch.WordTrace tailWord_4008095 prefixEnd_4008095 2058079243882601043579613 := by
  unfold tailWord_4008095
  simp only [CollatzResearch.WordTrace]
  refine ⟨146187234414363817973041739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97458156276242545315361159 146187234414363817973041739)
  ·
    refine ⟨219280851621545726959562609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146187234414363817973041739 219280851621545726959562609)
    ·
      refine ⟨164460638716159295219671957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219280851621545726959562609 164460638716159295219671957)
      ·
        refine ⟨7709092439819966963422123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164460638716159295219671957 7709092439819966963422123)
        ·
          refine ⟨11563638659729950445133185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709092439819966963422123 11563638659729950445133185)
          ·
            refine ⟨8672728994797462833849889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11563638659729950445133185 8672728994797462833849889)
            ·
              refine ⟨6504546746098097125387417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672728994797462833849889 6504546746098097125387417)
              ·
                refine ⟨4878410059573572844040563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504546746098097125387417 4878410059573572844040563)
                ·
                  refine ⟨7317615089360359266060845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878410059573572844040563 7317615089360359266060845)
                  ·
                    refine ⟨2744105658510134724772817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7317615089360359266060845 2744105658510134724772817)
                    ·
                      refine ⟨2058079243882601043579613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744105658510134724772817 2058079243882601043579613)
                      ·
                        rfl

theorem cell23_4008095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4008095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008095 prefixEnd_4008095 := by exact prefixLift 4008095
  have htrace : WordTrace (prefixWord ++ tailWord_4008095) baseStart_4008095 baseEnd_4008095 := by
    simpa [prefixWord, tailWord_4008095, baseEnd_4008095] using wordTrace_append hprefix tailTrace_4008095
  have hstable : (prefixWord ++ tailWord_4008095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008095).length < 2 ^ (prefixWord ++ tailWord_4008095).sum := by decide
  have hdescent : baseEnd_4008095 < baseStart_4008095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008142 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_4008142 : Nat := 118140960795 + 4008142 * 2 ^ 59
def prefixEnd_4008142 : Nat := 4983230072969 + 3 ^ 40 * 4008142 * 2
def baseEnd_4008142 : Nat := 2058103377473362359691897

theorem tailTrace_4008142 : CollatzResearch.WordTrace tailWord_4008142 prefixEnd_4008142 2058103377473362359691897 := by
  unfold tailWord_4008142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273618580649193125000335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97459299096795696666668453 18273618580649193125000335)
  ·
    refine ⟨27410427870973789687500503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273618580649193125000335 27410427870973789687500503)
    ·
      refine ⟨41115641806460684531250755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27410427870973789687500503 41115641806460684531250755)
      ·
        refine ⟨61673462709691026796876133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41115641806460684531250755 61673462709691026796876133)
        ·
          refine ⟨11563774258067067524414275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61673462709691026796876133 11563774258067067524414275)
          ·
            refine ⟨17345661387100601286621413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563774258067067524414275 17345661387100601286621413)
            ·
              refine ⟨3252311510081362741241515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17345661387100601286621413 3252311510081362741241515)
              ·
                refine ⟨4878467265122044111862273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252311510081362741241515 4878467265122044111862273)
                ·
                  refine ⟨3658850448841533083896705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878467265122044111862273 3658850448841533083896705)
                  ·
                    refine ⟨2744137836631149812922529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3658850448841533083896705 2744137836631149812922529)
                    ·
                      refine ⟨2058103377473362359691897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744137836631149812922529 2058103377473362359691897)
                      ·
                        rfl

theorem cell23_4008142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_4008142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008142 prefixEnd_4008142 := by exact prefixLift 4008142
  have htrace : WordTrace (prefixWord ++ tailWord_4008142) baseStart_4008142 baseEnd_4008142 := by
    simpa [prefixWord, tailWord_4008142, baseEnd_4008142] using wordTrace_append hprefix tailTrace_4008142
  have hstable : (prefixWord ++ tailWord_4008142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008142).length < 2 ^ (prefixWord ++ tailWord_4008142).sum := by decide
  have hdescent : baseEnd_4008142 < baseStart_4008142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008161 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 2, 5]
def baseStart_4008161 : Nat := 118140960795 + 4008161 * 2 ^ 59
def prefixEnd_4008161 : Nat := 4983230072969 + 3 ^ 40 * 4008161 * 2
def baseEnd_4008161 : Nat := 686037711201932595118103

theorem tailTrace_4008161 : CollatzResearch.WordTrace tailWord_4008161 prefixEnd_4008161 686037711201932595118103 := by
  unfold tailWord_4008161
  simp only [CollatzResearch.WordTrace]
  refine ⟨146189641632124711244944337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97459761088083140829962891 146189641632124711244944337)
  ·
    refine ⟨109642231224093533433708253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146189641632124711244944337 109642231224093533433708253)
    ·
      refine ⟨41115836709035075037640595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109642231224093533433708253 41115836709035075037640595)
      ·
        refine ⟨61673755063552612556460893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41115836709035075037640595 61673755063552612556460893)
        ·
          refine ⟨23127658148832229708672835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61673755063552612556460893 23127658148832229708672835)
          ·
            refine ⟨34691487223248344563009253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23127658148832229708672835 34691487223248344563009253)
            ·
              refine ⟨6504653854359064605564235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34691487223248344563009253 6504653854359064605564235)
              ·
                refine ⟨9756980781538596908346353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504653854359064605564235 9756980781538596908346353)
                ·
                  refine ⟨7317735586153947681259765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9756980781538596908346353 7317735586153947681259765)
                  ·
                    refine ⟨686037711201932595118103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7317735586153947681259765 686037711201932595118103)
                    ·
                      rfl

theorem cell23_4008161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_4008161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008161 prefixEnd_4008161 := by exact prefixLift 4008161
  have htrace : WordTrace (prefixWord ++ tailWord_4008161) baseStart_4008161 baseEnd_4008161 := by
    simpa [prefixWord, tailWord_4008161, baseEnd_4008161] using wordTrace_append hprefix tailTrace_4008161
  have hstable : (prefixWord ++ tailWord_4008161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008161).length < 2 ^ (prefixWord ++ tailWord_4008161).sum := by decide
  have hdescent : baseEnd_4008161 < baseStart_4008161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008191 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 3, 4]
def baseStart_4008191 : Nat := 118140960795 + 4008191 * 2 ^ 59
def prefixEnd_4008191 : Nat := 4983230072969 + 3 ^ 40 * 4008191 * 2
def baseEnd_4008191 : Nat := 686042846008477555993057

theorem tailTrace_4008191 : CollatzResearch.WordTrace tailWord_4008191 prefixEnd_4008191 686042846008477555993057 := by
  unfold tailWord_4008191
  simp only [CollatzResearch.WordTrace]
  refine ⟨146190735822016026368536427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97460490548010684245690951 146190735822016026368536427)
  ·
    refine ⟨219286103733024039552804641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146190735822016026368536427 219286103733024039552804641)
    ·
      refine ⟨164464577799768029664603481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219286103733024039552804641 164464577799768029664603481)
      ·
        refine ⟨123348433349826022248452611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164464577799768029664603481 123348433349826022248452611)
        ·
          refine ⟨185022650024739033372678917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123348433349826022248452611 185022650024739033372678917)
          ·
            refine ⟨34691746879638568757377297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185022650024739033372678917 34691746879638568757377297)
            ·
              refine ⟨26018810159728926568032973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34691746879638568757377297 26018810159728926568032973)
              ·
                refine ⟨9757053809898347463012365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26018810159728926568032973 9757053809898347463012365)
                ·
                  refine ⟨3658895178711880298629637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9757053809898347463012365 3658895178711880298629637)
                  ·
                    refine ⟨686042846008477555993057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658895178711880298629637 686042846008477555993057)
                    ·
                      rfl

theorem cell23_4008191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_4008191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008191 prefixEnd_4008191 := by exact prefixLift 4008191
  have htrace : WordTrace (prefixWord ++ tailWord_4008191) baseStart_4008191 baseEnd_4008191 := by
    simpa [prefixWord, tailWord_4008191, baseEnd_4008191] using wordTrace_append hprefix tailTrace_4008191
  have hstable : (prefixWord ++ tailWord_4008191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008191).length < 2 ^ (prefixWord ++ tailWord_4008191).sum := by decide
  have hdescent : baseEnd_4008191 < baseStart_4008191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008218 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_4008218 : Nat := 118140960795 + 4008218 * 2 ^ 59
def prefixEnd_4008218 : Nat := 4983230072969 + 3 ^ 40 * 4008218 * 2
def baseEnd_4008218 : Nat := 2058142402003104062341547

theorem tailTrace_4008218 : CollatzResearch.WordTrace tailWord_4008218 prefixEnd_4008218 2058142402003104062341547 := by
  unfold tailWord_4008218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36547930148229552494942327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97461147061945473319846205 36547930148229552494942327)
  ·
    refine ⟨54821895222344328742413491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36547930148229552494942327 54821895222344328742413491)
    ·
      refine ⟨82232842833516493113620237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54821895222344328742413491 82232842833516493113620237)
      ·
        refine ⟨30837316062568684917607589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82232842833516493113620237 30837316062568684917607589)
        ·
          refine ⟨5781996761731628422051423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30837316062568684917607589 5781996761731628422051423)
          ·
            refine ⟨8672995142597442633077135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781996761731628422051423 8672995142597442633077135)
            ·
              refine ⟨13009492713896163949615703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672995142597442633077135 13009492713896163949615703)
              ·
                refine ⟨19514239070844245924423555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13009492713896163949615703 19514239070844245924423555)
                ·
                  refine ⟨29271358606266368886635333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19514239070844245924423555 29271358606266368886635333)
                  ·
                    refine ⟨5488379738674944166244125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29271358606266368886635333 5488379738674944166244125)
                    ·
                      refine ⟨2058142402003104062341547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5488379738674944166244125 2058142402003104062341547)
                      ·
                        rfl

theorem cell23_4008218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_4008218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008218 prefixEnd_4008218 := by exact prefixLift 4008218
  have htrace : WordTrace (prefixWord ++ tailWord_4008218) baseStart_4008218 baseEnd_4008218 := by
    simpa [prefixWord, tailWord_4008218, baseEnd_4008218] using wordTrace_append hprefix tailTrace_4008218
  have hstable : (prefixWord ++ tailWord_4008218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008218).length < 2 ^ (prefixWord ++ tailWord_4008218).sum := by decide
  have hdescent : baseEnd_4008218 < baseStart_4008218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008248 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_4008248 : Nat := 118140960795 + 4008248 * 2 ^ 59
def prefixEnd_4008248 : Nat := 4983230072969 + 3 ^ 40 * 4008248 * 2
def baseEnd_4008248 : Nat := 2058157806422738944966409

theorem tailTrace_4008248 : CollatzResearch.WordTrace tailWord_4008248 prefixEnd_4008248 2058157806422738944966409 := by
  unfold tailWord_4008248
  simp only [CollatzResearch.WordTrace]
  refine ⟨73096407391404762551680699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97461876521873016735574265 73096407391404762551680699)
  ·
    refine ⟨109644611087107143827521049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73096407391404762551680699 109644611087107143827521049)
    ·
      refine ⟨82233458315330357870640787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109644611087107143827521049 82233458315330357870640787)
      ·
        refine ⟨123350187472995536805961181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82233458315330357870640787 123350187472995536805961181)
        ·
          refine ⟨46256320302373326302235443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123350187472995536805961181 46256320302373326302235443)
          ·
            refine ⟨69384480453559989453353165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46256320302373326302235443 69384480453559989453353165)
            ·
              refine ⟨26019180170084996045007437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69384480453559989453353165 26019180170084996045007437)
              ·
                refine ⟨9757192563781873516877789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26019180170084996045007437 9757192563781873516877789)
                ·
                  refine ⟨3658947211418202568829171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9757192563781873516877789 3658947211418202568829171)
                  ·
                    refine ⟨5488420817127303853243757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3658947211418202568829171 5488420817127303853243757)
                    ·
                      refine ⟨2058157806422738944966409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5488420817127303853243757 2058157806422738944966409)
                      ·
                        rfl

theorem cell23_4008248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_4008248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008248 prefixEnd_4008248 := by exact prefixLift 4008248
  have htrace : WordTrace (prefixWord ++ tailWord_4008248) baseStart_4008248 baseEnd_4008248 := by
    simpa [prefixWord, tailWord_4008248, baseEnd_4008248] using wordTrace_append hprefix tailTrace_4008248
  have hstable : (prefixWord ++ tailWord_4008248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008248).length < 2 ^ (prefixWord ++ tailWord_4008248).sum := by decide
  have hdescent : baseEnd_4008248 < baseStart_4008248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008268 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_4008268 : Nat := 118140960795 + 4008268 * 2 ^ 59
def prefixEnd_4008268 : Nat := 4983230072969 + 3 ^ 40 * 4008268 * 2
def baseEnd_4008268 : Nat := 686056025345276288905439

theorem tailTrace_4008268 : CollatzResearch.WordTrace tailWord_4008268 prefixEnd_4008268 686056025345276288905439 := by
  unfold tailWord_4008268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73096772121368534259544729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97462362828491379012726305 73096772121368534259544729)
  ·
    refine ⟨54822579091026400694658547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73096772121368534259544729 54822579091026400694658547)
    ·
      refine ⟨82233868636539601041987821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54822579091026400694658547 82233868636539601041987821)
      ·
        refine ⟨30837700738702350390745433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82233868636539601041987821 30837700738702350390745433)
        ·
          refine ⟨23128275554026762793059075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30837700738702350390745433 23128275554026762793059075)
          ·
            refine ⟨34692413331040144189588613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128275554026762793059075 34692413331040144189588613)
            ·
              refine ⟨6504827499570027035547865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34692413331040144189588613 6504827499570027035547865)
              ·
                refine ⟨4878620624677520276660899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504827499570027035547865 4878620624677520276660899)
                ·
                  refine ⟨7317930937016280414991349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878620624677520276660899 7317930937016280414991349)
                  ·
                    refine ⟨686056025345276288905439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7317930937016280414991349 686056025345276288905439)
                    ·
                      rfl

theorem cell23_4008268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_4008268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008268 prefixEnd_4008268 := by exact prefixLift 4008268
  have htrace : WordTrace (prefixWord ++ tailWord_4008268) baseStart_4008268 baseEnd_4008268 := by
    simpa [prefixWord, tailWord_4008268, baseEnd_4008268] using wordTrace_append hprefix tailTrace_4008268
  have hstable : (prefixWord ++ tailWord_4008268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008268).length < 2 ^ (prefixWord ++ tailWord_4008268).sum := by decide
  have hdescent : baseEnd_4008268 < baseStart_4008268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008286 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4008286 : Nat := 118140960795 + 4008286 * 2 ^ 59
def prefixEnd_4008286 : Nat := 4983230072969 + 3 ^ 40 * 4008286 * 2
def baseEnd_4008286 : Nat := 2058177318687609796291235

theorem tailTrace_4008286 : CollatzResearch.WordTrace tailWord_4008286 prefixEnd_4008286 2058177318687609796291235 := by
  unfold tailWord_4008286
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274275094583982199155589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97462800504447905062163141 18274275094583982199155589)
  ·
    refine ⟨3426426580234496662341673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18274275094583982199155589 3426426580234496662341673)
    ·
      refine ⟨2569819935175872496756255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3426426580234496662341673 2569819935175872496756255)
      ·
        refine ⟨3854729902763808745134383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569819935175872496756255 3854729902763808745134383)
        ·
          refine ⟨5782094854145713117701575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854729902763808745134383 5782094854145713117701575)
          ·
            refine ⟨8673142281218569676552363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782094854145713117701575 8673142281218569676552363)
            ·
              refine ⟨13009713421827854514828545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673142281218569676552363 13009713421827854514828545)
              ·
                refine ⟨9757285066370890886121409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13009713421827854514828545 9757285066370890886121409)
                ·
                  refine ⟨7317963799778168164591057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9757285066370890886121409 7317963799778168164591057)
                  ·
                    refine ⟨5488472849833626123443293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7317963799778168164591057 5488472849833626123443293)
                    ·
                      refine ⟨2058177318687609796291235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5488472849833626123443293 2058177318687609796291235)
                      ·
                        rfl

theorem cell23_4008286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4008286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008286 prefixEnd_4008286 := by exact prefixLift 4008286
  have htrace : WordTrace (prefixWord ++ tailWord_4008286) baseStart_4008286 baseEnd_4008286 := by
    simpa [prefixWord, tailWord_4008286, baseEnd_4008286] using wordTrace_append hprefix tailTrace_4008286
  have hstable : (prefixWord ++ tailWord_4008286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008286).length < 2 ^ (prefixWord ++ tailWord_4008286).sum := by decide
  have hdescent : baseEnd_4008286 < baseStart_4008286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008301 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4008301 : Nat := 118140960795 + 4008301 * 2 ^ 59
def prefixEnd_4008301 : Nat := 4983230072969 + 3 ^ 40 * 4008301 * 2
def baseEnd_4008301 : Nat := 2058185020897427237603665

theorem tailTrace_4008301 : CollatzResearch.WordTrace tailWord_4008301 prefixEnd_4008301 2058185020897427237603665 := by
  unfold tailWord_4008301
  simp only [CollatzResearch.WordTrace]
  refine ⟨146194747851617515155040757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97463165234411676770027171 146194747851617515155040757)
  ·
    refine ⟨13705757611089142045785071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146194747851617515155040757 13705757611089142045785071)
    ·
      refine ⟨20558636416633713068677607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13705757611089142045785071 20558636416633713068677607)
      ·
        refine ⟨30837954624950569603016411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20558636416633713068677607 30837954624950569603016411)
        ·
          refine ⟨46256931937425854404524617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30837954624950569603016411 46256931937425854404524617)
          ·
            refine ⟨34692698953069390803393463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46256931937425854404524617 34692698953069390803393463)
            ·
              refine ⟨52039048429604086205090195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34692698953069390803393463 52039048429604086205090195)
              ·
                refine ⟨78058572644406129307635293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52039048429604086205090195 78058572644406129307635293)
                ·
                  refine ⟨29271964741652298490363235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78058572644406129307635293 29271964741652298490363235)
                  ·
                    refine ⟨43907947112478447735544853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29271964741652298490363235 43907947112478447735544853)
                    ·
                      refine ⟨2058185020897427237603665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43907947112478447735544853 2058185020897427237603665)
                      ·
                        rfl

theorem cell23_4008301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4008301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008301 prefixEnd_4008301 := by exact prefixLift 4008301
  have htrace : WordTrace (prefixWord ++ tailWord_4008301) baseStart_4008301 baseEnd_4008301 := by
    simpa [prefixWord, tailWord_4008301, baseEnd_4008301] using wordTrace_append hprefix tailTrace_4008301
  have hstable : (prefixWord ++ tailWord_4008301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008301).length < 2 ^ (prefixWord ++ tailWord_4008301).sum := by decide
  have hdescent : baseEnd_4008301 < baseStart_4008301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008315 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 2, 4]
def baseStart_4008315 : Nat := 118140960795 + 4008315 * 2 ^ 59
def prefixEnd_4008315 : Nat := 4983230072969 + 3 ^ 40 * 4008315 * 2
def baseEnd_4008315 : Nat := 686064069875530060942867

theorem tailTrace_4008315 : CollatzResearch.WordTrace tailWord_4008315 prefixEnd_4008315 686064069875530060942867 := by
  unfold tailWord_4008315
  simp only [CollatzResearch.WordTrace]
  refine ⟨146195258473566795546050399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97463505649044530364033599 146195258473566795546050399)
  ·
    refine ⟨219292887710350193319075599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146195258473566795546050399 219292887710350193319075599)
    ·
      refine ⟨328939331565525289978613399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219292887710350193319075599 328939331565525289978613399)
      ·
        refine ⟨493408997348287934967920099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328939331565525289978613399 493408997348287934967920099)
        ·
          refine ⟨740113496022431902451880149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493408997348287934967920099 740113496022431902451880149)
          ·
            refine ⟨17346410063025747713715941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 740113496022431902451880149 17346410063025747713715941)
            ·
              refine ⟨3252451886817327696321739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17346410063025747713715941 3252451886817327696321739)
              ·
                refine ⟨4878677830225991544482609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252451886817327696321739 4878677830225991544482609)
                ·
                  refine ⟨3659008372669493658361957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878677830225991544482609 3659008372669493658361957)
                  ·
                    refine ⟨686064069875530060942867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659008372669493658361957 686064069875530060942867)
                    ·
                      rfl

theorem cell23_4008315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 4].length) (baseStart_4008315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008315 prefixEnd_4008315 := by exact prefixLift 4008315
  have htrace : WordTrace (prefixWord ++ tailWord_4008315) baseStart_4008315 baseEnd_4008315 := by
    simpa [prefixWord, tailWord_4008315, baseEnd_4008315] using wordTrace_append hprefix tailTrace_4008315
  have hstable : (prefixWord ++ tailWord_4008315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008315).length < 2 ^ (prefixWord ++ tailWord_4008315).sum := by decide
  have hdescent : baseEnd_4008315 < baseStart_4008315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008322 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4008322 : Nat := 118140960795 + 4008322 * 2 ^ 59
def prefixEnd_4008322 : Nat := 4983230072969 + 3 ^ 40 * 4008322 * 2
def baseEnd_4008322 : Nat := 2058195803991171655441069

theorem tailTrace_4008322 : CollatzResearch.WordTrace tailWord_4008322 prefixEnd_4008322 2058195803991171655441069 := by
  unfold tailWord_4008322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36548878446135358935388805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97463675856360957161036813 36548878446135358935388805)
  ·
    refine ⟨6852914708650379800385401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36548878446135358935388805 6852914708650379800385401)
    ·
      refine ⟨5139686031487784850289051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6852914708650379800385401 5139686031487784850289051)
      ·
        refine ⟨7709529047231677275433577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139686031487784850289051 7709529047231677275433577)
        ·
          refine ⟨5782146785423757956575183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7709529047231677275433577 5782146785423757956575183)
          ·
            refine ⟨8673220178135636934862775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782146785423757956575183 8673220178135636934862775)
            ·
              refine ⟨13009830267203455402294163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673220178135636934862775 13009830267203455402294163)
              ·
                refine ⟨19514745400805183103441245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13009830267203455402294163 19514745400805183103441245)
                ·
                  refine ⟨7318029525301943663790467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19514745400805183103441245 7318029525301943663790467)
                  ·
                    refine ⟨10977044287952915495685701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7318029525301943663790467 10977044287952915495685701)
                    ·
                      refine ⟨2058195803991171655441069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10977044287952915495685701 2058195803991171655441069)
                      ·
                        rfl

theorem cell23_4008322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4008322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008322 prefixEnd_4008322 := by exact prefixLift 4008322
  have htrace : WordTrace (prefixWord ++ tailWord_4008322) baseStart_4008322 baseEnd_4008322 := by
    simpa [prefixWord, tailWord_4008322, baseEnd_4008322] using wordTrace_append hprefix tailTrace_4008322
  have hstable : (prefixWord ++ tailWord_4008322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008322).length < 2 ^ (prefixWord ++ tailWord_4008322).sum := by decide
  have hdescent : baseEnd_4008322 < baseStart_4008322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008355 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 3]
def baseStart_4008355 : Nat := 118140960795 + 4008355 * 2 ^ 59
def prefixEnd_4008355 : Nat := 4983230072969 + 3 ^ 40 * 4008355 * 2
def baseEnd_4008355 : Nat := 2058212748852770026328417

theorem tailTrace_4008355 : CollatzResearch.WordTrace tailWord_4008355 prefixEnd_4008355 2058212748852770026328417 := by
  unfold tailWord_4008355
  simp only [CollatzResearch.WordTrace]
  refine ⟨146196717393421882377506519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97464478262281254918337679 146196717393421882377506519)
  ·
    refine ⟨219295076090132823566259779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146196717393421882377506519 219295076090132823566259779)
    ·
      refine ⟨328942614135199235349389669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219295076090132823566259779 328942614135199235349389669)
      ·
        refine ⟨61676740150349856628010563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328942614135199235349389669 61676740150349856628010563)
        ·
          refine ⟨92515110225524784942015845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61676740150349856628010563 92515110225524784942015845)
          ·
            refine ⟨17346583167285897176627971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92515110225524784942015845 17346583167285897176627971)
            ·
              refine ⟨26019874750928845764941957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17346583167285897176627971 26019874750928845764941957)
              ·
                refine ⟨4878726515799158580926617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26019874750928845764941957 4878726515799158580926617)
                ·
                  refine ⟨3659044886849368935694963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878726515799158580926617 3659044886849368935694963)
                  ·
                    refine ⟨5488567330274053403542445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659044886849368935694963 5488567330274053403542445)
                    ·
                      refine ⟨2058212748852770026328417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5488567330274053403542445 2058212748852770026328417)
                      ·
                        rfl

theorem cell23_4008355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_4008355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008355 prefixEnd_4008355 := by exact prefixLift 4008355
  have htrace : WordTrace (prefixWord ++ tailWord_4008355) baseStart_4008355 baseEnd_4008355 := by
    simpa [prefixWord, tailWord_4008355, baseEnd_4008355] using wordTrace_append hprefix tailTrace_4008355
  have hstable : (prefixWord ++ tailWord_4008355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008355).length < 2 ^ (prefixWord ++ tailWord_4008355).sum := by decide
  have hdescent : baseEnd_4008355 < baseStart_4008355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008395 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 4, 2, 2]
def baseStart_4008395 : Nat := 118140960795 + 4008395 * 2 ^ 59
def prefixEnd_4008395 : Nat := 4983230072969 + 3 ^ 40 * 4008395 * 2
def baseEnd_4008395 : Nat := 2058233288078949869828233

theorem tailTrace_4008395 : CollatzResearch.WordTrace tailWord_4008395 prefixEnd_4008395 2058233288078949869828233 := by
  unfold tailWord_4008395
  simp only [CollatzResearch.WordTrace]
  refine ⟨146198176313276969208962639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97465450875517979472641759 146198176313276969208962639)
  ·
    refine ⟨219297264469915453813443959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146198176313276969208962639 219297264469915453813443959)
    ·
      refine ⟨328945896704873180720165939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219297264469915453813443959 328945896704873180720165939)
      ·
        refine ⟨493418845057309771080248909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328945896704873180720165939 493418845057309771080248909)
        ·
          refine ⟨185032066896491164155093341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493418845057309771080248909 185032066896491164155093341)
          ·
            refine ⟨69387025086184186558160003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185032066896491164155093341 69387025086184186558160003)
            ·
              refine ⟨104080537629276279837240005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69387025086184186558160003 104080537629276279837240005)
              ·
                refine ⟨19515100805489302469482501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104080537629276279837240005 19515100805489302469482501)
                ·
                  refine ⟨3659081401029244213027969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19515100805489302469482501 3659081401029244213027969)
                  ·
                    refine ⟨2744311050771933159770977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659081401029244213027969 2744311050771933159770977)
                    ·
                      refine ⟨2058233288078949869828233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744311050771933159770977 2058233288078949869828233)
                      ·
                        rfl

theorem cell23_4008395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 2, 2].length) (baseStart_4008395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008395 prefixEnd_4008395 := by exact prefixLift 4008395
  have htrace : WordTrace (prefixWord ++ tailWord_4008395) baseStart_4008395 baseEnd_4008395 := by
    simpa [prefixWord, tailWord_4008395, baseEnd_4008395] using wordTrace_append hprefix tailTrace_4008395
  have hstable : (prefixWord ++ tailWord_4008395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008395).length < 2 ^ (prefixWord ++ tailWord_4008395).sum := by decide
  have hdescent : baseEnd_4008395 < baseStart_4008395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008428 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_4008428 : Nat := 118140960795 + 4008428 * 2 ^ 59
def prefixEnd_4008428 : Nat := 4983230072969 + 3 ^ 40 * 4008428 * 2
def baseEnd_4008428 : Nat := 2058250232940548240715581

theorem tailTrace_4008428 : CollatzResearch.WordTrace tailWord_4008428 prefixEnd_4008428 2058250232940548240715581 := by
  unfold tailWord_4008428
  simp only [CollatzResearch.WordTrace]
  refine ⟨73099689961078707922456969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97466253281438277229942625 73099689961078707922456969)
  ·
    refine ⟨54824767470809030941842727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73099689961078707922456969 54824767470809030941842727)
    ·
      refine ⟨82237151206213546412764091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54824767470809030941842727 82237151206213546412764091)
      ·
        refine ⟨123355726809320319619146137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82237151206213546412764091 123355726809320319619146137)
        ·
          refine ⟨92516795106990239714359603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123355726809320319619146137 92516795106990239714359603)
          ·
            refine ⟨138775192660485359571539405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92516795106990239714359603 138775192660485359571539405)
            ·
              refine ⟨52040697247682009839327277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138775192660485359571539405 52040697247682009839327277)
              ·
                refine ⟨19515261467880753689747729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52040697247682009839327277 19515261467880753689747729)
                ·
                  refine ⟨14636446100910565267310797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19515261467880753689747729 14636446100910565267310797)
                  ·
                    refine ⟨5488667287841461975241549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14636446100910565267310797 5488667287841461975241549)
                    ·
                      refine ⟨2058250232940548240715581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5488667287841461975241549 2058250232940548240715581)
                      ·
                        rfl

theorem cell23_4008428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_4008428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008428 prefixEnd_4008428 := by exact prefixLift 4008428
  have htrace : WordTrace (prefixWord ++ tailWord_4008428) baseStart_4008428 baseEnd_4008428 := by
    simpa [prefixWord, tailWord_4008428, baseEnd_4008428] using wordTrace_append hprefix tailTrace_4008428
  have hstable : (prefixWord ++ tailWord_4008428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008428).length < 2 ^ (prefixWord ++ tailWord_4008428).sum := by decide
  have hdescent : baseEnd_4008428 < baseStart_4008428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008429 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4008429 : Nat := 118140960795 + 4008429 * 2 ^ 59
def prefixEnd_4008429 : Nat := 4983230072969 + 3 ^ 40 * 4008429 * 2
def baseEnd_4008429 : Nat := 2058250746421202736803077

theorem tailTrace_4008429 : CollatzResearch.WordTrace tailWord_4008429 prefixEnd_4008429 2058250746421202736803077 := by
  unfold tailWord_4008429
  simp only [CollatzResearch.WordTrace]
  refine ⟨146199416395153793015700341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97466277596769195343800227 146199416395153793015700341)
  ·
    refine ⟨13706195287045668095221907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146199416395153793015700341 13706195287045668095221907)
    ·
      refine ⟨20559292930568502142832861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13706195287045668095221907 20559292930568502142832861)
      ·
        refine ⟨7709734848963188303562323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20559292930568502142832861 7709734848963188303562323)
        ·
          refine ⟨11564602273444782455343485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709734848963188303562323 11564602273444782455343485)
          ·
            refine ⟨4336725852541793420753807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11564602273444782455343485 4336725852541793420753807)
            ·
              refine ⟨6505088778812690131130711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336725852541793420753807 6505088778812690131130711)
              ·
                refine ⟨9757633168219035196696067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505088778812690131130711 9757633168219035196696067)
                ·
                  refine ⟨14636449752328552795044101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9757633168219035196696067 14636449752328552795044101)
                  ·
                    refine ⟨2744334328561603649070769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14636449752328552795044101 2744334328561603649070769)
                    ·
                      refine ⟨2058250746421202736803077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744334328561603649070769 2058250746421202736803077)
                      ·
                        rfl

theorem cell23_4008429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4008429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008429 prefixEnd_4008429 := by exact prefixLift 4008429
  have htrace : WordTrace (prefixWord ++ tailWord_4008429) baseStart_4008429 baseEnd_4008429 := by
    simpa [prefixWord, tailWord_4008429, baseEnd_4008429] using wordTrace_append hprefix tailTrace_4008429
  have hstable : (prefixWord ++ tailWord_4008429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008429).length < 2 ^ (prefixWord ++ tailWord_4008429).sum := by decide
  have hdescent : baseEnd_4008429 < baseStart_4008429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008452 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 5]
def baseStart_4008452 : Nat := 118140960795 + 4008452 * 2 ^ 59
def prefixEnd_4008452 : Nat := 4983230072969 + 3 ^ 40 * 4008452 * 2
def baseEnd_4008452 : Nat := 228695839608472905201719

theorem tailTrace_4008452 : CollatzResearch.WordTrace tailWord_4008452 prefixEnd_4008452 228695839608472905201719 := by
  unfold tailWord_4008452
  simp only [CollatzResearch.WordTrace]
  refine ⟨73100127637035233971893805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97466836849380311962525073 73100127637035233971893805)
  ·
    refine ⟨27412547863888212739460177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73100127637035233971893805 27412547863888212739460177)
    ·
      refine ⟨20559410897916159554595133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27412547863888212739460177 20559410897916159554595133)
      ·
        refine ⟨7709779086718559832973175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20559410897916159554595133 7709779086718559832973175)
        ·
          refine ⟨11564668630077839749459763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709779086718559832973175 11564668630077839749459763)
          ·
            refine ⟨17347002945116759624189645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11564668630077839749459763 17347002945116759624189645)
            ·
              refine ⟨6505126104418784859071117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17347002945116759624189645 6505126104418784859071117)
              ·
                refine ⟨2439422289157044322151669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6505126104418784859071117 2439422289157044322151669)
                ·
                  refine ⟨228695839608472905201719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2439422289157044322151669 228695839608472905201719)
                  ·
                    rfl

theorem cell23_4008452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_4008452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008452 prefixEnd_4008452 := by exact prefixLift 4008452
  have htrace : WordTrace (prefixWord ++ tailWord_4008452) baseStart_4008452 baseEnd_4008452 := by
    simpa [prefixWord, tailWord_4008452, baseEnd_4008452] using wordTrace_append hprefix tailTrace_4008452
  have hstable : (prefixWord ++ tailWord_4008452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008452).length < 2 ^ (prefixWord ++ tailWord_4008452).sum := by decide
  have hdescent : baseEnd_4008452 < baseStart_4008452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008458 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4008458 : Nat := 118140960795 + 4008458 * 2 ^ 59
def prefixEnd_4008458 : Nat := 4983230072969 + 3 ^ 40 * 4008458 * 2
def baseEnd_4008458 : Nat := 2058265637360183123340443

theorem tailTrace_4008458 : CollatzResearch.WordTrace tailWord_4008458 prefixEnd_4008458 2058265637360183123340443 := by
  unfold tailWord_4008458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36550118528012182742126507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97466982741365820645670685 36550118528012182742126507)
  ·
    refine ⟨54825177792018274113189761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36550118528012182742126507 54825177792018274113189761)
    ·
      refine ⟨41118883344013705584892321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54825177792018274113189761 41118883344013705584892321)
      ·
        refine ⟨30839162508010279188669241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41118883344013705584892321 30839162508010279188669241)
        ·
          refine ⟨23129371881007709391501931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30839162508010279188669241 23129371881007709391501931)
          ·
            refine ⟨34694057821511564087252897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23129371881007709391501931 34694057821511564087252897)
            ·
              refine ⟨26020543366133673065439673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34694057821511564087252897 26020543366133673065439673)
              ·
                refine ⟨19515407524600254799079755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26020543366133673065439673 19515407524600254799079755)
                ·
                  refine ⟨29273111286900382198619633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19515407524600254799079755 29273111286900382198619633)
                  ·
                    refine ⟨21954833465175286648964725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29273111286900382198619633 21954833465175286648964725)
                    ·
                      refine ⟨2058265637360183123340443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21954833465175286648964725 2058265637360183123340443)
                      ·
                        rfl

theorem cell23_4008458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4008458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008458 prefixEnd_4008458 := by exact prefixLift 4008458
  have htrace : WordTrace (prefixWord ++ tailWord_4008458) baseStart_4008458 baseEnd_4008458 := by
    simpa [prefixWord, tailWord_4008458, baseEnd_4008458] using wordTrace_append hprefix tailTrace_4008458
  have hstable : (prefixWord ++ tailWord_4008458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008458).length < 2 ^ (prefixWord ++ tailWord_4008458).sum := by decide
  have hdescent : baseEnd_4008458 < baseStart_4008458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008485 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 2, 4, 2]
def baseStart_4008485 : Nat := 118140960795 + 4008485 * 2 ^ 59
def prefixEnd_4008485 : Nat := 4983230072969 + 3 ^ 40 * 4008485 * 2
def baseEnd_4008485 : Nat := 2058279501337854517702819

theorem tailTrace_4008485 : CollatzResearch.WordTrace tailWord_4008485 prefixEnd_4008485 2058279501337854517702819 := by
  unfold tailWord_4008485
  simp only [CollatzResearch.WordTrace]
  refine ⟨146201458882950914579738909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97467639255300609719825939 146201458882950914579738909)
  ·
    refine ⟨54825547081106592967402091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146201458882950914579738909 54825547081106592967402091)
    ·
      refine ⟨82238320621659889451103137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54825547081106592967402091 82238320621659889451103137)
      ·
        refine ⟨61678740466244917088327353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82238320621659889451103137 61678740466244917088327353)
        ·
          refine ⟨46259055349683687816245515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61678740466244917088327353 46259055349683687816245515)
          ·
            refine ⟨69388583024525531724368273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46259055349683687816245515 69388583024525531724368273)
            ·
              refine ⟨52041437268394148793276205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69388583024525531724368273 52041437268394148793276205)
              ·
                refine ⟨19515538975647805797478577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52041437268394148793276205 19515538975647805797478577)
                ·
                  refine ⟨14636654231735854348108933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19515538975647805797478577 14636654231735854348108933)
                  ·
                    refine ⟨2744372668450472690270425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14636654231735854348108933 2744372668450472690270425)
                    ·
                      refine ⟨2058279501337854517702819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744372668450472690270425 2058279501337854517702819)
                      ·
                        rfl

theorem cell23_4008485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_4008485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008485 prefixEnd_4008485 := by exact prefixLift 4008485
  have htrace : WordTrace (prefixWord ++ tailWord_4008485) baseStart_4008485 baseEnd_4008485 := by
    simpa [prefixWord, tailWord_4008485, baseEnd_4008485] using wordTrace_append hprefix tailTrace_4008485
  have hstable : (prefixWord ++ tailWord_4008485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008485).length < 2 ^ (prefixWord ++ tailWord_4008485).sum := by decide
  have hdescent : baseEnd_4008485 < baseStart_4008485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008498 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_4008498 : Nat := 118140960795 + 4008498 * 2 ^ 59
def prefixEnd_4008498 : Nat := 4983230072969 + 3 ^ 40 * 4008498 * 2
def baseEnd_4008498 : Nat := 2058286176586362966840259

theorem tailTrace_4008498 : CollatzResearch.WordTrace tailWord_4008498 prefixEnd_4008498 2058286176586362966840259 := by
  unfold tailWord_4008498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36550483257975954449990537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97467955354602545199974765 36550483257975954449990537)
  ·
    refine ⟨27412862443481965837492903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36550483257975954449990537 27412862443481965837492903)
    ·
      refine ⟨41119293665222948756239355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27412862443481965837492903 41119293665222948756239355)
      ·
        refine ⟨61678940497834423134359033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41119293665222948756239355 61678940497834423134359033)
        ·
          refine ⟨46259205373375817350769275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61678940497834423134359033 46259205373375817350769275)
          ·
            refine ⟨69388808060063726026153913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46259205373375817350769275 69388808060063726026153913)
            ·
              refine ⟨52041606045047794519615435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69388808060063726026153913 52041606045047794519615435)
              ·
                refine ⟨78062409067571691779423153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52041606045047794519615435 78062409067571691779423153)
                ·
                  refine ⟨58546806800678768834567365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78062409067571691779423153 58546806800678768834567365)
                  ·
                    refine ⟨10977526275127269156481381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58546806800678768834567365 10977526275127269156481381)
                    ·
                      refine ⟨2058286176586362966840259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10977526275127269156481381 2058286176586362966840259)
                      ·
                        rfl

theorem cell23_4008498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_4008498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008498 prefixEnd_4008498 := by exact prefixLift 4008498
  have htrace : WordTrace (prefixWord ++ tailWord_4008498) baseStart_4008498 baseEnd_4008498 := by
    simpa [prefixWord, tailWord_4008498, baseEnd_4008498] using wordTrace_append hprefix tailTrace_4008498
  have hstable : (prefixWord ++ tailWord_4008498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008498).length < 2 ^ (prefixWord ++ tailWord_4008498).sum := by decide
  have hdescent : baseEnd_4008498 < baseStart_4008498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008502 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4008502 : Nat := 118140960795 + 4008502 * 2 ^ 59
def prefixEnd_4008502 : Nat := 4983230072969 + 3 ^ 40 * 4008502 * 2
def baseEnd_4008502 : Nat := 2058288230508980951190241

theorem tailTrace_4008502 : CollatzResearch.WordTrace tailWord_4008502 prefixEnd_4008502 2058288230508980951190241 := by
  unfold tailWord_4008502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9137629932743082905194235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97468052615926217655405173 9137629932743082905194235)
  ·
    refine ⟨13706444899114624357791353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9137629932743082905194235 13706444899114624357791353)
    ·
      refine ⟨10279833674335968268343515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13706444899114624357791353 10279833674335968268343515)
      ·
        refine ⟨15419750511503952402515273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279833674335968268343515 15419750511503952402515273)
        ·
          refine ⟨11564812883627964301886455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15419750511503952402515273 11564812883627964301886455)
          ·
            refine ⟨17347219325441946452829683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11564812883627964301886455 17347219325441946452829683)
            ·
              refine ⟨26020828988162919679244525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347219325441946452829683 26020828988162919679244525)
              ·
                refine ⟨9757810870561094879716697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26020828988162919679244525 9757810870561094879716697)
                ·
                  refine ⟨7318358152920821159787523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9757810870561094879716697 7318358152920821159787523)
                  ·
                    refine ⟨10977537229381231739681285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7318358152920821159787523 10977537229381231739681285)
                    ·
                      refine ⟨2058288230508980951190241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10977537229381231739681285 2058288230508980951190241)
                      ·
                        rfl

theorem cell23_4008502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4008502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008502 prefixEnd_4008502 := by exact prefixLift 4008502
  have htrace : WordTrace (prefixWord ++ tailWord_4008502) baseStart_4008502 baseEnd_4008502 := by
    simpa [prefixWord, tailWord_4008502, baseEnd_4008502] using wordTrace_append hprefix tailTrace_4008502
  have hstable : (prefixWord ++ tailWord_4008502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008502).length < 2 ^ (prefixWord ++ tailWord_4008502).sum := by decide
  have hdescent : baseEnd_4008502 < baseStart_4008502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008529 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 1, 4]
def baseStart_4008529 : Nat := 118140960795 + 4008529 * 2 ^ 59
def prefixEnd_4008529 : Nat := 4983230072969 + 3 ^ 40 * 4008529 * 2
def baseEnd_4008529 : Nat := 686100698162217448517539

theorem tailTrace_4008529 : CollatzResearch.WordTrace tailWord_4008529 prefixEnd_4008529 686100698162217448517539 := by
  unfold tailWord_4008529
  simp only [CollatzResearch.WordTrace]
  refine ⟨146203063694791510094340641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97468709129861006729560427 146203063694791510094340641)
  ·
    refine ⟨109652297771093632570755481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146203063694791510094340641 109652297771093632570755481)
    ·
      refine ⟨82239223328320224428066611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109652297771093632570755481 82239223328320224428066611)
      ·
        refine ⟨123358834992480336642099917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82239223328320224428066611 123358834992480336642099917)
        ·
          refine ⟨46259563122180126240787469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123358834992480336642099917 46259563122180126240787469)
          ·
            refine ⟨17347336170817547340295301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46259563122180126240787469 17347336170817547340295301)
            ·
              refine ⟨3252625532028290126305369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17347336170817547340295301 3252625532028290126305369)
              ·
                refine ⟨2439469149021217594729027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3252625532028290126305369 2439469149021217594729027)
                ·
                  refine ⟨3659203723531826392093541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439469149021217594729027 3659203723531826392093541)
                  ·
                    refine ⟨686100698162217448517539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659203723531826392093541 686100698162217448517539)
                    ·
                      rfl

theorem cell23_4008529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_4008529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008529 prefixEnd_4008529 := by exact prefixLift 4008529
  have htrace : WordTrace (prefixWord ++ tailWord_4008529) baseStart_4008529 baseEnd_4008529 := by
    simpa [prefixWord, tailWord_4008529, baseEnd_4008529] using wordTrace_append hprefix tailTrace_4008529
  have hstable : (prefixWord ++ tailWord_4008529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008529).length < 2 ^ (prefixWord ++ tailWord_4008529).sum := by decide
  have hdescent : baseEnd_4008529 < baseStart_4008529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008548 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4008548 : Nat := 118140960795 + 4008548 * 2 ^ 59
def prefixEnd_4008548 : Nat := 4983230072969 + 3 ^ 40 * 4008548 * 2
def baseEnd_4008548 : Nat := 2058311850619087771215029

theorem tailTrace_4008548 : CollatzResearch.WordTrace tailWord_4008548 prefixEnd_4008548 2058311850619087771215029 := by
  unfold tailWord_4008548
  simp only [CollatzResearch.WordTrace]
  refine ⟨73101878340861338169641149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97469171121148450892854865 73101878340861338169641149)
  ·
    refine ⟨27413204377823001813615431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73101878340861338169641149 27413204377823001813615431)
    ·
      refine ⟨41119806566734502720423147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27413204377823001813615431 41119806566734502720423147)
      ·
        refine ⟨61679709850101754080634721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41119806566734502720423147 61679709850101754080634721)
        ·
          refine ⟨46259782387576315560476041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61679709850101754080634721 46259782387576315560476041)
          ·
            refine ⟨34694836790682236670357031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46259782387576315560476041 34694836790682236670357031)
            ·
              refine ⟨52042255186023355005535547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34694836790682236670357031 52042255186023355005535547)
              ·
                refine ⟨78063382779035032508303321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52042255186023355005535547 78063382779035032508303321)
                ·
                  refine ⟨58547537084276274381227491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78063382779035032508303321 58547537084276274381227491)
                  ·
                    refine ⟨87821305626414411571841237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58547537084276274381227491 87821305626414411571841237)
                    ·
                      refine ⟨2058311850619087771215029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87821305626414411571841237 2058311850619087771215029)
                      ·
                        rfl

theorem cell23_4008548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4008548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008548 prefixEnd_4008548 := by exact prefixLift 4008548
  have htrace : WordTrace (prefixWord ++ tailWord_4008548) baseStart_4008548 baseEnd_4008548 := by
    simpa [prefixWord, tailWord_4008548, baseEnd_4008548] using wordTrace_append hprefix tailTrace_4008548
  have hstable : (prefixWord ++ tailWord_4008548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008548).length < 2 ^ (prefixWord ++ tailWord_4008548).sum := by decide
  have hdescent : baseEnd_4008548 < baseStart_4008548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008569 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 1, 1, 3]
def baseStart_4008569 : Nat := 118140960795 + 4008569 * 2 ^ 59
def prefixEnd_4008569 : Nat := 4983230072969 + 3 ^ 40 * 4008569 * 2
def baseEnd_4008569 : Nat := 2058322633712832189052433

theorem tailTrace_4008569 : CollatzResearch.WordTrace tailWord_4008569 prefixEnd_4008569 2058322633712832189052433 := by
  unfold tailWord_4008569
  simp only [CollatzResearch.WordTrace]
  refine ⟨146204522614646596925796761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97469681743097731283864507 146204522614646596925796761)
  ·
    refine ⟨109653391960984947694347571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146204522614646596925796761 109653391960984947694347571)
    ·
      refine ⟨164480087941477421541521357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109653391960984947694347571 164480087941477421541521357)
      ·
        refine ⟨61680032978054033078070509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164480087941477421541521357 61680032978054033078070509)
        ·
          refine ⟨23130012366770262404276441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61680032978054033078070509 23130012366770262404276441)
          ·
            refine ⟨17347509275077696803207331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23130012366770262404276441 17347509275077696803207331)
            ·
              refine ⟨26021263912616545204810997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347509275077696803207331 26021263912616545204810997)
              ·
                refine ⟨2439493491807801112951031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26021263912616545204810997 2439493491807801112951031)
                ·
                  refine ⟨3659240237711701669426547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439493491807801112951031 3659240237711701669426547)
                  ·
                    refine ⟨5488860356567552504139821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659240237711701669426547 5488860356567552504139821)
                    ·
                      refine ⟨2058322633712832189052433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5488860356567552504139821 2058322633712832189052433)
                      ·
                        rfl

theorem cell23_4008569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_4008569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008569 prefixEnd_4008569 := by exact prefixLift 4008569
  have htrace : WordTrace (prefixWord ++ tailWord_4008569) baseStart_4008569 baseEnd_4008569 := by
    simpa [prefixWord, tailWord_4008569, baseEnd_4008569] using wordTrace_append hprefix tailTrace_4008569
  have hstable : (prefixWord ++ tailWord_4008569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008569).length < 2 ^ (prefixWord ++ tailWord_4008569).sum := by decide
  have hdescent : baseEnd_4008569 < baseStart_4008569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008572 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_4008572 : Nat := 118140960795 + 4008572 * 2 ^ 59
def prefixEnd_4008572 : Nat := 4983230072969 + 3 ^ 40 * 4008572 * 2
def baseEnd_4008572 : Nat := 686108058051598559104973

theorem tailTrace_4008572 : CollatzResearch.WordTrace tailWord_4008572 prefixEnd_4008572 686108058051598559104973 := by
  unfold tailWord_4008572
  simp only [CollatzResearch.WordTrace]
  refine ⟨73102316016817864219077985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97469754689090485625437313 73102316016817864219077985)
  ·
    refine ⟨54826737012613398164308489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73102316016817864219077985 54826737012613398164308489)
    ·
      refine ⟨41120052759460048623231367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54826737012613398164308489 41120052759460048623231367)
      ·
        refine ⟨61680079139190072934847051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41120052759460048623231367 61680079139190072934847051)
        ·
          refine ⟨92520118708785109402270577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61680079139190072934847051 92520118708785109402270577)
          ·
            refine ⟨69390089031588832051702933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92520118708785109402270577 69390089031588832051702933)
            ·
              refine ⟨3252660423355726502423575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69390089031588832051702933 3252660423355726502423575)
              ·
                refine ⟨4878990635033589753635363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252660423355726502423575 4878990635033589753635363)
                ·
                  refine ⟨7318485952550384630453045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878990635033589753635363 7318485952550384630453045)
                  ·
                    refine ⟨686108058051598559104973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7318485952550384630453045 686108058051598559104973)
                    ·
                      rfl

theorem cell23_4008572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_4008572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008572 prefixEnd_4008572 := by exact prefixLift 4008572
  have htrace : WordTrace (prefixWord ++ tailWord_4008572) baseStart_4008572 baseEnd_4008572 := by
    simpa [prefixWord, tailWord_4008572, baseEnd_4008572] using wordTrace_append hprefix tailTrace_4008572
  have hstable : (prefixWord ++ tailWord_4008572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008572).length < 2 ^ (prefixWord ++ tailWord_4008572).sum := by decide
  have hdescent : baseEnd_4008572 < baseStart_4008572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008609 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4008609 : Nat := 118140960795 + 4008609 * 2 ^ 59
def prefixEnd_4008609 : Nat := 4983230072969 + 3 ^ 40 * 4008609 * 2
def baseEnd_4008609 : Nat := 2058343172939012032552249

theorem tailTrace_4008609 : CollatzResearch.WordTrace tailWord_4008609 prefixEnd_4008609 2058343172939012032552249 := by
  unfold tailWord_4008609
  simp only [CollatzResearch.WordTrace]
  refine ⟨146205981534501683757252881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97470654356334455838168587 146205981534501683757252881)
  ·
    refine ⟨109654486150876262817939661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146205981534501683757252881 109654486150876262817939661)
    ·
      refine ⟨41120432306578598556727373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109654486150876262817939661 41120432306578598556727373)
      ·
        refine ⟨15420162114966974458772765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41120432306578598556727373 15420162114966974458772765)
        ·
          refine ⟨5782560793112615422039787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15420162114966974458772765 5782560793112615422039787)
          ·
            refine ⟨8673841189668923133059681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782560793112615422039787 8673841189668923133059681)
            ·
              refine ⟨6505380892251692349794761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8673841189668923133059681 6505380892251692349794761)
              ·
                refine ⟨4879035669188769262346071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6505380892251692349794761 4879035669188769262346071)
                ·
                  refine ⟨7318553503783153893519107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879035669188769262346071 7318553503783153893519107)
                  ·
                    refine ⟨10977830255674730840278661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7318553503783153893519107 10977830255674730840278661)
                    ·
                      refine ⟨2058343172939012032552249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10977830255674730840278661 2058343172939012032552249)
                      ·
                        rfl

theorem cell23_4008609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4008609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008609 prefixEnd_4008609 := by exact prefixLift 4008609
  have htrace : WordTrace (prefixWord ++ tailWord_4008609) baseStart_4008609 baseEnd_4008609 := by
    simpa [prefixWord, tailWord_4008609, baseEnd_4008609] using wordTrace_append hprefix tailTrace_4008609
  have hstable : (prefixWord ++ tailWord_4008609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008609).length < 2 ^ (prefixWord ++ tailWord_4008609).sum := by decide
  have hdescent : baseEnd_4008609 < baseStart_4008609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008629 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4008629 : Nat := 118140960795 + 4008629 * 2 ^ 59
def prefixEnd_4008629 : Nat := 4983230072969 + 3 ^ 40 * 4008629 * 2
def baseEnd_4008629 : Nat := 2058353442552101954302157

theorem tailTrace_4008629 : CollatzResearch.WordTrace tailWord_4008629 prefixEnd_4008629 2058353442552101954302157 := by
  unfold tailWord_4008629
  simp only [CollatzResearch.WordTrace]
  refine ⟨146206710994429227172980941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97471140662952818115320627 146206710994429227172980941)
  ·
    refine ⟨54827516622910960189867853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146206710994429227172980941 54827516622910960189867853)
    ·
      refine ⟨20560318733591610071200445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54827516622910960189867853 20560318733591610071200445)
      ·
        refine ⟨7710119525096853776700167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20560318733591610071200445 7710119525096853776700167)
        ·
          refine ⟨11565179287645280665050251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710119525096853776700167 11565179287645280665050251)
          ·
            refine ⟨17347768931467920997575377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565179287645280665050251 17347768931467920997575377)
            ·
              refine ⟨13010826698600940748181533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17347768931467920997575377 13010826698600940748181533)
              ·
                refine ⟨4879060011975352780568075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13010826698600940748181533 4879060011975352780568075)
                ·
                  refine ⟨7318590017963029170852113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879060011975352780568075 7318590017963029170852113)
                  ·
                    refine ⟨5488942513472271878139085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7318590017963029170852113 5488942513472271878139085)
                    ·
                      refine ⟨2058353442552101954302157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5488942513472271878139085 2058353442552101954302157)
                      ·
                        rfl

theorem cell23_4008629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4008629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008629 prefixEnd_4008629 := by exact prefixLift 4008629
  have htrace : WordTrace (prefixWord ++ tailWord_4008629) baseStart_4008629 baseEnd_4008629 := by
    simpa [prefixWord, tailWord_4008629, baseEnd_4008629] using wordTrace_append hprefix tailTrace_4008629
  have hstable : (prefixWord ++ tailWord_4008629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008629).length < 2 ^ (prefixWord ++ tailWord_4008629).sum := by decide
  have hdescent : baseEnd_4008629 < baseStart_4008629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008695 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_4008695 : Nat := 118140960795 + 4008695 * 2 ^ 59
def prefixEnd_4008695 : Nat := 4983230072969 + 3 ^ 40 * 4008695 * 2
def baseEnd_4008695 : Nat := 2058387332275298696076853

theorem tailTrace_4008695 : CollatzResearch.WordTrace tailWord_4008695 prefixEnd_4008695 2058387332275298696076853 := by
  unfold tailWord_4008695
  simp only [CollatzResearch.WordTrace]
  refine ⟨146209118212190120444883539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97472745474793413629922359 146209118212190120444883539)
  ·
    refine ⟨219313677318285180667325309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146209118212190120444883539 219313677318285180667325309)
    ·
      refine ⟨82242628994356942750246991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219313677318285180667325309 82242628994356942750246991)
      ·
        refine ⟨123363943491535414125370487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82242628994356942750246991 123363943491535414125370487)
        ·
          refine ⟨185045915237303121188055731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123363943491535414125370487 185045915237303121188055731)
          ·
            refine ⟨277568872855954681782083597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185045915237303121188055731 277568872855954681782083597)
            ·
              refine ⟨104088327320983005668281349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277568872855954681782083597 104088327320983005668281349)
              ·
                refine ⟨19516561372684313562802753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104088327320983005668281349 19516561372684313562802753)
                ·
                  refine ⟨14637421029513235172102065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19516561372684313562802753 14637421029513235172102065)
                  ·
                    refine ⟨10978065772134926379076549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14637421029513235172102065 10978065772134926379076549)
                    ·
                      refine ⟨2058387332275298696076853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10978065772134926379076549 2058387332275298696076853)
                      ·
                        rfl

theorem cell23_4008695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_4008695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008695 prefixEnd_4008695 := by exact prefixLift 4008695
  have htrace : WordTrace (prefixWord ++ tailWord_4008695) baseStart_4008695 baseEnd_4008695 := by
    simpa [prefixWord, tailWord_4008695, baseEnd_4008695] using wordTrace_append hprefix tailTrace_4008695
  have hstable : (prefixWord ++ tailWord_4008695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008695).length < 2 ^ (prefixWord ++ tailWord_4008695).sum := by decide
  have hdescent : baseEnd_4008695 < baseStart_4008695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008705 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 7]
def baseStart_4008705 : Nat := 118140960795 + 4008705 * 2 ^ 59
def prefixEnd_4008705 : Nat := 4983230072969 + 3 ^ 40 * 4008705 * 2
def baseEnd_4008705 : Nat := 228710274120204850772423

theorem tailTrace_4008705 : CollatzResearch.WordTrace tailWord_4008705 prefixEnd_4008705 228710274120204850772423 := by
  unfold tailWord_4008705
  simp only [CollatzResearch.WordTrace]
  refine ⟨146209482942153892152747569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97472988628102594768498379 146209482942153892152747569)
  ·
    refine ⟨109657112206615419114560677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146209482942153892152747569 109657112206615419114560677)
    ·
      refine ⟨20560708538740391083980127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109657112206615419114560677 20560708538740391083980127)
      ·
        refine ⟨30841062808110586625970191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20560708538740391083980127 30841062808110586625970191)
        ·
          refine ⟨46261594212165879938955287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30841062808110586625970191 46261594212165879938955287)
          ·
            refine ⟨69392391318248819908432931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46261594212165879938955287 69392391318248819908432931)
            ·
              refine ⟨104088586977373229862649397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69392391318248819908432931 104088586977373229862649397)
              ·
                refine ⟨9758305029128740299623381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104088586977373229862649397 9758305029128740299623381)
                ·
                  refine ⟨228710274120204850772423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9758305029128740299623381 228710274120204850772423)
                  ·
                    rfl

theorem cell23_4008705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_4008705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008705 prefixEnd_4008705 := by exact prefixLift 4008705
  have htrace : WordTrace (prefixWord ++ tailWord_4008705) baseStart_4008705 baseEnd_4008705 := by
    simpa [prefixWord, tailWord_4008705, baseEnd_4008705] using wordTrace_append hprefix tailTrace_4008705
  have hstable : (prefixWord ++ tailWord_4008705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008705).length < 2 ^ (prefixWord ++ tailWord_4008705).sum := by decide
  have hdescent : baseEnd_4008705 < baseStart_4008705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008712 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_4008712 : Nat := 118140960795 + 4008712 * 2 ^ 59
def prefixEnd_4008712 : Nat := 4983230072969 + 3 ^ 40 * 4008712 * 2
def baseEnd_4008712 : Nat := 2058396061446425129564275

theorem tailTrace_4008712 : CollatzResearch.WordTrace tailWord_4008712 prefixEnd_4008712 2058396061446425129564275 := by
  unfold tailWord_4008712
  simp only [CollatzResearch.WordTrace]
  refine ⟨73104869126564266174126195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97473158835419021565501593 73104869126564266174126195)
  ·
    refine ⟨109657303689846399261189293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73104869126564266174126195 109657303689846399261189293)
    ·
      refine ⟨41121488883692399722945985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109657303689846399261189293 41121488883692399722945985)
      ·
        refine ⟨30841116662769299792209489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41121488883692399722945985 30841116662769299792209489)
        ·
          refine ⟨23130837497076974844157117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30841116662769299792209489 23130837497076974844157117)
          ·
            refine ⟨8674064061403865566558919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23130837497076974844157117 8674064061403865566558919)
            ·
              refine ⟨13011096092105798349838379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674064061403865566558919 13011096092105798349838379)
              ·
                refine ⟨19516644138158697524757569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13011096092105798349838379 19516644138158697524757569)
                ·
                  refine ⟨14637483103619023143568177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19516644138158697524757569 14637483103619023143568177)
                  ·
                    refine ⟨10978112327714267357676133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14637483103619023143568177 10978112327714267357676133)
                    ·
                      refine ⟨2058396061446425129564275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10978112327714267357676133 2058396061446425129564275)
                      ·
                        rfl

theorem cell23_4008712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_4008712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008712 prefixEnd_4008712 := by exact prefixLift 4008712
  have htrace : WordTrace (prefixWord ++ tailWord_4008712) baseStart_4008712 baseEnd_4008712 := by
    simpa [prefixWord, tailWord_4008712, baseEnd_4008712] using wordTrace_append hprefix tailTrace_4008712
  have hstable : (prefixWord ++ tailWord_4008712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008712).length < 2 ^ (prefixWord ++ tailWord_4008712).sum := by decide
  have hdescent : baseEnd_4008712 < baseStart_4008712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008750 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4008750 : Nat := 118140960795 + 4008750 * 2 ^ 59
def prefixEnd_4008750 : Nat := 4983230072969 + 3 ^ 40 * 4008750 * 2
def baseEnd_4008750 : Nat := 2058415573711295980889101

theorem tailTrace_4008750 : CollatzResearch.WordTrace tailWord_4008750 prefixEnd_4008750 2058415573711295980889101 := by
  unfold tailWord_4008750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18276390528373858104766963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97474082817993909892090469 18276390528373858104766963)
  ·
    refine ⟨27414585792560787157150445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18276390528373858104766963 27414585792560787157150445)
    ·
      refine ⟨10280469672210295183931417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27414585792560787157150445 10280469672210295183931417)
      ·
        refine ⟨7710352254157721387948563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10280469672210295183931417 7710352254157721387948563)
        ·
          refine ⟨11565528381236582081922845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710352254157721387948563 11565528381236582081922845)
          ·
            refine ⟨4337073142963718280721067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11565528381236582081922845 4337073142963718280721067)
            ·
              refine ⟨6505609714445577421081601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337073142963718280721067 6505609714445577421081601)
              ·
                refine ⟨4879207285834183065811201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6505609714445577421081601 4879207285834183065811201)
                ·
                  refine ⟨3659405464375637299358401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879207285834183065811201 3659405464375637299358401)
                  ·
                    refine ⟨2744554098281727974518801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659405464375637299358401 2744554098281727974518801)
                    ·
                      refine ⟨2058415573711295980889101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744554098281727974518801 2058415573711295980889101)
                      ·
                        rfl

theorem cell23_4008750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4008750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008750 prefixEnd_4008750 := by exact prefixLift 4008750
  have htrace : WordTrace (prefixWord ++ tailWord_4008750) baseStart_4008750 baseEnd_4008750 := by
    simpa [prefixWord, tailWord_4008750, baseEnd_4008750] using wordTrace_append hprefix tailTrace_4008750
  have hstable : (prefixWord ++ tailWord_4008750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008750).length < 2 ^ (prefixWord ++ tailWord_4008750).sum := by decide
  have hdescent : baseEnd_4008750 < baseStart_4008750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008792 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_4008792 : Nat := 118140960795 + 4008792 * 2 ^ 59
def prefixEnd_4008792 : Nat := 4983230072969 + 3 ^ 40 * 4008792 * 2
def baseEnd_4008792 : Nat := 2058437139898784816563907

theorem tailTrace_4008792 : CollatzResearch.WordTrace tailWord_4008792 prefixEnd_4008792 2058437139898784816563907 := by
  unfold tailWord_4008792
  simp only [CollatzResearch.WordTrace]
  refine ⟨73106328046419353005582315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97475104061892470674109753 73106328046419353005582315)
  ·
    refine ⟨109659492069629029508373473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73106328046419353005582315 109659492069629029508373473)
    ·
      refine ⟨82244619052221772131280105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109659492069629029508373473 82244619052221772131280105)
      ·
        refine ⟨61683464289166329098460079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82244619052221772131280105 61683464289166329098460079)
        ·
          refine ⟨92525196433749493647690119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61683464289166329098460079 92525196433749493647690119)
          ·
            refine ⟨138787794650624240471535179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92525196433749493647690119 138787794650624240471535179)
            ·
              refine ⟨208181691975936360707302769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138787794650624240471535179 208181691975936360707302769)
              ·
                refine ⟨156136268981952270530477077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208181691975936360707302769 156136268981952270530477077)
                ·
                  refine ⟨7318887608529012681116113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156136268981952270530477077 7318887608529012681116113)
                  ·
                    refine ⟨5489165706396759510837085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7318887608529012681116113 5489165706396759510837085)
                    ·
                      refine ⟨2058437139898784816563907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5489165706396759510837085 2058437139898784816563907)
                      ·
                        rfl

theorem cell23_4008792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_4008792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008792 prefixEnd_4008792 := by exact prefixLift 4008792
  have htrace : WordTrace (prefixWord ++ tailWord_4008792) baseStart_4008792 baseEnd_4008792 := by
    simpa [prefixWord, tailWord_4008792, baseEnd_4008792] using wordTrace_append hprefix tailTrace_4008792
  have hstable : (prefixWord ++ tailWord_4008792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008792).length < 2 ^ (prefixWord ++ tailWord_4008792).sum := by decide
  have hdescent : baseEnd_4008792 < baseStart_4008792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008812 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 6]
def baseStart_4008812 : Nat := 118140960795 + 4008812 * 2 ^ 59
def prefixEnd_4008812 : Nat := 4983230072969 + 3 ^ 40 * 4008812 * 2
def baseEnd_4008812 : Nat := 228716378834652748701535

theorem tailTrace_4008812 : CollatzResearch.WordTrace tailWord_4008812 prefixEnd_4008812 228716378834652748701535 := by
  unfold tailWord_4008812
  simp only [CollatzResearch.WordTrace]
  refine ⟨73106692776383124713446345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97475590368510832951261793 73106692776383124713446345)
  ·
    refine ⟨54830019582287343535084759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73106692776383124713446345 54830019582287343535084759)
    ·
      refine ⟨82245029373431015302627139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54830019582287343535084759 82245029373431015302627139)
      ·
        refine ⟨123367544060146522953940709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82245029373431015302627139 123367544060146522953940709)
        ·
          refine ⟨23131414511277473053863883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123367544060146522953940709 23131414511277473053863883)
          ·
            refine ⟨34697121766916209580795825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23131414511277473053863883 34697121766916209580795825)
            ·
              refine ⟨26022841325187157185596869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34697121766916209580795825 26022841325187157185596869)
              ·
                refine ⟨4879282748472591972299413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26022841325187157185596869 4879282748472591972299413)
                ·
                  refine ⟨228716378834652748701535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4879282748472591972299413 228716378834652748701535)
                  ·
                    rfl

theorem cell23_4008812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_4008812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008812 prefixEnd_4008812 := by exact prefixLift 4008812
  have htrace : WordTrace (prefixWord ++ tailWord_4008812) baseStart_4008812 baseEnd_4008812 := by
    simpa [prefixWord, tailWord_4008812, baseEnd_4008812] using wordTrace_append hprefix tailTrace_4008812
  have hstable : (prefixWord ++ tailWord_4008812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008812).length < 2 ^ (prefixWord ++ tailWord_4008812).sum := by decide
  have hdescent : baseEnd_4008812 < baseStart_4008812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008815 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_4008815 : Nat := 118140960795 + 4008815 * 2 ^ 59
def prefixEnd_4008815 : Nat := 4983230072969 + 3 ^ 40 * 4008815 * 2
def baseEnd_4008815 : Nat := 2058448949953838226576301

theorem tailTrace_4008815 : CollatzResearch.WordTrace tailWord_4008815 prefixEnd_4008815 2058448949953838226576301 := by
  unfold tailWord_4008815
  simp only [CollatzResearch.WordTrace]
  refine ⟨146213494971755380939251899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97475663314503587292834599 146213494971755380939251899)
  ·
    refine ⟨219320242457633071408877849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146213494971755380939251899 219320242457633071408877849)
    ·
      refine ⟨164490181843224803556658387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219320242457633071408877849 164490181843224803556658387)
      ·
        refine ⟨246735272764837205334987581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164490181843224803556658387 246735272764837205334987581)
        ·
          refine ⟨92525727286813952000620343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246735272764837205334987581 92525727286813952000620343)
          ·
            refine ⟨138788590930220928000930515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92525727286813952000620343 138788590930220928000930515)
            ·
              refine ⟨208182886395331392001395773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138788590930220928000930515 208182886395331392001395773)
              ·
                refine ⟨78068582398249272000523415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208182886395331392001395773 78068582398249272000523415)
                ·
                  refine ⟨117102873597373908000785123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78068582398249272000523415 117102873597373908000785123)
                  ·
                    refine ⟨175654310396060862001177685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117102873597373908000785123 175654310396060862001177685)
                    ·
                      refine ⟨2058448949953838226576301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 175654310396060862001177685 2058448949953838226576301)
                      ·
                        rfl

theorem cell23_4008815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_4008815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008815 prefixEnd_4008815 := by exact prefixLift 4008815
  have htrace : WordTrace (prefixWord ++ tailWord_4008815) baseStart_4008815 baseEnd_4008815 := by
    simpa [prefixWord, tailWord_4008815, baseEnd_4008815] using wordTrace_append hprefix tailTrace_4008815
  have hstable : (prefixWord ++ tailWord_4008815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008815).length < 2 ^ (prefixWord ++ tailWord_4008815).sum := by decide
  have hdescent : baseEnd_4008815 < baseStart_4008815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008829 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 6]
def baseStart_4008829 : Nat := 118140960795 + 4008829 * 2 ^ 59
def prefixEnd_4008829 : Nat := 4983230072969 + 3 ^ 40 * 4008829 * 2
def baseEnd_4008829 : Nat := 228717348742555685755693

theorem tailTrace_4008829 : CollatzResearch.WordTrace tailWord_4008829 prefixEnd_4008829 228717348742555685755693 := by
  unfold tailWord_4008829
  simp only [CollatzResearch.WordTrace]
  refine ⟨146214005593704661330261541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97476003729136440886841027 146214005593704661330261541)
  ·
    refine ⟨27415126048819623999424039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146214005593704661330261541 27415126048819623999424039)
    ·
      refine ⟨41122689073229435999136059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27415126048819623999424039 41122689073229435999136059)
      ·
        refine ⟨61684033609844153998704089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41122689073229435999136059 61684033609844153998704089)
        ·
          refine ⟨46263025207383115499028067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61684033609844153998704089 46263025207383115499028067)
          ·
            refine ⟨69394537811074673248542101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46263025207383115499028067 69394537811074673248542101)
            ·
              refine ⟨3252868959894125308525411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69394537811074673248542101 3252868959894125308525411)
              ·
                refine ⟨4879303439841187962788117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252868959894125308525411 4879303439841187962788117)
                ·
                  refine ⟨228717348742555685755693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4879303439841187962788117 228717348742555685755693)
                  ·
                    rfl

theorem cell23_4008829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_4008829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008829 prefixEnd_4008829 := by exact prefixLift 4008829
  have htrace : WordTrace (prefixWord ++ tailWord_4008829) baseStart_4008829 baseEnd_4008829 := by
    simpa [prefixWord, tailWord_4008829, baseEnd_4008829] using wordTrace_append hprefix tailTrace_4008829
  have hstable : (prefixWord ++ tailWord_4008829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008829).length < 2 ^ (prefixWord ++ tailWord_4008829).sum := by decide
  have hdescent : baseEnd_4008829 < baseStart_4008829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008889 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 1, 6]
def baseStart_4008889 : Nat := 118140960795 + 4008889 * 2 ^ 59
def prefixEnd_4008889 : Nat := 4983230072969 + 3 ^ 40 * 4008889 * 2
def baseEnd_4008889 : Nat := 686162315840756979016987

theorem tailTrace_4008889 : CollatzResearch.WordTrace tailWord_4008889 prefixEnd_4008889 686162315840756979016987 := by
  unfold tailWord_4008889
  simp only [CollatzResearch.WordTrace]
  refine ⟨146216193973487291577445721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97477462648991527718297147 146216193973487291577445721)
  ·
    refine ⟨109662145480115468683084291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146216193973487291577445721 109662145480115468683084291)
    ·
      refine ⟨164493218220173203024626437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109662145480115468683084291 164493218220173203024626437)
      ·
        refine ⟨30842478416282475567117457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164493218220173203024626437 30842478416282475567117457)
        ·
          refine ⟨23131858812211856675338093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30842478416282475567117457 23131858812211856675338093)
          ·
            refine ⟨8674447054579446253251785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23131858812211856675338093 8674447054579446253251785)
            ·
              refine ⟨6505835290934584689938839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8674447054579446253251785 6505835290934584689938839)
              ·
                refine ⟨9758752936401877034908259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505835290934584689938839 9758752936401877034908259)
                ·
                  refine ⟨14638129404602815552362389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9758752936401877034908259 14638129404602815552362389)
                  ·
                    refine ⟨686162315840756979016987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14638129404602815552362389 686162315840756979016987)
                    ·
                      rfl

theorem cell23_4008889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_4008889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008889 prefixEnd_4008889 := by exact prefixLift 4008889
  have htrace : WordTrace (prefixWord ++ tailWord_4008889) baseStart_4008889 baseEnd_4008889 := by
    simpa [prefixWord, tailWord_4008889, baseEnd_4008889] using wordTrace_append hprefix tailTrace_4008889
  have hstable : (prefixWord ++ tailWord_4008889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008889).length < 2 ^ (prefixWord ++ tailWord_4008889).sum := by decide
  have hdescent : baseEnd_4008889 < baseStart_4008889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008896 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 5, 2, 2]
def baseStart_4008896 : Nat := 118140960795 + 4008896 * 2 ^ 59
def prefixEnd_4008896 : Nat := 4983230072969 + 3 ^ 40 * 4008896 * 2
def baseEnd_4008896 : Nat := 2058490541886852409663429

theorem tailTrace_4008896 : CollatzResearch.WordTrace tailWord_4008896 prefixEnd_4008896 2058490541886852409663429 := by
  unfold tailWord_4008896
  simp only [CollatzResearch.WordTrace]
  refine ⟨73108224642230965886475271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97477632856307954515300361 73108224642230965886475271)
  ·
    refine ⟨109662336963346448829712907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73108224642230965886475271 109662336963346448829712907)
    ·
      refine ⟨164493505445019673244569361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109662336963346448829712907 164493505445019673244569361)
      ·
        refine ⟨123370129083764754933427021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164493505445019673244569361 123370129083764754933427021)
        ·
          refine ⟨46263798406411783100035133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123370129083764754933427021 46263798406411783100035133)
          ·
            refine ⟨17348924402404418662513175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46263798406411783100035133 17348924402404418662513175)
            ·
              refine ⟨26023386603606627993769763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17348924402404418662513175 26023386603606627993769763)
              ·
                refine ⟨39035079905409941990654645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26023386603606627993769763 39035079905409941990654645)
                ·
                  refine ⟨3659538741132182061623873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39035079905409941990654645 3659538741132182061623873)
                  ·
                    refine ⟨2744654055849136546217905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659538741132182061623873 2744654055849136546217905)
                    ·
                      refine ⟨2058490541886852409663429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744654055849136546217905 2058490541886852409663429)
                      ·
                        rfl

theorem cell23_4008896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_4008896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008896 prefixEnd_4008896 := by exact prefixLift 4008896
  have htrace : WordTrace (prefixWord ++ tailWord_4008896) baseStart_4008896 baseEnd_4008896 := by
    simpa [prefixWord, tailWord_4008896, baseEnd_4008896] using wordTrace_append hprefix tailTrace_4008896
  have hstable : (prefixWord ++ tailWord_4008896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008896).length < 2 ^ (prefixWord ++ tailWord_4008896).sum := by decide
  have hdescent : baseEnd_4008896 < baseStart_4008896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008930 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4008930 : Nat := 118140960795 + 4008930 * 2 ^ 59
def prefixEnd_4008930 : Nat := 4983230072969 + 3 ^ 40 * 4008930 * 2
def baseEnd_4008930 : Nat := 2058508000229105276638273

theorem tailTrace_4008930 : CollatzResearch.WordTrace tailWord_4008930 prefixEnd_4008930 2058508000229105276638273 := by
  unfold tailWord_4008930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36554422341584688894922061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97478459577559170386458829 36554422341584688894922061)
  ·
    refine ⟨13707908378094258335595773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36554422341584688894922061 13707908378094258335595773)
    ·
      refine ⟨5140465641785346875848415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13707908378094258335595773 5140465641785346875848415)
      ·
        refine ⟨7710698462678020313772623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140465641785346875848415 7710698462678020313772623)
        ·
          refine ⟨11566047694017030470658935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710698462678020313772623 11566047694017030470658935)
          ·
            refine ⟨17349071541025545705988403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566047694017030470658935 17349071541025545705988403)
            ·
              refine ⟨26023607311538318558982605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17349071541025545705988403 26023607311538318558982605)
              ·
                refine ⟨9758852741826869459618477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26023607311538318558982605 9758852741826869459618477)
                ·
                  refine ⟨3659569778185076047356929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9758852741826869459618477 3659569778185076047356929)
                  ·
                    refine ⟨2744677333638807035517697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659569778185076047356929 2744677333638807035517697)
                    ·
                      refine ⟨2058508000229105276638273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744677333638807035517697 2058508000229105276638273)
                      ·
                        rfl

theorem cell23_4008930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4008930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008930 prefixEnd_4008930 := by exact prefixLift 4008930
  have htrace : WordTrace (prefixWord ++ tailWord_4008930) baseStart_4008930 baseEnd_4008930 := by
    simpa [prefixWord, tailWord_4008930, baseEnd_4008930] using wordTrace_append hprefix tailTrace_4008930
  have hstable : (prefixWord ++ tailWord_4008930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008930).length < 2 ^ (prefixWord ++ tailWord_4008930).sum := by decide
  have hdescent : baseEnd_4008930 < baseStart_4008930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008932 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_4008932 : Nat := 118140960795 + 4008932 * 2 ^ 59
def prefixEnd_4008932 : Nat := 4983230072969 + 3 ^ 40 * 4008932 * 2
def baseEnd_4008932 : Nat := 686169675730138089604421

theorem tailTrace_4008932 : CollatzResearch.WordTrace tailWord_4008932 prefixEnd_4008932 686169675730138089604421 := by
  unfold tailWord_4008932
  simp only [CollatzResearch.WordTrace]
  refine ⟨73108881156165754960630525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97478508208221006614174033 73108881156165754960630525)
  ·
    refine ⟨27415830433562158110236447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73108881156165754960630525 27415830433562158110236447)
    ·
      refine ⟨41123745650343237165354671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27415830433562158110236447 41123745650343237165354671)
      ·
        refine ⟨61685618475514855748032007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41123745650343237165354671 61685618475514855748032007)
        ·
          refine ⟨92528427713272283622048011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61685618475514855748032007 92528427713272283622048011)
          ·
            refine ⟨138792641569908425433072017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92528427713272283622048011 138792641569908425433072017)
            ·
              refine ⟨104094481177431319074804013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138792641569908425433072017 104094481177431319074804013)
              ·
                refine ⟨39035430441536744653051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104094481177431319074804013 39035430441536744653051505)
                ·
                  refine ⟨29276572831152558489788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39035430441536744653051505 29276572831152558489788629)
                  ·
                    refine ⟨686169675730138089604421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29276572831152558489788629 686169675730138089604421)
                    ·
                      rfl

theorem cell23_4008932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_4008932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4008932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4008932 prefixEnd_4008932 := by exact prefixLift 4008932
  have htrace : WordTrace (prefixWord ++ tailWord_4008932) baseStart_4008932 baseEnd_4008932 := by
    simpa [prefixWord, tailWord_4008932, baseEnd_4008932] using wordTrace_append hprefix tailTrace_4008932
  have hstable : (prefixWord ++ tailWord_4008932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008932).length < 2 ^ (prefixWord ++ tailWord_4008932).sum := by decide
  have hdescent : baseEnd_4008932 < baseStart_4008932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009003 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 2, 2, 2]
def baseStart_4009003 : Nat := 118140960795 + 4009003 * 2 ^ 59
def prefixEnd_4009003 : Nat := 4983230072969 + 3 ^ 40 * 4009003 * 2
def baseEnd_4009003 : Nat := 2058545484316883491025437

theorem tailTrace_4009003 : CollatzResearch.WordTrace tailWord_4009003 prefixEnd_4009003 2058545484316883491025437 := by
  unfold tailWord_4009003
  simp only [CollatzResearch.WordTrace]
  refine ⟨146220351895074289047095663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97480234596716192698063775 146220351895074289047095663)
  ·
    refine ⟨219330527842611433570643495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146220351895074289047095663 219330527842611433570643495)
    ·
      refine ⟨328995791763917150355965243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219330527842611433570643495 328995791763917150355965243)
      ·
        refine ⟨493493687645875725533947865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328995791763917150355965243 493493687645875725533947865)
        ·
          refine ⟨370120265734406794150460899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493493687645875725533947865 370120265734406794150460899)
          ·
            refine ⟨555180398601610191225691349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370120265734406794150460899 555180398601610191225691349)
            ·
              refine ⟨13012040592225238856852141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 555180398601610191225691349 13012040592225238856852141)
              ·
                refine ⟨4879515222084464571319553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13012040592225238856852141 4879515222084464571319553)
                ·
                  refine ⟨3659636416563348428489665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879515222084464571319553 3659636416563348428489665)
                  ·
                    refine ⟨2744727312422511321367249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659636416563348428489665 2744727312422511321367249)
                    ·
                      refine ⟨2058545484316883491025437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744727312422511321367249 2058545484316883491025437)
                      ·
                        rfl

theorem cell23_4009003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 2, 2].length) (baseStart_4009003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009003 prefixEnd_4009003 := by exact prefixLift 4009003
  have htrace : WordTrace (prefixWord ++ tailWord_4009003) baseStart_4009003 baseEnd_4009003 := by
    simpa [prefixWord, tailWord_4009003, baseEnd_4009003] using wordTrace_append hprefix tailTrace_4009003
  have hstable : (prefixWord ++ tailWord_4009003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009003).length < 2 ^ (prefixWord ++ tailWord_4009003).sum := by decide
  have hdescent : baseEnd_4009003 < baseStart_4009003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009037 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4009037 : Nat := 118140960795 + 4009037 * 2 ^ 59
def prefixEnd_4009037 : Nat := 4983230072969 + 3 ^ 40 * 4009037 * 2
def baseEnd_4009037 : Nat := 2058562942659136358000281

theorem tailTrace_4009037 : CollatzResearch.WordTrace tailWord_4009037 prefixEnd_4009037 2058562942659136358000281 := by
  unfold tailWord_4009037
  simp only [CollatzResearch.WordTrace]
  refine ⟨146221591976951112853833365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97481061317967408569222243 146221591976951112853833365)
  ·
    refine ⟨6854137123919583415023439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146221591976951112853833365 6854137123919583415023439)
    ·
      refine ⟨10281205685879375122535159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6854137123919583415023439 10281205685879375122535159)
      ·
        refine ⟨15421808528819062683802739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10281205685879375122535159 15421808528819062683802739)
        ·
          refine ⟨23132712793228594025704109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15421808528819062683802739 23132712793228594025704109)
          ·
            refine ⟨8674767297460722759639041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23132712793228594025704109 8674767297460722759639041)
            ·
              refine ⟨6506075473095542069729281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8674767297460722759639041 6506075473095542069729281)
              ·
                refine ⟨4879556604821656552296961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6506075473095542069729281 4879556604821656552296961)
                ·
                  refine ⟨3659667453616242414222721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879556604821656552296961 3659667453616242414222721)
                  ·
                    refine ⟨2744750590212181810667041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659667453616242414222721 2744750590212181810667041)
                    ·
                      refine ⟨2058562942659136358000281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744750590212181810667041 2058562942659136358000281)
                      ·
                        rfl

theorem cell23_4009037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4009037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009037 prefixEnd_4009037 := by exact prefixLift 4009037
  have htrace : WordTrace (prefixWord ++ tailWord_4009037) baseStart_4009037 baseEnd_4009037 := by
    simpa [prefixWord, tailWord_4009037, baseEnd_4009037] using wordTrace_append hprefix tailTrace_4009037
  have hstable : (prefixWord ++ tailWord_4009037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009037).length < 2 ^ (prefixWord ++ tailWord_4009037).sum := by decide
  have hdescent : baseEnd_4009037 < baseStart_4009037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009054 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4009054 : Nat := 118140960795 + 4009054 * 2 ^ 59
def prefixEnd_4009054 : Nat := 4983230072969 + 3 ^ 40 * 4009054 * 2
def baseEnd_4009054 : Nat := 2058571671830262791487703

theorem tailTrace_4009054 : CollatzResearch.WordTrace tailWord_4009054 prefixEnd_4009054 2058571671830262791487703 := by
  unfold tailWord_4009054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277776502236190594650277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97481474678593016504801477 18277776502236190594650277)
  ·
    refine ⟨3427083094169285736496927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18277776502236190594650277 3427083094169285736496927)
    ·
      refine ⟨5140624641253928604745391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427083094169285736496927 5140624641253928604745391)
      ·
        refine ⟨7710936961880892907118087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140624641253928604745391 7710936961880892907118087)
        ·
          refine ⟨11566405442821339360677131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710936961880892907118087 11566405442821339360677131)
          ·
            refine ⟨17349608164232009041015697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566405442821339360677131 17349608164232009041015697)
            ·
              refine ⟨13012206123174006780761773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17349608164232009041015697 13012206123174006780761773)
              ·
                refine ⟨4879577296190252542785665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13012206123174006780761773 4879577296190252542785665)
                ·
                  refine ⟨3659682972142689407089249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879577296190252542785665 3659682972142689407089249)
                  ·
                    refine ⟨2744762229107017055316937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659682972142689407089249 2744762229107017055316937)
                    ·
                      refine ⟨2058571671830262791487703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744762229107017055316937 2058571671830262791487703)
                      ·
                        rfl

theorem cell23_4009054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4009054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009054 prefixEnd_4009054 := by exact prefixLift 4009054
  have htrace : WordTrace (prefixWord ++ tailWord_4009054) baseStart_4009054 baseEnd_4009054 := by
    simpa [prefixWord, tailWord_4009054, baseEnd_4009054] using wordTrace_append hprefix tailTrace_4009054
  have hstable : (prefixWord ++ tailWord_4009054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009054).length < 2 ^ (prefixWord ++ tailWord_4009054).sum := by decide
  have hdescent : baseEnd_4009054 < baseStart_4009054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009059 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4009059 : Nat := 118140960795 + 4009059 * 2 ^ 59
def prefixEnd_4009059 : Nat := 4983230072969 + 3 ^ 40 * 4009059 * 2
def baseEnd_4009059 : Nat := 2058574239233535271925179

theorem tailTrace_4009059 : CollatzResearch.WordTrace tailWord_4009059 prefixEnd_4009059 2058574239233535271925179 := by
  unfold tailWord_4009059
  simp only [CollatzResearch.WordTrace]
  refine ⟨146222394382871410611134231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97481596255247607074089487 146222394382871410611134231)
  ·
    refine ⟨219333591574307115916701347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146222394382871410611134231 219333591574307115916701347)
    ·
      refine ⟨329000387361460673875052021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219333591574307115916701347 329000387361460673875052021)
      ·
        refine ⟨30843786315136938175786127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329000387361460673875052021 30843786315136938175786127)
        ·
          refine ⟨46265679472705407263679191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30843786315136938175786127 46265679472705407263679191)
          ·
            refine ⟨69398519209058110895518787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46265679472705407263679191 69398519209058110895518787)
            ·
              refine ⟨104097778813587166343278181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69398519209058110895518787 104097778813587166343278181)
              ·
                refine ⟨19518333527547593689364659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104097778813587166343278181 19518333527547593689364659)
                ·
                  refine ⟨29277500291321390534046989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19518333527547593689364659 29277500291321390534046989)
                  ·
                    refine ⟨10979062609245521450267621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29277500291321390534046989 10979062609245521450267621)
                    ·
                      refine ⟨2058574239233535271925179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10979062609245521450267621 2058574239233535271925179)
                      ·
                        rfl

theorem cell23_4009059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4009059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009059 prefixEnd_4009059 := by exact prefixLift 4009059
  have htrace : WordTrace (prefixWord ++ tailWord_4009059) baseStart_4009059 baseEnd_4009059 := by
    simpa [prefixWord, tailWord_4009059, baseEnd_4009059] using wordTrace_append hprefix tailTrace_4009059
  have hstable : (prefixWord ++ tailWord_4009059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009059).length < 2 ^ (prefixWord ++ tailWord_4009059).sum := by decide
  have hdescent : baseEnd_4009059 < baseStart_4009059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009137 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 1, 4]
def baseStart_4009137 : Nat := 118140960795 + 4009137 * 2 ^ 59
def prefixEnd_4009137 : Nat := 4983230072969 + 3 ^ 40 * 4009137 * 2
def baseEnd_4009137 : Nat := 686204763574861988916607

theorem tailTrace_4009137 : CollatzResearch.WordTrace tailWord_4009137 prefixEnd_4009137 686204763574861988916607 := by
  unfold tailWord_4009137
  simp only [CollatzResearch.WordTrace]
  refine ⟨146225239276588829932473665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97483492851059219954982443 146225239276588829932473665)
  ·
    refine ⟨109668929457441622449355249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146225239276588829932473665 109668929457441622449355249)
    ·
      refine ⟨82251697093081216837016437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109668929457441622449355249 82251697093081216837016437)
      ·
        refine ⟨7711096602476364078470291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82251697093081216837016437 7711096602476364078470291)
        ·
          refine ⟨11566644903714546117705437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711096602476364078470291 11566644903714546117705437)
          ·
            refine ⟨4337491838892954794139539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11566644903714546117705437 4337491838892954794139539)
            ·
              refine ⟨6506237758339432191209309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337491838892954794139539 6506237758339432191209309)
              ·
                refine ⟨2439839159377287071703491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6506237758339432191209309 2439839159377287071703491)
                ·
                  refine ⟨3659758739065930607555237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439839159377287071703491 3659758739065930607555237)
                  ·
                    refine ⟨686204763574861988916607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659758739065930607555237 686204763574861988916607)
                    ·
                      rfl

theorem cell23_4009137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_4009137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009137 prefixEnd_4009137 := by exact prefixLift 4009137
  have htrace : WordTrace (prefixWord ++ tailWord_4009137) baseStart_4009137 baseEnd_4009137 := by
    simpa [prefixWord, tailWord_4009137, baseEnd_4009137] using wordTrace_append hprefix tailTrace_4009137
  have hstable : (prefixWord ++ tailWord_4009137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009137).length < 2 ^ (prefixWord ++ tailWord_4009137).sum := by decide
  have hdescent : baseEnd_4009137 < baseStart_4009137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009154 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4009154 : Nat := 118140960795 + 4009154 * 2 ^ 59
def prefixEnd_4009154 : Nat := 4983230072969 + 3 ^ 40 * 4009154 * 2
def baseEnd_4009154 : Nat := 686207673298570800079081

theorem tailTrace_4009154 : CollatzResearch.WordTrace tailWord_4009154 prefixEnd_4009154 686207673298570800079081 := by
  unfold tailWord_4009154
  simp only [CollatzResearch.WordTrace]
  refine ⟨36556464829381810458960629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97483906211684827890561677 36556464829381810458960629)
  ·
    refine ⟨3427168577754544730527559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36556464829381810458960629 3427168577754544730527559)
    ·
      refine ⟨5140752866631817095791339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427168577754544730527559 5140752866631817095791339)
      ·
        refine ⟨7711129299947725643687009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140752866631817095791339 7711129299947725643687009)
        ·
          refine ⟨5783346974960794232765257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711129299947725643687009 5783346974960794232765257)
          ·
            refine ⟨4337510231220595674573943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5783346974960794232765257 4337510231220595674573943)
            ·
              refine ⟨6506265346830893511860915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337510231220595674573943 6506265346830893511860915)
              ·
                refine ⟨9759398020246340267791373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506265346830893511860915 9759398020246340267791373)
                ·
                  refine ⟨3659774257592377600421765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9759398020246340267791373 3659774257592377600421765)
                  ·
                    refine ⟨686207673298570800079081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659774257592377600421765 686207673298570800079081)
                    ·
                      rfl

theorem cell23_4009154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4009154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009154 prefixEnd_4009154 := by exact prefixLift 4009154
  have htrace : WordTrace (prefixWord ++ tailWord_4009154) baseStart_4009154 baseEnd_4009154 := by
    simpa [prefixWord, tailWord_4009154, baseEnd_4009154] using wordTrace_append hprefix tailTrace_4009154
  have hstable : (prefixWord ++ tailWord_4009154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009154).length < 2 ^ (prefixWord ++ tailWord_4009154).sum := by decide
  have hdescent : baseEnd_4009154 < baseStart_4009154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009160 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_4009160 : Nat := 118140960795 + 4009160 * 2 ^ 59
def prefixEnd_4009160 : Nat := 4983230072969 + 3 ^ 40 * 4009160 * 2
def baseEnd_4009160 : Nat := 2058626100779639376762215

theorem tailTrace_4009160 : CollatzResearch.WordTrace tailWord_4009160 prefixEnd_4009160 2058626100779639376762215 := by
  unfold tailWord_4009160
  simp only [CollatzResearch.WordTrace]
  refine ⟨73113039077752752430280467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97484052103670336573707289 73113039077752752430280467)
  ·
    refine ⟨109669558616629128645420701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73113039077752752430280467 109669558616629128645420701)
    ·
      refine ⟨41126084481235923242032763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109669558616629128645420701 41126084481235923242032763)
      ·
        refine ⟨61689126721853884863049145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41126084481235923242032763 61689126721853884863049145)
        ·
          refine ⟨46266845041390413647286859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61689126721853884863049145 46266845041390413647286859)
          ·
            refine ⟨69400267562085620470930289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46266845041390413647286859 69400267562085620470930289)
            ·
              refine ⟨52050200671564215353197717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69400267562085620470930289 52050200671564215353197717)
              ·
                refine ⟨2439853156479572594681143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52050200671564215353197717 2439853156479572594681143)
                ·
                  refine ⟨3659779734719358892021715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439853156479572594681143 3659779734719358892021715)
                  ·
                    refine ⟨5489669602079038338032573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659779734719358892021715 5489669602079038338032573)
                    ·
                      refine ⟨2058626100779639376762215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5489669602079038338032573 2058626100779639376762215)
                      ·
                        rfl

theorem cell23_4009160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_4009160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009160 prefixEnd_4009160 := by exact prefixLift 4009160
  have htrace : WordTrace (prefixWord ++ tailWord_4009160) baseStart_4009160 baseEnd_4009160 := by
    simpa [prefixWord, tailWord_4009160, baseEnd_4009160] using wordTrace_append hprefix tailTrace_4009160
  have hstable : (prefixWord ++ tailWord_4009160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009160).length < 2 ^ (prefixWord ++ tailWord_4009160).sum := by decide
  have hdescent : baseEnd_4009160 < baseStart_4009160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_4009179 : Nat := 118140960795 + 4009179 * 2 ^ 59
def prefixEnd_4009179 : Nat := 4983230072969 + 3 ^ 40 * 4009179 * 2
def baseEnd_4009179 : Nat := 2058635856912074802424627

theorem tailTrace_4009179 : CollatzResearch.WordTrace tailWord_4009179 prefixEnd_4009179 2058635856912074802424627 := by
  unfold tailWord_4009179
  simp only [CollatzResearch.WordTrace]
  refine ⟨146226771142436671105502591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97484514094957780737001727 146226771142436671105502591)
  ·
    refine ⟨219340156713655006658253887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146226771142436671105502591 219340156713655006658253887)
    ·
      refine ⟨329010235070482509987380831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219340156713655006658253887 329010235070482509987380831)
      ·
        refine ⟨493515352605723764981071247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329010235070482509987380831 493515352605723764981071247)
        ·
          refine ⟨740273028908585647471606871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493515352605723764981071247 740273028908585647471606871)
          ·
            refine ⟨1110409543362878471207410307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740273028908585647471606871 1110409543362878471207410307)
            ·
              refine ⟨1665614315044317706811115461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110409543362878471207410307 1665614315044317706811115461)
              ·
                refine ⟨312302684070809570027084149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1665614315044317706811115461 312302684070809570027084149)
                ·
                  refine ⟨29278376631638397190039139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312302684070809570027084149 29278376631638397190039139)
                  ·
                    refine ⟨43917564947457595785058709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29278376631638397190039139 43917564947457595785058709)
                    ·
                      refine ⟨2058635856912074802424627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43917564947457595785058709 2058635856912074802424627)
                      ·
                        rfl

theorem cell23_4009179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_4009179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009179 prefixEnd_4009179 := by exact prefixLift 4009179
  have htrace : WordTrace (prefixWord ++ tailWord_4009179) baseStart_4009179 baseEnd_4009179 := by
    simpa [prefixWord, tailWord_4009179, baseEnd_4009179] using wordTrace_append hprefix tailTrace_4009179
  have hstable : (prefixWord ++ tailWord_4009179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009179).length < 2 ^ (prefixWord ++ tailWord_4009179).sum := by decide
  have hdescent : baseEnd_4009179 < baseStart_4009179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009183 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 4]
def baseStart_4009183 : Nat := 118140960795 + 4009183 * 2 ^ 59
def prefixEnd_4009183 : Nat := 4983230072969 + 3 ^ 40 * 4009183 * 2
def baseEnd_4009183 : Nat := 2058637910834692786774609

theorem tailTrace_4009183 : CollatzResearch.WordTrace tailWord_4009183 prefixEnd_4009183 2058637910834692786774609 := by
  unfold tailWord_4009183
  simp only [CollatzResearch.WordTrace]
  refine ⟨146226917034422179788648203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97484611356281453192432135 146226917034422179788648203)
  ·
    refine ⟨219340375551633269682972305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146226917034422179788648203 219340375551633269682972305)
    ·
      refine ⟨164505281663724952262229229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219340375551633269682972305 164505281663724952262229229)
      ·
        refine ⟨61689480623896857098335961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164505281663724952262229229 61689480623896857098335961)
        ·
          refine ⟨46267110467922642823751971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61689480623896857098335961 46267110467922642823751971)
          ·
            refine ⟨69400665701883964235627957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46267110467922642823751971 69400665701883964235627957)
            ·
              refine ⟨6506312409551621647090121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69400665701883964235627957 6506312409551621647090121)
              ·
                refine ⟨4879734307163716235317591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6506312409551621647090121 4879734307163716235317591)
                ·
                  refine ⟨7319601460745574352976387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879734307163716235317591 7319601460745574352976387)
                  ·
                    refine ⟨10979402191118361529464581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7319601460745574352976387 10979402191118361529464581)
                    ·
                      refine ⟨2058637910834692786774609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10979402191118361529464581 2058637910834692786774609)
                      ·
                        rfl

theorem cell23_4009183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_4009183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009183 prefixEnd_4009183 := by exact prefixLift 4009183
  have htrace : WordTrace (prefixWord ++ tailWord_4009183) baseStart_4009183 baseEnd_4009183 := by
    simpa [prefixWord, tailWord_4009183, baseEnd_4009183] using wordTrace_append hprefix tailTrace_4009183
  have hstable : (prefixWord ++ tailWord_4009183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009183).length < 2 ^ (prefixWord ++ tailWord_4009183).sum := by decide
  have hdescent : baseEnd_4009183 < baseStart_4009183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009196 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_4009196 : Nat := 118140960795 + 4009196 * 2 ^ 59
def prefixEnd_4009196 : Nat := 4983230072969 + 3 ^ 40 * 4009196 * 2
def baseEnd_4009196 : Nat := 2058644586083201235912049

theorem tailTrace_4009196 : CollatzResearch.WordTrace tailWord_4009196 prefixEnd_4009196 2058644586083201235912049 := by
  unfold tailWord_4009196
  simp only [CollatzResearch.WordTrace]
  refine ⟨73113695591687541504435721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97484927455583388672580961 73113695591687541504435721)
  ·
    refine ⟨54835271693765656128326791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73113695591687541504435721 54835271693765656128326791)
    ·
      refine ⟨82252907540648484192490187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54835271693765656128326791 82252907540648484192490187)
      ·
        refine ⟨123379361310972726288735281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82252907540648484192490187 123379361310972726288735281)
        ·
          refine ⟨92534520983229544716551461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123379361310972726288735281 92534520983229544716551461)
          ·
            refine ⟨17350222684355539634353399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92534520983229544716551461 17350222684355539634353399)
            ·
              refine ⟨26025334026533309451530099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17350222684355539634353399 26025334026533309451530099)
              ·
                refine ⟨39038001039799964177295149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26025334026533309451530099 39038001039799964177295149)
                ·
                  refine ⟨14639250389924986566485681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39038001039799964177295149 14639250389924986566485681)
                  ·
                    refine ⟨10979437792443739924864261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14639250389924986566485681 10979437792443739924864261)
                    ·
                      refine ⟨2058644586083201235912049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10979437792443739924864261 2058644586083201235912049)
                      ·
                        rfl

theorem cell23_4009196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_4009196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009196 prefixEnd_4009196 := by exact prefixLift 4009196
  have htrace : WordTrace (prefixWord ++ tailWord_4009196) baseStart_4009196 baseEnd_4009196 := by
    simpa [prefixWord, tailWord_4009196, baseEnd_4009196] using wordTrace_append hprefix tailTrace_4009196
  have hstable : (prefixWord ++ tailWord_4009196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009196).length < 2 ^ (prefixWord ++ tailWord_4009196).sum := by decide
  have hdescent : baseEnd_4009196 < baseStart_4009196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009203 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 5]
def baseStart_4009203 : Nat := 118140960795 + 4009203 * 2 ^ 59
def prefixEnd_4009203 : Nat := 4983230072969 + 3 ^ 40 * 4009203 * 2
def baseEnd_4009203 : Nat := 2058648180447782708524517

theorem tailTrace_4009203 : CollatzResearch.WordTrace tailWord_4009203 prefixEnd_4009203 2058648180447782708524517 := by
  unfold tailWord_4009203
  simp only [CollatzResearch.WordTrace]
  refine ⟨146227646494349723204376263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97485097662899815469584175 146227646494349723204376263)
  ·
    refine ⟨219341469741524584806564395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146227646494349723204376263 219341469741524584806564395)
    ·
      refine ⟨329012204612286877209846593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219341469741524584806564395 329012204612286877209846593)
      ·
        refine ⟨246759153459215157907384945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329012204612286877209846593 246759153459215157907384945)
        ·
          refine ⟨185069365094411368430538709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246759153459215157907384945 185069365094411368430538709)
          ·
            refine ⟨4337563244400266447590751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 185069365094411368430538709 4337563244400266447590751)
            ·
              refine ⟨6506344866600399671386127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337563244400266447590751 6506344866600399671386127)
              ·
                refine ⟨9759517299900599507079191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506344866600399671386127 9759517299900599507079191)
                ·
                  refine ⟨14639275949850899260618787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9759517299900599507079191 14639275949850899260618787)
                  ·
                    refine ⟨21958913924776348890928181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14639275949850899260618787 21958913924776348890928181)
                    ·
                      refine ⟨2058648180447782708524517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21958913924776348890928181 2058648180447782708524517)
                      ·
                        rfl

theorem cell23_4009203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_4009203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009203 prefixEnd_4009203 := by exact prefixLift 4009203
  have htrace : WordTrace (prefixWord ++ tailWord_4009203) baseStart_4009203 baseEnd_4009203 := by
    simpa [prefixWord, tailWord_4009203, baseEnd_4009203] using wordTrace_append hprefix tailTrace_4009203
  have hstable : (prefixWord ++ tailWord_4009203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009203).length < 2 ^ (prefixWord ++ tailWord_4009203).sum := by decide
  have hdescent : baseEnd_4009203 < baseStart_4009203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009216 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_4009216 : Nat := 118140960795 + 4009216 * 2 ^ 59
def prefixEnd_4009216 : Nat := 4983230072969 + 3 ^ 40 * 4009216 * 2
def baseEnd_4009216 : Nat := 2058654855696291157661957

theorem tailTrace_4009216 : CollatzResearch.WordTrace tailWord_4009216 prefixEnd_4009216 2058654855696291157661957 := by
  unfold tailWord_4009216
  simp only [CollatzResearch.WordTrace]
  refine ⟨73114060321651313212299751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97485413762201750949733001 73114060321651313212299751)
  ·
    refine ⟨109671090482476969818449627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73114060321651313212299751 109671090482476969818449627)
    ·
      refine ⟨164506635723715454727674441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109671090482476969818449627 164506635723715454727674441)
      ·
        refine ⟨123379976792786591045755831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164506635723715454727674441 123379976792786591045755831)
        ·
          refine ⟨185069965189179886568633747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123379976792786591045755831 185069965189179886568633747)
          ·
            refine ⟨277604947783769829852950621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185069965189179886568633747 277604947783769829852950621)
            ·
              refine ⟨104101855418913686194856483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277604947783769829852950621 104101855418913686194856483)
              ·
                refine ⟨156152783128370529292284725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104101855418913686194856483 156152783128370529292284725)
                ·
                  refine ⟨14639323418284737121151693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156152783128370529292284725 14639323418284737121151693)
                  ·
                    refine ⟨5489746281856776420431885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14639323418284737121151693 5489746281856776420431885)
                    ·
                      refine ⟨2058654855696291157661957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5489746281856776420431885 2058654855696291157661957)
                      ·
                        rfl

theorem cell23_4009216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_4009216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009216 prefixEnd_4009216 := by exact prefixLift 4009216
  have htrace : WordTrace (prefixWord ++ tailWord_4009216) baseStart_4009216 baseEnd_4009216 := by
    simpa [prefixWord, tailWord_4009216, baseEnd_4009216] using wordTrace_append hprefix tailTrace_4009216
  have hstable : (prefixWord ++ tailWord_4009216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009216).length < 2 ^ (prefixWord ++ tailWord_4009216).sum := by decide
  have hdescent : baseEnd_4009216 < baseStart_4009216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009233 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_4009233 : Nat := 118140960795 + 4009233 * 2 ^ 59
def prefixEnd_4009233 : Nat := 4983230072969 + 3 ^ 40 * 4009233 * 2
def baseEnd_4009233 : Nat := 2058663584867417591149379

theorem tailTrace_4009233 : CollatzResearch.WordTrace tailWord_4009233 prefixEnd_4009233 2058663584867417591149379 := by
  unfold tailWord_4009233
  simp only [CollatzResearch.WordTrace]
  refine ⟨146228740684241038327968353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97485827122827358885312235 146228740684241038327968353)
  ·
    refine ⟨109671555513180778745976265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146228740684241038327968353 109671555513180778745976265)
    ·
      refine ⟨82253666634885584059482199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109671555513180778745976265 82253666634885584059482199)
      ·
        refine ⟨123380499952328376089223299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82253666634885584059482199 123380499952328376089223299)
        ·
          refine ⟨185070749928492564133834949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123380499952328376089223299 185070749928492564133834949)
          ·
            refine ⟨34700765611592355775094053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185070749928492564133834949 34700765611592355775094053)
            ·
              refine ⟨6506393552173566707830135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34700765611592355775094053 6506393552173566707830135)
              ·
                refine ⟨9759590328260350061745203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506393552173566707830135 9759590328260350061745203)
                ·
                  refine ⟨14639385492390525092617805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9759590328260350061745203 14639385492390525092617805)
                  ·
                    refine ⟨5489769559646446909731677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14639385492390525092617805 5489769559646446909731677)
                    ·
                      refine ⟨2058663584867417591149379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5489769559646446909731677 2058663584867417591149379)
                      ·
                        rfl

theorem cell23_4009233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_4009233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009233 prefixEnd_4009233 := by exact prefixLift 4009233
  have htrace : WordTrace (prefixWord ++ tailWord_4009233) baseStart_4009233 baseEnd_4009233 := by
    simpa [prefixWord, tailWord_4009233, baseEnd_4009233] using wordTrace_append hprefix tailTrace_4009233
  have hstable : (prefixWord ++ tailWord_4009233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009233).length < 2 ^ (prefixWord ++ tailWord_4009233).sum := by decide
  have hdescent : baseEnd_4009233 < baseStart_4009233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009267 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 3]
def baseStart_4009267 : Nat := 118140960795 + 4009267 * 2 ^ 59
def prefixEnd_4009267 : Nat := 4983230072969 + 3 ^ 40 * 4009267 * 2
def baseEnd_4009267 : Nat := 2058681043209670458124223

theorem tailTrace_4009267 : CollatzResearch.WordTrace tailWord_4009267 prefixEnd_4009267 2058681043209670458124223 := by
  unfold tailWord_4009267
  simp only [CollatzResearch.WordTrace]
  refine ⟨146229980766117862134706055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97486653844078574756470703 146229980766117862134706055)
  ·
    refine ⟨219344971149176793202059083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146229980766117862134706055 219344971149176793202059083)
    ·
      refine ⟨329017456723765189803088625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219344971149176793202059083 329017456723765189803088625)
      ·
        refine ⟨246763092542823892352316469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329017456723765189803088625 246763092542823892352316469)
        ·
          refine ⟨23134039925889739908029669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246763092542823892352316469 23134039925889739908029669)
          ·
            refine ⟨4337632486104326232755563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23134039925889739908029669 4337632486104326232755563)
            ·
              refine ⟨6506448729156489349133345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337632486104326232755563 6506448729156489349133345)
              ·
                refine ⟨4879836546867367011850009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6506448729156489349133345 4879836546867367011850009)
                ·
                  refine ⟨3659877410150525258887507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879836546867367011850009 3659877410150525258887507)
                  ·
                    refine ⟨5489816115225787888331261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659877410150525258887507 5489816115225787888331261)
                    ·
                      refine ⟨2058681043209670458124223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5489816115225787888331261 2058681043209670458124223)
                      ·
                        rfl

theorem cell23_4009267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_4009267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009267 prefixEnd_4009267 := by exact prefixLift 4009267
  have htrace : WordTrace (prefixWord ++ tailWord_4009267) baseStart_4009267 baseEnd_4009267 := by
    simpa [prefixWord, tailWord_4009267, baseEnd_4009267] using wordTrace_append hprefix tailTrace_4009267
  have hstable : (prefixWord ++ tailWord_4009267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009267).length < 2 ^ (prefixWord ++ tailWord_4009267).sum := by decide
  have hdescent : baseEnd_4009267 < baseStart_4009267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009296 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 7]
def baseStart_4009296 : Nat := 118140960795 + 4009296 * 2 ^ 59
def prefixEnd_4009296 : Nat := 4983230072969 + 3 ^ 40 * 4009296 * 2
def baseEnd_4009296 : Nat := 228743992683183427184621

theorem tailTrace_4009296 : CollatzResearch.WordTrace tailWord_4009296 prefixEnd_4009296 228743992683183427184621 := by
  unfold tailWord_4009296
  simp only [CollatzResearch.WordTrace]
  refine ⟨73115519241506400043755871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97487358988675200058341161 73115519241506400043755871)
  ·
    refine ⟨109673278862259600065633807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73115519241506400043755871 109673278862259600065633807)
    ·
      refine ⟨164509918293389400098450711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109673278862259600065633807 164509918293389400098450711)
      ·
        refine ⟨246764877440084100147676067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164509918293389400098450711 246764877440084100147676067)
        ·
          refine ⟨370147316160126150221514101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246764877440084100147676067 370147316160126150221514101)
          ·
            refine ⟨34701310890011826583266947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370147316160126150221514101 34701310890011826583266947)
            ·
              refine ⟨52051966335017739874900421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34701310890011826583266947 52051966335017739874900421)
              ·
                refine ⟨9759743687815826226543829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52051966335017739874900421 9759743687815826226543829)
                ·
                  refine ⟨228743992683183427184621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9759743687815826226543829 228743992683183427184621)
                  ·
                    rfl

theorem cell23_4009296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_4009296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009296 prefixEnd_4009296 := by exact prefixLift 4009296
  have htrace : WordTrace (prefixWord ++ tailWord_4009296) baseStart_4009296 baseEnd_4009296 := by
    simpa [prefixWord, tailWord_4009296, baseEnd_4009296] using wordTrace_append hprefix tailTrace_4009296
  have hstable : (prefixWord ++ tailWord_4009296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009296).length < 2 ^ (prefixWord ++ tailWord_4009296).sum := by decide
  have hdescent : baseEnd_4009296 < baseStart_4009296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009302 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4009302 : Nat := 118140960795 + 4009302 * 2 ^ 59
def prefixEnd_4009302 : Nat := 4983230072969 + 3 ^ 40 * 4009302 * 2
def baseEnd_4009302 : Nat := 2058699015032577821186563

theorem tailTrace_4009302 : CollatzResearch.WordTrace tailWord_4009302 prefixEnd_4009302 2058699015032577821186563 := by
  unfold tailWord_4009302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139453582561941444514385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97487504880660708741486773 9139453582561941444514385)
  ·
    refine ⟨6854590186921456083385789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9139453582561941444514385 6854590186921456083385789)
    ·
      refine ⟨2570471320095546031269671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6854590186921456083385789 2570471320095546031269671)
      ·
        refine ⟨3855706980143319046904507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570471320095546031269671 3855706980143319046904507)
        ·
          refine ⟨5783560470214978570356761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855706980143319046904507 5783560470214978570356761)
          ·
            refine ⟨4337670352661233927767571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5783560470214978570356761 4337670352661233927767571)
            ·
              refine ⟨6506505528991850891651357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337670352661233927767571 6506505528991850891651357)
              ·
                refine ⟨2439939573371944084369259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6506505528991850891651357 2439939573371944084369259)
                ·
                  refine ⟨3659909360057916126553889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439939573371944084369259 3659909360057916126553889)
                  ·
                    refine ⟨2744932020043437094915417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3659909360057916126553889 2744932020043437094915417)
                    ·
                      refine ⟨2058699015032577821186563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744932020043437094915417 2058699015032577821186563)
                      ·
                        rfl

theorem cell23_4009302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4009302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009302 prefixEnd_4009302 := by exact prefixLift 4009302
  have htrace : WordTrace (prefixWord ++ tailWord_4009302) baseStart_4009302 baseEnd_4009302 := by
    simpa [prefixWord, tailWord_4009302, baseEnd_4009302] using wordTrace_append hprefix tailTrace_4009302
  have hstable : (prefixWord ++ tailWord_4009302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009302).length < 2 ^ (prefixWord ++ tailWord_4009302).sum := by decide
  have hdescent : baseEnd_4009302 < baseStart_4009302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009380 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_4009380 : Nat := 118140960795 + 4009380 * 2 ^ 59
def prefixEnd_4009380 : Nat := 4983230072969 + 3 ^ 40 * 4009380 * 2
def baseEnd_4009380 : Nat := 2058739066523628516011203

theorem tailTrace_4009380 : CollatzResearch.WordTrace tailWord_4009380 prefixEnd_4009380 2058739066523628516011203 := by
  unfold tailWord_4009380
  simp only [CollatzResearch.WordTrace]
  refine ⟨73117051107354241216784797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97489401476472321622379729 73117051107354241216784797)
  ·
    refine ⟨27418894165257840456294299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73117051107354241216784797 27418894165257840456294299)
    ·
      refine ⟨41128341247886760684441449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27418894165257840456294299 41128341247886760684441449)
      ·
        refine ⟨30846255935915070513331087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41128341247886760684441449 30846255935915070513331087)
        ·
          refine ⟨46269383903872605769996631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30846255935915070513331087 46269383903872605769996631)
          ·
            refine ⟨69404075855808908654994947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46269383903872605769996631 69404075855808908654994947)
            ·
              refine ⟨104106113783713362982492421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69404075855808908654994947 104106113783713362982492421)
              ·
                refine ⟨19519896334446255559217329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104106113783713362982492421 19519896334446255559217329)
                ·
                  refine ⟨14639922250834691669412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19519896334446255559217329 14639922250834691669412997)
                  ·
                    refine ⟨2744985422031504688014937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14639922250834691669412997 2744985422031504688014937)
                    ·
                      refine ⟨2058739066523628516011203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744985422031504688014937 2058739066523628516011203)
                      ·
                        rfl

theorem cell23_4009380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_4009380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009380 prefixEnd_4009380 := by exact prefixLift 4009380
  have htrace : WordTrace (prefixWord ++ tailWord_4009380) baseStart_4009380 baseEnd_4009380 := by
    simpa [prefixWord, tailWord_4009380, baseEnd_4009380] using wordTrace_append hprefix tailTrace_4009380
  have hstable : (prefixWord ++ tailWord_4009380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009380).length < 2 ^ (prefixWord ++ tailWord_4009380).sum := by decide
  have hdescent : baseEnd_4009380 < baseStart_4009380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009383 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4009383 : Nat := 118140960795 + 4009383 * 2 ^ 59
def prefixEnd_4009383 : Nat := 4983230072969 + 3 ^ 40 * 4009383 * 2
def baseEnd_4009383 : Nat := 2058740606965592004273689

theorem tailTrace_4009383 : CollatzResearch.WordTrace tailWord_4009383 prefixEnd_4009383 2058740606965592004273689 := by
  unfold tailWord_4009383
  simp only [CollatzResearch.WordTrace]
  refine ⟨146234211633697613945928803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97489474422465075963952535 146234211633697613945928803)
  ·
    refine ⟨219351317450546420918893205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146234211633697613945928803 219351317450546420918893205)
    ·
      refine ⟨10282093005494363480573119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219351317450546420918893205 10282093005494363480573119)
      ·
        refine ⟨15423139508241545220859679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10282093005494363480573119 15423139508241545220859679)
        ·
          refine ⟨23134709262362317831289519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423139508241545220859679 23134709262362317831289519)
          ·
            refine ⟨34702063893543476746934279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23134709262362317831289519 34702063893543476746934279)
            ·
              refine ⟨52053095840315215120401419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34702063893543476746934279 52053095840315215120401419)
              ·
                refine ⟨78079643760472822680602129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52053095840315215120401419 78079643760472822680602129)
                ·
                  refine ⟨58559732820354617010451597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78079643760472822680602129 58559732820354617010451597)
                  ·
                    refine ⟨21959899807632981378919349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58559732820354617010451597 21959899807632981378919349)
                    ·
                      refine ⟨2058740606965592004273689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21959899807632981378919349 2058740606965592004273689)
                      ·
                        rfl

theorem cell23_4009383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4009383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009383 prefixEnd_4009383 := by exact prefixLift 4009383
  have htrace : WordTrace (prefixWord ++ tailWord_4009383) baseStart_4009383 baseEnd_4009383 := by
    simpa [prefixWord, tailWord_4009383, baseEnd_4009383] using wordTrace_append hprefix tailTrace_4009383
  have hstable : (prefixWord ++ tailWord_4009383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009383).length < 2 ^ (prefixWord ++ tailWord_4009383).sum := by decide
  have hdescent : baseEnd_4009383 < baseStart_4009383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009397 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_4009397 : Nat := 118140960795 + 4009397 * 2 ^ 59
def prefixEnd_4009397 : Nat := 4983230072969 + 3 ^ 40 * 4009397 * 2
def baseEnd_4009397 : Nat := 2058747795694754949498625

theorem tailTrace_4009397 : CollatzResearch.WordTrace tailWord_4009397 prefixEnd_4009397 2058747795694754949498625 := by
  unfold tailWord_4009397
  simp only [CollatzResearch.WordTrace]
  refine ⟨146234722255646894336938445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97489814837097929557958963 146234722255646894336938445)
  ·
    refine ⟨54838020845867585376351917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146234722255646894336938445 54838020845867585376351917)
    ·
      refine ⟨20564257817200344516131969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54838020845867585376351917 20564257817200344516131969)
      ·
        refine ⟨15423193362900258387098977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20564257817200344516131969 15423193362900258387098977)
        ·
          refine ⟨11567395022175193790324233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15423193362900258387098977 11567395022175193790324233)
          ·
            refine ⟨8675546266631395342743175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11567395022175193790324233 8675546266631395342743175)
            ·
              refine ⟨13013319399947093014114763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675546266631395342743175 13013319399947093014114763)
              ·
                refine ⟨19519979099920639521172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13013319399947093014114763 19519979099920639521172145)
                ·
                  refine ⟨14639984324940479640879109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19519979099920639521172145 14639984324940479640879109)
                  ·
                    refine ⟨2744997060926339932664833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14639984324940479640879109 2744997060926339932664833)
                    ·
                      refine ⟨2058747795694754949498625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2744997060926339932664833 2058747795694754949498625)
                      ·
                        rfl

theorem cell23_4009397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_4009397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009397 prefixEnd_4009397 := by exact prefixLift 4009397
  have htrace : WordTrace (prefixWord ++ tailWord_4009397) baseStart_4009397 baseEnd_4009397 := by
    simpa [prefixWord, tailWord_4009397, baseEnd_4009397] using wordTrace_append hprefix tailTrace_4009397
  have hstable : (prefixWord ++ tailWord_4009397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009397).length < 2 ^ (prefixWord ++ tailWord_4009397).sum := by decide
  have hdescent : baseEnd_4009397 < baseStart_4009397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009437 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 6]
def baseStart_4009437 : Nat := 118140960795 + 4009437 * 2 ^ 59
def prefixEnd_4009437 : Nat := 4983230072969 + 3 ^ 40 * 4009437 * 2
def baseEnd_4009437 : Nat := 228752037213437199222049

theorem tailTrace_4009437 : CollatzResearch.WordTrace tailWord_4009437 prefixEnd_4009437 228752037213437199222049 := by
  unfold tailWord_4009437
  simp only [CollatzResearch.WordTrace]
  refine ⟨146236181175501981168394565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97490787450334654112263043 146236181175501981168394565)
  ·
    refine ⟨27419283970406621469073981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146236181175501981168394565 27419283970406621469073981)
    ·
      refine ⟨10282231488902483050902743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27419283970406621469073981 10282231488902483050902743)
      ·
        refine ⟨15423347233353724576354115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10282231488902483050902743 15423347233353724576354115)
        ·
          refine ⟨23135020850030586864531173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423347233353724576354115 23135020850030586864531173)
          ·
            refine ⟨4337816409380735037099595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23135020850030586864531173 4337816409380735037099595)
            ·
              refine ⟨6506724614071102555649393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337816409380735037099595 6506724614071102555649393)
              ·
                refine ⟨4880043460553326916737045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6506724614071102555649393 4880043460553326916737045)
                ·
                  refine ⟨228752037213437199222049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4880043460553326916737045 228752037213437199222049)
                  ·
                    rfl

theorem cell23_4009437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_4009437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009437 prefixEnd_4009437 := by exact prefixLift 4009437
  have htrace : WordTrace (prefixWord ++ tailWord_4009437) baseStart_4009437 baseEnd_4009437 := by
    simpa [prefixWord, tailWord_4009437, baseEnd_4009437] using wordTrace_append hprefix tailTrace_4009437
  have hstable : (prefixWord ++ tailWord_4009437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009437).length < 2 ^ (prefixWord ++ tailWord_4009437).sum := by decide
  have hdescent : baseEnd_4009437 < baseStart_4009437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009447 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4009447 : Nat := 118140960795 + 4009447 * 2 ^ 59
def prefixEnd_4009447 : Nat := 4983230072969 + 3 ^ 40 * 4009447 * 2
def baseEnd_4009447 : Nat := 2058773469727479753873395

theorem tailTrace_4009447 : CollatzResearch.WordTrace tailWord_4009447 prefixEnd_4009447 2058773469727479753873395 := by
  unfold tailWord_4009447
  simp only [CollatzResearch.WordTrace]
  refine ⟨146236545905465752876258595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97491030603643835250839063 146236545905465752876258595)
  ·
    refine ⟨219354818858198629314387893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146236545905465752876258595 219354818858198629314387893)
    ·
      refine ⟨20564514267956121498223865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219354818858198629314387893 20564514267956121498223865)
      ·
        refine ⟨15423385700967091123667899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20564514267956121498223865 15423385700967091123667899)
        ·
          refine ⟨23135078551450636685501849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423385700967091123667899 23135078551450636685501849)
          ·
            refine ⟨17351308913587977514126387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23135078551450636685501849 17351308913587977514126387)
            ·
              refine ⟨26026963370381966271189581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17351308913587977514126387 26026963370381966271189581)
              ·
                refine ⟨9760111263893237351696093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26026963370381966271189581 9760111263893237351696093)
                ·
                  refine ⟨3660041723959964006886035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9760111263893237351696093 3660041723959964006886035)
                  ·
                    refine ⟨5490062585939946010329053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660041723959964006886035 5490062585939946010329053)
                    ·
                      refine ⟨2058773469727479753873395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490062585939946010329053 2058773469727479753873395)
                      ·
                        rfl

theorem cell23_4009447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4009447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009447 prefixEnd_4009447 := by exact prefixLift 4009447
  have htrace : WordTrace (prefixWord ++ tailWord_4009447) baseStart_4009447 baseEnd_4009447 := by
    simpa [prefixWord, tailWord_4009447, baseEnd_4009447] using wordTrace_append hprefix tailTrace_4009447
  have hstable : (prefixWord ++ tailWord_4009447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009447).length < 2 ^ (prefixWord ++ tailWord_4009447).sum := by decide
  have hdescent : baseEnd_4009447 < baseStart_4009447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
