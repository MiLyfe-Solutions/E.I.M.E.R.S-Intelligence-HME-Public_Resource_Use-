import V185TrunkScan23Chunk0744

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4404918 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4404918 : Nat := 118140960795 + 4404918 * 2 ^ 59
def prefixEnd_4404918 : Nat := 4983230072969 + 3 ^ 40 * 4404918 * 2
def baseEnd_4404918 : Nat := 2261840177641701971767157

theorem tailTrace_4404918 : CollatzResearch.WordTrace tailWord_4404918 prefixEnd_4404918 2261840177641701971767157 := by
  unfold tailWord_4404918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041284890983866309114963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107107038837161240630559605 10041284890983866309114963)
  ·
    refine ⟨15061927336475799463672445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10041284890983866309114963 15061927336475799463672445)
    ·
      refine ⟨5648222751178424798877167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15061927336475799463672445 5648222751178424798877167)
      ·
        refine ⟨8472334126767637198315751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648222751178424798877167 8472334126767637198315751)
        ·
          refine ⟨12708501190151455797473627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8472334126767637198315751 12708501190151455797473627)
          ·
            refine ⟨19062751785227183696210441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12708501190151455797473627 19062751785227183696210441)
            ·
              refine ⟨14297063838920387772157831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19062751785227183696210441 14297063838920387772157831)
              ·
                refine ⟨21445595758380581658236747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14297063838920387772157831 21445595758380581658236747)
                ·
                  refine ⟨32168393637570872487355121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21445595758380581658236747 32168393637570872487355121)
                  ·
                    refine ⟨24126295228178154365516341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32168393637570872487355121 24126295228178154365516341)
                    ·
                      refine ⟨2261840177641701971767157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24126295228178154365516341 2261840177641701971767157)
                      ·
                        rfl

theorem cell23_4404918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4404918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404918 prefixEnd_4404918 := by exact prefixLift 4404918
  have htrace : WordTrace (prefixWord ++ tailWord_4404918) baseStart_4404918 baseEnd_4404918 := by
    simpa [prefixWord, tailWord_4404918, baseEnd_4404918] using wordTrace_append hprefix tailTrace_4404918
  have hstable : (prefixWord ++ tailWord_4404918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404918).length < 2 ^ (prefixWord ++ tailWord_4404918).sum := by decide
  have hdescent : baseEnd_4404918 < baseStart_4404918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404938 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_4404938 : Nat := 118140960795 + 4404938 * 2 ^ 59
def prefixEnd_4404938 : Nat := 4983230072969 + 3 ^ 40 * 4404938 * 2
def baseEnd_4404938 : Nat := 753950149084930631172355

theorem tailTrace_4404938 : CollatzResearch.WordTrace tailWord_4404938 prefixEnd_4404938 753950149084930631172355 := by
  unfold tailWord_4404938
  simp only [CollatzResearch.WordTrace]
  refine ⟨40165321928917351090391867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107107525143779602907711645 40165321928917351090391867)
  ·
    refine ⟨60247982893376026635587801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40165321928917351090391867 60247982893376026635587801)
    ·
      refine ⟨45185987170032019976690851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60247982893376026635587801 45185987170032019976690851)
      ·
        refine ⟨67778980755048029965036277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45185987170032019976690851 67778980755048029965036277)
        ·
          refine ⟨6354279445785752809222151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67778980755048029965036277 6354279445785752809222151)
          ·
            refine ⟨9531419168678629213833227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354279445785752809222151 9531419168678629213833227)
            ·
              refine ⟨14297128753017943820749841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9531419168678629213833227 14297128753017943820749841)
              ·
                refine ⟨10722846564763457865562381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14297128753017943820749841 10722846564763457865562381)
                ·
                  refine ⟨4021067461786296699585893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10722846564763457865562381 4021067461786296699585893)
                  ·
                    refine ⟨753950149084930631172355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4021067461786296699585893 753950149084930631172355)
                    ·
                      rfl

theorem cell23_4404938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_4404938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404938 prefixEnd_4404938 := by exact prefixLift 4404938
  have htrace : WordTrace (prefixWord ++ tailWord_4404938) baseStart_4404938 baseEnd_4404938 := by
    simpa [prefixWord, tailWord_4404938, baseEnd_4404938] using wordTrace_append hprefix tailTrace_4404938
  have hstable : (prefixWord ++ tailWord_4404938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404938).length < 2 ^ (prefixWord ++ tailWord_4404938).sum := by decide
  have hdescent : baseEnd_4404938 < baseStart_4404938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404944 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_4404944 : Nat := 118140960795 + 4404944 * 2 ^ 59
def prefixEnd_4404944 : Nat := 4983230072969 + 3 ^ 40 * 4404944 * 2
def baseEnd_4404944 : Nat := 2261853528138718870042037

theorem tailTrace_4404944 : CollatzResearch.WordTrace tailWord_4404944 prefixEnd_4404944 2261853528138718870042037 := by
  unfold tailWord_4404944
  simp only [CollatzResearch.WordTrace]
  refine ⟨80330753276823833693142943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107107671035765111590857257 80330753276823833693142943)
  ·
    refine ⟨120496129915235750539714415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80330753276823833693142943 120496129915235750539714415)
    ·
      refine ⟨180744194872853625809571623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120496129915235750539714415 180744194872853625809571623)
      ·
        refine ⟨271116292309280438714357435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180744194872853625809571623 271116292309280438714357435)
        ·
          refine ⟨406674438463920658071536153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271116292309280438714357435 406674438463920658071536153)
          ·
            refine ⟨305005828847940493553652115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406674438463920658071536153 305005828847940493553652115)
            ·
              refine ⟨457508743271910740330478173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305005828847940493553652115 457508743271910740330478173)
              ·
                refine ⟨171565778726966527623929315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457508743271910740330478173 171565778726966527623929315)
                ·
                  refine ⟨257348668090449791435893973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171565778726966527623929315 257348668090449791435893973)
                  ·
                    refine ⟨6031609408369916986778765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 257348668090449791435893973 6031609408369916986778765)
                    ·
                      refine ⟨2261853528138718870042037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6031609408369916986778765 2261853528138718870042037)
                      ·
                        rfl

theorem cell23_4404944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_4404944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404944 prefixEnd_4404944 := by exact prefixLift 4404944
  have htrace : WordTrace (prefixWord ++ tailWord_4404944) baseStart_4404944 baseEnd_4404944 := by
    simpa [prefixWord, tailWord_4404944, baseEnd_4404944] using wordTrace_append hprefix tailTrace_4404944
  have hstable : (prefixWord ++ tailWord_4404944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404944).length < 2 ^ (prefixWord ++ tailWord_4404944).sum := by decide
  have hdescent : baseEnd_4404944 < baseStart_4404944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404948 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4404948 : Nat := 118140960795 + 4404948 * 2 ^ 59
def prefixEnd_4404948 : Nat := 4983230072969 + 3 ^ 40 * 4404948 * 2
def baseEnd_4404948 : Nat := 2261855582061336854392019

theorem tailTrace_4404948 : CollatzResearch.WordTrace tailWord_4404948 prefixEnd_4404948 2261855582061336854392019 := by
  unfold tailWord_4404948
  simp only [CollatzResearch.WordTrace]
  refine ⟨80330826222816588034715749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107107768297088784046287665 80330826222816588034715749)
  ·
    refine ⟨15062029916778110256509203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80330826222816588034715749 15062029916778110256509203)
    ·
      refine ⟨22593044875167165384763805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15062029916778110256509203 22593044875167165384763805)
      ·
        refine ⟨8472391828187687019286427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22593044875167165384763805 8472391828187687019286427)
        ·
          refine ⟨12708587742281530528929641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8472391828187687019286427 12708587742281530528929641)
          ·
            refine ⟨9531440806711147896697231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12708587742281530528929641 9531440806711147896697231)
            ·
              refine ⟨14297161210066721845045847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9531440806711147896697231 14297161210066721845045847)
              ·
                refine ⟨21445741815100082767568771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14297161210066721845045847 21445741815100082767568771)
                ·
                  refine ⟨32168612722650124151353157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21445741815100082767568771 32168612722650124151353157)
                  ·
                    refine ⟨6031614885496898278378717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32168612722650124151353157 6031614885496898278378717)
                    ·
                      refine ⟨2261855582061336854392019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6031614885496898278378717 2261855582061336854392019)
                      ·
                        rfl

theorem cell23_4404948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4404948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404948 prefixEnd_4404948 := by exact prefixLift 4404948
  have htrace : WordTrace (prefixWord ++ tailWord_4404948) baseStart_4404948 baseEnd_4404948 := by
    simpa [prefixWord, tailWord_4404948, baseEnd_4404948] using wordTrace_append hprefix tailTrace_4404948
  have hstable : (prefixWord ++ tailWord_4404948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404948).length < 2 ^ (prefixWord ++ tailWord_4404948).sum := by decide
  have hdescent : baseEnd_4404948 < baseStart_4404948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404968 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 6]
def baseStart_4404968 : Nat := 118140960795 + 4404968 * 2 ^ 59
def prefixEnd_4404968 : Nat := 4983230072969 + 3 ^ 40 * 4404968 * 2
def baseEnd_4404968 : Nat := 251318427963825197349103

theorem tailTrace_4404968 : CollatzResearch.WordTrace tailWord_4404968 prefixEnd_4404968 251318427963825197349103 := by
  unfold tailWord_4404968
  simp only [CollatzResearch.WordTrace]
  refine ⟨80331190952780359742579779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107108254603707146323439705 80331190952780359742579779)
  ·
    refine ⟨120496786429170539613869669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80331190952780359742579779 120496786429170539613869669)
    ·
      refine ⟨22593147455469476177600563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120496786429170539613869669 22593147455469476177600563)
      ·
        refine ⟨33889721183204214266400845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22593147455469476177600563 33889721183204214266400845)
        ·
          refine ⟨12708645443701580349900317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33889721183204214266400845 12708645443701580349900317)
          ·
            refine ⟨4765742041388092631212619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12708645443701580349900317 4765742041388092631212619)
            ·
              refine ⟨7148613062082138946818929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765742041388092631212619 7148613062082138946818929)
              ·
                refine ⟨5361459796561604210114197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7148613062082138946818929 5361459796561604210114197)
                ·
                  refine ⟨251318427963825197349103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5361459796561604210114197 251318427963825197349103)
                  ·
                    rfl

theorem cell23_4404968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 6].length) (baseStart_4404968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404968 prefixEnd_4404968 := by exact prefixLift 4404968
  have htrace : WordTrace (prefixWord ++ tailWord_4404968) baseStart_4404968 baseEnd_4404968 := by
    simpa [prefixWord, tailWord_4404968, baseEnd_4404968] using wordTrace_append hprefix tailTrace_4404968
  have hstable : (prefixWord ++ tailWord_4404968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404968).length < 2 ^ (prefixWord ++ tailWord_4404968).sum := by decide
  have hdescent : baseEnd_4404968 < baseStart_4404968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4404984 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_4404984 : Nat := 118140960795 + 4404984 * 2 ^ 59
def prefixEnd_4404984 : Nat := 4983230072969 + 3 ^ 40 * 4404984 * 2
def baseEnd_4404984 : Nat := 2261874067364898713541853

theorem tailTrace_4404984 : CollatzResearch.WordTrace tailWord_4404984 prefixEnd_4404984 2261874067364898713541853 := by
  unfold tailWord_4404984
  simp only [CollatzResearch.WordTrace]
  refine ⟨80331482736751377108871003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107108643649001836145161337 80331482736751377108871003)
  ·
    refine ⟨120497224105127065663306505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80331482736751377108871003 120497224105127065663306505)
    ·
      refine ⟨90372918078845299247479879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120497224105127065663306505 90372918078845299247479879)
      ·
        refine ⟨135559377118267948871219819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90372918078845299247479879 135559377118267948871219819)
        ·
          refine ⟨203339065677401923306829729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135559377118267948871219819 203339065677401923306829729)
          ·
            refine ⟨152504299258051442480122297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203339065677401923306829729 152504299258051442480122297)
            ·
              refine ⟨114378224443538581860091723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152504299258051442480122297 114378224443538581860091723)
              ·
                refine ⟨171567336665307872790137585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114378224443538581860091723 171567336665307872790137585)
                ·
                  refine ⟨128675502498980904592603189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171567336665307872790137585 128675502498980904592603189)
                  ·
                    refine ⟨12063328359279459805556549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128675502498980904592603189 12063328359279459805556549)
                    ·
                      refine ⟨2261874067364898713541853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12063328359279459805556549 2261874067364898713541853)
                      ·
                        rfl

theorem cell23_4404984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_4404984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4404984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4404984 prefixEnd_4404984 := by exact prefixLift 4404984
  have htrace : WordTrace (prefixWord ++ tailWord_4404984) baseStart_4404984 baseEnd_4404984 := by
    simpa [prefixWord, tailWord_4404984, baseEnd_4404984] using wordTrace_append hprefix tailTrace_4404984
  have hstable : (prefixWord ++ tailWord_4404984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4404984).length < 2 ^ (prefixWord ++ tailWord_4404984).sum := by decide
  have hdescent : baseEnd_4404984 < baseStart_4404984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4404984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405001 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 8, 2]
def baseStart_4405001 : Nat := 118140960795 + 4405001 * 2 ^ 59
def prefixEnd_4405001 : Nat := 4983230072969 + 3 ^ 40 * 4405001 * 2
def baseEnd_4405001 : Nat := 2261882796536025147029275

theorem tailTrace_4405001 : CollatzResearch.WordTrace tailWord_4405001 prefixEnd_4405001 2261882796536025147029275 := by
  unfold tailWord_4405001
  simp only [CollatzResearch.WordTrace]
  refine ⟨160663585514441166121110857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107109057009627444080740571 160663585514441166121110857)
  ·
    refine ⟨120497689135830874590833143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160663585514441166121110857 120497689135830874590833143)
    ·
      refine ⟨180746533703746311886249715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120497689135830874590833143 180746533703746311886249715)
      ·
        refine ⟨271119800555619467829374573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180746533703746311886249715 271119800555619467829374573)
        ·
          refine ⟨101669925208357300436015465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271119800555619467829374573 101669925208357300436015465)
          ·
            refine ⟨76252443906267975327011599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101669925208357300436015465 76252443906267975327011599)
            ·
              refine ⟨114378665859401962990517399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76252443906267975327011599 114378665859401962990517399)
              ·
                refine ⟨171567998789102944485776099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114378665859401962990517399 171567998789102944485776099)
                ·
                  refine ⟨257351998183654416728664149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171567998789102944485776099 257351998183654416728664149)
                  ·
                    refine ⟨3015843728714700196039033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 257351998183654416728664149 3015843728714700196039033)
                    ·
                      refine ⟨2261882796536025147029275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015843728714700196039033 2261882796536025147029275)
                      ·
                        rfl

theorem cell23_4405001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 8, 2].length) (baseStart_4405001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405001 prefixEnd_4405001 := by exact prefixLift 4405001
  have htrace : WordTrace (prefixWord ++ tailWord_4405001) baseStart_4405001 baseEnd_4405001 := by
    simpa [prefixWord, tailWord_4405001, baseEnd_4405001] using wordTrace_append hprefix tailTrace_4405001
  have hstable : (prefixWord ++ tailWord_4405001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405001).length < 2 ^ (prefixWord ++ tailWord_4405001).sum := by decide
  have hdescent : baseEnd_4405001 < baseStart_4405001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405018 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_4405018 : Nat := 118140960795 + 4405018 * 2 ^ 59
def prefixEnd_4405018 : Nat := 4983230072969 + 3 ^ 40 * 4405018 * 2
def baseEnd_4405018 : Nat := 2261891525707151580516697

theorem tailTrace_4405018 : CollatzResearch.WordTrace tailWord_4405018 prefixEnd_4405018 2261891525707151580516697 := by
  unfold tailWord_4405018
  simp only [CollatzResearch.WordTrace]
  refine ⟨40166051388844894506119927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107109470370253052016319805 40166051388844894506119927)
  ·
    refine ⟨60249077083267341759179891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40166051388844894506119927 60249077083267341759179891)
    ·
      refine ⟨90373615624901012638769837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60249077083267341759179891 90373615624901012638769837)
      ·
        refine ⟨33890105859337879739538689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90373615624901012638769837 33890105859337879739538689)
        ·
          refine ⟨25417579394503409804654017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33890105859337879739538689 25417579394503409804654017)
          ·
            refine ⟨19063184545877557353490513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25417579394503409804654017 19063184545877557353490513)
            ·
              refine ⟨14297388409408168015117885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19063184545877557353490513 14297388409408168015117885)
              ·
                refine ⟨5361520653528063005669207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14297388409408168015117885 5361520653528063005669207)
                ·
                  refine ⟨8042280980292094508503811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5361520653528063005669207 8042280980292094508503811)
                  ·
                    refine ⟨12063421470438141762755717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8042280980292094508503811 12063421470438141762755717)
                    ·
                      refine ⟨2261891525707151580516697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12063421470438141762755717 2261891525707151580516697)
                      ·
                        rfl

theorem cell23_4405018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_4405018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405018 prefixEnd_4405018 := by exact prefixLift 4405018
  have htrace : WordTrace (prefixWord ++ tailWord_4405018) baseStart_4405018 baseEnd_4405018 := by
    simpa [prefixWord, tailWord_4405018, baseEnd_4405018] using wordTrace_append hprefix tailTrace_4405018
  have hstable : (prefixWord ++ tailWord_4405018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405018).length < 2 ^ (prefixWord ++ tailWord_4405018).sum := by decide
  have hdescent : baseEnd_4405018 < baseStart_4405018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405028 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_4405028 : Nat := 118140960795 + 4405028 * 2 ^ 59
def prefixEnd_4405028 : Nat := 4983230072969 + 3 ^ 40 * 4405028 * 2
def baseEnd_4405028 : Nat := 753965553504565513797217

theorem tailTrace_4405028 : CollatzResearch.WordTrace tailWord_4405028 prefixEnd_4405028 753965553504565513797217 := by
  unfold tailWord_4405028
  simp only [CollatzResearch.WordTrace]
  refine ⟨80332285142671674866171869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107109713523562233154895825 80332285142671674866171869)
  ·
    refine ⟨30124606928501878074814451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80332285142671674866171869 30124606928501878074814451)
    ·
      refine ⟨45186910392752817112221677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30124606928501878074814451 45186910392752817112221677)
      ·
        refine ⟨16945091397282306417083129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45186910392752817112221677 16945091397282306417083129)
        ·
          refine ⟨12708818547961729812812347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16945091397282306417083129 12708818547961729812812347)
          ·
            refine ⟨19063227821942594719218521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12708818547961729812812347 19063227821942594719218521)
            ·
              refine ⟨14297420866456946039413891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19063227821942594719218521 14297420866456946039413891)
              ·
                refine ⟨21446131299685419059120837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14297420866456946039413891 21446131299685419059120837)
                ·
                  refine ⟨4021149618691016073585157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21446131299685419059120837 4021149618691016073585157)
                  ·
                    refine ⟨753965553504565513797217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4021149618691016073585157 753965553504565513797217)
                    ·
                      rfl

theorem cell23_4405028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_4405028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405028 prefixEnd_4405028 := by exact prefixLift 4405028
  have htrace : WordTrace (prefixWord ++ tailWord_4405028) baseStart_4405028 baseEnd_4405028 := by
    simpa [prefixWord, tailWord_4405028, baseEnd_4405028] using wordTrace_append hprefix tailTrace_4405028
  have hstable : (prefixWord ++ tailWord_4405028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405028).length < 2 ^ (prefixWord ++ tailWord_4405028).sum := by decide
  have hdescent : baseEnd_4405028 < baseStart_4405028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405041 : List Nat := [1, 2, 2, 3, 2, 3, 2, 8]
def baseStart_4405041 : Nat := 118140960795 + 4405041 * 2 ^ 59
def prefixEnd_4405041 : Nat := 4983230072969 + 3 ^ 40 * 4405041 * 2
def baseEnd_4405041 : Nat := 83774197620822407056633

theorem tailTrace_4405041 : CollatzResearch.WordTrace tailWord_4405041 prefixEnd_4405041 83774197620822407056633 := by
  unfold tailWord_4405041
  simp only [CollatzResearch.WordTrace]
  refine ⟨160665044434296252952566977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107110029622864168635044651 160665044434296252952566977)
  ·
    refine ⟨120498783325722189714425233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160665044434296252952566977 120498783325722189714425233)
    ·
      refine ⟨90374087494291642285818925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120498783325722189714425233 90374087494291642285818925)
      ·
        refine ⟨33890282810359365857182097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90374087494291642285818925 33890282810359365857182097)
        ·
          refine ⟨25417712107769524392886573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33890282810359365857182097 25417712107769524392886573)
          ·
            refine ⟨9531642040413571647332465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25417712107769524392886573 9531642040413571647332465)
            ·
              refine ⟨7148731530310178735499349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9531642040413571647332465 7148731530310178735499349)
              ·
                refine ⟨83774197620822407056633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7148731530310178735499349 83774197620822407056633)
                ·
                  rfl

theorem cell23_4405041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 8].length) (baseStart_4405041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405041 prefixEnd_4405041 := by exact prefixLift 4405041
  have htrace : WordTrace (prefixWord ++ tailWord_4405041) baseStart_4405041 baseEnd_4405041 := by
    simpa [prefixWord, tailWord_4405041, baseEnd_4405041] using wordTrace_append hprefix tailTrace_4405041
  have hstable : (prefixWord ++ tailWord_4405041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405041).length < 2 ^ (prefixWord ++ tailWord_4405041).sum := by decide
  have hdescent : baseEnd_4405041 < baseStart_4405041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405045 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_4405045 : Nat := 118140960795 + 4405045 * 2 ^ 59
def prefixEnd_4405045 : Nat := 4983230072969 + 3 ^ 40 * 4405045 * 2
def baseEnd_4405045 : Nat := 753968463228274324959691

theorem tailTrace_4405045 : CollatzResearch.WordTrace tailWord_4405045 prefixEnd_4405045 753968463228274324959691 := by
  unfold tailWord_4405045
  simp only [CollatzResearch.WordTrace]
  refine ⟨160665190326281761635712589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107110126884187841090475059 160665190326281761635712589)
  ·
    refine ⟨60249446372355660613392221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160665190326281761635712589 60249446372355660613392221)
    ·
      refine ⟨22593542389633372730022083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60249446372355660613392221 22593542389633372730022083)
      ·
        refine ⟨33890313584450059095033125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22593542389633372730022083 33890313584450059095033125)
        ·
          refine ⟨6354433797084386080318711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33890313584450059095033125 6354433797084386080318711)
          ·
            refine ⟨9531650695626579120478067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354433797084386080318711 9531650695626579120478067)
            ·
              refine ⟨14297476043439868680717101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9531650695626579120478067 14297476043439868680717101)
              ·
                refine ⟨5361553516289950755268913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14297476043439868680717101 5361553516289950755268913)
                ·
                  refine ⟨4021165137217463066451685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5361553516289950755268913 4021165137217463066451685)
                  ·
                    refine ⟨753968463228274324959691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4021165137217463066451685 753968463228274324959691)
                    ·
                      rfl

theorem cell23_4405045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_4405045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405045 prefixEnd_4405045 := by exact prefixLift 4405045
  have htrace : WordTrace (prefixWord ++ tailWord_4405045) baseStart_4405045 baseEnd_4405045 := by
    simpa [prefixWord, tailWord_4405045, baseEnd_4405045] using wordTrace_append hprefix tailTrace_4405045
  have hstable : (prefixWord ++ tailWord_4405045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405045).length < 2 ^ (prefixWord ++ tailWord_4405045).sum := by decide
  have hdescent : baseEnd_4405045 < baseStart_4405045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405101 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_4405101 : Nat := 118140960795 + 4405101 * 2 ^ 59
def prefixEnd_4405101 : Nat := 4983230072969 + 3 ^ 40 * 4405101 * 2
def baseEnd_4405101 : Nat := 753978048200491585259605

theorem tailTrace_4405101 : CollatzResearch.WordTrace tailWord_4405101 prefixEnd_4405101 753978048200491585259605 := by
  unfold tailWord_4405101
  simp only [CollatzResearch.WordTrace]
  refine ⟨160667232814078883199751157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107111488542719255466500771 160667232814078883199751157)
  ·
    refine ⟨15062553076319895299976671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160667232814078883199751157 15062553076319895299976671)
    ·
      refine ⟨22593829614479842949965007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15062553076319895299976671 22593829614479842949965007)
      ·
        refine ⟨33890744421719764424947511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22593829614479842949965007 33890744421719764424947511)
        ·
          refine ⟨50836116632579646637421267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33890744421719764424947511 50836116632579646637421267)
          ·
            refine ⟨76254174948869469956131901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50836116632579646637421267 76254174948869469956131901)
            ·
              refine ⟨28595315605826051233549463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76254174948869469956131901 28595315605826051233549463)
              ·
                refine ⟨42892973408739076850324195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28595315605826051233549463 42892973408739076850324195)
                ·
                  refine ⟨64339460113108615275486293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42892973408739076850324195 64339460113108615275486293)
                  ·
                    refine ⟨753978048200491585259605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64339460113108615275486293 753978048200491585259605)
                    ·
                      rfl

theorem cell23_4405101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_4405101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405101 prefixEnd_4405101 := by exact prefixLift 4405101
  have htrace : WordTrace (prefixWord ++ tailWord_4405101) baseStart_4405101 baseEnd_4405101 := by
    simpa [prefixWord, tailWord_4405101, baseEnd_4405101] using wordTrace_append hprefix tailTrace_4405101
  have hstable : (prefixWord ++ tailWord_4405101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405101).length < 2 ^ (prefixWord ++ tailWord_4405101).sum := by decide
  have hdescent : baseEnd_4405101 < baseStart_4405101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405102 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4405102 : Nat := 118140960795 + 4405102 * 2 ^ 59
def prefixEnd_4405102 : Nat := 4983230072969 + 3 ^ 40 * 4405102 * 2
def baseEnd_4405102 : Nat := 2261934658082129251866311

theorem tailTrace_4405102 : CollatzResearch.WordTrace tailWord_4405102 prefixEnd_4405102 2261934658082129251866311 := by
  unfold tailWord_4405102
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083408660884407546317195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107111512858050173580358373 20083408660884407546317195)
  ·
    refine ⟨30125112991326611319475793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20083408660884407546317195 30125112991326611319475793)
    ·
      refine ⟨22593834743494958489606845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30125112991326611319475793 22593834743494958489606845)
      ·
        refine ⟨8472688028810609433602567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22593834743494958489606845 8472688028810609433602567)
        ·
          refine ⟨12709032043215914150403851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8472688028810609433602567 12709032043215914150403851)
          ·
            refine ⟨19063548064823871225605777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12709032043215914150403851 19063548064823871225605777)
            ·
              refine ⟨14297661048617903419204333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19063548064823871225605777 14297661048617903419204333)
              ·
                refine ⟨5361622893231713782201625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14297661048617903419204333 5361622893231713782201625)
                ·
                  refine ⟨4021217169923785336651219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5361622893231713782201625 4021217169923785336651219)
                  ·
                    refine ⟨6031825754885678004976829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4021217169923785336651219 6031825754885678004976829)
                    ·
                      refine ⟨2261934658082129251866311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6031825754885678004976829 2261934658082129251866311)
                      ·
                        rfl

theorem cell23_4405102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4405102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405102 prefixEnd_4405102 := by exact prefixLift 4405102
  have htrace : WordTrace (prefixWord ++ tailWord_4405102) baseStart_4405102 baseEnd_4405102 := by
    simpa [prefixWord, tailWord_4405102, baseEnd_4405102] using wordTrace_append hprefix tailTrace_4405102
  have hstable : (prefixWord ++ tailWord_4405102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405102).length < 2 ^ (prefixWord ++ tailWord_4405102).sum := by decide
  have hdescent : baseEnd_4405102 < baseStart_4405102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405125 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 4, 2, 2]
def baseStart_4405125 : Nat := 118140960795 + 4405125 * 2 ^ 59
def prefixEnd_4405125 : Nat := 4983230072969 + 3 ^ 40 * 4405125 * 2
def baseEnd_4405125 : Nat := 2261946468137182661878705

theorem tailTrace_4405125 : CollatzResearch.WordTrace tailWord_4405125 prefixEnd_4405125 2261946468137182661878705 := by
  unfold tailWord_4405125
  simp only [CollatzResearch.WordTrace]
  refine ⟨160668108165991935298624829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107112072110661290199083219 160668108165991935298624829)
  ·
    refine ⟨60250540562246975736984311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160668108165991935298624829 60250540562246975736984311)
    ·
      refine ⟨90375810843370463605476467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60250540562246975736984311 90375810843370463605476467)
      ·
        refine ⟨135563716265055695408214701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90375810843370463605476467 135563716265055695408214701)
        ·
          refine ⟨50836393599395885778080513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135563716265055695408214701 50836393599395885778080513)
          ·
            refine ⟨38127295199546914333560385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50836393599395885778080513 38127295199546914333560385)
            ·
              refine ⟨28595471399660185750170289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38127295199546914333560385 28595471399660185750170289)
              ·
                refine ⟨21446603549745139312627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28595471399660185750170289 21446603549745139312627717)
                ·
                  refine ⟨4021238165577213621117697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21446603549745139312627717 4021238165577213621117697)
                  ·
                    refine ⟨3015928624182910215838273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021238165577213621117697 3015928624182910215838273)
                    ·
                      refine ⟨2261946468137182661878705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3015928624182910215838273 2261946468137182661878705)
                      ·
                        rfl

theorem cell23_4405125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_4405125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405125 prefixEnd_4405125 := by exact prefixLift 4405125
  have htrace : WordTrace (prefixWord ++ tailWord_4405125) baseStart_4405125 baseEnd_4405125 := by
    simpa [prefixWord, tailWord_4405125, baseEnd_4405125] using wordTrace_append hprefix tailTrace_4405125
  have hstable : (prefixWord ++ tailWord_4405125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405125).length < 2 ^ (prefixWord ++ tailWord_4405125).sum := by decide
  have hdescent : baseEnd_4405125 < baseStart_4405125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405148 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 7]
def baseStart_4405148 : Nat := 118140960795 + 4405148 * 2 ^ 59
def prefixEnd_4405148 : Nat := 4983230072969 + 3 ^ 40 * 4405148 * 2
def baseEnd_4405148 : Nat := 251328697576915119099011

theorem tailTrace_4405148 : CollatzResearch.WordTrace tailWord_4405148 prefixEnd_4405148 251328697576915119099011 := by
  unfold tailWord_4405148
  simp only [CollatzResearch.WordTrace]
  refine ⟨80334473522454305113356049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107112631363272406817808065 80334473522454305113356049)
  ·
    refine ⟨60250855141840728835017037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80334473522454305113356049 60250855141840728835017037)
    ·
      refine ⟨22594070678190273313131389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60250855141840728835017037 22594070678190273313131389)
      ·
        refine ⟨8472776504321352492424271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22594070678190273313131389 8472776504321352492424271)
        ·
          refine ⟨12709164756482028738636407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8472776504321352492424271 12709164756482028738636407)
          ·
            refine ⟨19063747134723043107954611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12709164756482028738636407 19063747134723043107954611)
            ·
              refine ⟨28595620702084564661931917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19063747134723043107954611 28595620702084564661931917)
              ·
                refine ⟨10723357763281711748224469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28595620702084564661931917 10723357763281711748224469)
                ·
                  refine ⟨251328697576915119099011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10723357763281711748224469 251328697576915119099011)
                  ·
                    rfl

theorem cell23_4405148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_4405148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405148 prefixEnd_4405148 := by exact prefixLift 4405148
  have htrace : WordTrace (prefixWord ++ tailWord_4405148) baseStart_4405148 baseEnd_4405148 := by
    simpa [prefixWord, tailWord_4405148, baseEnd_4405148] using wordTrace_append hprefix tailTrace_4405148
  have hstable : (prefixWord ++ tailWord_4405148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405148).length < 2 ^ (prefixWord ++ tailWord_4405148).sum := by decide
  have hdescent : baseEnd_4405148 < baseStart_4405148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405161 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_4405161 : Nat := 118140960795 + 4405161 * 2 ^ 59
def prefixEnd_4405161 : Nat := 4983230072969 + 3 ^ 40 * 4405161 * 2
def baseEnd_4405161 : Nat := 753988317813581507009513

theorem tailTrace_4405161 : CollatzResearch.WordTrace tailWord_4405161 prefixEnd_4405161 753988317813581507009513 := by
  unfold tailWord_4405161
  simp only [CollatzResearch.WordTrace]
  refine ⟨160669421193861513446935337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107112947462574342297956891 160669421193861513446935337)
  ·
    refine ⟨120502065895396135085201503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160669421193861513446935337 120502065895396135085201503)
    ·
      refine ⟨180753098843094202627802255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120502065895396135085201503 180753098843094202627802255)
      ·
        refine ⟨271129648264641303941703383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180753098843094202627802255 271129648264641303941703383)
        ·
          refine ⟨406694472396961955912555075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271129648264641303941703383 406694472396961955912555075)
          ·
            refine ⟨610041708595442933868832613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406694472396961955912555075 610041708595442933868832613)
            ·
              refine ⟨114382820361645550100406115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 610041708595442933868832613 114382820361645550100406115)
              ·
                refine ⟨171574230542468325150609173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114382820361645550100406115 171574230542468325150609173)
                ·
                  refine ⟨8042542056678202741434805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171574230542468325150609173 8042542056678202741434805)
                  ·
                    refine ⟨753988317813581507009513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8042542056678202741434805 753988317813581507009513)
                    ·
                      rfl

theorem cell23_4405161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_4405161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405161 prefixEnd_4405161 := by exact prefixLift 4405161
  have htrace : WordTrace (prefixWord ++ tailWord_4405161) baseStart_4405161 baseEnd_4405161 := by
    simpa [prefixWord, tailWord_4405161, baseEnd_4405161] using wordTrace_append hprefix tailTrace_4405161
  have hstable : (prefixWord ++ tailWord_4405161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405161).length < 2 ^ (prefixWord ++ tailWord_4405161).sum := by decide
  have hdescent : baseEnd_4405161 < baseStart_4405161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405182 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_4405182 : Nat := 118140960795 + 4405182 * 2 ^ 59
def prefixEnd_4405182 : Nat := 4983230072969 + 3 ^ 40 * 4405182 * 2
def baseEnd_4405182 : Nat := 251330637392720993207327

theorem tailTrace_4405182 : CollatzResearch.WordTrace tailWord_4405182 prefixEnd_4405182 251330637392720993207327 := by
  unfold tailWord_4405182
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083773390848179254181225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107113458084523622688966533 20083773390848179254181225)
  ·
    refine ⟨15062830043136134440635919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20083773390848179254181225 15062830043136134440635919)
    ·
      refine ⟨22594245064704201660953879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15062830043136134440635919 22594245064704201660953879)
      ·
        refine ⟨33891367597056302491430819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22594245064704201660953879 33891367597056302491430819)
        ·
          refine ⟨50837051395584453737146229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33891367597056302491430819 50837051395584453737146229)
          ·
            refine ⟨4765973568336042537857459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50837051395584453737146229 4765973568336042537857459)
            ·
              refine ⟨7148960352504063806786189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765973568336042537857459 7148960352504063806786189)
              ·
                refine ⟨2680860132189023927544821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7148960352504063806786189 2680860132189023927544821)
                ·
                  refine ⟨251330637392720993207327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2680860132189023927544821 251330637392720993207327)
                  ·
                    rfl

theorem cell23_4405182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_4405182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405182 prefixEnd_4405182 := by exact prefixLift 4405182
  have htrace : WordTrace (prefixWord ++ tailWord_4405182) baseStart_4405182 baseEnd_4405182 := by
    simpa [prefixWord, tailWord_4405182, baseEnd_4405182] using wordTrace_append hprefix tailTrace_4405182
  have hstable : (prefixWord ++ tailWord_4405182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405182).length < 2 ^ (prefixWord ++ tailWord_4405182).sum := by decide
  have hdescent : baseEnd_4405182 < baseStart_4405182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405201 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_4405201 : Nat := 118140960795 + 4405201 * 2 ^ 59
def prefixEnd_4405201 : Nat := 4983230072969 + 3 ^ 40 * 4405201 * 2
def baseEnd_4405201 : Nat := 2261985492666924364528355

theorem tailTrace_4405201 : CollatzResearch.WordTrace tailWord_4405201 prefixEnd_4405201 2261985492666924364528355 := by
  unfold tailWord_4405201
  simp only [CollatzResearch.WordTrace]
  refine ⟨160670880113716600278391457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107113920075811066852260971 160670880113716600278391457)
  ·
    refine ⟨120503160085287450208793593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160670880113716600278391457 120503160085287450208793593)
    ·
      refine ⟨90377370063965587656595195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120503160085287450208793593 90377370063965587656595195)
      ·
        refine ⟨135566055095948381484892793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90377370063965587656595195 135566055095948381484892793)
        ·
          refine ⟨101674541321961286113669595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135566055095948381484892793 101674541321961286113669595)
          ·
            refine ⟨152511811982941929170504393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101674541321961286113669595 152511811982941929170504393)
            ·
              refine ⟨114383858987206446877878295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152511811982941929170504393 114383858987206446877878295)
              ·
                refine ⟨171575788480809670316817443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114383858987206446877878295 171575788480809670316817443)
                ·
                  refine ⟨257363682721214505475226165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171575788480809670316817443 257363682721214505475226165)
                  ·
                    refine ⟨24127845255113859888302453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 257363682721214505475226165 24127845255113859888302453)
                    ·
                      refine ⟨2261985492666924364528355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24127845255113859888302453 2261985492666924364528355)
                      ·
                        rfl

theorem cell23_4405201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_4405201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405201 prefixEnd_4405201 := by exact prefixLift 4405201
  have htrace : WordTrace (prefixWord ++ tailWord_4405201) baseStart_4405201 baseEnd_4405201 := by
    simpa [prefixWord, tailWord_4405201, baseEnd_4405201] using wordTrace_append hprefix tailTrace_4405201
  have hstable : (prefixWord ++ tailWord_4405201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405201).length < 2 ^ (prefixWord ++ tailWord_4405201).sum := by decide
  have hdescent : baseEnd_4405201 < baseStart_4405201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405255 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 6]
def baseStart_4405255 : Nat := 118140960795 + 4405255 * 2 ^ 59
def prefixEnd_4405255 : Nat := 4983230072969 + 3 ^ 40 * 4405255 * 2
def baseEnd_4405255 : Nat := 251334802291363017028123

theorem tailTrace_4405255 : CollatzResearch.WordTrace tailWord_4405255 prefixEnd_4405255 251334802291363017028123 := by
  unfold tailWord_4405255
  simp only [CollatzResearch.WordTrace]
  refine ⟨160672849655520967500857219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107115233103680645000571479 160672849655520967500857219)
  ·
    refine ⟨241009274483281451251285829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160672849655520967500857219 241009274483281451251285829)
    ·
      refine ⟨45189238965615272109616093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241009274483281451251285829 45189238965615272109616093)
      ·
        refine ⟨16945964612105727041106035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45189238965615272109616093 16945964612105727041106035)
        ·
          refine ⟨25418946918158590561659053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16945964612105727041106035 25418946918158590561659053)
          ·
            refine ⟨9532105094309471460622145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25418946918158590561659053 9532105094309471460622145)
            ·
              refine ⟨7149078820732103595466609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9532105094309471460622145 7149078820732103595466609)
              ·
                refine ⟨5361809115549077696599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7149078820732103595466609 5361809115549077696599957)
                ·
                  refine ⟨251334802291363017028123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5361809115549077696599957 251334802291363017028123)
                  ·
                    rfl

theorem cell23_4405255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 6].length) (baseStart_4405255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405255 prefixEnd_4405255 := by exact prefixLift 4405255
  have htrace : WordTrace (prefixWord ++ tailWord_4405255) baseStart_4405255 baseEnd_4405255 := by
    simpa [prefixWord, tailWord_4405255, baseEnd_4405255] using wordTrace_append hprefix tailTrace_4405255
  have hstable : (prefixWord ++ tailWord_4405255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405255).length < 2 ^ (prefixWord ++ tailWord_4405255).sum := by decide
  have hdescent : baseEnd_4405255 < baseStart_4405255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405282 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_4405282 : Nat := 118140960795 + 4405282 * 2 ^ 59
def prefixEnd_4405282 : Nat := 4983230072969 + 3 ^ 40 * 4405282 * 2
def baseEnd_4405282 : Nat := 2262027084599938547615483

theorem tailTrace_4405282 : CollatzResearch.WordTrace tailWord_4405282 prefixEnd_4405282 2262027084599938547615483 := by
  unfold tailWord_4405282
  simp only [CollatzResearch.WordTrace]
  refine ⟨40168458606605787778022525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107115889617615434074726733 40168458606605787778022525)
  ·
    refine ⟨15063171977477170416758447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40168458606605787778022525 15063171977477170416758447)
    ·
      refine ⟨22594757966215755625137671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15063171977477170416758447 22594757966215755625137671)
      ·
        refine ⟨33892136949323633437706507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22594757966215755625137671 33892136949323633437706507)
        ·
          refine ⟨50838205423985450156559761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33892136949323633437706507 50838205423985450156559761)
          ·
            refine ⟨38128654067989087617419821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50838205423985450156559761 38128654067989087617419821)
            ·
              refine ⟨14298245275495907856532433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38128654067989087617419821 14298245275495907856532433)
              ·
                refine ⟨10723683956621930892399325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14298245275495907856532433 10723683956621930892399325)
                ·
                  refine ⟨4021381483733224084649747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10723683956621930892399325 4021381483733224084649747)
                  ·
                    refine ⟨6032072225599836126974621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4021381483733224084649747 6032072225599836126974621)
                    ·
                      refine ⟨2262027084599938547615483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6032072225599836126974621 2262027084599938547615483)
                      ·
                        rfl

theorem cell23_4405282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_4405282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405282 prefixEnd_4405282 := by exact prefixLift 4405282
  have htrace : WordTrace (prefixWord ++ tailWord_4405282) baseStart_4405282 baseEnd_4405282 := by
    simpa [prefixWord, tailWord_4405282, baseEnd_4405282] using wordTrace_append hprefix tailTrace_4405282
  have hstable : (prefixWord ++ tailWord_4405282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405282).length < 2 ^ (prefixWord ++ tailWord_4405282).sum := by decide
  have hdescent : baseEnd_4405282 < baseStart_4405282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405302 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4405302 : Nat := 118140960795 + 4405302 * 2 ^ 59
def prefixEnd_4405302 : Nat := 4983230072969 + 3 ^ 40 * 4405302 * 2
def baseEnd_4405302 : Nat := 754012451404342823121797

theorem tailTrace_4405302 : CollatzResearch.WordTrace tailWord_4405302 prefixEnd_4405302 754012451404342823121797 := by
  unfold tailWord_4405302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042160242896918407988635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107116375924233796351878773 10042160242896918407988635)
  ·
    refine ⟨15063240364345377611982953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10042160242896918407988635 15063240364345377611982953)
    ·
      refine ⟨11297430273259033208987215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15063240364345377611982953 11297430273259033208987215)
      ·
        refine ⟨16946145409888549813480823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11297430273259033208987215 16946145409888549813480823)
        ·
          refine ⟨25419218114832824720221235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16946145409888549813480823 25419218114832824720221235)
          ·
            refine ⟨38128827172249237080331853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25419218114832824720221235 38128827172249237080331853)
            ·
              refine ⟨14298310189593463905124445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38128827172249237080331853 14298310189593463905124445)
              ·
                refine ⟨5361866321097548964421667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14298310189593463905124445 5361866321097548964421667)
                ·
                  refine ⟨8042799481646323446632501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5361866321097548964421667 8042799481646323446632501)
                  ·
                    refine ⟨754012451404342823121797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8042799481646323446632501 754012451404342823121797)
                    ·
                      rfl

theorem cell23_4405302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4405302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405302 prefixEnd_4405302 := by exact prefixLift 4405302
  have htrace : WordTrace (prefixWord ++ tailWord_4405302) baseStart_4405302 baseEnd_4405302 := by
    simpa [prefixWord, tailWord_4405302, baseEnd_4405302] using wordTrace_append hprefix tailTrace_4405302
  have hstable : (prefixWord ++ tailWord_4405302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405302).length < 2 ^ (prefixWord ++ tailWord_4405302).sum := by decide
  have hdescent : baseEnd_4405302 < baseStart_4405302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405315 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 2, 4]
def baseStart_4405315 : Nat := 118140960795 + 4405315 * 2 ^ 59
def prefixEnd_4405315 : Nat := 4983230072969 + 3 ^ 40 * 4405315 * 2
def baseEnd_4405315 : Nat := 754014676487178972834277

theorem tailTrace_4405315 : CollatzResearch.WordTrace tailWord_4405315 prefixEnd_4405315 754014676487178972834277 := by
  unfold tailWord_4405315
  simp only [CollatzResearch.WordTrace]
  refine ⟨160675038035303597748041399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107116692023535731832027599 160675038035303597748041399)
  ·
    refine ⟨241012557052955396622062099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160675038035303597748041399 241012557052955396622062099)
    ·
      refine ⟨361518835579433094933093149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241012557052955396622062099 361518835579433094933093149)
      ·
        refine ⟨135569563342287410599909931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 361518835579433094933093149 135569563342287410599909931)
        ·
          refine ⟨203354345013431115899864897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135569563342287410599909931 203354345013431115899864897)
          ·
            refine ⟨152515758760073336924898673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203354345013431115899864897 152515758760073336924898673)
            ·
              refine ⟨114386819070055002693674005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152515758760073336924898673 114386819070055002693674005)
              ·
                refine ⟨5361882143908828251265969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114386819070055002693674005 5361882143908828251265969)
                ·
                  refine ⟨4021411607931621188449477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5361882143908828251265969 4021411607931621188449477)
                  ·
                    refine ⟨754014676487178972834277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4021411607931621188449477 754014676487178972834277)
                    ·
                      rfl

theorem cell23_4405315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 4].length) (baseStart_4405315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405315 prefixEnd_4405315 := by exact prefixLift 4405315
  have htrace : WordTrace (prefixWord ++ tailWord_4405315) baseStart_4405315 baseEnd_4405315 := by
    simpa [prefixWord, tailWord_4405315, baseEnd_4405315] using wordTrace_append hprefix tailTrace_4405315
  have hstable : (prefixWord ++ tailWord_4405315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405315).length < 2 ^ (prefixWord ++ tailWord_4405315).sum := by decide
  have hdescent : baseEnd_4405315 < baseStart_4405315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405335 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_4405335 : Nat := 118140960795 + 4405335 * 2 ^ 59
def prefixEnd_4405335 : Nat := 4983230072969 + 3 ^ 40 * 4405335 * 2
def baseEnd_4405335 : Nat := 2262054299074626840252739

theorem tailTrace_4405335 : CollatzResearch.WordTrace tailWord_4405335 prefixEnd_4405335 2262054299074626840252739 := by
  unfold tailWord_4405335
  simp only [CollatzResearch.WordTrace]
  refine ⟨160675767495231141163769459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107117178330154094109179639 160675767495231141163769459)
  ·
    refine ⟨241013651242846711745654189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160675767495231141163769459 241013651242846711745654189)
    ·
      refine ⟨90380119216067516904620321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241013651242846711745654189 90380119216067516904620321)
      ·
        refine ⟨67785089412050637678465241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90380119216067516904620321 67785089412050637678465241)
        ·
          refine ⟨50838817059037978258848931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67785089412050637678465241 50838817059037978258848931)
          ·
            refine ⟨76258225588556967388273397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50838817059037978258848931 76258225588556967388273397)
            ·
              refine ⟨7149208648927215692650631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76258225588556967388273397 7149208648927215692650631)
              ·
                refine ⟨10723812973390823538975947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7149208648927215692650631 10723812973390823538975947)
                ·
                  refine ⟨16085719460086235308463921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10723812973390823538975947 16085719460086235308463921)
                  ·
                    refine ⟨12064289595064676481347941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16085719460086235308463921 12064289595064676481347941)
                    ·
                      refine ⟨2262054299074626840252739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12064289595064676481347941 2262054299074626840252739)
                      ·
                        rfl

theorem cell23_4405335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_4405335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405335 prefixEnd_4405335 := by exact prefixLift 4405335
  have htrace : WordTrace (prefixWord ++ tailWord_4405335) baseStart_4405335 baseEnd_4405335 := by
    simpa [prefixWord, tailWord_4405335, baseEnd_4405335] using wordTrace_append hprefix tailTrace_4405335
  have hstable : (prefixWord ++ tailWord_4405335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405335).length < 2 ^ (prefixWord ++ tailWord_4405335).sum := by decide
  have hdescent : baseEnd_4405335 < baseStart_4405335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405356 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 1, 2, 2]
def baseStart_4405356 : Nat := 118140960795 + 4405356 * 2 ^ 59
def prefixEnd_4405356 : Nat := 4983230072969 + 3 ^ 40 * 4405356 * 2
def baseEnd_4405356 : Nat := 2262065082168371258090143

theorem tailTrace_4405356 : CollatzResearch.WordTrace tailWord_4405356 prefixEnd_4405356 2262065082168371258090143 := by
  unfold tailWord_4405356
  simp only [CollatzResearch.WordTrace]
  refine ⟨80338266714077530875141961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107117688952103374500189281 80338266714077530875141961)
  ·
    refine ⟨60253700035558148156356471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80338266714077530875141961 60253700035558148156356471)
    ·
      refine ⟨90380550053337222234534707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60253700035558148156356471 90380550053337222234534707)
      ·
        refine ⟨135570825080005833351802061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90380550053337222234534707 135570825080005833351802061)
        ·
          refine ⟨50839059405002187506925773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135570825080005833351802061 50839059405002187506925773)
          ·
            refine ⟨19064647276875820315097165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50839059405002187506925773 19064647276875820315097165)
            ·
              refine ⟨7149242728828432618161437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19064647276875820315097165 7149242728828432618161437)
              ·
                refine ⟨2680966023310662231810539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7149242728828432618161437 2680966023310662231810539)
                ·
                  refine ⟨4021449034965993347715809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680966023310662231810539 4021449034965993347715809)
                  ·
                    refine ⟨3016086776224495010786857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021449034965993347715809 3016086776224495010786857)
                    ·
                      refine ⟨2262065082168371258090143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016086776224495010786857 2262065082168371258090143)
                      ·
                        rfl

theorem cell23_4405356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_4405356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405356 prefixEnd_4405356 := by exact prefixLift 4405356
  have htrace : WordTrace (prefixWord ++ tailWord_4405356) baseStart_4405356 baseEnd_4405356 := by
    simpa [prefixWord, tailWord_4405356, baseEnd_4405356] using wordTrace_append hprefix tailTrace_4405356
  have hstable : (prefixWord ++ tailWord_4405356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405356).length < 2 ^ (prefixWord ++ tailWord_4405356).sum := by decide
  have hdescent : baseEnd_4405356 < baseStart_4405356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405368 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_4405368 : Nat := 118140960795 + 4405368 * 2 ^ 59
def prefixEnd_4405368 : Nat := 4983230072969 + 3 ^ 40 * 4405368 * 2
def baseEnd_4405368 : Nat := 2262071243936225211140087

theorem tailTrace_4405368 : CollatzResearch.WordTrace tailWord_4405368 prefixEnd_4405368 2262071243936225211140087 := by
  unfold tailWord_4405368
  simp only [CollatzResearch.WordTrace]
  refine ⟨80338485552055793899860379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107117980736074391866480505 80338485552055793899860379)
  ·
    refine ⟨120507728328083690849790569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80338485552055793899860379 120507728328083690849790569)
    ·
      refine ⟨90380796246062768137342927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120507728328083690849790569 90380796246062768137342927)
      ·
        refine ⟨135571194369094152206014391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90380796246062768137342927 135571194369094152206014391)
        ·
          refine ⟨203356791553641228309021587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135571194369094152206014391 203356791553641228309021587)
          ·
            refine ⟨305035187330461842463532381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203356791553641228309021587 305035187330461842463532381)
            ·
              refine ⟨114388195248923190923824643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305035187330461842463532381 114388195248923190923824643)
              ·
                refine ⟨171582292873384786385736965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114388195248923190923824643 171582292873384786385736965)
                ·
                  refine ⟨32171679913759647447325681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171582292873384786385736965 32171679913759647447325681)
                  ·
                    refine ⟨24128759935319735585494261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32171679913759647447325681 24128759935319735585494261)
                    ·
                      refine ⟨2262071243936225211140087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24128759935319735585494261 2262071243936225211140087)
                      ·
                        rfl

theorem cell23_4405368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_4405368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405368 prefixEnd_4405368 := by exact prefixLift 4405368
  have htrace : WordTrace (prefixWord ++ tailWord_4405368) baseStart_4405368 baseEnd_4405368 := by
    simpa [prefixWord, tailWord_4405368, baseEnd_4405368] using wordTrace_append hprefix tailTrace_4405368
  have hstable : (prefixWord ++ tailWord_4405368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405368).length < 2 ^ (prefixWord ++ tailWord_4405368).sum := by decide
  have hdescent : baseEnd_4405368 < baseStart_4405368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405372 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_4405372 : Nat := 118140960795 + 4405372 * 2 ^ 59
def prefixEnd_4405372 : Nat := 4983230072969 + 3 ^ 40 * 4405372 * 2
def baseEnd_4405372 : Nat := 2262073297858843195490069

theorem tailTrace_4405372 : CollatzResearch.WordTrace tailWord_4405372 prefixEnd_4405372 2262073297858843195490069 := by
  unfold tailWord_4405372
  simp only [CollatzResearch.WordTrace]
  refine ⟨80338558498048548241433185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107118077997398064321910913 80338558498048548241433185)
  ·
    refine ⟨60253918873536411181074889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80338558498048548241433185 60253918873536411181074889)
    ·
      refine ⟨45190439155152308385806167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60253918873536411181074889 45190439155152308385806167)
      ·
        refine ⟨67785658732728462578709251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45190439155152308385806167 67785658732728462578709251)
        ·
          refine ⟨101678488099092693868063877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67785658732728462578709251 101678488099092693868063877)
          ·
            refine ⟨19064716518579880100261977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101678488099092693868063877 19064716518579880100261977)
            ·
              refine ⟨14298537388934910075196483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19064716518579880100261977 14298537388934910075196483)
              ·
                refine ⟨21447806083402365112794725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14298537388934910075196483 21447806083402365112794725)
                ·
                  refine ⟨4021463640637943458649011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21447806083402365112794725 4021463640637943458649011)
                  ·
                    refine ⟨6032195460956915187973517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4021463640637943458649011 6032195460956915187973517)
                    ·
                      refine ⟨2262073297858843195490069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6032195460956915187973517 2262073297858843195490069)
                      ·
                        rfl

theorem cell23_4405372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_4405372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405372 prefixEnd_4405372 := by exact prefixLift 4405372
  have htrace : WordTrace (prefixWord ++ tailWord_4405372) baseStart_4405372 baseEnd_4405372 := by
    simpa [prefixWord, tailWord_4405372, baseEnd_4405372] using wordTrace_append hprefix tailTrace_4405372
  have hstable : (prefixWord ++ tailWord_4405372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405372).length < 2 ^ (prefixWord ++ tailWord_4405372).sum := by decide
  have hdescent : baseEnd_4405372 < baseStart_4405372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405373 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_4405373 : Nat := 118140960795 + 4405373 * 2 ^ 59
def prefixEnd_4405373 : Nat := 4983230072969 + 3 ^ 40 * 4405373 * 2
def baseEnd_4405373 : Nat := 2262073811339497691577565

theorem tailTrace_4405373 : CollatzResearch.WordTrace tailWord_4405373 prefixEnd_4405373 2262073811339497691577565 := by
  unfold tailWord_4405373
  simp only [CollatzResearch.WordTrace]
  refine ⟨160677153469093473653652773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107118102312728982435768515 160677153469093473653652773)
  ·
    refine ⟨30126966275455026310059895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160677153469093473653652773 30126966275455026310059895)
    ·
      refine ⟨45190449413182539465089843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30126966275455026310059895 45190449413182539465089843)
      ·
        refine ⟨67785674119773809197634765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45190449413182539465089843 67785674119773809197634765)
        ·
          refine ⟨25419627794915178449113037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67785674119773809197634765 25419627794915178449113037)
          ·
            refine ⟨9532360423093191918417389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25419627794915178449113037 9532360423093191918417389)
            ·
              refine ⟨3574635158659946969406521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9532360423093191918417389 3574635158659946969406521)
              ·
                refine ⟨2680976368994960227054891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3574635158659946969406521 2680976368994960227054891)
                ·
                  refine ⟨4021464553492440340582337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680976368994960227054891 4021464553492440340582337)
                  ·
                    refine ⟨3016098415119330255436753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021464553492440340582337 3016098415119330255436753)
                    ·
                      refine ⟨2262073811339497691577565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016098415119330255436753 2262073811339497691577565)
                      ·
                        rfl

theorem cell23_4405373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_4405373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405373 prefixEnd_4405373 := by exact prefixLift 4405373
  have htrace : WordTrace (prefixWord ++ tailWord_4405373) baseStart_4405373 baseEnd_4405373 := by
    simpa [prefixWord, tailWord_4405373, baseEnd_4405373] using wordTrace_append hprefix tailTrace_4405373
  have hstable : (prefixWord ++ tailWord_4405373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405373).length < 2 ^ (prefixWord ++ tailWord_4405373).sum := by decide
  have hdescent : baseEnd_4405373 < baseStart_4405373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405399 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 3, 3, 2]
def baseStart_4405399 : Nat := 118140960795 + 4405399 * 2 ^ 59
def prefixEnd_4405399 : Nat := 4983230072969 + 3 ^ 40 * 4405399 * 2
def baseEnd_4405399 : Nat := 2262087161836514589852445

theorem tailTrace_4405399 : CollatzResearch.WordTrace tailWord_4405399 prefixEnd_4405399 2262087161836514589852445 := by
  unfold tailWord_4405399
  simp only [CollatzResearch.WordTrace]
  refine ⟨160678101766999280094099251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107118734511332853396066167 160678101766999280094099251)
  ·
    refine ⟨241017152650498920141148877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160678101766999280094099251 241017152650498920141148877)
    ·
      refine ⟨90381432243937095052930829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241017152650498920141148877 90381432243937095052930829)
      ·
        refine ⟨33893037091476410644849061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90381432243937095052930829 33893037091476410644849061)
        ·
          refine ⟨6354944454651826995909199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33893037091476410644849061 6354944454651826995909199)
          ·
            refine ⟨9532416681977740493863799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354944454651826995909199 9532416681977740493863799)
            ·
              refine ⟨14298625022966610740795699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9532416681977740493863799 14298625022966610740795699)
              ·
                refine ⟨21447937534449916111193549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14298625022966610740795699 21447937534449916111193549)
                ·
                  refine ⟨8042976575418718541697581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21447937534449916111193549 8042976575418718541697581)
                  ·
                    refine ⟨3016116215782019453136593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8042976575418718541697581 3016116215782019453136593)
                    ·
                      refine ⟨2262087161836514589852445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016116215782019453136593 2262087161836514589852445)
                      ·
                        rfl

theorem cell23_4405399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_4405399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405399 prefixEnd_4405399 := by exact prefixLift 4405399
  have htrace : WordTrace (prefixWord ++ tailWord_4405399) baseStart_4405399 baseEnd_4405399 := by
    simpa [prefixWord, tailWord_4405399, baseEnd_4405399] using wordTrace_append hprefix tailTrace_4405399
  have hstable : (prefixWord ++ tailWord_4405399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405399).length < 2 ^ (prefixWord ++ tailWord_4405399).sum := by decide
  have hdescent : baseEnd_4405399 < baseStart_4405399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405445 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_4405445 : Nat := 118140960795 + 4405445 * 2 ^ 59
def prefixEnd_4405445 : Nat := 4983230072969 + 3 ^ 40 * 4405445 * 2
def baseEnd_4405445 : Nat := 2262110781946621409877233

theorem tailTrace_4405445 : CollatzResearch.WordTrace tailWord_4405445 prefixEnd_4405445 2262110781946621409877233 := by
  unfold tailWord_4405445
  simp only [CollatzResearch.WordTrace]
  refine ⟨160679779524832629950273789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107119853016555086633515859 160679779524832629950273789)
  ·
    refine ⟨60254917321812236231352671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160679779524832629950273789 60254917321812236231352671)
    ·
      refine ⟨90382375982718354347029007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60254917321812236231352671 90382375982718354347029007)
      ·
        refine ⟨135573563974077531520543511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90382375982718354347029007 135573563974077531520543511)
        ·
          refine ⟨203360345961116297280815267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135573563974077531520543511 203360345961116297280815267)
          ·
            refine ⟨305040518941674445921222901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203360345961116297280815267 305040518941674445921222901)
            ·
              refine ⟨28597548650781979305114647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 305040518941674445921222901 28597548650781979305114647)
              ·
                refine ⟨42896322976172968957671971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28597548650781979305114647 42896322976172968957671971)
                ·
                  refine ⟨64344484464259453436507957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42896322976172968957671971 64344484464259453436507957)
                  ·
                    refine ⟨6032295418524323759672621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64344484464259453436507957 6032295418524323759672621)
                    ·
                      refine ⟨2262110781946621409877233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6032295418524323759672621 2262110781946621409877233)
                      ·
                        rfl

theorem cell23_4405445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_4405445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405445 prefixEnd_4405445 := by exact prefixLift 4405445
  have htrace : WordTrace (prefixWord ++ tailWord_4405445) baseStart_4405445 baseEnd_4405445 := by
    simpa [prefixWord, tailWord_4405445, baseEnd_4405445] using wordTrace_append hprefix tailTrace_4405445
  have hstable : (prefixWord ++ tailWord_4405445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405445).length < 2 ^ (prefixWord ++ tailWord_4405445).sum := by decide
  have hdescent : baseEnd_4405445 < baseStart_4405445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405469 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 5]
def baseStart_4405469 : Nat := 118140960795 + 4405469 * 2 ^ 59
def prefixEnd_4405469 : Nat := 4983230072969 + 3 ^ 40 * 4405469 * 2
def baseEnd_4405469 : Nat := 251347011720258812886347

theorem tailTrace_4405469 : CollatzResearch.WordTrace tailWord_4405469 prefixEnd_4405469 251347011720258812886347 := by
  unfold tailWord_4405469
  simp only [CollatzResearch.WordTrace]
  refine ⟨160680654876745682049147461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107120436584497121366098307 160680654876745682049147461)
  ·
    refine ⟨30127622789389815384215149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160680654876745682049147461 30127622789389815384215149)
    ·
      refine ⟨11297858546021180769080681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30127622789389815384215149 11297858546021180769080681)
      ·
        refine ⟨8473393909515885576810511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11297858546021180769080681 8473393909515885576810511)
        ·
          refine ⟨12710090864273828365215767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8473393909515885576810511 12710090864273828365215767)
          ·
            refine ⟨19065136296410742547823651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12710090864273828365215767 19065136296410742547823651)
            ·
              refine ⟨28597704444616113821735477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19065136296410742547823651 28597704444616113821735477)
              ·
                refine ⟨2681034791682760670787701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28597704444616113821735477 2681034791682760670787701)
                ·
                  refine ⟨251347011720258812886347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2681034791682760670787701 251347011720258812886347)
                  ·
                    rfl

theorem cell23_4405469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_4405469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405469 prefixEnd_4405469 := by exact prefixLift 4405469
  have htrace : WordTrace (prefixWord ++ tailWord_4405469) baseStart_4405469 baseEnd_4405469 := by
    simpa [prefixWord, tailWord_4405469, baseEnd_4405469] using wordTrace_append hprefix tailTrace_4405469
  have hstable : (prefixWord ++ tailWord_4405469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405469).length < 2 ^ (prefixWord ++ tailWord_4405469).sum := by decide
  have hdescent : baseEnd_4405469 < baseStart_4405469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405502 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4405502 : Nat := 118140960795 + 4405502 * 2 ^ 59
def prefixEnd_4405502 : Nat := 4983230072969 + 3 ^ 40 * 4405502 * 2
def baseEnd_4405502 : Nat := 2262140050343927686864471

theorem tailTrace_4405502 : CollatzResearch.WordTrace tailWord_4405502 prefixEnd_4405502 2262140050343927686864471 := by
  unfold tailWord_4405502
  simp only [CollatzResearch.WordTrace]
  refine ⟨20085232310703266085637345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107121238990417419123399173 20085232310703266085637345)
  ·
    refine ⟨15063924233027449564228009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20085232310703266085637345 15063924233027449564228009)
    ·
      refine ⟨11297943174770587173171007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15063924233027449564228009 11297943174770587173171007)
      ·
        refine ⟨16946914762155880759756511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11297943174770587173171007 16946914762155880759756511)
        ·
          refine ⟨25420372143233821139634767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16946914762155880759756511 25420372143233821139634767)
          ·
            refine ⟨38130558214850731709452151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25420372143233821139634767 38130558214850731709452151)
            ·
              refine ⟨57195837322276097564178227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38130558214850731709452151 57195837322276097564178227)
              ·
                refine ⟨85793755983414146346267341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57195837322276097564178227 85793755983414146346267341)
                ·
                  refine ⟨32172658493780304879850253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85793755983414146346267341 32172658493780304879850253)
                  ·
                    refine ⟨12064746935167614329943845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32172658493780304879850253 12064746935167614329943845)
                    ·
                      refine ⟨2262140050343927686864471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12064746935167614329943845 2262140050343927686864471)
                      ·
                        rfl

theorem cell23_4405502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4405502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405502 prefixEnd_4405502 := by exact prefixLift 4405502
  have htrace : WordTrace (prefixWord ++ tailWord_4405502) baseStart_4405502 baseEnd_4405502 := by
    simpa [prefixWord, tailWord_4405502, baseEnd_4405502] using wordTrace_append hprefix tailTrace_4405502
  have hstable : (prefixWord ++ tailWord_4405502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405502).length < 2 ^ (prefixWord ++ tailWord_4405502).sum := by decide
  have hdescent : baseEnd_4405502 < baseStart_4405502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405515 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4]
def baseStart_4405515 : Nat := 118140960795 + 4405515 * 2 ^ 59
def prefixEnd_4405515 : Nat := 4983230072969 + 3 ^ 40 * 4405515 * 2
def baseEnd_4405515 : Nat := 2262146725592436136001911

theorem tailTrace_4405515 : CollatzResearch.WordTrace tailWord_4405515 prefixEnd_4405515 2262146725592436136001911 := by
  unfold tailWord_4405515
  simp only [CollatzResearch.WordTrace]
  refine ⟨160682332634579031905321999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107121555089719354603547999 160682332634579031905321999)
  ·
    refine ⟨241023498951868547857982999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160682332634579031905321999 241023498951868547857982999)
    ·
      refine ⟨361535248427802821786974499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241023498951868547857982999 361535248427802821786974499)
      ·
        refine ⟨542302872641704232680461749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361535248427802821786974499 542302872641704232680461749)
        ·
          refine ⟨50840894310159771813793289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 542302872641704232680461749 50840894310159771813793289)
          ·
            refine ⟨38130670732619828860344967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50840894310159771813793289 38130670732619828860344967)
            ·
              refine ⟨57196006098929743290517451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38130670732619828860344967 57196006098929743290517451)
              ·
                refine ⟨85794009148394614935776177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57196006098929743290517451 85794009148394614935776177)
                ·
                  refine ⟨64345506861295961201832133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85794009148394614935776177 64345506861295961201832133)
                  ·
                    refine ⟨12064782536492992725343525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64345506861295961201832133 12064782536492992725343525)
                    ·
                      refine ⟨2262146725592436136001911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12064782536492992725343525 2262146725592436136001911)
                      ·
                        rfl

theorem cell23_4405515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_4405515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405515 prefixEnd_4405515 := by exact prefixLift 4405515
  have htrace : WordTrace (prefixWord ++ tailWord_4405515) baseStart_4405515 baseEnd_4405515 := by
    simpa [prefixWord, tailWord_4405515, baseEnd_4405515] using wordTrace_append hprefix tailTrace_4405515
  have hstable : (prefixWord ++ tailWord_4405515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405515).length < 2 ^ (prefixWord ++ tailWord_4405515).sum := by decide
  have hdescent : baseEnd_4405515 < baseStart_4405515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405525 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 8]
def baseStart_4405525 : Nat := 118140960795 + 4405525 * 2 ^ 59
def prefixEnd_4405525 : Nat := 4983230072969 + 3 ^ 40 * 4405525 * 2
def baseEnd_4405525 : Nat := 251350206710997899652985

theorem tailTrace_4405525 : CollatzResearch.WordTrace tailWord_4405525 prefixEnd_4405525 251350206710997899652985 := by
  unfold tailWord_4405525
  simp only [CollatzResearch.WordTrace]
  refine ⟨160682697364542803613186029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107121798243028535742124019 160682697364542803613186029)
  ·
    refine ⟨60256011511703551354944761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160682697364542803613186029 60256011511703551354944761)
    ·
      refine ⟨45192008633777663516208571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60256011511703551354944761 45192008633777663516208571)
      ·
        refine ⟨67788012950666495274312857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45192008633777663516208571 67788012950666495274312857)
        ·
          refine ⟨50841009712999871455734643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67788012950666495274312857 50841009712999871455734643)
          ·
            refine ⟨76261514569499807183601965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50841009712999871455734643 76261514569499807183601965)
            ·
              refine ⟨28598067963562427693850737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76261514569499807183601965 28598067963562427693850737)
              ·
                refine ⟨21448550972671820770388053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28598067963562427693850737 21448550972671820770388053)
                ·
                  refine ⟨251350206710997899652985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21448550972671820770388053 251350206710997899652985)
                  ·
                    rfl

theorem cell23_4405525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_4405525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405525 prefixEnd_4405525 := by exact prefixLift 4405525
  have htrace : WordTrace (prefixWord ++ tailWord_4405525) baseStart_4405525 baseEnd_4405525 := by
    simpa [prefixWord, tailWord_4405525, baseEnd_4405525] using wordTrace_append hprefix tailTrace_4405525
  have hstable : (prefixWord ++ tailWord_4405525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405525).length < 2 ^ (prefixWord ++ tailWord_4405525).sum := by decide
  have hdescent : baseEnd_4405525 < baseStart_4405525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405615 : List Nat := [1, 1, 2, 1, 3, 1, 2, 12]
def baseStart_4405615 : Nat := 118140960795 + 4405615 * 2 ^ 59
def prefixEnd_4405615 : Nat := 4983230072969 + 3 ^ 40 * 4405615 * 2
def baseEnd_4405615 : Nat := 83785113839180953509313

theorem tailTrace_4405615 : CollatzResearch.WordTrace tailWord_4405615 prefixEnd_4405615 83785113839180953509313 := by
  unfold tailWord_4405615
  simp only [CollatzResearch.WordTrace]
  refine ⟨160685979934216748983962299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107123986622811165989308199 160685979934216748983962299)
  ·
    refine ⟨241028969901325123475943449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160685979934216748983962299 241028969901325123475943449)
    ·
      refine ⟨180771727425993842606957587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241028969901325123475943449 180771727425993842606957587)
      ·
        refine ⟨271157591138990763910436381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180771727425993842606957587 271157591138990763910436381)
        ·
          refine ⟨101684096677121536466413643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271157591138990763910436381 101684096677121536466413643)
          ·
            refine ⟨152526145015682304699620465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101684096677121536466413643 152526145015682304699620465)
            ·
              refine ⟨114394608761761728524715349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152526145015682304699620465 114394608761761728524715349)
              ·
                refine ⟨83785113839180953509313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 114394608761761728524715349 83785113839180953509313)
                ·
                  rfl

theorem cell23_4405615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 12].length) (baseStart_4405615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405615 prefixEnd_4405615 := by exact prefixLift 4405615
  have htrace : WordTrace (prefixWord ++ tailWord_4405615) baseStart_4405615 baseEnd_4405615 := by
    simpa [prefixWord, tailWord_4405615, baseEnd_4405615] using wordTrace_append hprefix tailTrace_4405615
  have hstable : (prefixWord ++ tailWord_4405615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405615).length < 2 ^ (prefixWord ++ tailWord_4405615).sum := by decide
  have hdescent : baseEnd_4405615 < baseStart_4405615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405629 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_4405629 : Nat := 118140960795 + 4405629 * 2 ^ 59
def prefixEnd_4405629 : Nat := 4983230072969 + 3 ^ 40 * 4405629 * 2
def baseEnd_4405629 : Nat := 2262205262387048689976387

theorem tailTrace_4405629 : CollatzResearch.WordTrace tailWord_4405629 prefixEnd_4405629 2262205262387048689976387 := by
  unfold tailWord_4405629
  simp only [CollatzResearch.WordTrace]
  refine ⟨160686490556166029374971941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107124327037444019583314627 160686490556166029374971941)
  ·
    refine ⟨30128716979281130507807239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160686490556166029374971941 30128716979281130507807239)
    ·
      refine ⟨45193075468921695761710859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30128716979281130507807239 45193075468921695761710859)
      ·
        refine ⟨67789613203382543642566289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45193075468921695761710859 67789613203382543642566289)
        ·
          refine ⟨50842209902536907731924717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67789613203382543642566289 50842209902536907731924717)
          ·
            refine ⟨19065828713451340399471769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50842209902536907731924717 19065828713451340399471769)
            ·
              refine ⟨14299371535088505299603827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19065828713451340399471769 14299371535088505299603827)
              ·
                refine ⟨21449057302632757949405741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14299371535088505299603827 21449057302632757949405741)
                ·
                  refine ⟨8043396488487284231027153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21449057302632757949405741 8043396488487284231027153)
                  ·
                    refine ⟨6032547366365463173270365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8043396488487284231027153 6032547366365463173270365)
                    ·
                      refine ⟨2262205262387048689976387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6032547366365463173270365 2262205262387048689976387)
                      ·
                        rfl

theorem cell23_4405629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_4405629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405629 prefixEnd_4405629 := by exact prefixLift 4405629
  have htrace : WordTrace (prefixWord ++ tailWord_4405629) baseStart_4405629 baseEnd_4405629 := by
    simpa [prefixWord, tailWord_4405629, baseEnd_4405629] using wordTrace_append hprefix tailTrace_4405629
  have hstable : (prefixWord ++ tailWord_4405629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405629).length < 2 ^ (prefixWord ++ tailWord_4405629).sum := by decide
  have hdescent : baseEnd_4405629 < baseStart_4405629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405643 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 1, 2, 2]
def baseStart_4405643 : Nat := 118140960795 + 4405643 * 2 ^ 59
def prefixEnd_4405643 : Nat := 4983230072969 + 3 ^ 40 * 4405643 * 2
def baseEnd_4405643 : Nat := 2262212451116211635201323

theorem tailTrace_4405643 : CollatzResearch.WordTrace tailWord_4405643 prefixEnd_4405643 2262212451116211635201323 := by
  unfold tailWord_4405643
  simp only [CollatzResearch.WordTrace]
  refine ⟨160687001178115309765981583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107124667452076873177321055 160687001178115309765981583)
  ·
    refine ⟨241030501767172964648972375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160687001178115309765981583 241030501767172964648972375)
    ·
      refine ⟨361545752650759446973458563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241030501767172964648972375 361545752650759446973458563)
      ·
        refine ⟨542318628976139170460187845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361545752650759446973458563 542318628976139170460187845)
        ·
          refine ⟨101684742933026094461285221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 542318628976139170460187845 101684742933026094461285221)
          ·
            refine ⟨19065889299942392711490979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101684742933026094461285221 19065889299942392711490979)
            ·
              refine ⟨28598833949913589067236469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19065889299942392711490979 28598833949913589067236469)
              ·
                refine ⟨2681140682804398975053419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28598833949913589067236469 2681140682804398975053419)
                ·
                  refine ⟨4021711024206598462580129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681140682804398975053419 4021711024206598462580129)
                  ·
                    refine ⟨3016283268154948846935097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021711024206598462580129 3016283268154948846935097)
                    ·
                      refine ⟨2262212451116211635201323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016283268154948846935097 2262212451116211635201323)
                      ·
                        rfl

theorem cell23_4405643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 2, 2].length) (baseStart_4405643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405643 prefixEnd_4405643 := by exact prefixLift 4405643
  have htrace : WordTrace (prefixWord ++ tailWord_4405643) baseStart_4405643 baseEnd_4405643 := by
    simpa [prefixWord, tailWord_4405643, baseEnd_4405643] using wordTrace_append hprefix tailTrace_4405643
  have hstable : (prefixWord ++ tailWord_4405643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405643).length < 2 ^ (prefixWord ++ tailWord_4405643).sum := by decide
  have hdescent : baseEnd_4405643 < baseStart_4405643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405699 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 3, 4, 2]
def baseStart_4405699 : Nat := 118140960795 + 4405699 * 2 ^ 59
def prefixEnd_4405699 : Nat := 4983230072969 + 3 ^ 40 * 4405699 * 2
def baseEnd_4405699 : Nat := 2262241206032863416101065

theorem tailTrace_4405699 : CollatzResearch.WordTrace tailWord_4405699 prefixEnd_4405699 2262241206032863416101065 := by
  unfold tailWord_4405699
  simp only [CollatzResearch.WordTrace]
  refine ⟨160689043665912431330020151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107126029110608287553346767 160689043665912431330020151)
  ·
    refine ⟨241033565498868646995030227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160689043665912431330020151 241033565498868646995030227)
    ·
      refine ⟨361550348248302970492545341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241033565498868646995030227 361550348248302970492545341)
      ·
        refine ⟨135581380593113613934704503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 361550348248302970492545341 135581380593113613934704503)
        ·
          refine ⟨203372070889670420902056755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135581380593113613934704503 203372070889670420902056755)
          ·
            refine ⟨305058106334505631353085133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203372070889670420902056755 305058106334505631353085133)
            ·
              refine ⟨114396789875439611757406925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305058106334505631353085133 114396789875439611757406925)
              ·
                refine ⟨42898796203289854409027597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114396789875439611757406925 42898796203289854409027597)
                ·
                  refine ⟨16087048576233695403385349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42898796203289854409027597 16087048576233695403385349)
                  ·
                    refine ⟨3016321608043817888134753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16087048576233695403385349 3016321608043817888134753)
                    ·
                      refine ⟨2262241206032863416101065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016321608043817888134753 2262241206032863416101065)
                      ·
                        rfl

theorem cell23_4405699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_4405699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405699 prefixEnd_4405699 := by exact prefixLift 4405699
  have htrace : WordTrace (prefixWord ++ tailWord_4405699) baseStart_4405699 baseEnd_4405699 := by
    simpa [prefixWord, tailWord_4405699, baseEnd_4405699] using wordTrace_append hprefix tailTrace_4405699
  have hstable : (prefixWord ++ tailWord_4405699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405699).length < 2 ^ (prefixWord ++ tailWord_4405699).sum := by decide
  have hdescent : baseEnd_4405699 < baseStart_4405699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405783 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4405783 : Nat := 118140960795 + 4405783 * 2 ^ 59
def prefixEnd_4405783 : Nat := 4983230072969 + 3 ^ 40 * 4405783 * 2
def baseEnd_4405783 : Nat := 2262284338407841087450679

theorem tailTrace_4405783 : CollatzResearch.WordTrace tailWord_4405783 prefixEnd_4405783 2262284338407841087450679 := by
  unfold tailWord_4405783
  simp only [CollatzResearch.WordTrace]
  refine ⟨160692107397608113676078003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107128071598405409117385335 160692107397608113676078003)
  ·
    refine ⟨241038161096412170514117005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160692107397608113676078003 241038161096412170514117005)
    ·
      refine ⟨90389310411154563942793877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241038161096412170514117005 90389310411154563942793877)
      ·
        refine ⟨4236998925522870184818463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90389310411154563942793877 4236998925522870184818463)
        ·
          refine ⟨6355498388284305277227695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236998925522870184818463 6355498388284305277227695)
          ·
            refine ⟨9533247582426457915841543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355498388284305277227695 9533247582426457915841543)
            ·
              refine ⟨14299871373639686873762315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9533247582426457915841543 14299871373639686873762315)
              ·
                refine ⟨21449807060459530310643473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14299871373639686873762315 21449807060459530310643473)
                ·
                  refine ⟨16087355295344647732982605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21449807060459530310643473 16087355295344647732982605)
                  ·
                    refine ⟨6032758235754242899868477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16087355295344647732982605 6032758235754242899868477)
                    ·
                      refine ⟨2262284338407841087450679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6032758235754242899868477 2262284338407841087450679)
                      ·
                        rfl

theorem cell23_4405783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4405783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405783 prefixEnd_4405783 := by exact prefixLift 4405783
  have htrace : WordTrace (prefixWord ++ tailWord_4405783) baseStart_4405783 baseEnd_4405783 := by
    simpa [prefixWord, tailWord_4405783, baseEnd_4405783] using wordTrace_append hprefix tailTrace_4405783
  have hstable : (prefixWord ++ tailWord_4405783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405783).length < 2 ^ (prefixWord ++ tailWord_4405783).sum := by decide
  have hdescent : baseEnd_4405783 < baseStart_4405783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405829 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 8]
def baseStart_4405829 : Nat := 118140960795 + 4405829 * 2 ^ 59
def prefixEnd_4405829 : Nat := 4983230072969 + 3 ^ 40 * 4405829 * 2
def baseEnd_4405829 : Nat := 251367550946438656386163

theorem tailTrace_4405829 : CollatzResearch.WordTrace tailWord_4405829 prefixEnd_4405829 251367550946438656386163 := by
  unfold tailWord_4405829
  simp only [CollatzResearch.WordTrace]
  refine ⟨160693785155441463532252541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107129190103627642354835027 160693785155441463532252541)
  ·
    refine ⟨60260169433290548824594703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160693785155441463532252541 60260169433290548824594703)
    ·
      refine ⟨90390254149935823236892055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60260169433290548824594703 90390254149935823236892055)
      ·
        refine ⟨135585381224903734855338083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90390254149935823236892055 135585381224903734855338083)
        ·
          refine ⟨203378071837355602283007125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135585381224903734855338083 203378071837355602283007125)
          ·
            refine ⟨9533347117376043857015959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203378071837355602283007125 9533347117376043857015959)
            ·
              refine ⟨14300020676064065785523939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9533347117376043857015959 14300020676064065785523939)
              ·
                refine ⟨21450031014096098678285909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14300020676064065785523939 21450031014096098678285909)
                ·
                  refine ⟨251367550946438656386163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21450031014096098678285909 251367550946438656386163)
                  ·
                    rfl

theorem cell23_4405829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_4405829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405829 prefixEnd_4405829 := by exact prefixLift 4405829
  have htrace : WordTrace (prefixWord ++ tailWord_4405829) baseStart_4405829 baseEnd_4405829 := by
    simpa [prefixWord, tailWord_4405829, baseEnd_4405829] using wordTrace_append hprefix tailTrace_4405829
  have hstable : (prefixWord ++ tailWord_4405829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405829).length < 2 ^ (prefixWord ++ tailWord_4405829).sum := by decide
  have hdescent : baseEnd_4405829 < baseStart_4405829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405899 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5]
def baseStart_4405899 : Nat := 118140960795 + 4405899 * 2 ^ 59
def prefixEnd_4405899 : Nat := 4983230072969 + 3 ^ 40 * 4405899 * 2
def baseEnd_4405899 : Nat := 2262343902163762633600145

theorem tailTrace_4405899 : CollatzResearch.WordTrace tailWord_4405899 prefixEnd_4405899 2262343902163762633600145 := by
  unfold tailWord_4405899
  simp only [CollatzResearch.WordTrace]
  refine ⟨160696338265187865487300751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107130892176791910324867167 160696338265187865487300751)
  ·
    refine ⟨241044507397781798230951127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160696338265187865487300751 241044507397781798230951127)
    ·
      refine ⟨361566761096672697346426691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241044507397781798230951127 361566761096672697346426691)
      ·
        refine ⟨542350141645009046019640037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361566761096672697346426691 542350141645009046019640037)
        ·
          refine ⟨101690651558439196128682507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 542350141645009046019640037 101690651558439196128682507)
          ·
            refine ⟨152535977337658794193023761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101690651558439196128682507 152535977337658794193023761)
            ·
              refine ⟨114401983003244095644767821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152535977337658794193023761 114401983003244095644767821)
              ·
                refine ⟨42900743626216535866787933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114401983003244095644767821 42900743626216535866787933)
                ·
                  refine ⟨16087778859831200950045475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42900743626216535866787933 16087778859831200950045475)
                  ·
                    refine ⟨24131668289746801425068213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16087778859831200950045475 24131668289746801425068213)
                    ·
                      refine ⟨2262343902163762633600145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24131668289746801425068213 2262343902163762633600145)
                      ·
                        rfl

theorem cell23_4405899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_4405899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405899 prefixEnd_4405899 := by exact prefixLift 4405899
  have htrace : WordTrace (prefixWord ++ tailWord_4405899) baseStart_4405899 baseEnd_4405899 := by
    simpa [prefixWord, tailWord_4405899, baseEnd_4405899] using wordTrace_append hprefix tailTrace_4405899
  have hstable : (prefixWord ++ tailWord_4405899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405899).length < 2 ^ (prefixWord ++ tailWord_4405899).sum := by decide
  have hdescent : baseEnd_4405899 < baseStart_4405899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405913 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 5, 2, 2]
def baseStart_4405913 : Nat := 118140960795 + 4405913 * 2 ^ 59
def prefixEnd_4405913 : Nat := 4983230072969 + 3 ^ 40 * 4405913 * 2
def baseEnd_4405913 : Nat := 2262351090892925578825081

theorem tailTrace_4405913 : CollatzResearch.WordTrace tailWord_4405913 prefixEnd_4405913 2262351090892925578825081 := by
  unfold tailWord_4405913
  simp only [CollatzResearch.WordTrace]
  refine ⟨160696848887137145878310393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107131232591424763918873595 160696848887137145878310393)
  ·
    refine ⟨120522636665352859408732795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160696848887137145878310393 120522636665352859408732795)
    ·
      refine ⟨180783954998029289113099193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120522636665352859408732795 180783954998029289113099193)
      ·
        refine ⟨135587966248521966834824395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180783954998029289113099193 135587966248521966834824395)
        ·
          refine ⟨203381949372782950252236593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135587966248521966834824395 203381949372782950252236593)
          ·
            refine ⟨152536462029587212689177445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203381949372782950252236593 152536462029587212689177445)
            ·
              refine ⟨28600586630547602379220771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152536462029587212689177445 28600586630547602379220771)
              ·
                refine ⟨42900879945821403568831157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28600586630547602379220771 42900879945821403568831157)
                ·
                  refine ⟨4021957494920756584577921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42900879945821403568831157 4021957494920756584577921)
                  ·
                    refine ⟨3016468121190567438433441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021957494920756584577921 3016468121190567438433441)
                    ·
                      refine ⟨2262351090892925578825081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016468121190567438433441 2262351090892925578825081)
                      ·
                        rfl

theorem cell23_4405913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_4405913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405913 prefixEnd_4405913 := by exact prefixLift 4405913
  have htrace : WordTrace (prefixWord ++ tailWord_4405913) baseStart_4405913 baseEnd_4405913 := by
    simpa [prefixWord, tailWord_4405913, baseEnd_4405913] using wordTrace_append hprefix tailTrace_4405913
  have hstable : (prefixWord ++ tailWord_4405913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405913).length < 2 ^ (prefixWord ++ tailWord_4405913).sum := by decide
  have hdescent : baseEnd_4405913 < baseStart_4405913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405927 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 1, 5]
def baseStart_4405927 : Nat := 118140960795 + 4405927 * 2 ^ 59
def prefixEnd_4405927 : Nat := 4983230072969 + 3 ^ 40 * 4405927 * 2
def baseEnd_4405927 : Nat := 754119426540696174683339

theorem tailTrace_4405927 : CollatzResearch.WordTrace tailWord_4405927 prefixEnd_4405927 754119426540696174683339 := by
  unfold tailWord_4405927
  simp only [CollatzResearch.WordTrace]
  refine ⟨160697359509086426269320035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107131573006057617512880023 160697359509086426269320035)
  ·
    refine ⟨241046039263629639403980053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160697359509086426269320035 241046039263629639403980053)
    ·
      refine ⟨11299033090482639347061565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 241046039263629639403980053 11299033090482639347061565)
      ·
        refine ⟨4237137408930989755148087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11299033090482639347061565 4237137408930989755148087)
        ·
          refine ⟨6355706113396484632722131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237137408930989755148087 6355706113396484632722131)
          ·
            refine ⟨9533559170094726949083197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355706113396484632722131 9533559170094726949083197)
            ·
              refine ⟨3575084688785522605906199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9533559170094726949083197 3575084688785522605906199)
              ·
                refine ⟨5362627033178283908859299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575084688785522605906199 5362627033178283908859299)
                ·
                  refine ⟨8043940549767425863288949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5362627033178283908859299 8043940549767425863288949)
                  ·
                    refine ⟨754119426540696174683339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8043940549767425863288949 754119426540696174683339)
                    ·
                      rfl

theorem cell23_4405927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_4405927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405927 prefixEnd_4405927 := by exact prefixLift 4405927
  have htrace : WordTrace (prefixWord ++ tailWord_4405927) baseStart_4405927 baseEnd_4405927 := by
    simpa [prefixWord, tailWord_4405927, baseEnd_4405927] using wordTrace_append hprefix tailTrace_4405927
  have hstable : (prefixWord ++ tailWord_4405927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405927).length < 2 ^ (prefixWord ++ tailWord_4405927).sum := by decide
  have hdescent : baseEnd_4405927 < baseStart_4405927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405933 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_4405933 : Nat := 118140960795 + 4405933 * 2 ^ 59
def prefixEnd_4405933 : Nat := 4983230072969 + 3 ^ 40 * 4405933 * 2
def baseEnd_4405933 : Nat := 2262361360506015500574989

theorem tailTrace_4405933 : CollatzResearch.WordTrace tailWord_4405933 prefixEnd_4405933 2262361360506015500574989 := by
  unfold tailWord_4405933
  simp only [CollatzResearch.WordTrace]
  refine ⟨160697578347064689294038453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107131718898043126196025635 160697578347064689294038453)
  ·
    refine ⟨15065397970037314621316105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160697578347064689294038453 15065397970037314621316105)
    ·
      refine ⟨11299048477527985965987079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15065397970037314621316105 11299048477527985965987079)
      ·
        refine ⟨16948572716291978948980619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11299048477527985965987079 16948572716291978948980619)
        ·
          refine ⟨25422859074437968423470929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16948572716291978948980619 25422859074437968423470929)
          ·
            refine ⟨19067144305828476317603197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25422859074437968423470929 19067144305828476317603197)
            ·
              refine ⟨7150179114685678619101199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19067144305828476317603197 7150179114685678619101199)
              ·
                refine ⟨10725268672028517928651799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150179114685678619101199 10725268672028517928651799)
                ·
                  refine ⟨16087903008042776892977699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10725268672028517928651799 16087903008042776892977699)
                  ·
                    refine ⟨24131854512064165339466549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16087903008042776892977699 24131854512064165339466549)
                    ·
                      refine ⟨2262361360506015500574989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24131854512064165339466549 2262361360506015500574989)
                      ·
                        rfl

theorem cell23_4405933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_4405933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405933 prefixEnd_4405933 := by exact prefixLift 4405933
  have htrace : WordTrace (prefixWord ++ tailWord_4405933) baseStart_4405933 baseEnd_4405933 := by
    simpa [prefixWord, tailWord_4405933, baseEnd_4405933] using wordTrace_append hprefix tailTrace_4405933
  have hstable : (prefixWord ++ tailWord_4405933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405933).length < 2 ^ (prefixWord ++ tailWord_4405933).sum := by decide
  have hdescent : baseEnd_4405933 < baseStart_4405933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405946 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_4405946 : Nat := 118140960795 + 4405946 * 2 ^ 59
def prefixEnd_4405946 : Nat := 4983230072969 + 3 ^ 40 * 4405946 * 2
def baseEnd_4405946 : Nat := 2262368035754523949712429

theorem tailTrace_4405946 : CollatzResearch.WordTrace tailWord_4405946 prefixEnd_4405946 2262368035754523949712429 := by
  unfold tailWord_4405946
  simp only [CollatzResearch.WordTrace]
  refine ⟨40174513124004398128565423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107132034997345061676174461 40174513124004398128565423)
  ·
    refine ⟨60261769686006597192848135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40174513124004398128565423 60261769686006597192848135)
    ·
      refine ⟨90392654529009895789272203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60261769686006597192848135 90392654529009895789272203)
      ·
        refine ⟨135588981793514843683908305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90392654529009895789272203 135588981793514843683908305)
        ·
          refine ⟨101691736345136132762931229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135588981793514843683908305 101691736345136132762931229)
          ·
            refine ⟨38134401129426049786099211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101691736345136132762931229 38134401129426049786099211)
            ·
              refine ⟨57201601694139074679148817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38134401129426049786099211 57201601694139074679148817)
              ·
                refine ⟨42901201270604306009361613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57201601694139074679148817 42901201270604306009361613)
                ·
                  refine ⟨16087950476476614753510605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42901201270604306009361613 16087950476476614753510605)
                  ·
                    refine ⟨6032981428678730532566477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16087950476476614753510605 6032981428678730532566477)
                    ·
                      refine ⟨2262368035754523949712429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6032981428678730532566477 2262368035754523949712429)
                      ·
                        rfl

theorem cell23_4405946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_4405946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405946 prefixEnd_4405946 := by exact prefixLift 4405946
  have htrace : WordTrace (prefixWord ++ tailWord_4405946) baseStart_4405946 baseEnd_4405946 := by
    simpa [prefixWord, tailWord_4405946, baseEnd_4405946] using wordTrace_append hprefix tailTrace_4405946
  have hstable : (prefixWord ++ tailWord_4405946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405946).length < 2 ^ (prefixWord ++ tailWord_4405946).sum := by decide
  have hdescent : baseEnd_4405946 < baseStart_4405946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4405980 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4405980 : Nat := 118140960795 + 4405980 * 2 ^ 59
def prefixEnd_4405980 : Nat := 4983230072969 + 3 ^ 40 * 4405980 * 2
def baseEnd_4405980 : Nat := 2262385494096776816687273

theorem tailTrace_4405980 : CollatzResearch.WordTrace tailWord_4405980 prefixEnd_4405980 2262385494096776816687273 := by
  unfold tailWord_4405980
  simp only [CollatzResearch.WordTrace]
  refine ⟨80349646288947208160499697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107132861718596277547332929 80349646288947208160499697)
  ·
    refine ⟨60262234716710406120374773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80349646288947208160499697 60262234716710406120374773)
    ·
      refine ⟨5649584504691600573785135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60262234716710406120374773 5649584504691600573785135)
      ·
        refine ⟨8474376757037400860677703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5649584504691600573785135 8474376757037400860677703)
        ·
          refine ⟨12711565135556101291016555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8474376757037400860677703 12711565135556101291016555)
          ·
            refine ⟨19067347703334151936524833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12711565135556101291016555 19067347703334151936524833)
            ·
              refine ⟨14300510777500613952393625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19067347703334151936524833 14300510777500613952393625)
              ·
                refine ⟨10725383083125460464295219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14300510777500613952393625 10725383083125460464295219)
                ·
                  refine ⟨16088074624688190696442829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10725383083125460464295219 16088074624688190696442829)
                  ·
                    refine ⟨6033027984258071511166061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16088074624688190696442829 6033027984258071511166061)
                    ·
                      refine ⟨2262385494096776816687273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6033027984258071511166061 2262385494096776816687273)
                      ·
                        rfl

theorem cell23_4405980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4405980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4405980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4405980 prefixEnd_4405980 := by exact prefixLift 4405980
  have htrace : WordTrace (prefixWord ++ tailWord_4405980) baseStart_4405980 baseEnd_4405980 := by
    simpa [prefixWord, tailWord_4405980, baseEnd_4405980] using wordTrace_append hprefix tailTrace_4405980
  have hstable : (prefixWord ++ tailWord_4405980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4405980).length < 2 ^ (prefixWord ++ tailWord_4405980).sum := by decide
  have hdescent : baseEnd_4405980 < baseStart_4405980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4405980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406014 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_4406014 : Nat := 118140960795 + 4406014 * 2 ^ 59
def prefixEnd_4406014 : Nat := 4983230072969 + 3 ^ 40 * 4406014 * 2
def baseEnd_4406014 : Nat := 2262402952439029683662117

theorem tailTrace_4406014 : CollatzResearch.WordTrace tailWord_4406014 prefixEnd_4406014 2262402952439029683662117 := by
  unfold tailWord_4406014
  simp only [CollatzResearch.WordTrace]
  refine ⟨20087566582471405015967137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107133688439847493418491397 20087566582471405015967137)
  ·
    refine ⟨15065674936853553761975353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20087566582471405015967137 15065674936853553761975353)
    ·
      refine ⟨11299256202640165321481515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15065674936853553761975353 11299256202640165321481515)
      ·
        refine ⟨16948884303960247982222273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11299256202640165321481515 16948884303960247982222273)
        ·
          refine ⟨12711663227970185986666705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16948884303960247982222273 12711663227970185986666705)
          ·
            refine ⟨9533747420977639490000029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12711663227970185986666705 9533747420977639490000029)
            ·
              refine ⟨3575155282866614808750011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9533747420977639490000029 3575155282866614808750011)
              ·
                refine ⟨5362732924299922213125017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575155282866614808750011 5362732924299922213125017)
                ·
                  refine ⟨4022049693224941659843763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5362732924299922213125017 4022049693224941659843763)
                  ·
                    refine ⟨6033074539837412489765645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4022049693224941659843763 6033074539837412489765645)
                    ·
                      refine ⟨2262402952439029683662117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6033074539837412489765645 2262402952439029683662117)
                      ·
                        rfl

theorem cell23_4406014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_4406014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406014 prefixEnd_4406014 := by exact prefixLift 4406014
  have htrace : WordTrace (prefixWord ++ tailWord_4406014) baseStart_4406014 baseEnd_4406014 := by
    simpa [prefixWord, tailWord_4406014, baseEnd_4406014] using wordTrace_append hprefix tailTrace_4406014
  have hstable : (prefixWord ++ tailWord_4406014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406014).length < 2 ^ (prefixWord ++ tailWord_4406014).sum := by decide
  have hdescent : baseEnd_4406014 < baseStart_4406014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406026 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_4406026 : Nat := 118140960795 + 4406026 * 2 ^ 59
def prefixEnd_4406026 : Nat := 4983230072969 + 3 ^ 40 * 4406026 * 2
def baseEnd_4406026 : Nat := 251378790467431515190229

theorem tailTrace_4406026 : CollatzResearch.WordTrace tailWord_4406026 prefixEnd_4406026 251378790467431515190229 := by
  unfold tailWord_4406026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40175242583931941544293483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107133980223818510784782621 40175242583931941544293483)
  ·
    refine ⟨60262863875897912316440225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40175242583931941544293483 60262863875897912316440225)
    ·
      refine ⟨45197147906923434237330169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60262863875897912316440225 45197147906923434237330169)
      ·
        refine ⟨33897860930192575677997627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45197147906923434237330169 33897860930192575677997627)
        ·
          refine ⟨50846791395288863516996441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33897860930192575677997627 50846791395288863516996441)
          ·
            refine ⟨38135093546466647637747331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50846791395288863516996441 38135093546466647637747331)
            ·
              refine ⟨57202640319699971456620997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38135093546466647637747331 57202640319699971456620997)
              ·
                refine ⟨10725495059943744648116437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57202640319699971456620997 10725495059943744648116437)
                ·
                  refine ⟨251378790467431515190229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10725495059943744648116437 251378790467431515190229)
                  ·
                    rfl

theorem cell23_4406026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_4406026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406026 prefixEnd_4406026 := by exact prefixLift 4406026
  have htrace : WordTrace (prefixWord ++ tailWord_4406026) baseStart_4406026 baseEnd_4406026 := by
    simpa [prefixWord, tailWord_4406026, baseEnd_4406026] using wordTrace_append hprefix tailTrace_4406026
  have hstable : (prefixWord ++ tailWord_4406026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406026).length < 2 ^ (prefixWord ++ tailWord_4406026).sum := by decide
  have hdescent : baseEnd_4406026 < baseStart_4406026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406060 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 5]
def baseStart_4406060 : Nat := 118140960795 + 4406060 * 2 ^ 59
def prefixEnd_4406060 : Nat := 4983230072969 + 3 ^ 40 * 4406060 * 2
def baseEnd_4406060 : Nat := 251380730283237389298545

theorem tailTrace_4406060 : CollatzResearch.WordTrace tailWord_4406060 prefixEnd_4406060 251380730283237389298545 := by
  unfold tailWord_4406060
  simp only [CollatzResearch.WordTrace]
  refine ⟨80351105208802294991955817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107134806945069726655941089 80351105208802294991955817)
  ·
    refine ⟨60263328906601721243966863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80351105208802294991955817 60263328906601721243966863)
    ·
      refine ⟨90394993359902581865950295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60263328906601721243966863 90394993359902581865950295)
      ·
        refine ⟨135592490039853872798925443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90394993359902581865950295 135592490039853872798925443)
        ·
          refine ⟨203388735059780809198388165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135592490039853872798925443 203388735059780809198388165)
          ·
            refine ⟨38135387823708901724697781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203388735059780809198388165 38135387823708901724697781)
            ·
              refine ⟨3575192608472709536690417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38135387823708901724697781 3575192608472709536690417)
              ·
                refine ⟨2681394456354532152517813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575192608472709536690417 2681394456354532152517813)
                ·
                  refine ⟨251380730283237389298545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2681394456354532152517813 251380730283237389298545)
                  ·
                    rfl

theorem cell23_4406060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_4406060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406060 prefixEnd_4406060 := by exact prefixLift 4406060
  have htrace : WordTrace (prefixWord ++ tailWord_4406060) baseStart_4406060 baseEnd_4406060 := by
    simpa [prefixWord, tailWord_4406060, baseEnd_4406060] using wordTrace_append hprefix tailTrace_4406060
  have hstable : (prefixWord ++ tailWord_4406060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406060).length < 2 ^ (prefixWord ++ tailWord_4406060).sum := by decide
  have hdescent : baseEnd_4406060 < baseStart_4406060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406113 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_4406113 : Nat := 118140960795 + 4406113 * 2 ^ 59
def prefixEnd_4406113 : Nat := 4983230072969 + 3 ^ 40 * 4406113 * 2
def baseEnd_4406113 : Nat := 2262453787023824796324161

theorem tailTrace_4406113 : CollatzResearch.WordTrace tailWord_4406113 prefixEnd_4406113 2262453787023824796324161 := by
  unfold tailWord_4406113
  simp only [CollatzResearch.WordTrace]
  refine ⟨160704143486412580035590993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107136095657608386690393995 160704143486412580035590993)
  ·
    refine ⟨120528107614809435026693245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160704143486412580035590993 120528107614809435026693245)
    ·
      refine ⟨45198040355553538135009967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120528107614809435026693245 45198040355553538135009967)
      ·
        refine ⟨67797060533330307202514951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45198040355553538135009967 67797060533330307202514951)
        ·
          refine ⟨101695590799995460803772427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67797060533330307202514951 101695590799995460803772427)
          ·
            refine ⟨152543386199993191205658641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101695590799995460803772427 152543386199993191205658641)
            ·
              refine ⟨114407539649994893404243981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152543386199993191205658641 114407539649994893404243981)
              ·
                refine ⟨42902827368748085026591493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114407539649994893404243981 42902827368748085026591493)
                ·
                  refine ⟨8044280131640265942485905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42902827368748085026591493 8044280131640265942485905)
                  ·
                    refine ⟨6033210098730199456864429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8044280131640265942485905 6033210098730199456864429)
                    ·
                      refine ⟨2262453787023824796324161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6033210098730199456864429 2262453787023824796324161)
                      ·
                        rfl

theorem cell23_4406113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_4406113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406113 prefixEnd_4406113 := by exact prefixLift 4406113
  have htrace : WordTrace (prefixWord ++ tailWord_4406113) baseStart_4406113 baseEnd_4406113 := by
    simpa [prefixWord, tailWord_4406113, baseEnd_4406113] using wordTrace_append hprefix tailTrace_4406113
  have hstable : (prefixWord ++ tailWord_4406113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406113).length < 2 ^ (prefixWord ++ tailWord_4406113).sum := by decide
  have hdescent : baseEnd_4406113 < baseStart_4406113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_4406136 : Nat := 118140960795 + 4406136 * 2 ^ 59
def prefixEnd_4406136 : Nat := 4983230072969 + 3 ^ 40 * 4406136 * 2
def baseEnd_4406136 : Nat := 2262465597078878206336555

theorem tailTrace_4406136 : CollatzResearch.WordTrace tailWord_4406136 prefixEnd_4406136 2262465597078878206336555 := by
  unfold tailWord_4406136
  simp only [CollatzResearch.WordTrace]
  refine ⟨80352491182664627481839131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107136654910219503309118841 80352491182664627481839131)
  ·
    refine ⟨120528736773996941222758697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80352491182664627481839131 120528736773996941222758697)
    ·
      refine ⟨90396552580497705917069023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120528736773996941222758697 90396552580497705917069023)
      ·
        refine ⟨135594828870746558875603535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90396552580497705917069023 135594828870746558875603535)
        ·
          refine ⟨203392243306119838313405303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135594828870746558875603535 203392243306119838313405303)
          ·
            refine ⟨305088364959179757470107955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203392243306119838313405303 305088364959179757470107955)
            ·
              refine ⟨457632547438769636205161933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305088364959179757470107955 457632547438769636205161933)
              ·
                refine ⟨171612205289538613576935725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457632547438769636205161933 171612205289538613576935725)
                ·
                  refine ⟨64354576983576980091350897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171612205289538613576935725 64354576983576980091350897)
                  ·
                    refine ⟨48265932737682735068513173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64354576983576980091350897 48265932737682735068513173)
                    ·
                      refine ⟨2262465597078878206336555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48265932737682735068513173 2262465597078878206336555)
                      ·
                        rfl

theorem cell23_4406136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_4406136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406136 prefixEnd_4406136 := by exact prefixLift 4406136
  have htrace : WordTrace (prefixWord ++ tailWord_4406136) baseStart_4406136 baseEnd_4406136 := by
    simpa [prefixWord, tailWord_4406136, baseEnd_4406136] using wordTrace_append hprefix tailTrace_4406136
  have hstable : (prefixWord ++ tailWord_4406136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406136).length < 2 ^ (prefixWord ++ tailWord_4406136).sum := by decide
  have hdescent : baseEnd_4406136 < baseStart_4406136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406154 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_4406154 : Nat := 118140960795 + 4406154 * 2 ^ 59
def prefixEnd_4406154 : Nat := 4983230072969 + 3 ^ 40 * 4406154 * 2
def baseEnd_4406154 : Nat := 754158279910219711970491

theorem tailTrace_4406154 : CollatzResearch.WordTrace tailWord_4406154 prefixEnd_4406154 754158279910219711970491 := by
  unfold tailWord_4406154
  simp only [CollatzResearch.WordTrace]
  refine ⟨40176409719816011009458379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107137092586176029358555677 40176409719816011009458379)
  ·
    refine ⟨60264614579724016514187569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40176409719816011009458379 60264614579724016514187569)
    ·
      refine ⟨45198460934793012385640677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60264614579724016514187569 45198460934793012385640677)
      ·
        refine ⟨8474711425273689822307627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45198460934793012385640677 8474711425273689822307627)
        ·
          refine ⟨12712067137910534733461441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8474711425273689822307627 12712067137910534733461441)
          ·
            refine ⟨9534050353432901050096081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12712067137910534733461441 9534050353432901050096081)
            ·
              refine ⟨7150537765074675787572061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9534050353432901050096081 7150537765074675787572061)
              ·
                refine ⟨2681451661903003420339523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7150537765074675787572061 2681451661903003420339523)
                ·
                  refine ⟨4022177492854505130509285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681451661903003420339523 4022177492854505130509285)
                  ·
                    refine ⟨754158279910219711970491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022177492854505130509285 754158279910219711970491)
                    ·
                      rfl

theorem cell23_4406154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_4406154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406154 prefixEnd_4406154 := by exact prefixLift 4406154
  have htrace : WordTrace (prefixWord ++ tailWord_4406154) baseStart_4406154 baseEnd_4406154 := by
    simpa [prefixWord, tailWord_4406154, baseEnd_4406154] using wordTrace_append hprefix tailTrace_4406154
  have hstable : (prefixWord ++ tailWord_4406154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406154).length < 2 ^ (prefixWord ++ tailWord_4406154).sum := by decide
  have hdescent : baseEnd_4406154 < baseStart_4406154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406177 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4406177 : Nat := 118140960795 + 4406177 * 2 ^ 59
def prefixEnd_4406177 : Nat := 4983230072969 + 3 ^ 40 * 4406177 * 2
def baseEnd_4406177 : Nat := 2262486649785712545923867

theorem tailTrace_4406177 : CollatzResearch.WordTrace tailWord_4406177 prefixEnd_4406177 2262486649785712545923867 := by
  unfold tailWord_4406177
  simp only [CollatzResearch.WordTrace]
  refine ⟨160706477758180718965920785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107137651838787145977280523 160706477758180718965920785)
  ·
    refine ⟨120529858318635539224440589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160706477758180718965920785 120529858318635539224440589)
    ·
      refine ⟨45198696869488327209165221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120529858318635539224440589 45198696869488327209165221)
      ·
        refine ⟨8474755663029061351718479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45198696869488327209165221 8474755663029061351718479)
        ·
          refine ⟨12712133494543592027577719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8474755663029061351718479 12712133494543592027577719)
          ·
            refine ⟨19068200241815388041366579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12712133494543592027577719 19068200241815388041366579)
            ·
              refine ⟨28602300362723082062049869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19068200241815388041366579 28602300362723082062049869)
              ·
                refine ⟨10725862636021155773268701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28602300362723082062049869 10725862636021155773268701)
                ·
                  refine ⟨4022198488507933414975763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10725862636021155773268701 4022198488507933414975763)
                  ·
                    refine ⟨6033297732761900122463645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4022198488507933414975763 6033297732761900122463645)
                    ·
                      refine ⟨2262486649785712545923867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6033297732761900122463645 2262486649785712545923867)
                      ·
                        rfl

theorem cell23_4406177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4406177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406177 prefixEnd_4406177 := by exact prefixLift 4406177
  have htrace : WordTrace (prefixWord ++ tailWord_4406177) baseStart_4406177 baseEnd_4406177 := by
    simpa [prefixWord, tailWord_4406177, baseEnd_4406177] using wordTrace_append hprefix tailTrace_4406177
  have hstable : (prefixWord ++ tailWord_4406177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406177).length < 2 ^ (prefixWord ++ tailWord_4406177).sum := by decide
  have hdescent : baseEnd_4406177 < baseStart_4406177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406200 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_4406200 : Nat := 118140960795 + 4406200 * 2 ^ 59
def prefixEnd_4406200 : Nat := 4983230072969 + 3 ^ 40 * 4406200 * 2
def baseEnd_4406200 : Nat := 2262498459840765955936261

theorem tailTrace_4406200 : CollatzResearch.WordTrace tailWord_4406200 prefixEnd_4406200 2262498459840765955936261 := by
  unfold tailWord_4406200
  simp only [CollatzResearch.WordTrace]
  refine ⟨80353658318548696947004027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107138211091398262596005369 80353658318548696947004027)
  ·
    refine ⟨120530487477823045420506041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80353658318548696947004027 120530487477823045420506041)
    ·
      refine ⟨90397865608367284065379531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120530487477823045420506041 90397865608367284065379531)
      ·
        refine ⟨135596798412550926098069297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90397865608367284065379531 135596798412550926098069297)
        ·
          refine ⟨101697598809413194573551973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135596798412550926098069297 101697598809413194573551973)
          ·
            refine ⟨19068299776764973982540995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101697598809413194573551973 19068299776764973982540995)
            ·
              refine ⟨28602449665147460973811493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19068299776764973982540995 28602449665147460973811493)
              ·
                refine ⟨5362959312215148932589655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28602449665147460973811493 5362959312215148932589655)
                ·
                  refine ⟨8044438968322723398884483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5362959312215148932589655 8044438968322723398884483)
                  ·
                    refine ⟨12066658452484085098326725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8044438968322723398884483 12066658452484085098326725)
                    ·
                      refine ⟨2262498459840765955936261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12066658452484085098326725 2262498459840765955936261)
                      ·
                        rfl

theorem cell23_4406200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_4406200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406200 prefixEnd_4406200 := by exact prefixLift 4406200
  have htrace : WordTrace (prefixWord ++ tailWord_4406200) baseStart_4406200 baseEnd_4406200 := by
    simpa [prefixWord, tailWord_4406200, baseEnd_4406200] using wordTrace_append hprefix tailTrace_4406200
  have hstable : (prefixWord ++ tailWord_4406200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406200).length < 2 ^ (prefixWord ++ tailWord_4406200).sum := by decide
  have hdescent : baseEnd_4406200 < baseStart_4406200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406220 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4406220 : Nat := 118140960795 + 4406220 * 2 ^ 59
def prefixEnd_4406220 : Nat := 4983230072969 + 3 ^ 40 * 4406220 * 2
def baseEnd_4406220 : Nat := 2262508729453855877686169

theorem tailTrace_4406220 : CollatzResearch.WordTrace tailWord_4406220 prefixEnd_4406220 2262508729453855877686169 := by
  unfold tailWord_4406220
  simp only [CollatzResearch.WordTrace]
  refine ⟨80354023048512468654868057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107138697398016624873157409 80354023048512468654868057)
  ·
    refine ⟨60265517286384351491151043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80354023048512468654868057 60265517286384351491151043)
    ·
      refine ⟨90398275929576527236726565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60265517286384351491151043 90398275929576527236726565)
      ·
        refine ⟨16949676736795598856886231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90398275929576527236726565 16949676736795598856886231)
        ·
          refine ⟨25424515105193398285329347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16949676736795598856886231 25424515105193398285329347)
          ·
            refine ⟨38136772657790097427994021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25424515105193398285329347 38136772657790097427994021)
            ·
              refine ⟨7150644873335643267748879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38136772657790097427994021 7150644873335643267748879)
              ·
                refine ⟨10725967310003464901623319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150644873335643267748879 10725967310003464901623319)
                ·
                  refine ⟨16088950965005197352434979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10725967310003464901623319 16088950965005197352434979)
                  ·
                    refine ⟨24133426447507796028652469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16088950965005197352434979 24133426447507796028652469)
                    ·
                      refine ⟨2262508729453855877686169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24133426447507796028652469 2262508729453855877686169)
                      ·
                        rfl

theorem cell23_4406220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4406220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406220 prefixEnd_4406220 := by exact prefixLift 4406220
  have htrace : WordTrace (prefixWord ++ tailWord_4406220) baseStart_4406220 baseEnd_4406220 := by
    simpa [prefixWord, tailWord_4406220, baseEnd_4406220] using wordTrace_append hprefix tailTrace_4406220
  have hstable : (prefixWord ++ tailWord_4406220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406220).length < 2 ^ (prefixWord ++ tailWord_4406220).sum := by decide
  have hdescent : baseEnd_4406220 < baseStart_4406220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406223 : List Nat := [1, 1, 2, 1, 1, 8, 9]
def baseStart_4406223 : Nat := 118140960795 + 4406223 * 2 ^ 59
def prefixEnd_4406223 : Nat := 4983230072969 + 3 ^ 40 * 4406223 * 2
def baseEnd_4406223 : Nat := 27932225554269374888255

theorem tailTrace_4406223 : CollatzResearch.WordTrace tailWord_4406223 prefixEnd_4406223 27932225554269374888255 := by
  unfold tailWord_4406223
  simp only [CollatzResearch.WordTrace]
  refine ⟨160708155516014068822095323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107138770344009379214730215 160708155516014068822095323)
  ·
    refine ⟨241062233274021103233142985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160708155516014068822095323 241062233274021103233142985)
    ·
      refine ⟨180796674955515827424857239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241062233274021103233142985 180796674955515827424857239)
      ·
        refine ⟨271195012433273741137285859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180796674955515827424857239 271195012433273741137285859)
        ·
          refine ⟨406792518649910611705928789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271195012433273741137285859 406792518649910611705928789)
          ·
            refine ⟨4767099827928639980928853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 406792518649910611705928789 4767099827928639980928853)
            ·
              refine ⟨27932225554269374888255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4767099827928639980928853 27932225554269374888255)
              ·
                rfl

theorem cell23_4406223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 9].length) (baseStart_4406223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406223 prefixEnd_4406223 := by exact prefixLift 4406223
  have htrace : WordTrace (prefixWord ++ tailWord_4406223) baseStart_4406223 baseEnd_4406223 := by
    simpa [prefixWord, tailWord_4406223, baseEnd_4406223] using wordTrace_append hprefix tailTrace_4406223
  have hstable : (prefixWord ++ tailWord_4406223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406223).length < 2 ^ (prefixWord ++ tailWord_4406223).sum := by decide
  have hdescent : baseEnd_4406223 < baseStart_4406223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406234 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2]
def baseStart_4406234 : Nat := 118140960795 + 4406234 * 2 ^ 59
def prefixEnd_4406234 : Nat := 4983230072969 + 3 ^ 40 * 4406234 * 2
def baseEnd_4406234 : Nat := 2262515918183018822911105

theorem tailTrace_4406234 : CollatzResearch.WordTrace tailWord_4406234 prefixEnd_4406234 2262515918183018822911105 := by
  unfold tailWord_4406234
  simp only [CollatzResearch.WordTrace]
  refine ⟨40177139179743554425186439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107139037812649478467163837 40177139179743554425186439)
  ·
    refine ⟨60265708769615331637779659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40177139179743554425186439 60265708769615331637779659)
    ·
      refine ⟨90398563154422997456669489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60265708769615331637779659 90398563154422997456669489)
      ·
        refine ⟨67798922365817248092502117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90398563154422997456669489 67798922365817248092502117)
        ·
          refine ⟨12712297943590734017344147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67798922365817248092502117 12712297943590734017344147)
          ·
            refine ⟨19068446915386101026016221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12712297943590734017344147 19068446915386101026016221)
            ·
              refine ⟨7150667593269787884756083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19068446915386101026016221 7150667593269787884756083)
              ·
                refine ⟨10726001389904681827134125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150667593269787884756083 10726001389904681827134125)
                ·
                  refine ⟨4022250521214255685175297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10726001389904681827134125 4022250521214255685175297)
                  ·
                    refine ⟨3016687890910691763881473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022250521214255685175297 3016687890910691763881473)
                    ·
                      refine ⟨2262515918183018822911105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016687890910691763881473 2262515918183018822911105)
                      ·
                        rfl

theorem cell23_4406234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_4406234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406234 prefixEnd_4406234 := by exact prefixLift 4406234
  have htrace : WordTrace (prefixWord ++ tailWord_4406234) baseStart_4406234 baseEnd_4406234 := by
    simpa [prefixWord, tailWord_4406234, baseEnd_4406234] using wordTrace_append hprefix tailTrace_4406234
  have hstable : (prefixWord ++ tailWord_4406234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406234).length < 2 ^ (prefixWord ++ tailWord_4406234).sum := by decide
  have hdescent : baseEnd_4406234 < baseStart_4406234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406243 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4406243 : Nat := 118140960795 + 4406243 * 2 ^ 59
def prefixEnd_4406243 : Nat := 4983230072969 + 3 ^ 40 * 4406243 * 2
def baseEnd_4406243 : Nat := 2262520539508909287698563

theorem tailTrace_4406243 : CollatzResearch.WordTrace tailWord_4406243 prefixEnd_4406243 2262520539508909287698563 := by
  unfold tailWord_4406243
  simp only [CollatzResearch.WordTrace]
  refine ⟨160708884975941612237823383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107139256650627741491882255 160708884975941612237823383)
  ·
    refine ⟨241063327463912418356735075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160708884975941612237823383 241063327463912418356735075)
    ·
      refine ⟨361594991195868627535102613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241063327463912418356735075 361594991195868627535102613)
      ·
        refine ⟨16949765212306341915707935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 361594991195868627535102613 16949765212306341915707935)
        ·
          refine ⟨25424647818459512873561903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16949765212306341915707935 25424647818459512873561903)
          ·
            refine ⟨38136971727689269310342855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25424647818459512873561903 38136971727689269310342855)
            ·
              refine ⟨57205457591533903965514283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38136971727689269310342855 57205457591533903965514283)
              ·
                refine ⟨85808186387300855948271425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57205457591533903965514283 85808186387300855948271425)
                ·
                  refine ⟨64356139790475641961203569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85808186387300855948271425 64356139790475641961203569)
                  ·
                    refine ⟨48267104842856731470902677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64356139790475641961203569 48267104842856731470902677)
                    ·
                      refine ⟨2262520539508909287698563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48267104842856731470902677 2262520539508909287698563)
                      ·
                        rfl

theorem cell23_4406243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4406243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406243 prefixEnd_4406243 := by exact prefixLift 4406243
  have htrace : WordTrace (prefixWord ++ tailWord_4406243) baseStart_4406243 baseEnd_4406243 := by
    simpa [prefixWord, tailWord_4406243, baseEnd_4406243] using wordTrace_append hprefix tailTrace_4406243
  have hstable : (prefixWord ++ tailWord_4406243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406243).length < 2 ^ (prefixWord ++ tailWord_4406243).sum := by decide
  have hdescent : baseEnd_4406243 < baseStart_4406243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406284 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_4406284 : Nat := 118140960795 + 4406284 * 2 ^ 59
def prefixEnd_4406284 : Nat := 4983230072969 + 3 ^ 40 * 4406284 * 2
def baseEnd_4406284 : Nat := 2262541592215743627285875

theorem tailTrace_4406284 : CollatzResearch.WordTrace tailWord_4406284 prefixEnd_4406284 2262541592215743627285875 := by
  unfold tailWord_4406284
  simp only [CollatzResearch.WordTrace]
  refine ⟨80355190184396538120032953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107140253579195384160043937 80355190184396538120032953)
  ·
    refine ⟨60266392638297403590024715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80355190184396538120032953 60266392638297403590024715)
    ·
      refine ⟨90399588957446105385037073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60266392638297403590024715 90399588957446105385037073)
      ·
        refine ⟨67799691718084579038777805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90399588957446105385037073 67799691718084579038777805)
        ·
          refine ⟨25424884394281717139541677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67799691718084579038777805 25424884394281717139541677)
          ·
            refine ⟨9534331647855643927328129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25424884394281717139541677 9534331647855643927328129)
            ·
              refine ⟨7150748735891732945496097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9534331647855643927328129 7150748735891732945496097)
              ·
                refine ⟨5363061551918799709122073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7150748735891732945496097 5363061551918799709122073)
                ·
                  refine ⟨4022296163939099781841555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363061551918799709122073 4022296163939099781841555)
                  ·
                    refine ⟨6033444245908649672762333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4022296163939099781841555 6033444245908649672762333)
                    ·
                      refine ⟨2262541592215743627285875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6033444245908649672762333 2262541592215743627285875)
                      ·
                        rfl

theorem cell23_4406284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_4406284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406284 prefixEnd_4406284 := by exact prefixLift 4406284
  have htrace : WordTrace (prefixWord ++ tailWord_4406284) baseStart_4406284 baseEnd_4406284 := by
    simpa [prefixWord, tailWord_4406284, baseEnd_4406284] using wordTrace_append hprefix tailTrace_4406284
  have hstable : (prefixWord ++ tailWord_4406284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406284).length < 2 ^ (prefixWord ++ tailWord_4406284).sum := by decide
  have hdescent : baseEnd_4406284 < baseStart_4406284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406307 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 1, 4, 2]
def baseStart_4406307 : Nat := 118140960795 + 4406307 * 2 ^ 59
def prefixEnd_4406307 : Nat := 4983230072969 + 3 ^ 40 * 4406307 * 2
def baseEnd_4406307 : Nat := 2262553402270797037298269

theorem tailTrace_4406307 : CollatzResearch.WordTrace tailWord_4406307 prefixEnd_4406307 2262553402270797037298269 := by
  unfold tailWord_4406307
  simp only [CollatzResearch.WordTrace]
  refine ⟨160711219247709751168153175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107140812831806500778768783 160711219247709751168153175)
  ·
    refine ⟨241066828871564626752229763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160711219247709751168153175 241066828871564626752229763)
    ·
      refine ⟨361600243307346940128344645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241066828871564626752229763 361600243307346940128344645)
      ·
        refine ⟨67800045620127551274064621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 361600243307346940128344645 67800045620127551274064621)
        ·
          refine ⟨25425017107547831727774233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67800045620127551274064621 25425017107547831727774233)
          ·
            refine ⟨19068762830660873795830675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25425017107547831727774233 19068762830660873795830675)
            ·
              refine ⟨28603144245991310693746013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19068762830660873795830675 28603144245991310693746013)
              ·
                refine ⟨10726179092246741510154755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28603144245991310693746013 10726179092246741510154755)
                ·
                  refine ⟨16089268638370112265232133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10726179092246741510154755 16089268638370112265232133)
                  ·
                    refine ⟨3016737869694396049731025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16089268638370112265232133 3016737869694396049731025)
                    ·
                      refine ⟨2262553402270797037298269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016737869694396049731025 2262553402270797037298269)
                      ·
                        rfl

theorem cell23_4406307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_4406307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406307 prefixEnd_4406307 := by exact prefixLift 4406307
  have htrace : WordTrace (prefixWord ++ tailWord_4406307) baseStart_4406307 baseEnd_4406307 := by
    simpa [prefixWord, tailWord_4406307, baseEnd_4406307] using wordTrace_append hprefix tailTrace_4406307
  have hstable : (prefixWord ++ tailWord_4406307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406307).length < 2 ^ (prefixWord ++ tailWord_4406307).sum := by decide
  have hdescent : baseEnd_4406307 < baseStart_4406307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406323 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_4406323 : Nat := 118140960795 + 4406323 * 2 ^ 59
def prefixEnd_4406323 : Nat := 4983230072969 + 3 ^ 40 * 4406323 * 2
def baseEnd_4406323 : Nat := 2262561617961268974698195

theorem tailTrace_4406323 : CollatzResearch.WordTrace tailWord_4406323 prefixEnd_4406323 2262561617961268974698195 := by
  unfold tailWord_4406323
  simp only [CollatzResearch.WordTrace]
  refine ⟨160711802815651785900735623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107141201877101190600490415 160711802815651785900735623)
  ·
    refine ⟨241067704223477678851103435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160711802815651785900735623 241067704223477678851103435)
    ·
      refine ⟨361601556335216518276655153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241067704223477678851103435 361601556335216518276655153)
      ·
        refine ⟨271201167251412388707491365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361601556335216518276655153 271201167251412388707491365)
        ·
          refine ⟨50850218859639822882654631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271201167251412388707491365 50850218859639822882654631)
          ·
            refine ⟨76275328289459734323981947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50850218859639822882654631 76275328289459734323981947)
            ·
              refine ⟨114412992434189601485972921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76275328289459734323981947 114412992434189601485972921)
              ·
                refine ⟨85809744325642201114479691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114412992434189601485972921 85809744325642201114479691)
                ·
                  refine ⟨128714616488463301671719537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85809744325642201114479691 128714616488463301671719537)
                  ·
                    refine ⟨96535962366347476253789653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128714616488463301671719537 96535962366347476253789653)
                    ·
                      refine ⟨2262561617961268974698195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96535962366347476253789653 2262561617961268974698195)
                      ·
                        rfl

theorem cell23_4406323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_4406323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406323 prefixEnd_4406323 := by exact prefixLift 4406323
  have htrace : WordTrace (prefixWord ++ tailWord_4406323) baseStart_4406323 baseEnd_4406323 := by
    simpa [prefixWord, tailWord_4406323, baseEnd_4406323] using wordTrace_append hprefix tailTrace_4406323
  have hstable : (prefixWord ++ tailWord_4406323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406323).length < 2 ^ (prefixWord ++ tailWord_4406323).sum := by decide
  have hdescent : baseEnd_4406323 < baseStart_4406323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406380 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_4406380 : Nat := 118140960795 + 4406380 * 2 ^ 59
def prefixEnd_4406380 : Nat := 4983230072969 + 3 ^ 40 * 4406380 * 2
def baseEnd_4406380 : Nat := 2262590886358575251685433

theorem tailTrace_4406380 : CollatzResearch.WordTrace tailWord_4406380 prefixEnd_4406380 2262590886358575251685433 := by
  unfold tailWord_4406380
  simp only [CollatzResearch.WordTrace]
  refine ⟨80356940888222642317780297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107142587850963523090373729 80356940888222642317780297)
  ·
    refine ⟨60267705666166981738335223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80356940888222642317780297 60267705666166981738335223)
    ·
      refine ⟨90401558499250472607502835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60267705666166981738335223 90401558499250472607502835)
      ·
        refine ⟨135602337748875708911254253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90401558499250472607502835 135602337748875708911254253)
        ·
          refine ⟨50850876655828390841720345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135602337748875708911254253 50850876655828390841720345)
          ·
            refine ⟨38138157491871293131290259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50850876655828390841720345 38138157491871293131290259)
            ·
              refine ⟨57207236237806939696935389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38138157491871293131290259 57207236237806939696935389)
              ·
                refine ⟨21452713589177602386350771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57207236237806939696935389 21452713589177602386350771)
                ·
                  refine ⟨32179070383766403579526157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21452713589177602386350771 32179070383766403579526157)
                  ·
                    refine ⟨12067151393912401342322309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32179070383766403579526157 12067151393912401342322309)
                    ·
                      refine ⟨2262590886358575251685433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12067151393912401342322309 2262590886358575251685433)
                      ·
                        rfl

theorem cell23_4406380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_4406380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406380 prefixEnd_4406380 := by exact prefixLift 4406380
  have htrace : WordTrace (prefixWord ++ tailWord_4406380) baseStart_4406380 baseEnd_4406380 := by
    simpa [prefixWord, tailWord_4406380, baseEnd_4406380] using wordTrace_append hprefix tailTrace_4406380
  have hstable : (prefixWord ++ tailWord_4406380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406380).length < 2 ^ (prefixWord ++ tailWord_4406380).sum := by decide
  have hdescent : baseEnd_4406380 < baseStart_4406380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406397 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_4406397 : Nat := 118140960795 + 4406397 * 2 ^ 59
def prefixEnd_4406397 : Nat := 4983230072969 + 3 ^ 40 * 4406397 * 2
def baseEnd_4406397 : Nat := 2262599615529701685172855

theorem tailTrace_4406397 : CollatzResearch.WordTrace tailWord_4406397 prefixEnd_4406397 2262599615529701685172855 := by
  unfold tailWord_4406397
  simp only [CollatzResearch.WordTrace]
  refine ⟨160714501817383696538929445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107143001211589131025952963 160714501817383696538929445)
  ·
    refine ⟨30133969090759443101049271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160714501817383696538929445 30133969090759443101049271)
    ·
      refine ⟨45200953636139164651573907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30133969090759443101049271 45200953636139164651573907)
      ·
        refine ⟨67801430454208746977360861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45200953636139164651573907 67801430454208746977360861)
        ·
          refine ⟨25425536420328280116510323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67801430454208746977360861 25425536420328280116510323)
          ·
            refine ⟨38138304630492420174765485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25425536420328280116510323 38138304630492420174765485)
            ·
              refine ⟨14301864236434657565537057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38138304630492420174765485 14301864236434657565537057)
              ·
                refine ⟨10726398177325993174152793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14301864236434657565537057 10726398177325993174152793)
                ·
                  refine ⟨8044798632994494880614595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10726398177325993174152793 8044798632994494880614595)
                  ·
                    refine ⟨12067197949491742320921893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8044798632994494880614595 12067197949491742320921893)
                    ·
                      refine ⟨2262599615529701685172855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12067197949491742320921893 2262599615529701685172855)
                      ·
                        rfl

theorem cell23_4406397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_4406397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406397 prefixEnd_4406397 := by exact prefixLift 4406397
  have htrace : WordTrace (prefixWord ++ tailWord_4406397) baseStart_4406397 baseEnd_4406397 := by
    simpa [prefixWord, tailWord_4406397, baseEnd_4406397] using wordTrace_append hprefix tailTrace_4406397
  have hstable : (prefixWord ++ tailWord_4406397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406397).length < 2 ^ (prefixWord ++ tailWord_4406397).sum := by decide
  have hdescent : baseEnd_4406397 < baseStart_4406397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406398 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_4406398 : Nat := 118140960795 + 4406398 * 2 ^ 59
def prefixEnd_4406398 : Nat := 4983230072969 + 3 ^ 40 * 4406398 * 2
def baseEnd_4406398 : Nat := 251400014334484020140039

theorem tailTrace_4406398 : CollatzResearch.WordTrace tailWord_4406398 prefixEnd_4406398 251400014334484020140039 := by
  unfold tailWord_4406398
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089317286297509213714481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107143025526920049139810565 20089317286297509213714481)
  ·
    refine ⟨15066987964723131910285861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20089317286297509213714481 15066987964723131910285861)
    ·
      refine ⟨2825060243385587233178599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15066987964723131910285861 2825060243385587233178599)
      ·
        refine ⟨4237590365078380849767899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825060243385587233178599 4237590365078380849767899)
        ·
          refine ⟨6356385547617571274651849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237590365078380849767899 6356385547617571274651849)
          ·
            refine ⟨4767289160713178455988887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6356385547617571274651849 4767289160713178455988887)
            ·
              refine ⟨7150933741069767683983331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767289160713178455988887 7150933741069767683983331)
              ·
                refine ⟨10726400611604651525974997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150933741069767683983331 10726400611604651525974997)
                ·
                  refine ⟨251400014334484020140039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10726400611604651525974997 251400014334484020140039)
                  ·
                    rfl

theorem cell23_4406398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_4406398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406398 prefixEnd_4406398 := by exact prefixLift 4406398
  have htrace : WordTrace (prefixWord ++ tailWord_4406398) baseStart_4406398 baseEnd_4406398 := by
    simpa [prefixWord, tailWord_4406398, baseEnd_4406398] using wordTrace_append hprefix tailTrace_4406398
  have hstable : (prefixWord ++ tailWord_4406398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406398).length < 2 ^ (prefixWord ++ tailWord_4406398).sum := by decide
  have hdescent : baseEnd_4406398 < baseStart_4406398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406487 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_4406487 : Nat := 118140960795 + 4406487 * 2 ^ 59
def prefixEnd_4406487 : Nat := 4983230072969 + 3 ^ 40 * 4406487 * 2
def baseEnd_4406487 : Nat := 2262645828788606333047441

theorem tailTrace_4406487 : CollatzResearch.WordTrace tailWord_4406487 prefixEnd_4406487 2262645828788606333047441 := by
  unfold tailWord_4406487
  simp only [CollatzResearch.WordTrace]
  refine ⟨160717784387057641909705715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107145189591371761273137143 160717784387057641909705715)
  ·
    refine ⟨241076676580586462864558573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160717784387057641909705715 241076676580586462864558573)
    ·
      refine ⟨90403753717719923574209465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241076676580586462864558573 90403753717719923574209465)
      ·
        refine ⟨67802815288289942680657099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90403753717719923574209465 67802815288289942680657099)
        ·
          refine ⟨101704222932434914020985649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67802815288289942680657099 101704222932434914020985649)
          ·
            refine ⟨76278167199326185515739237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101704222932434914020985649 76278167199326185515739237)
            ·
              refine ⟨14302156349873659784201107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76278167199326185515739237 14302156349873659784201107)
              ·
                refine ⟨21453234524810489676301661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14302156349873659784201107 21453234524810489676301661)
                ·
                  refine ⟨8044962946803933628613123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21453234524810489676301661 8044962946803933628613123)
                  ·
                    refine ⟨12067444420205900442919685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8044962946803933628613123 12067444420205900442919685)
                    ·
                      refine ⟨2262645828788606333047441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12067444420205900442919685 2262645828788606333047441)
                      ·
                        rfl

theorem cell23_4406487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_4406487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406487 prefixEnd_4406487 := by exact prefixLift 4406487
  have htrace : WordTrace (prefixWord ++ tailWord_4406487) baseStart_4406487 baseEnd_4406487 := by
    simpa [prefixWord, tailWord_4406487, baseEnd_4406487] using wordTrace_append hprefix tailTrace_4406487
  have hstable : (prefixWord ++ tailWord_4406487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406487).length < 2 ^ (prefixWord ++ tailWord_4406487).sum := by decide
  have hdescent : baseEnd_4406487 < baseStart_4406487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406497 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_4406497 : Nat := 118140960795 + 4406497 * 2 ^ 59
def prefixEnd_4406497 : Nat := 4983230072969 + 3 ^ 40 * 4406497 * 2
def baseEnd_4406497 : Nat := 754216987865050431307465

theorem tailTrace_4406497 : CollatzResearch.WordTrace tailWord_4406497 prefixEnd_4406497 754216987865050431307465 := by
  unfold tailWord_4406497
  simp only [CollatzResearch.WordTrace]
  refine ⟨160718149117021413617569745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107145432744680942411713163 160718149117021413617569745)
  ·
    refine ⟨120538611837766060213177309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160718149117021413617569745 120538611837766060213177309)
    ·
      refine ⟨45201979439162272579941491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120538611837766060213177309 45201979439162272579941491)
      ·
        refine ⟨67802969158743408869912237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45201979439162272579941491 67802969158743408869912237)
        ·
          refine ⟨25426113434528778326217089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67802969158743408869912237 25426113434528778326217089)
          ·
            refine ⟨19069585075896583744662817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25426113434528778326217089 19069585075896583744662817)
            ·
              refine ⟨14302188806922437808497113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19069585075896583744662817 14302188806922437808497113)
              ·
                refine ⟨10726641605191828356372835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14302188806922437808497113 10726641605191828356372835)
                ·
                  refine ⟨16089962407787742534559253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10726641605191828356372835 16089962407787742534559253)
                  ·
                    refine ⟨754216987865050431307465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16089962407787742534559253 754216987865050431307465)
                    ·
                      rfl

theorem cell23_4406497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_4406497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406497 prefixEnd_4406497 := by exact prefixLift 4406497
  have htrace : WordTrace (prefixWord ++ tailWord_4406497) baseStart_4406497 baseEnd_4406497 := by
    simpa [prefixWord, tailWord_4406497, baseEnd_4406497] using wordTrace_append hprefix tailTrace_4406497
  have hstable : (prefixWord ++ tailWord_4406497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406497).length < 2 ^ (prefixWord ++ tailWord_4406497).sum := by decide
  have hdescent : baseEnd_4406497 < baseStart_4406497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406504 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4406504 : Nat := 118140960795 + 4406504 * 2 ^ 59
def prefixEnd_4406504 : Nat := 4983230072969 + 3 ^ 40 * 4406504 * 2
def baseEnd_4406504 : Nat := 2262654557959732766534863

theorem tailTrace_4406504 : CollatzResearch.WordTrace tailWord_4406504 prefixEnd_4406504 2262654557959732766534863 := by
  unfold tailWord_4406504
  simp only [CollatzResearch.WordTrace]
  refine ⟨80359202213998026906537283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107145602951997369208716377 80359202213998026906537283)
  ·
    refine ⟨120538803320997040359805925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80359202213998026906537283 120538803320997040359805925)
    ·
      refine ⟨22601025622686945067463611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120538803320997040359805925 22601025622686945067463611)
      ·
        refine ⟨33901538434030417601195417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22601025622686945067463611 33901538434030417601195417)
        ·
          refine ⟨25426153825522813200896563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33901538434030417601195417 25426153825522813200896563)
          ·
            refine ⟨38139230738284219801344845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25426153825522813200896563 38139230738284219801344845)
            ·
              refine ⟨14302211526856582425504317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38139230738284219801344845 14302211526856582425504317)
              ·
                refine ⟨5363329322571218409564119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14302211526856582425504317 5363329322571218409564119)
                ·
                  refine ⟨8044993983856827614346179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363329322571218409564119 8044993983856827614346179)
                  ·
                    refine ⟨12067490975785241421519269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8044993983856827614346179 12067490975785241421519269)
                    ·
                      refine ⟨2262654557959732766534863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12067490975785241421519269 2262654557959732766534863)
                      ·
                        rfl

theorem cell23_4406504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4406504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406504 prefixEnd_4406504 := by exact prefixLift 4406504
  have htrace : WordTrace (prefixWord ++ tailWord_4406504) baseStart_4406504 baseEnd_4406504 := by
    simpa [prefixWord, tailWord_4406504, baseEnd_4406504] using wordTrace_append hprefix tailTrace_4406504
  have hstable : (prefixWord ++ tailWord_4406504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406504).length < 2 ^ (prefixWord ++ tailWord_4406504).sum := by decide
  have hdescent : baseEnd_4406504 < baseStart_4406504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406520 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_4406520 : Nat := 118140960795 + 4406520 * 2 ^ 59
def prefixEnd_4406520 : Nat := 4983230072969 + 3 ^ 40 * 4406520 * 2
def baseEnd_4406520 : Nat := 2262662773650204703934789

theorem tailTrace_4406520 : CollatzResearch.WordTrace tailWord_4406520 prefixEnd_4406520 2262662773650204703934789 := by
  unfold tailWord_4406520
  simp only [CollatzResearch.WordTrace]
  refine ⟨80359493997969044272828507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107145991997292059030438009 80359493997969044272828507)
  ·
    refine ⟨120539240996953566409242761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80359493997969044272828507 120539240996953566409242761)
    ·
      refine ⟨90404430747715174806932071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120539240996953566409242761 90404430747715174806932071)
      ·
        refine ⟨135606646121572762210398107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90404430747715174806932071 135606646121572762210398107)
        ·
          refine ⟨203409969182359143315597161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135606646121572762210398107 203409969182359143315597161)
          ·
            refine ⟨152557476886769357486697871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203409969182359143315597161 152557476886769357486697871)
            ·
              refine ⟨228836215330154036230046807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152557476886769357486697871 228836215330154036230046807)
              ·
                refine ⟨343254322995231054345070211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228836215330154036230046807 343254322995231054345070211)
                ·
                  refine ⟨514881484492846581517605317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343254322995231054345070211 514881484492846581517605317)
                  ·
                    refine ⟨96540278342408734034550997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514881484492846581517605317 96540278342408734034550997)
                    ·
                      refine ⟨2262662773650204703934789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96540278342408734034550997 2262662773650204703934789)
                      ·
                        rfl

theorem cell23_4406520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_4406520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406520 prefixEnd_4406520 := by exact prefixLift 4406520
  have htrace : WordTrace (prefixWord ++ tailWord_4406520) baseStart_4406520 baseEnd_4406520 := by
    simpa [prefixWord, tailWord_4406520, baseEnd_4406520] using wordTrace_append hprefix tailTrace_4406520
  have hstable : (prefixWord ++ tailWord_4406520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406520).length < 2 ^ (prefixWord ++ tailWord_4406520).sum := by decide
  have hdescent : baseEnd_4406520 < baseStart_4406520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406521 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 3, 2, 2]
def baseStart_4406521 : Nat := 118140960795 + 4406521 * 2 ^ 59
def prefixEnd_4406521 : Nat := 4983230072969 + 3 ^ 40 * 4406521 * 2
def baseEnd_4406521 : Nat := 2262663287130859200022285

theorem tailTrace_4406521 : CollatzResearch.WordTrace tailWord_4406521 prefixEnd_4406521 2262663287130859200022285 := by
  unfold tailWord_4406521
  simp only [CollatzResearch.WordTrace]
  refine ⟨160719024468934465716443417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107146016312622977144295611 160719024468934465716443417)
  ·
    refine ⟨120539268351700849287332563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160719024468934465716443417 120539268351700849287332563)
    ·
      refine ⟨180808902527551273930998845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120539268351700849287332563 180808902527551273930998845)
      ·
        refine ⟨67803338447831727724124567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180808902527551273930998845 67803338447831727724124567)
        ·
          refine ⟨101705007671747591586186851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67803338447831727724124567 101705007671747591586186851)
          ·
            refine ⟨152557511507621387379280277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101705007671747591586186851 152557511507621387379280277)
            ·
              refine ⟨7151133351919752533403763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 152557511507621387379280277 7151133351919752533403763)
              ·
                refine ⟨10726700027879628800105645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7151133351919752533403763 10726700027879628800105645)
                ·
                  refine ⟨4022512510454860800039617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10726700027879628800105645 4022512510454860800039617)
                  ·
                    refine ⟨3016884382841145600029713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022512510454860800039617 3016884382841145600029713)
                    ·
                      refine ⟨2262663287130859200022285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016884382841145600029713 2262663287130859200022285)
                      ·
                        rfl

theorem cell23_4406521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_4406521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406521 prefixEnd_4406521 := by exact prefixLift 4406521
  have htrace : WordTrace (prefixWord ++ tailWord_4406521) baseStart_4406521 baseEnd_4406521 := by
    simpa [prefixWord, tailWord_4406521, baseEnd_4406521] using wordTrace_append hprefix tailTrace_4406521
  have hstable : (prefixWord ++ tailWord_4406521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406521).length < 2 ^ (prefixWord ++ tailWord_4406521).sum := by decide
  have hdescent : baseEnd_4406521 < baseStart_4406521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406524 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_4406524 : Nat := 118140960795 + 4406524 * 2 ^ 59
def prefixEnd_4406524 : Nat := 4983230072969 + 3 ^ 40 * 4406524 * 2
def baseEnd_4406524 : Nat := 2262664827572822688284771

theorem tailTrace_4406524 : CollatzResearch.WordTrace tailWord_4406524 prefixEnd_4406524 2262664827572822688284771 := by
  unfold tailWord_4406524
  simp only [CollatzResearch.WordTrace]
  refine ⟨80359566943961798614401313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107146089258615731485868417 80359566943961798614401313)
  ·
    refine ⟨60269675207971348960800985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80359566943961798614401313 60269675207971348960800985)
    ·
      refine ⟨45202256405978511720600739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60269675207971348960800985 45202256405978511720600739)
      ·
        refine ⟨67803384608967767580901109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45202256405978511720600739 67803384608967767580901109)
        ·
          refine ⟨6356567307090728210709479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67803384608967767580901109 6356567307090728210709479)
          ·
            refine ⟨9534850960636092316064219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6356567307090728210709479 9534850960636092316064219)
            ·
              refine ⟨14302276440954138474096329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9534850960636092316064219 14302276440954138474096329)
              ·
                refine ⟨10726707330715603855572247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14302276440954138474096329 10726707330715603855572247)
                ·
                  refine ⟨16090060996073405783358371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10726707330715603855572247 16090060996073405783358371)
                  ·
                    refine ⟨24135091494110108675037557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16090060996073405783358371 24135091494110108675037557)
                    ·
                      refine ⟨2262664827572822688284771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24135091494110108675037557 2262664827572822688284771)
                      ·
                        rfl

theorem cell23_4406524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_4406524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406524 prefixEnd_4406524 := by exact prefixLift 4406524
  have htrace : WordTrace (prefixWord ++ tailWord_4406524) baseStart_4406524 baseEnd_4406524 := by
    simpa [prefixWord, tailWord_4406524, baseEnd_4406524] using wordTrace_append hprefix tailTrace_4406524
  have hstable : (prefixWord ++ tailWord_4406524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406524).length < 2 ^ (prefixWord ++ tailWord_4406524).sum := by decide
  have hdescent : baseEnd_4406524 < baseStart_4406524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406531 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 2, 4]
def baseStart_4406531 : Nat := 118140960795 + 4406531 * 2 ^ 59
def prefixEnd_4406531 : Nat := 4983230072969 + 3 ^ 40 * 4406531 * 2
def baseEnd_4406531 : Nat := 754222807312468053632413

theorem tailTrace_4406531 : CollatzResearch.WordTrace tailWord_4406531 prefixEnd_4406531 754222807312468053632413 := by
  unfold tailWord_4406531
  simp only [CollatzResearch.WordTrace]
  refine ⟨160719389198898237424307447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107146259465932158282871631 160719389198898237424307447)
  ·
    refine ⟨241079083798347356136461171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160719389198898237424307447 241079083798347356136461171)
    ·
      refine ⟨361618625697521034204691757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241079083798347356136461171 361618625697521034204691757)
      ·
        refine ⟨135606984636570387826759409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 361618625697521034204691757 135606984636570387826759409)
        ·
          refine ⟨101705238477427790870069557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135606984636570387826759409 101705238477427790870069557)
          ·
            refine ⟨9534866107258855394069021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101705238477427790870069557 9534866107258855394069021)
            ·
              refine ⟨3575574790222070772775883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9534866107258855394069021 3575574790222070772775883)
              ·
                refine ⟨5363362185333106159163825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575574790222070772775883 5363362185333106159163825)
                ·
                  refine ⟨4022521638999829619372869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363362185333106159163825 4022521638999829619372869)
                  ·
                    refine ⟨754222807312468053632413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022521638999829619372869 754222807312468053632413)
                    ·
                      rfl

theorem cell23_4406531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 4].length) (baseStart_4406531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406531 prefixEnd_4406531 := by exact prefixLift 4406531
  have htrace : WordTrace (prefixWord ++ tailWord_4406531) baseStart_4406531 baseEnd_4406531 := by
    simpa [prefixWord, tailWord_4406531, baseEnd_4406531] using wordTrace_append hprefix tailTrace_4406531
  have hstable : (prefixWord ++ tailWord_4406531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406531).length < 2 ^ (prefixWord ++ tailWord_4406531).sum := by decide
  have hdescent : baseEnd_4406531 < baseStart_4406531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406558 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4406558 : Nat := 118140960795 + 4406558 * 2 ^ 59
def prefixEnd_4406558 : Nat := 4983230072969 + 3 ^ 40 * 4406558 * 2
def baseEnd_4406558 : Nat := 2262682285915075555259615

theorem tailTrace_4406558 : CollatzResearch.WordTrace tailWord_4406558 prefixEnd_4406558 2262682285915075555259615 := by
  unfold tailWord_4406558
  simp only [CollatzResearch.WordTrace]
  refine ⟨20090046746225052629442541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107146915979866947357026885 20090046746225052629442541)
  ·
    refine ⟨7533767529834394736040953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20090046746225052629442541 7533767529834394736040953)
    ·
      refine ⟨5650325647375796052030715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7533767529834394736040953 5650325647375796052030715)
      ·
        refine ⟨8475488471063694078046073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650325647375796052030715 8475488471063694078046073)
        ·
          refine ⟨6356616353297770558534555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8475488471063694078046073 6356616353297770558534555)
          ·
            refine ⟨9534924529946655837801833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6356616353297770558534555 9534924529946655837801833)
            ·
              refine ⟨7151193397459991878351375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9534924529946655837801833 7151193397459991878351375)
              ·
                refine ⟨10726790096189987817527063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7151193397459991878351375 10726790096189987817527063)
                ·
                  refine ⟨16090185144284981726290595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10726790096189987817527063 16090185144284981726290595)
                  ·
                    refine ⟨24135277716427472589435893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16090185144284981726290595 24135277716427472589435893)
                    ·
                      refine ⟨2262682285915075555259615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24135277716427472589435893 2262682285915075555259615)
                      ·
                        rfl

theorem cell23_4406558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4406558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406558 prefixEnd_4406558 := by exact prefixLift 4406558
  have htrace : WordTrace (prefixWord ++ tailWord_4406558) baseStart_4406558 baseEnd_4406558 := by
    simpa [prefixWord, tailWord_4406558, baseEnd_4406558] using wordTrace_append hprefix tailTrace_4406558
  have hstable : (prefixWord ++ tailWord_4406558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406558).length < 2 ^ (prefixWord ++ tailWord_4406558).sum := by decide
  have hdescent : baseEnd_4406558 < baseStart_4406558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406582 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4406582 : Nat := 118140960795 + 4406582 * 2 ^ 59
def prefixEnd_4406582 : Nat := 4983230072969 + 3 ^ 40 * 4406582 * 2
def baseEnd_4406582 : Nat := 754231536483594487119835

theorem tailTrace_4406582 : CollatzResearch.WordTrace tailWord_4406582 prefixEnd_4406582 754231536483594487119835 := by
  unfold tailWord_4406582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045078082607092070900875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107147499547808982089609333 10045078082607092070900875)
  ·
    refine ⟨15067617123910638106351313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10045078082607092070900875 15067617123910638106351313)
    ·
      refine ⟨11300712842932978579763485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15067617123910638106351313 11300712842932978579763485)
      ·
        refine ⟨4237767316099866967411307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11300712842932978579763485 4237767316099866967411307)
        ·
          refine ⟨6356650974149800451116961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237767316099866967411307 6356650974149800451116961)
          ·
            refine ⟨4767488230612350338337721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6356650974149800451116961 4767488230612350338337721)
            ·
              refine ⟨3575616172959262753753291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4767488230612350338337721 3575616172959262753753291)
              ·
                refine ⟨5363424259438894130629937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575616172959262753753291 5363424259438894130629937)
                ·
                  refine ⟨4022568194579170597972453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363424259438894130629937 4022568194579170597972453)
                  ·
                    refine ⟨754231536483594487119835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022568194579170597972453 754231536483594487119835)
                    ·
                      rfl

theorem cell23_4406582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4406582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406582 prefixEnd_4406582 := by exact prefixLift 4406582
  have htrace : WordTrace (prefixWord ++ tailWord_4406582) baseStart_4406582 baseEnd_4406582 := by
    simpa [prefixWord, tailWord_4406582, baseEnd_4406582] using wordTrace_append hprefix tailTrace_4406582
  have hstable : (prefixWord ++ tailWord_4406582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406582).length < 2 ^ (prefixWord ++ tailWord_4406582).sum := by decide
  have hdescent : baseEnd_4406582 < baseStart_4406582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406588 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_4406588 : Nat := 118140960795 + 4406588 * 2 ^ 59
def prefixEnd_4406588 : Nat := 4983230072969 + 3 ^ 40 * 4406588 * 2
def baseEnd_4406588 : Nat := 2262697690334710437884477

theorem tailTrace_4406588 : CollatzResearch.WordTrace tailWord_4406588 prefixEnd_4406588 2262697690334710437884477 := by
  unfold tailWord_4406588
  simp only [CollatzResearch.WordTrace]
  refine ⟨80360734079845868079566209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107147645439794490772754945 80360734079845868079566209)
  ·
    refine ⟨60270550559884401059674657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80360734079845868079566209 60270550559884401059674657)
    ·
      refine ⟨45202912919913300794755993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60270550559884401059674657 45202912919913300794755993)
      ·
        refine ⟨33902184689934975596066995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45202912919913300794755993 33902184689934975596066995)
        ·
          refine ⟨50853277034902463394100493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33902184689934975596066995 50853277034902463394100493)
          ·
            refine ⟨19069978888088423772787685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50853277034902463394100493 19069978888088423772787685)
            ·
              refine ⟨3575621041516579457397691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19069978888088423772787685 3575621041516579457397691)
              ·
                refine ⟨5363431562274869186096537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575621041516579457397691 5363431562274869186096537)
                ·
                  refine ⟨4022573671706151889572403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363431562274869186096537 4022573671706151889572403)
                  ·
                    refine ⟨6033860507559227834358605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4022573671706151889572403 6033860507559227834358605)
                    ·
                      refine ⟨2262697690334710437884477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6033860507559227834358605 2262697690334710437884477)
                      ·
                        rfl

theorem cell23_4406588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_4406588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406588 prefixEnd_4406588 := by exact prefixLift 4406588
  have htrace : WordTrace (prefixWord ++ tailWord_4406588) baseStart_4406588 baseEnd_4406588 := by
    simpa [prefixWord, tailWord_4406588, baseEnd_4406588] using wordTrace_append hprefix tailTrace_4406588
  have hstable : (prefixWord ++ tailWord_4406588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406588).length < 2 ^ (prefixWord ++ tailWord_4406588).sum := by decide
  have hdescent : baseEnd_4406588 < baseStart_4406588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406628 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_4406628 : Nat := 118140960795 + 4406628 * 2 ^ 59
def prefixEnd_4406628 : Nat := 4983230072969 + 3 ^ 40 * 4406628 * 2
def baseEnd_4406628 : Nat := 2262718229560890281384293

theorem tailTrace_4406628 : CollatzResearch.WordTrace tailWord_4406628 prefixEnd_4406628 2262718229560890281384293 := by
  unfold tailWord_4406628
  simp only [CollatzResearch.WordTrace]
  refine ⟨80361463539773411495294269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107148618053031215327059025 80361463539773411495294269)
  ·
    refine ⟨30135548827415029310735351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80361463539773411495294269 30135548827415029310735351)
    ·
      refine ⟨45203323241122543966103027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30135548827415029310735351 45203323241122543966103027)
      ·
        refine ⟨67804984861683815949154541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45203323241122543966103027 67804984861683815949154541)
        ·
          refine ⟨25426869323131430980932953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67804984861683815949154541 25426869323131430980932953)
          ·
            refine ⟨19070151992348573235699715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25426869323131430980932953 19070151992348573235699715)
            ·
              refine ⟨28605227988522859853549573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19070151992348573235699715 28605227988522859853549573)
              ·
                refine ⟨5363480247848036222540545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28605227988522859853549573 5363480247848036222540545)
                ·
                  refine ⟨4022610185886027166905409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363480247848036222540545 4022610185886027166905409)
                  ·
                    refine ⟨3016957639414520375179057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022610185886027166905409 3016957639414520375179057)
                    ·
                      refine ⟨2262718229560890281384293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3016957639414520375179057 2262718229560890281384293)
                      ·
                        rfl

theorem cell23_4406628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_4406628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406628 prefixEnd_4406628 := by exact prefixLift 4406628
  have htrace : WordTrace (prefixWord ++ tailWord_4406628) baseStart_4406628 baseEnd_4406628 := by
    simpa [prefixWord, tailWord_4406628, baseEnd_4406628] using wordTrace_append hprefix tailTrace_4406628
  have hstable : (prefixWord ++ tailWord_4406628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406628).length < 2 ^ (prefixWord ++ tailWord_4406628).sum := by decide
  have hdescent : baseEnd_4406628 < baseStart_4406628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406647 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 1, 7]
def baseStart_4406647 : Nat := 118140960795 + 4406647 * 2 ^ 59
def prefixEnd_4406647 : Nat := 4983230072969 + 3 ^ 40 * 4406647 * 2
def baseEnd_4406647 : Nat := 754242661897775235682235

theorem tailTrace_4406647 : CollatzResearch.WordTrace tailWord_4406647 prefixEnd_4406647 754242661897775235682235 := by
  unfold tailWord_4406647
  simp only [CollatzResearch.WordTrace]
  refine ⟨160723620066477989235530195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107149080044318659490353463 160723620066477989235530195)
  ·
    refine ⟨241085430099716983853295293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160723620066477989235530195 241085430099716983853295293)
    ·
      refine ⟨90407036287393868944985735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241085430099716983853295293 90407036287393868944985735)
      ·
        refine ⟨135610554431090803417478603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90407036287393868944985735 135610554431090803417478603)
        ·
          refine ⟨203415831646636205126217905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135610554431090803417478603 203415831646636205126217905)
          ·
            refine ⟨152561873734977153844663429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203415831646636205126217905 152561873734977153844663429)
            ·
              refine ⟨28605351325308216345874393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152561873734977153844663429 28605351325308216345874393)
              ·
                refine ⟨21454013493981162259405795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28605351325308216345874393 21454013493981162259405795)
                ·
                  refine ⟨32181020240971743389108693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21454013493981162259405795 32181020240971743389108693)
                  ·
                    refine ⟨754242661897775235682235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32181020240971743389108693 754242661897775235682235)
                    ·
                      rfl

theorem cell23_4406647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_4406647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406647 prefixEnd_4406647 := by exact prefixLift 4406647
  have htrace : WordTrace (prefixWord ++ tailWord_4406647) baseStart_4406647 baseEnd_4406647 := by
    simpa [prefixWord, tailWord_4406647, baseEnd_4406647] using wordTrace_append hprefix tailTrace_4406647
  have hstable : (prefixWord ++ tailWord_4406647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406647).length < 2 ^ (prefixWord ++ tailWord_4406647).sum := by decide
  have hdescent : baseEnd_4406647 < baseStart_4406647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406664 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_4406664 : Nat := 118140960795 + 4406664 * 2 ^ 59
def prefixEnd_4406664 : Nat := 4983230072969 + 3 ^ 40 * 4406664 * 2
def baseEnd_4406664 : Nat := 754245571621484046844709

theorem tailTrace_4406664 : CollatzResearch.WordTrace tailWord_4406664 prefixEnd_4406664 754245571621484046844709 := by
  unfold tailWord_4406664
  simp only [CollatzResearch.WordTrace]
  refine ⟨80362120053708200569449523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107149493404944267425932697 80362120053708200569449523)
  ·
    refine ⟨120543180080562300854174285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80362120053708200569449523 120543180080562300854174285)
    ·
      refine ⟨45203692530210862820315357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120543180080562300854174285 45203692530210862820315357)
      ·
        refine ⟨16951384698829073557618259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45203692530210862820315357 16951384698829073557618259)
        ·
          refine ⟨25427077048243610336427389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16951384698829073557618259 25427077048243610336427389)
          ·
            refine ⟨9535153893091353876160271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25427077048243610336427389 9535153893091353876160271)
            ·
              refine ⟨14302730839637030814240407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9535153893091353876160271 14302730839637030814240407)
              ·
                refine ⟨21454096259455546221360611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14302730839637030814240407 21454096259455546221360611)
                ·
                  refine ⟨32181144389183319332040917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21454096259455546221360611 32181144389183319332040917)
                  ·
                    refine ⟨754245571621484046844709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32181144389183319332040917 754245571621484046844709)
                    ·
                      rfl

theorem cell23_4406664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_4406664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406664 prefixEnd_4406664 := by exact prefixLift 4406664
  have htrace : WordTrace (prefixWord ++ tailWord_4406664) baseStart_4406664 baseEnd_4406664 := by
    simpa [prefixWord, tailWord_4406664, baseEnd_4406664] using wordTrace_append hprefix tailTrace_4406664
  have hstable : (prefixWord ++ tailWord_4406664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406664).length < 2 ^ (prefixWord ++ tailWord_4406664).sum := by decide
  have hdescent : baseEnd_4406664 < baseStart_4406664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406701 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4406701 : Nat := 118140960795 + 4406701 * 2 ^ 59
def prefixEnd_4406701 : Nat := 4983230072969 + 3 ^ 40 * 4406701 * 2
def baseEnd_4406701 : Nat := 2262755713648668495771457

theorem tailTrace_4406701 : CollatzResearch.WordTrace tailWord_4406701 prefixEnd_4406701 2262755713648668495771457 := by
  unfold tailWord_4406701
  simp only [CollatzResearch.WordTrace]
  refine ⟨160725589608282356457995957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107150393072188237638663971 160725589608282356457995957)
  ·
    refine ⟨15068024025776470917937121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160725589608282356457995957 15068024025776470917937121)
    ·
      refine ⟨11301018019332353188452841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15068024025776470917937121 11301018019332353188452841)
      ·
        refine ⟨8475763514499264891339631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11301018019332353188452841 8475763514499264891339631)
        ·
          refine ⟨12713645271748897337009447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8475763514499264891339631 12713645271748897337009447)
          ·
            refine ⟨19070467907623346005514171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12713645271748897337009447 19070467907623346005514171)
            ·
              refine ⟨28605701861435019008271257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19070467907623346005514171 28605701861435019008271257)
              ·
                refine ⟨21454276396076264256203443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28605701861435019008271257 21454276396076264256203443)
                ·
                  refine ⟨32181414594114396384305165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21454276396076264256203443 32181414594114396384305165)
                  ·
                    refine ⟨12068030472792898644114437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32181414594114396384305165 12068030472792898644114437)
                    ·
                      refine ⟨2262755713648668495771457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12068030472792898644114437 2262755713648668495771457)
                      ·
                        rfl

theorem cell23_4406701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4406701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406701 prefixEnd_4406701 := by exact prefixLift 4406701
  have htrace : WordTrace (prefixWord ++ tailWord_4406701) baseStart_4406701 baseEnd_4406701 := by
    simpa [prefixWord, tailWord_4406701, baseEnd_4406701] using wordTrace_append hprefix tailTrace_4406701
  have hstable : (prefixWord ++ tailWord_4406701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406701).length < 2 ^ (prefixWord ++ tailWord_4406701).sum := by decide
  have hdescent : baseEnd_4406701 < baseStart_4406701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406704 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_4406704 : Nat := 118140960795 + 4406704 * 2 ^ 59
def prefixEnd_4406704 : Nat := 4983230072969 + 3 ^ 40 * 4406704 * 2
def baseEnd_4406704 : Nat := 2262757254090631984033943

theorem tailTrace_4406704 : CollatzResearch.WordTrace tailWord_4406704 prefixEnd_4406704 2262757254090631984033943 := by
  unfold tailWord_4406704
  simp only [CollatzResearch.WordTrace]
  refine ⟨80362849513635743985177583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107150466018180991980236777 80362849513635743985177583)
  ·
    refine ⟨120544274270453615977766375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80362849513635743985177583 120544274270453615977766375)
    ·
      refine ⟨180816411405680423966649563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120544274270453615977766375 180816411405680423966649563)
      ·
        refine ⟨271224617108520635949974345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180816411405680423966649563 271224617108520635949974345)
        ·
          refine ⟨203418462831390476962480759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271224617108520635949974345 203418462831390476962480759)
          ·
            refine ⟨305127694247085715443721139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203418462831390476962480759 305127694247085715443721139)
            ·
              refine ⟨457691541370628573165581709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305127694247085715443721139 457691541370628573165581709)
              ·
                refine ⟨171634328013985714937093141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457691541370628573165581709 171634328013985714937093141)
                ·
                  refine ⟨8045359125655580387676241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171634328013985714937093141 8045359125655580387676241)
                  ·
                    refine ⟨6034019344241685290757181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8045359125655580387676241 6034019344241685290757181)
                    ·
                      refine ⟨2262757254090631984033943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034019344241685290757181 2262757254090631984033943)
                      ·
                        rfl

theorem cell23_4406704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_4406704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406704 prefixEnd_4406704 := by exact prefixLift 4406704
  have htrace : WordTrace (prefixWord ++ tailWord_4406704) baseStart_4406704 baseEnd_4406704 := by
    simpa [prefixWord, tailWord_4406704, baseEnd_4406704] using wordTrace_append hprefix tailTrace_4406704
  have hstable : (prefixWord ++ tailWord_4406704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406704).length < 2 ^ (prefixWord ++ tailWord_4406704).sum := by decide
  have hdescent : baseEnd_4406704 < baseStart_4406704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406745 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 1, 4]
def baseStart_4406745 : Nat := 118140960795 + 4406745 * 2 ^ 59
def prefixEnd_4406745 : Nat := 4983230072969 + 3 ^ 40 * 4406745 * 2
def baseEnd_4406745 : Nat := 754259435599155441207085

theorem tailTrace_4406745 : CollatzResearch.WordTrace tailWord_4406745 prefixEnd_4406745 754259435599155441207085 := by
  unfold tailWord_4406745
  simp only [CollatzResearch.WordTrace]
  refine ⟨160727194420122951972597689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107151462946748634648398459 160727194420122951972597689)
  ·
    refine ⟨120545395815092213979448267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160727194420122951972597689 120545395815092213979448267)
    ·
      refine ⟨180818093722638320969172401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120545395815092213979448267 180818093722638320969172401)
      ·
        refine ⟨135613570291978740726879301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180818093722638320969172401 135613570291978740726879301)
        ·
          refine ⟨25427544429746013886289869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135613570291978740726879301 25427544429746013886289869)
          ·
            refine ⟨9535329161154755207358701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25427544429746013886289869 9535329161154755207358701)
            ·
              refine ⟨3575748435433033202759513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9535329161154755207358701 3575748435433033202759513)
              ·
                refine ⟨2681811326574774902069635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575748435433033202759513 2681811326574774902069635)
                ·
                  refine ⟨4022716989862162353104453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681811326574774902069635 4022716989862162353104453)
                  ·
                    refine ⟨754259435599155441207085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022716989862162353104453 754259435599155441207085)
                    ·
                      rfl

theorem cell23_4406745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 4].length) (baseStart_4406745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406745 prefixEnd_4406745 := by exact prefixLift 4406745
  have htrace : WordTrace (prefixWord ++ tailWord_4406745) baseStart_4406745 baseEnd_4406745 := by
    simpa [prefixWord, tailWord_4406745, baseEnd_4406745] using wordTrace_append hprefix tailTrace_4406745
  have hstable : (prefixWord ++ tailWord_4406745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406745).length < 2 ^ (prefixWord ++ tailWord_4406745).sum := by decide
  have hdescent : baseEnd_4406745 < baseStart_4406745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406778 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2]
def baseStart_4406778 : Nat := 118140960795 + 4406778 * 2 ^ 59
def prefixEnd_4406778 : Nat := 4983230072969 + 3 ^ 40 * 4406778 * 2
def baseEnd_4406778 : Nat := 2262795251659064694508603

theorem tailTrace_4406778 : CollatzResearch.WordTrace tailWord_4406778 prefixEnd_4406778 2262795251659064694508603 := by
  unfold tailWord_4406778
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182099507250849652137247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107152265352668932405699325 40182099507250849652137247)
  ·
    refine ⟨60273149260876274478205871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40182099507250849652137247 60273149260876274478205871)
    ·
      refine ⟨90409723891314411717308807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60273149260876274478205871 90409723891314411717308807)
      ·
        refine ⟨135614585836971617575963211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90409723891314411717308807 135614585836971617575963211)
        ·
          refine ⟨203421878755457426363944817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135614585836971617575963211 203421878755457426363944817)
          ·
            refine ⟨152566409066593069772958613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203421878755457426363944817 152566409066593069772958613)
            ·
              refine ⟨7151550424996550145607435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 152566409066593069772958613 7151550424996550145607435)
              ·
                refine ⟨10727325637494825218411153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7151550424996550145607435 10727325637494825218411153)
                ·
                  refine ⟨8045494228121118913808365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10727325637494825218411153 8045494228121118913808365)
                  ·
                    refine ⟨3017060335545419592678137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8045494228121118913808365 3017060335545419592678137)
                    ·
                      refine ⟨2262795251659064694508603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017060335545419592678137 2262795251659064694508603)
                      ·
                        rfl

theorem cell23_4406778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_4406778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406778 prefixEnd_4406778 := by exact prefixLift 4406778
  have htrace : WordTrace (prefixWord ++ tailWord_4406778) baseStart_4406778 baseEnd_4406778 := by
    simpa [prefixWord, tailWord_4406778, baseEnd_4406778] using wordTrace_append hprefix tailTrace_4406778
  have hstable : (prefixWord ++ tailWord_4406778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406778).length < 2 ^ (prefixWord ++ tailWord_4406778).sum := by decide
  have hdescent : baseEnd_4406778 < baseStart_4406778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406818 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4406818 : Nat := 118140960795 + 4406818 * 2 ^ 59
def prefixEnd_4406818 : Nat := 4983230072969 + 3 ^ 40 * 4406818 * 2
def baseEnd_4406818 : Nat := 754271930295081512669473

theorem tailTrace_4406818 : CollatzResearch.WordTrace tailWord_4406818 prefixEnd_4406818 754271930295081512669473 := by
  unfold tailWord_4406818
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182464237214621360001277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107153237965905656960003405 40182464237214621360001277)
  ·
    refine ⟨15068424088955483010000479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40182464237214621360001277 15068424088955483010000479)
    ·
      refine ⟨22602636133433224515000719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15068424088955483010000479 22602636133433224515000719)
      ·
        refine ⟨33903954200149836772501079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22602636133433224515000719 33903954200149836772501079)
        ·
          refine ⟨50855931300224755158751619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33903954200149836772501079 50855931300224755158751619)
          ·
            refine ⟨76283896950337132738127429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50855931300224755158751619 76283896950337132738127429)
            ·
              refine ⟨14303230678188212388398893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76283896950337132738127429 14303230678188212388398893)
              ·
                refine ⟨5363711504320579645649585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14303230678188212388398893 5363711504320579645649585)
                ·
                  refine ⟨4022783628240434734237189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363711504320579645649585 4022783628240434734237189)
                  ·
                    refine ⟨754271930295081512669473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4022783628240434734237189 754271930295081512669473)
                    ·
                      rfl

theorem cell23_4406818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4406818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406818 prefixEnd_4406818 := by exact prefixLift 4406818
  have htrace : WordTrace (prefixWord ++ tailWord_4406818) baseStart_4406818 baseEnd_4406818 := by
    simpa [prefixWord, tailWord_4406818, baseEnd_4406818] using wordTrace_append hprefix tailTrace_4406818
  have hstable : (prefixWord ++ tailWord_4406818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406818).length < 2 ^ (prefixWord ++ tailWord_4406818).sum := by decide
  have hdescent : baseEnd_4406818 < baseStart_4406818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406842 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2]
def baseStart_4406842 : Nat := 118140960795 + 4406842 * 2 ^ 59
def prefixEnd_4406842 : Nat := 4983230072969 + 3 ^ 40 * 4406842 * 2
def baseEnd_4406842 : Nat := 2262828114420952444108309

theorem tailTrace_4406842 : CollatzResearch.WordTrace tailWord_4406842 prefixEnd_4406842 2262828114420952444108309 := by
  unfold tailWord_4406842
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182683075192884384719695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107153821533847691692585853 40182683075192884384719695)
  ·
    refine ⟨60274024612789326577079543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40182683075192884384719695 60274024612789326577079543)
    ·
      refine ⟨90411036919183989865619315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60274024612789326577079543 90411036919183989865619315)
      ·
        refine ⟨135616555378775984798428973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90411036919183989865619315 135616555378775984798428973)
        ·
          refine ⟨50856208267040994299410865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135616555378775984798428973 50856208267040994299410865)
          ·
            refine ⟨38142156200280745724558149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50856208267040994299410865 38142156200280745724558149)
            ·
              refine ⟨7151654287552639823354653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38142156200280745724558149 7151654287552639823354653)
              ·
                refine ⟨2681870357832239933757995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7151654287552639823354653 2681870357832239933757995)
                ·
                  refine ⟨4022805536748359900636993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681870357832239933757995 4022805536748359900636993)
                  ·
                    refine ⟨3017104152561269925477745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022805536748359900636993 3017104152561269925477745)
                    ·
                      refine ⟨2262828114420952444108309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017104152561269925477745 2262828114420952444108309)
                      ·
                        rfl

theorem cell23_4406842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_4406842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406842 prefixEnd_4406842 := by exact prefixLift 4406842
  have htrace : WordTrace (prefixWord ++ tailWord_4406842) baseStart_4406842 baseEnd_4406842 := by
    simpa [prefixWord, tailWord_4406842, baseEnd_4406842] using wordTrace_append hprefix tailTrace_4406842
  have hstable : (prefixWord ++ tailWord_4406842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406842).length < 2 ^ (prefixWord ++ tailWord_4406842).sum := by decide
  have hdescent : baseEnd_4406842 < baseStart_4406842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406845 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_4406845 : Nat := 118140960795 + 4406845 * 2 ^ 59
def prefixEnd_4406845 : Nat := 4983230072969 + 3 ^ 40 * 4406845 * 2
def baseEnd_4406845 : Nat := 2262829654862915932370795

theorem tailTrace_4406845 : CollatzResearch.WordTrace tailWord_4406845 prefixEnd_4406845 2262829654862915932370795 := by
  unfold tailWord_4406845
  simp only [CollatzResearch.WordTrace]
  refine ⟨160730841719760669051237989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107153894479840446034158659 160730841719760669051237989)
  ·
    refine ⟨30137032822455125447107123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160730841719760669051237989 30137032822455125447107123)
    ·
      refine ⟨45205549233682688170660685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30137032822455125447107123 45205549233682688170660685)
      ·
        refine ⟨16952080962631008063997757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45205549233682688170660685 16952080962631008063997757)
        ·
          refine ⟨6357030360986628023999159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16952080962631008063997757 6357030360986628023999159)
          ·
            refine ⟨9535545541479942035998739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6357030360986628023999159 9535545541479942035998739)
            ·
              refine ⟨14303318312219913053998109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9535545541479942035998739 14303318312219913053998109)
              ·
                refine ⟨5363744367082467395249291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14303318312219913053998109 5363744367082467395249291)
                ·
                  refine ⟨8045616550623701092873937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363744367082467395249291 8045616550623701092873937)
                  ·
                    refine ⟨6034212412967775819655453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8045616550623701092873937 6034212412967775819655453)
                    ·
                      refine ⟨2262829654862915932370795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034212412967775819655453 2262829654862915932370795)
                      ·
                        rfl

theorem cell23_4406845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_4406845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406845 prefixEnd_4406845 := by exact prefixLift 4406845
  have htrace : WordTrace (prefixWord ++ tailWord_4406845) baseStart_4406845 baseEnd_4406845 := by
    simpa [prefixWord, tailWord_4406845, baseEnd_4406845] using wordTrace_append hprefix tailTrace_4406845
  have hstable : (prefixWord ++ tailWord_4406845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406845).length < 2 ^ (prefixWord ++ tailWord_4406845).sum := by decide
  have hdescent : baseEnd_4406845 < baseStart_4406845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406858 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_4406858 : Nat := 118140960795 + 4406858 * 2 ^ 59
def prefixEnd_4406858 : Nat := 4983230072969 + 3 ^ 40 * 4406858 * 2
def baseEnd_4406858 : Nat := 2262836330111424381508235

theorem tailTrace_4406858 : CollatzResearch.WordTrace tailWord_4406858 prefixEnd_4406858 2262836330111424381508235 := by
  unfold tailWord_4406858
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182828967178393067865307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107154210579142381514307485 40182828967178393067865307)
  ·
    refine ⟨60274243450767589601797961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40182828967178393067865307 60274243450767589601797961)
    ·
      refine ⟨45205682588075692201348471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60274243450767589601797961 45205682588075692201348471)
      ·
        refine ⟨67808523882113538302022707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45205682588075692201348471 67808523882113538302022707)
        ·
          refine ⟨101712785823170307453034061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67808523882113538302022707 101712785823170307453034061)
          ·
            refine ⟨38142294683688865294887773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101712785823170307453034061 38142294683688865294887773)
            ·
              refine ⟨14303360506383324485582915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38142294683688865294887773 14303360506383324485582915)
              ·
                refine ⟨21455040759574986728374373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14303360506383324485582915 21455040759574986728374373)
                ·
                  refine ⟨4022820142420310011570195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21455040759574986728374373 4022820142420310011570195)
                  ·
                    refine ⟨6034230213630465017355293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4022820142420310011570195 6034230213630465017355293)
                    ·
                      refine ⟨2262836330111424381508235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034230213630465017355293 2262836330111424381508235)
                      ·
                        rfl

theorem cell23_4406858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_4406858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406858 prefixEnd_4406858 := by exact prefixLift 4406858
  have htrace : WordTrace (prefixWord ++ tailWord_4406858) baseStart_4406858 baseEnd_4406858 := by
    simpa [prefixWord, tailWord_4406858, baseEnd_4406858] using wordTrace_append hprefix tailTrace_4406858
  have hstable : (prefixWord ++ tailWord_4406858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406858).length < 2 ^ (prefixWord ++ tailWord_4406858).sum := by decide
  have hdescent : baseEnd_4406858 < baseStart_4406858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406885 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 1, 3, 2]
def baseStart_4406885 : Nat := 118140960795 + 4406885 * 2 ^ 59
def prefixEnd_4406885 : Nat := 4983230072969 + 3 ^ 40 * 4406885 * 2
def baseEnd_4406885 : Nat := 2262850194089095775870611

theorem tailTrace_4406885 : CollatzResearch.WordTrace tailWord_4406885 prefixEnd_4406885 2262850194089095775870611 := by
  unfold tailWord_4406885
  simp only [CollatzResearch.WordTrace]
  refine ⟨160732300639615755882694109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107154867093077170588462739 160732300639615755882694109)
  ·
    refine ⟨60274612739855908456010291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160732300639615755882694109 60274612739855908456010291)
    ·
      refine ⟨90411919109783862684015437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60274612739855908456010291 90411919109783862684015437)
      ·
        refine ⟨33904469666168948506505789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90411919109783862684015437 33904469666168948506505789)
        ·
          refine ⟨12714176124813355689939671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33904469666168948506505789 12714176124813355689939671)
          ·
            refine ⟨19071264187220033534909507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12714176124813355689939671 19071264187220033534909507)
            ·
              refine ⟨28606896280830050302364261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19071264187220033534909507 28606896280830050302364261)
              ·
                refine ⟨5363793052655634431693299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28606896280830050302364261 5363793052655634431693299)
                ·
                  refine ⟨8045689578983451647539949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363793052655634431693299 8045689578983451647539949)
                  ·
                    refine ⟨3017133592118794367827481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8045689578983451647539949 3017133592118794367827481)
                    ·
                      refine ⟨2262850194089095775870611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017133592118794367827481 2262850194089095775870611)
                      ·
                        rfl

theorem cell23_4406885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_4406885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406885 prefixEnd_4406885 := by exact prefixLift 4406885
  have htrace : WordTrace (prefixWord ++ tailWord_4406885) baseStart_4406885 baseEnd_4406885 := by
    simpa [prefixWord, tailWord_4406885, baseEnd_4406885] using wordTrace_append hprefix tailTrace_4406885
  have hstable : (prefixWord ++ tailWord_4406885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406885).length < 2 ^ (prefixWord ++ tailWord_4406885).sum := by decide
  have hdescent : baseEnd_4406885 < baseStart_4406885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406902 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4406902 : Nat := 118140960795 + 4406902 * 2 ^ 59
def prefixEnd_4406902 : Nat := 4983230072969 + 3 ^ 40 * 4406902 * 2
def baseEnd_4406902 : Nat := 2262858923260222209358033

theorem tailTrace_4406902 : CollatzResearch.WordTrace tailWord_4406902 prefixEnd_4406902 2262858923260222209358033 := by
  unfold tailWord_4406902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045807542534635486628935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107155280453702778524041973 10045807542534635486628935)
  ·
    refine ⟨15068711313801953229943403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10045807542534635486628935 15068711313801953229943403)
    ·
      refine ⟨22603066970702929844915105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15068711313801953229943403 22603066970702929844915105)
      ·
        refine ⟨16952300228027197383686329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22603066970702929844915105 16952300228027197383686329)
        ·
          refine ⟨12714225171020398037764747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16952300228027197383686329 12714225171020398037764747)
          ·
            refine ⟨19071337756530597056647121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12714225171020398037764747 19071337756530597056647121)
            ·
              refine ⟨14303503317397947792485341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19071337756530597056647121 14303503317397947792485341)
              ·
                refine ⟨5363813744024230422182003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14303503317397947792485341 5363813744024230422182003)
                ·
                  refine ⟨8045720616036345633273005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363813744024230422182003 8045720616036345633273005)
                  ·
                    refine ⟨3017145231013629612477377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8045720616036345633273005 3017145231013629612477377)
                    ·
                      refine ⟨2262858923260222209358033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017145231013629612477377 2262858923260222209358033)
                      ·
                        rfl

theorem cell23_4406902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4406902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406902 prefixEnd_4406902 := by exact prefixLift 4406902
  have htrace : WordTrace (prefixWord ++ tailWord_4406902) baseStart_4406902 baseEnd_4406902 := by
    simpa [prefixWord, tailWord_4406902, baseEnd_4406902] using wordTrace_append hprefix tailTrace_4406902
  have hstable : (prefixWord ++ tailWord_4406902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406902).length < 2 ^ (prefixWord ++ tailWord_4406902).sum := by decide
  have hdescent : baseEnd_4406902 < baseStart_4406902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406915 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 2, 2, 2]
def baseStart_4406915 : Nat := 118140960795 + 4406915 * 2 ^ 59
def prefixEnd_4406915 : Nat := 4983230072969 + 3 ^ 40 * 4406915 * 2
def baseEnd_4406915 : Nat := 2262865598508730658495473

theorem tailTrace_4406915 : CollatzResearch.WordTrace tailWord_4406915 prefixEnd_4406915 2262865598508730658495473 := by
  unfold tailWord_4406915
  simp only [CollatzResearch.WordTrace]
  refine ⟨160733394829507071006286199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107155596553004714004190799 160733394829507071006286199)
  ·
    refine ⟨241100092244260606509429299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160733394829507071006286199 241100092244260606509429299)
    ·
      refine ⟨361650138366390909764143949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241100092244260606509429299 361650138366390909764143949)
      ·
        refine ⟨135618801887396591161553981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 361650138366390909764143949 135618801887396591161553981)
        ·
          refine ⟨50857050707773721685582743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135618801887396591161553981 50857050707773721685582743)
          ·
            refine ⟨76285576061660582528374115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50857050707773721685582743 76285576061660582528374115)
            ·
              refine ⟨114428364092490873792561173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76285576061660582528374115 114428364092490873792561173)
              ·
                refine ⟨5363829566835509709026305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114428364092490873792561173 5363829566835509709026305)
                ·
                  refine ⟨4022872175126632281769729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363829566835509709026305 4022872175126632281769729)
                  ·
                    refine ⟨3017154131344974211327297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022872175126632281769729 3017154131344974211327297)
                    ·
                      refine ⟨2262865598508730658495473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017154131344974211327297 2262865598508730658495473)
                      ·
                        rfl

theorem cell23_4406915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_4406915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406915 prefixEnd_4406915 := by exact prefixLift 4406915
  have htrace : WordTrace (prefixWord ++ tailWord_4406915) baseStart_4406915 baseEnd_4406915 := by
    simpa [prefixWord, tailWord_4406915, baseEnd_4406915] using wordTrace_append hprefix tailTrace_4406915
  have hstable : (prefixWord ++ tailWord_4406915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406915).length < 2 ^ (prefixWord ++ tailWord_4406915).sum := by decide
  have hdescent : baseEnd_4406915 < baseStart_4406915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406921 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 7]
def baseStart_4406921 : Nat := 118140960795 + 4406921 * 2 ^ 59
def prefixEnd_4406921 : Nat := 4983230072969 + 3 ^ 40 * 4406921 * 2
def baseEnd_4406921 : Nat := 251429853265850848335605

theorem tailTrace_4406921 : CollatzResearch.WordTrace tailWord_4406921 prefixEnd_4406921 251429853265850848335605 := by
  unfold tailWord_4406921
  simp only [CollatzResearch.WordTrace]
  refine ⟨160733613667485334031004617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107155742444990222687336411 160733613667485334031004617)
  ·
    refine ⟨120550210250614000523253463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160733613667485334031004617 120550210250614000523253463)
    ·
      refine ⟨180825315375921000784880195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120550210250614000523253463 180825315375921000784880195)
      ·
        refine ⟨271237973063881501177320293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180825315375921000784880195 271237973063881501177320293)
        ·
          refine ⟨50857119949477781470747555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271237973063881501177320293 50857119949477781470747555)
          ·
            refine ⟨76285679924216672206121333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50857119949477781470747555 76285679924216672206121333)
            ·
              refine ⟨7151782492895313019323875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76285679924216672206121333 7151782492895313019323875)
              ·
                refine ⟨10727673739342969528985813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7151782492895313019323875 10727673739342969528985813)
                ·
                  refine ⟨251429853265850848335605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10727673739342969528985813 251429853265850848335605)
                  ·
                    rfl

theorem cell23_4406921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_4406921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406921 prefixEnd_4406921 := by exact prefixLift 4406921
  have htrace : WordTrace (prefixWord ++ tailWord_4406921) baseStart_4406921 baseEnd_4406921 := by
    simpa [prefixWord, tailWord_4406921, baseEnd_4406921] using wordTrace_append hprefix tailTrace_4406921
  have hstable : (prefixWord ++ tailWord_4406921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406921).length < 2 ^ (prefixWord ++ tailWord_4406921).sum := by decide
  have hdescent : baseEnd_4406921 < baseStart_4406921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406966 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4406966 : Nat := 118140960795 + 4406966 * 2 ^ 59
def prefixEnd_4406966 : Nat := 4983230072969 + 3 ^ 40 * 4406966 * 2
def baseEnd_4406966 : Nat := 2262891786022109958957739

theorem tailTrace_4406966 : CollatzResearch.WordTrace tailWord_4406966 prefixEnd_4406966 2262891786022109958957739 := by
  unfold tailWord_4406966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045953434520144169774547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107156836634881537810928501 10045953434520144169774547)
  ·
    refine ⟨15068930151780216254661821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10045953434520144169774547 15068930151780216254661821)
    ·
      refine ⟨5650848806917581095498183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15068930151780216254661821 5650848806917581095498183)
      ·
        refine ⟨8476273210376371643247275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650848806917581095498183 8476273210376371643247275)
        ·
          refine ⟨12714409815564557464870913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8476273210376371643247275 12714409815564557464870913)
          ·
            refine ⟨9535807361673418098653185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12714409815564557464870913 9535807361673418098653185)
            ·
              refine ⟨7151855521255063573989889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9535807361673418098653185 7151855521255063573989889)
              ·
                refine ⟨5363891640941297680492417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7151855521255063573989889 5363891640941297680492417)
                ·
                  refine ⟨4022918730705973260369313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363891640941297680492417 4022918730705973260369313)
                  ·
                    refine ⟨3017189048029479945276985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022918730705973260369313 3017189048029479945276985)
                    ·
                      refine ⟨2262891786022109958957739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017189048029479945276985 2262891786022109958957739)
                      ·
                        rfl

theorem cell23_4406966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4406966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406966 prefixEnd_4406966 := by exact prefixLift 4406966
  have htrace : WordTrace (prefixWord ++ tailWord_4406966) baseStart_4406966 baseEnd_4406966 := by
    simpa [prefixWord, tailWord_4406966, baseEnd_4406966] using wordTrace_append hprefix tailTrace_4406966
  have hstable : (prefixWord ++ tailWord_4406966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406966).length < 2 ^ (prefixWord ++ tailWord_4406966).sum := by decide
  have hdescent : baseEnd_4406966 < baseStart_4406966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406972 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 5]
def baseStart_4406972 : Nat := 118140960795 + 4406972 * 2 ^ 59
def prefixEnd_4406972 : Nat := 4983230072969 + 3 ^ 40 * 4406972 * 2
def baseEnd_4406972 : Nat := 251432762989559659498079

theorem tailTrace_4406972 : CollatzResearch.WordTrace tailWord_4406972 prefixEnd_4406972 251432762989559659498079 := by
  unfold tailWord_4406972
  simp only [CollatzResearch.WordTrace]
  refine ⟨80367736895150284870555585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107156982526867046494074113 80367736895150284870555585)
  ·
    refine ⟨60275802671362713652916689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80367736895150284870555585 60275802671362713652916689)
    ·
      refine ⟨45206852003522035239687517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60275802671362713652916689 45206852003522035239687517)
      ·
        refine ⟨16952569501320763214882819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45206852003522035239687517 16952569501320763214882819)
        ·
          refine ⟨25428854251981144822324229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16952569501320763214882819 25428854251981144822324229)
          ·
            refine ⟨4767910172246464654185793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25428854251981144822324229 4767910172246464654185793)
            ·
              refine ⟨3575932629184848490639345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4767910172246464654185793 3575932629184848490639345)
              ·
                refine ⟨2681949471888636367979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575932629184848490639345 2681949471888636367979509)
                ·
                  refine ⟨251432762989559659498079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2681949471888636367979509 251432762989559659498079)
                  ·
                    rfl

theorem cell23_4406972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_4406972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406972 prefixEnd_4406972 := by exact prefixLift 4406972
  have htrace : WordTrace (prefixWord ++ tailWord_4406972) baseStart_4406972 baseEnd_4406972 := by
    simpa [prefixWord, tailWord_4406972, baseEnd_4406972] using wordTrace_append hprefix tailTrace_4406972
  have hstable : (prefixWord ++ tailWord_4406972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406972).length < 2 ^ (prefixWord ++ tailWord_4406972).sum := by decide
  have hdescent : baseEnd_4406972 < baseStart_4406972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4406982 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4406982 : Nat := 118140960795 + 4406982 * 2 ^ 59
def prefixEnd_4406982 : Nat := 4983230072969 + 3 ^ 40 * 4406982 * 2
def baseEnd_4406982 : Nat := 2262900001712581896357665

theorem tailTrace_4406982 : CollatzResearch.WordTrace tailWord_4406982 prefixEnd_4406982 2262900001712581896357665 := by
  unfold tailWord_4406982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022994953758260670280475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107157225680176227632650133 5022994953758260670280475)
  ·
    refine ⟨7534492430637391005420713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022994953758260670280475 7534492430637391005420713)
    ·
      refine ⟨5650869322978043254065535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7534492430637391005420713 5650869322978043254065535)
      ·
        refine ⟨8476303984467064881098303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650869322978043254065535 8476303984467064881098303)
        ·
          refine ⟨12714455976700597321647455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8476303984467064881098303 12714455976700597321647455)
          ·
            refine ⟨19071683965050895982471183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12714455976700597321647455 19071683965050895982471183)
            ·
              refine ⟨28607525947576343973706775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19071683965050895982471183 28607525947576343973706775)
              ·
                refine ⟨42911288921364515960560163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28607525947576343973706775 42911288921364515960560163)
                ·
                  refine ⟨64366933382046773940840245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42911288921364515960560163 64366933382046773940840245)
                  ·
                    refine ⟨6034400004566885056953773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64366933382046773940840245 6034400004566885056953773)
                    ·
                      refine ⟨2262900001712581896357665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034400004566885056953773 2262900001712581896357665)
                      ·
                        rfl

theorem cell23_4406982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4406982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4406982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4406982 prefixEnd_4406982 := by exact prefixLift 4406982
  have htrace : WordTrace (prefixWord ++ tailWord_4406982) baseStart_4406982 baseEnd_4406982 := by
    simpa [prefixWord, tailWord_4406982, baseEnd_4406982] using wordTrace_append hprefix tailTrace_4406982
  have hstable : (prefixWord ++ tailWord_4406982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4406982).length < 2 ^ (prefixWord ++ tailWord_4406982).sum := by decide
  have hdescent : baseEnd_4406982 < baseStart_4406982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4406982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407031 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_4407031 : Nat := 118140960795 + 4407031 * 2 ^ 59
def prefixEnd_4407031 : Nat := 4983230072969 + 3 ^ 40 * 4407031 * 2
def baseEnd_4407031 : Nat := 2262925162264652204644939

theorem tailTrace_4407031 : CollatzResearch.WordTrace tailWord_4407031 prefixEnd_4407031 2262925162264652204644939 := by
  unfold tailWord_4407031
  simp only [CollatzResearch.WordTrace]
  refine ⟨160737625697086822817508947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107158417131391215211672631 160737625697086822817508947)
  ·
    refine ⟨241106438545630234226263421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160737625697086822817508947 241106438545630234226263421)
    ·
      refine ⟨90414914454611337834848783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241106438545630234226263421 90414914454611337834848783)
      ·
        refine ⟨135622371681917006752273175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90414914454611337834848783 135622371681917006752273175)
        ·
          refine ⟨203433557522875510128409763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135622371681917006752273175 203433557522875510128409763)
          ·
            refine ⟨305150336284313265192614645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203433557522875510128409763 305150336284313265192614645)
            ·
              refine ⟨28607844026654368611807623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 305150336284313265192614645 28607844026654368611807623)
              ·
                refine ⟨42911766039981552917711435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28607844026654368611807623 42911766039981552917711435)
                ·
                  refine ⟨64367649059972329376567153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42911766039981552917711435 64367649059972329376567153)
                  ·
                    refine ⟨48275736794979247032425365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64367649059972329376567153 48275736794979247032425365)
                    ·
                      refine ⟨2262925162264652204644939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48275736794979247032425365 2262925162264652204644939)
                      ·
                        rfl

theorem cell23_4407031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_4407031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407031 prefixEnd_4407031 := by exact prefixLift 4407031
  have htrace : WordTrace (prefixWord ++ tailWord_4407031) baseStart_4407031 baseEnd_4407031 := by
    simpa [prefixWord, tailWord_4407031, baseEnd_4407031] using wordTrace_append hprefix tailTrace_4407031
  have hstable : (prefixWord ++ tailWord_4407031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407031).length < 2 ^ (prefixWord ++ tailWord_4407031).sum := by decide
  have hdescent : baseEnd_4407031 < baseStart_4407031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407051 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_4407051 : Nat := 118140960795 + 4407051 * 2 ^ 59
def prefixEnd_4407051 : Nat := 4983230072969 + 3 ^ 40 * 4407051 * 2
def baseEnd_4407051 : Nat := 2262935431877742126394847

theorem tailTrace_4407051 : CollatzResearch.WordTrace tailWord_4407051 prefixEnd_4407051 2262935431877742126394847 := by
  unfold tailWord_4407051
  simp only [CollatzResearch.WordTrace]
  refine ⟨160738355157014366233237007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107158903438009577488824671 160738355157014366233237007)
  ·
    refine ⟨241107532735521549349855511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160738355157014366233237007 241107532735521549349855511)
    ·
      refine ⟨361661299103282324024783267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241107532735521549349855511 361661299103282324024783267)
      ·
        refine ⟨542491948654923486037174901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361661299103282324024783267 542491948654923486037174901)
        ·
          refine ⟨50858620186399076815985147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 542491948654923486037174901 50858620186399076815985147)
          ·
            refine ⟨76287930279598615223977721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50858620186399076815985147 76287930279598615223977721)
            ·
              refine ⟨57215947709698961417983291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76287930279598615223977721 57215947709698961417983291)
              ·
                refine ⟨85823921564548442126974937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57215947709698961417983291 85823921564548442126974937)
                ·
                  refine ⟨64367941173411331595231203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85823921564548442126974937 64367941173411331595231203)
                  ·
                    refine ⟨96551911760116997392846805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64367941173411331595231203 96551911760116997392846805)
                    ·
                      refine ⟨2262935431877742126394847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96551911760116997392846805 2262935431877742126394847)
                      ·
                        rfl

theorem cell23_4407051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_4407051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407051 prefixEnd_4407051 := by exact prefixLift 4407051
  have htrace : WordTrace (prefixWord ++ tailWord_4407051) baseStart_4407051 baseEnd_4407051 := by
    simpa [prefixWord, tailWord_4407051, baseEnd_4407051] using wordTrace_append hprefix tailTrace_4407051
  have hstable : (prefixWord ++ tailWord_4407051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407051).length < 2 ^ (prefixWord ++ tailWord_4407051).sum := by decide
  have hdescent : baseEnd_4407051 < baseStart_4407051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407112 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_4407112 : Nat := 118140960795 + 4407112 * 2 ^ 59
def prefixEnd_4407112 : Nat := 4983230072969 + 3 ^ 40 * 4407112 * 2
def baseEnd_4407112 : Nat := 2262966754197666387732067

theorem tailTrace_4407112 : CollatzResearch.WordTrace tailWord_4407112 prefixEnd_4407112 2262966754197666387732067 := by
  unfold tailWord_4407112
  simp only [CollatzResearch.WordTrace]
  refine ⟨80370290004896686825603795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107160386673195582434138393 80370290004896686825603795)
  ·
    refine ⟨120555435007345030238405693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80370290004896686825603795 120555435007345030238405693)
    ·
      refine ⟨45208288127754386339402135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120555435007345030238405693 45208288127754386339402135)
      ·
        refine ⟨67812432191631579509103203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45208288127754386339402135 67812432191631579509103203)
        ·
          refine ⟨101718648287447369263654805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67812432191631579509103203 101718648287447369263654805)
          ·
            refine ⟨4768061638474095434233819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101718648287447369263654805 4768061638474095434233819)
            ·
              refine ⟨7152092457711143151350729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768061638474095434233819 7152092457711143151350729)
              ·
                refine ⟨5364069343283357363513047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152092457711143151350729 5364069343283357363513047)
                ·
                  refine ⟨8046104014925036045269571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5364069343283357363513047 8046104014925036045269571)
                  ·
                    refine ⟨12069156022387554067904357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8046104014925036045269571 12069156022387554067904357)
                    ·
                      refine ⟨2262966754197666387732067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12069156022387554067904357 2262966754197666387732067)
                      ·
                        rfl

theorem cell23_4407112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_4407112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407112 prefixEnd_4407112 := by exact prefixLift 4407112
  have htrace : WordTrace (prefixWord ++ tailWord_4407112) baseStart_4407112 baseEnd_4407112 := by
    simpa [prefixWord, tailWord_4407112, baseEnd_4407112] using wordTrace_append hprefix tailTrace_4407112
  have hstable : (prefixWord ++ tailWord_4407112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407112).length < 2 ^ (prefixWord ++ tailWord_4407112).sum := by decide
  have hdescent : baseEnd_4407112 < baseStart_4407112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407125 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4407125 : Nat := 118140960795 + 4407125 * 2 ^ 59
def prefixEnd_4407125 : Nat := 4983230072969 + 3 ^ 40 * 4407125 * 2
def baseEnd_4407125 : Nat := 2262973429446174836869507

theorem tailTrace_4407125 : CollatzResearch.WordTrace tailWord_4407125 prefixEnd_4407125 2262973429446174836869507 := by
  unfold tailWord_4407125
  simp only [CollatzResearch.WordTrace]
  refine ⟨160741054158746276871430829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107160702772497517914287219 160741054158746276871430829)
  ·
    refine ⟨60277895309529853826786561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160741054158746276871430829 60277895309529853826786561)
    ·
      refine ⟨45208421482147390370089921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60277895309529853826786561 45208421482147390370089921)
      ·
        refine ⟨33906316111610542777567441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45208421482147390370089921 33906316111610542777567441)
        ·
          refine ⟨25429737083707907083175581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33906316111610542777567441 25429737083707907083175581)
          ·
            refine ⟨9536151406390465156190843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25429737083707907083175581 9536151406390465156190843)
            ·
              refine ⟨14304227109585697734286265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9536151406390465156190843 14304227109585697734286265)
              ·
                refine ⟨10728170332189273300714699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14304227109585697734286265 10728170332189273300714699)
                ·
                  refine ⟨16092255498283909951072049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10728170332189273300714699 16092255498283909951072049)
                  ·
                    refine ⟨12069191623712932463304037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16092255498283909951072049 12069191623712932463304037)
                    ·
                      refine ⟨2262973429446174836869507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12069191623712932463304037 2262973429446174836869507)
                      ·
                        rfl

theorem cell23_4407125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4407125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407125 prefixEnd_4407125 := by exact prefixLift 4407125
  have htrace : WordTrace (prefixWord ++ tailWord_4407125) baseStart_4407125 baseEnd_4407125 := by
    simpa [prefixWord, tailWord_4407125, baseEnd_4407125] using wordTrace_append hprefix tailTrace_4407125
  have hstable : (prefixWord ++ tailWord_4407125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407125).length < 2 ^ (prefixWord ++ tailWord_4407125).sum := by decide
  have hdescent : baseEnd_4407125 < baseStart_4407125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407129 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 1, 2, 2]
def baseStart_4407129 : Nat := 118140960795 + 4407129 * 2 ^ 59
def prefixEnd_4407129 : Nat := 4983230072969 + 3 ^ 40 * 4407129 * 2
def baseEnd_4407129 : Nat := 2262975483368792821219489

theorem tailTrace_4407129 : CollatzResearch.WordTrace tailWord_4407129 prefixEnd_4407129 2262975483368792821219489 := by
  unfold tailWord_4407129
  simp only [CollatzResearch.WordTrace]
  refine ⟨160741200050731785554576441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107160800033821190369717627 160741200050731785554576441)
  ·
    refine ⟨120555900038048839165932331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160741200050731785554576441 120555900038048839165932331)
    ·
      refine ⟨180833850057073258748898497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120555900038048839165932331 180833850057073258748898497)
      ·
        refine ⟨135625387542804944061673873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180833850057073258748898497 135625387542804944061673873)
        ·
          refine ⟨101719040657103708046255405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135625387542804944061673873 101719040657103708046255405)
          ·
            refine ⟨38144640246413890517345777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101719040657103708046255405 38144640246413890517345777)
            ·
              refine ⟨28608480184810417888009333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38144640246413890517345777 28608480184810417888009333)
              ·
                refine ⟨2682045017325976677000875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28608480184810417888009333 2682045017325976677000875)
                ·
                  refine ⟨4023067525988965015501313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682045017325976677000875 4023067525988965015501313)
                  ·
                    refine ⟨3017300644491723761625985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023067525988965015501313 3017300644491723761625985)
                    ·
                      refine ⟨2262975483368792821219489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017300644491723761625985 2262975483368792821219489)
                      ·
                        rfl

theorem cell23_4407129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_4407129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407129 prefixEnd_4407129 := by exact prefixLift 4407129
  have htrace : WordTrace (prefixWord ++ tailWord_4407129) baseStart_4407129 baseEnd_4407129 := by
    simpa [prefixWord, tailWord_4407129, baseEnd_4407129] using wordTrace_append hprefix tailTrace_4407129
  have hstable : (prefixWord ++ tailWord_4407129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407129).length < 2 ^ (prefixWord ++ tailWord_4407129).sum := by decide
  have hdescent : baseEnd_4407129 < baseStart_4407129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407145 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 3]
def baseStart_4407145 : Nat := 118140960795 + 4407145 * 2 ^ 59
def prefixEnd_4407145 : Nat := 4983230072969 + 3 ^ 40 * 4407145 * 2
def baseEnd_4407145 : Nat := 2262983699059264758619415

theorem tailTrace_4407145 : CollatzResearch.WordTrace tailWord_4407145 prefixEnd_4407145 2262983699059264758619415 := by
  unfold tailWord_4407145
  simp only [CollatzResearch.WordTrace]
  refine ⟨160741783618673820287158889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107161189079115880191439259 160741783618673820287158889)
  ·
    refine ⟨120556337714005365215369167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160741783618673820287158889 120556337714005365215369167)
    ·
      refine ⟨180834506571008047823053751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120556337714005365215369167 180834506571008047823053751)
      ·
        refine ⟨271251759856512071734580627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180834506571008047823053751 271251759856512071734580627)
        ·
          refine ⟨406877639784768107601870941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271251759856512071734580627 406877639784768107601870941)
          ·
            refine ⟨152579114919288040350701603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406877639784768107601870941 152579114919288040350701603)
            ·
              refine ⟨228868672378932060526052405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152579114919288040350701603 228868672378932060526052405)
              ·
                refine ⟨21456438035524880674317413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228868672378932060526052405 21456438035524880674317413)
                ·
                  refine ⟨4023082131660915126434515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21456438035524880674317413 4023082131660915126434515)
                  ·
                    refine ⟨6034623197491372689651773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023082131660915126434515 6034623197491372689651773)
                    ·
                      refine ⟨2262983699059264758619415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034623197491372689651773 2262983699059264758619415)
                      ·
                        rfl

theorem cell23_4407145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_4407145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407145 prefixEnd_4407145 := by exact prefixLift 4407145
  have htrace : WordTrace (prefixWord ++ tailWord_4407145) baseStart_4407145 baseEnd_4407145 := by
    simpa [prefixWord, tailWord_4407145, baseEnd_4407145] using wordTrace_append hprefix tailTrace_4407145
  have hstable : (prefixWord ++ tailWord_4407145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407145).length < 2 ^ (prefixWord ++ tailWord_4407145).sum := by decide
  have hdescent : baseEnd_4407145 < baseStart_4407145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407148 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_4407148 : Nat := 118140960795 + 4407148 * 2 ^ 59
def prefixEnd_4407148 : Nat := 4983230072969 + 3 ^ 40 * 4407148 * 2
def baseEnd_4407148 : Nat := 754328413167076082293967

theorem tailTrace_4407148 : CollatzResearch.WordTrace tailWord_4407148 prefixEnd_4407148 754328413167076082293967 := by
  unfold tailWord_4407148
  simp only [CollatzResearch.WordTrace]
  refine ⟨80370946518831475899759049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107161262025108634533012065 80370946518831475899759049)
  ·
    refine ⟨60278209889123606924819287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80370946518831475899759049 60278209889123606924819287)
    ·
      refine ⟨90417314833685410387228931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60278209889123606924819287 90417314833685410387228931)
      ·
        refine ⟨135625972250528115580843397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90417314833685410387228931 135625972250528115580843397)
        ·
          refine ⟨25429869796974021671408137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135625972250528115580843397 25429869796974021671408137)
          ·
            refine ⟨19072402347730516253556103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25429869796974021671408137 19072402347730516253556103)
            ·
              refine ⟨28608603521595774380334155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19072402347730516253556103 28608603521595774380334155)
              ·
                refine ⟨42912905282393661570501233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28608603521595774380334155 42912905282393661570501233)
                ·
                  refine ⟨32184678961795246177875925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42912905282393661570501233 32184678961795246177875925)
                  ·
                    refine ⟨754328413167076082293967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32184678961795246177875925 754328413167076082293967)
                    ·
                      rfl

theorem cell23_4407148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_4407148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407148 prefixEnd_4407148 := by exact prefixLift 4407148
  have htrace : WordTrace (prefixWord ++ tailWord_4407148) baseStart_4407148 baseEnd_4407148 := by
    simpa [prefixWord, tailWord_4407148, baseEnd_4407148] using wordTrace_append hprefix tailTrace_4407148
  have hstable : (prefixWord ++ tailWord_4407148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407148).length < 2 ^ (prefixWord ++ tailWord_4407148).sum := by decide
  have hdescent : baseEnd_4407148 < baseStart_4407148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407162 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_4407162 : Nat := 118140960795 + 4407162 * 2 ^ 59
def prefixEnd_4407162 : Nat := 4983230072969 + 3 ^ 40 * 4407162 * 2
def baseEnd_4407162 : Nat := 2262992428230391192106837

theorem tailTrace_4407162 : CollatzResearch.WordTrace tailWord_4407162 prefixEnd_4407162 2262992428230391192106837 := by
  unfold tailWord_4407162
  simp only [CollatzResearch.WordTrace]
  refine ⟨40185600914903058047631935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107161602439741488127018493 40185600914903058047631935)
  ·
    refine ⟨60278401372354587071447903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40185600914903058047631935 60278401372354587071447903)
    ·
      refine ⟨90417602058531880607171855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60278401372354587071447903 90417602058531880607171855)
      ·
        refine ⟨135626403087797820910757783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90417602058531880607171855 135626403087797820910757783)
        ·
          refine ⟨203439604631696731366136675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135626403087797820910757783 203439604631696731366136675)
          ·
            refine ⟨305159406947545097049205013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203439604631696731366136675 305159406947545097049205013)
            ·
              refine ⟨14304347200666176424181485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 305159406947545097049205013 14304347200666176424181485)
              ·
                refine ⟨5364130200249816159068057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14304347200666176424181485 5364130200249816159068057)
                ·
                  refine ⟨4023097650187362119301043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5364130200249816159068057 4023097650187362119301043)
                  ·
                    refine ⟨6034646475281043178951565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023097650187362119301043 6034646475281043178951565)
                    ·
                      refine ⟨2262992428230391192106837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034646475281043178951565 2262992428230391192106837)
                      ·
                        rfl

theorem cell23_4407162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_4407162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407162 prefixEnd_4407162 := by exact prefixLift 4407162
  have htrace : WordTrace (prefixWord ++ tailWord_4407162) baseStart_4407162 baseEnd_4407162 := by
    simpa [prefixWord, tailWord_4407162, baseEnd_4407162] using wordTrace_append hprefix tailTrace_4407162
  have hstable : (prefixWord ++ tailWord_4407162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407162).length < 2 ^ (prefixWord ++ tailWord_4407162).sum := by decide
  have hdescent : baseEnd_4407162 < baseStart_4407162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407168 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_4407168 : Nat := 118140960795 + 4407168 * 2 ^ 59
def prefixEnd_4407168 : Nat := 4983230072969 + 3 ^ 40 * 4407168 * 2
def baseEnd_4407168 : Nat := 2262995509114318168631809

theorem tailTrace_4407168 : CollatzResearch.WordTrace tailWord_4407168 prefixEnd_4407168 2262995509114318168631809 := by
  unfold tailWord_4407168
  simp only [CollatzResearch.WordTrace]
  refine ⟨80371311248795247607623079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107161748331726996810164105 80371311248795247607623079)
  ·
    refine ⟨120556966873192871411434619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80371311248795247607623079 120556966873192871411434619)
    ·
      refine ⟨180835450309789307117151929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120556966873192871411434619 180835450309789307117151929)
      ·
        refine ⟨135626587732341980337863947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180835450309789307117151929 135626587732341980337863947)
        ·
          refine ⟨203439881598512970506795921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135626587732341980337863947 203439881598512970506795921)
          ·
            refine ⟨152579911198884727880096941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203439881598512970506795921 152579911198884727880096941)
            ·
              refine ⟨57217466699581772955036353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152579911198884727880096941 57217466699581772955036353)
              ·
                refine ⟨42913100024686329716277265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57217466699581772955036353 42913100024686329716277265)
                ·
                  refine ⟨32184825018514747287207949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42913100024686329716277265 32184825018514747287207949)
                  ·
                    refine ⟨12069309381943030232702981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32184825018514747287207949 12069309381943030232702981)
                    ·
                      refine ⟨2262995509114318168631809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12069309381943030232702981 2262995509114318168631809)
                      ·
                        rfl

theorem cell23_4407168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_4407168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407168 prefixEnd_4407168 := by exact prefixLift 4407168
  have htrace : WordTrace (prefixWord ++ tailWord_4407168) baseStart_4407168 baseEnd_4407168 := by
    simpa [prefixWord, tailWord_4407168, baseEnd_4407168] using wordTrace_append hprefix tailTrace_4407168
  have hstable : (prefixWord ++ tailWord_4407168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407168).length < 2 ^ (prefixWord ++ tailWord_4407168).sum := by decide
  have hdescent : baseEnd_4407168 < baseStart_4407168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407172 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_4407172 : Nat := 118140960795 + 4407172 * 2 ^ 59
def prefixEnd_4407172 : Nat := 4983230072969 + 3 ^ 40 * 4407172 * 2
def baseEnd_4407172 : Nat := 2262997563036936152981791

theorem tailTrace_4407172 : CollatzResearch.WordTrace tailWord_4407172 prefixEnd_4407172 2262997563036936152981791 := by
  unfold tailWord_4407172
  simp only [CollatzResearch.WordTrace]
  refine ⟨80371384194788001949195885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107161845593050669265594513 80371384194788001949195885)
  ·
    refine ⟨30139269073045500730948457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80371384194788001949195885 30139269073045500730948457)
    ·
      refine ⟨22604451804784125548211343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30139269073045500730948457 22604451804784125548211343)
      ·
        refine ⟨33906677707176188322317015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22604451804784125548211343 33906677707176188322317015)
        ·
          refine ⟨50860016560764282483475523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33906677707176188322317015 50860016560764282483475523)
          ·
            refine ⟨76290024841146423725213285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50860016560764282483475523 76290024841146423725213285)
            ·
              refine ⟨14304379657714954448477491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76290024841146423725213285 14304379657714954448477491)
              ·
                refine ⟨21456569486572431672716237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14304379657714954448477491 21456569486572431672716237)
                ·
                  refine ⟨8046213557464661877268589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21456569486572431672716237 8046213557464661877268589)
                  ·
                    refine ⟨3017330084049248203975721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8046213557464661877268589 3017330084049248203975721)
                    ·
                      refine ⟨2262997563036936152981791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017330084049248203975721 2262997563036936152981791)
                      ·
                        rfl

theorem cell23_4407172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_4407172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407172 prefixEnd_4407172 := by exact prefixLift 4407172
  have htrace : WordTrace (prefixWord ++ tailWord_4407172) baseStart_4407172 baseEnd_4407172 := by
    simpa [prefixWord, tailWord_4407172, baseEnd_4407172] using wordTrace_append hprefix tailTrace_4407172
  have hstable : (prefixWord ++ tailWord_4407172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407172).length < 2 ^ (prefixWord ++ tailWord_4407172).sum := by decide
  have hdescent : baseEnd_4407172 < baseStart_4407172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407190 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4407190 : Nat := 118140960795 + 4407190 * 2 ^ 59
def prefixEnd_4407190 : Nat := 4983230072969 + 3 ^ 40 * 4407190 * 2
def baseEnd_4407190 : Nat := 754335601896239027518903

theorem tailTrace_4407190 : CollatzResearch.WordTrace tailWord_4407190 prefixEnd_4407190 754335601896239027518903 := by
  unfold tailWord_4407190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046464056469424560784189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107162283269007195315031349 10046464056469424560784189)
  ·
    refine ⟨3767424021176034210294071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10046464056469424560784189 3767424021176034210294071)
    ·
      refine ⟨5651136031764051315441107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767424021176034210294071 5651136031764051315441107)
      ·
        refine ⟨8476704047646076973161661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651136031764051315441107 8476704047646076973161661)
        ·
          refine ⟨3178764017867278864935623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8476704047646076973161661 3178764017867278864935623)
          ·
            refine ⟨4768146026800918297403435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178764017867278864935623 4768146026800918297403435)
            ·
              refine ⟨7152219040201377446105153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768146026800918297403435 7152219040201377446105153)
              ·
                refine ⟨5364164280151033084578865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152219040201377446105153 5364164280151033084578865)
                ·
                  refine ⟨4023123210113274813434149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5364164280151033084578865 4023123210113274813434149)
                  ·
                    refine ⟨754335601896239027518903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023123210113274813434149 754335601896239027518903)
                    ·
                      rfl

theorem cell23_4407190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4407190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407190 prefixEnd_4407190 := by exact prefixLift 4407190
  have htrace : WordTrace (prefixWord ++ tailWord_4407190) baseStart_4407190 baseEnd_4407190 := by
    simpa [prefixWord, tailWord_4407190, baseEnd_4407190] using wordTrace_append hprefix tailTrace_4407190
  have hstable : (prefixWord ++ tailWord_4407190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407190).length < 2 ^ (prefixWord ++ tailWord_4407190).sum := by decide
  have hdescent : baseEnd_4407190 < baseStart_4407190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407196 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4407196 : Nat := 118140960795 + 4407196 * 2 ^ 59
def prefixEnd_4407196 : Nat := 4983230072969 + 3 ^ 40 * 4407196 * 2
def baseEnd_4407196 : Nat := 2263009886572644059081681

theorem tailTrace_4407196 : CollatzResearch.WordTrace tailWord_4407196 prefixEnd_4407196 2263009886572644059081681 := by
  unfold tailWord_4407196
  simp only [CollatzResearch.WordTrace]
  refine ⟨80371821870744527998632721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107162429160992703998176961 80371821870744527998632721)
  ·
    refine ⟨60278866403058395998974541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80371821870744527998632721 60278866403058395998974541)
    ·
      refine ⟨22604574901146898499615453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60278866403058395998974541 22604574901146898499615453)
      ·
        refine ⟨8476715587930086937355795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22604574901146898499615453 8476715587930086937355795)
        ·
          refine ⟨12715073381895130406033693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8476715587930086937355795 12715073381895130406033693)
          ·
            refine ⟨4768152518210673902262635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12715073381895130406033693 4768152518210673902262635)
            ·
              refine ⟨7152228777316010853393953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768152518210673902262635 7152228777316010853393953)
              ·
                refine ⟨5364171582987008140045465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152228777316010853393953 5364171582987008140045465)
                ·
                  refine ⟨4023128687240256105034099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5364171582987008140045465 4023128687240256105034099)
                  ·
                    refine ⟨6034693030860384157551149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023128687240256105034099 6034693030860384157551149)
                    ·
                      refine ⟨2263009886572644059081681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034693030860384157551149 2263009886572644059081681)
                      ·
                        rfl

theorem cell23_4407196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4407196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407196 prefixEnd_4407196 := by exact prefixLift 4407196
  have htrace : WordTrace (prefixWord ++ tailWord_4407196) baseStart_4407196 baseEnd_4407196 := by
    simpa [prefixWord, tailWord_4407196, baseEnd_4407196] using wordTrace_append hprefix tailTrace_4407196
  have hstable : (prefixWord ++ tailWord_4407196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407196).length < 2 ^ (prefixWord ++ tailWord_4407196).sum := by decide
  have hdescent : baseEnd_4407196 < baseStart_4407196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407218 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_4407218 : Nat := 118140960795 + 4407218 * 2 ^ 59
def prefixEnd_4407218 : Nat := 4983230072969 + 3 ^ 40 * 4407218 * 2
def baseEnd_4407218 : Nat := 2263021183147042973006579

theorem tailTrace_4407218 : CollatzResearch.WordTrace tailWord_4407218 prefixEnd_4407218 2263021183147042973006579 := by
  unfold tailWord_4407218
  simp only [CollatzResearch.WordTrace]
  refine ⟨40186111536852338438641577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107162964098272902503044205 40186111536852338438641577)
  ·
    refine ⟨30139583652639253828981183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40186111536852338438641577 30139583652639253828981183)
    ·
      refine ⟨45209375478958880743471775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30139583652639253828981183 45209375478958880743471775)
      ·
        refine ⟨67814063218438321115207663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45209375478958880743471775 67814063218438321115207663)
        ·
          refine ⟨101721094827657481672811495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67814063218438321115207663 101721094827657481672811495)
          ·
            refine ⟨152581642241486222509217243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101721094827657481672811495 152581642241486222509217243)
            ·
              refine ⟨228872463362229333763825865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152581642241486222509217243 228872463362229333763825865)
              ·
                refine ⟨171654347521672000322869399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228872463362229333763825865 171654347521672000322869399)
                ·
                  refine ⟨257481521282508000484304099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171654347521672000322869399 257481521282508000484304099)
                  ·
                    refine ⟨386222281923762000726456149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 257481521282508000484304099 386222281923762000726456149)
                    ·
                      refine ⟨2263021183147042973006579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 386222281923762000726456149 2263021183147042973006579)
                      ·
                        rfl

theorem cell23_4407218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_4407218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407218 prefixEnd_4407218 := by exact prefixLift 4407218
  have htrace : WordTrace (prefixWord ++ tailWord_4407218) baseStart_4407218 baseEnd_4407218 := by
    simpa [prefixWord, tailWord_4407218, baseEnd_4407218] using wordTrace_append hprefix tailTrace_4407218
  have hstable : (prefixWord ++ tailWord_4407218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407218).length < 2 ^ (prefixWord ++ tailWord_4407218).sum := by decide
  have hdescent : baseEnd_4407218 < baseStart_4407218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407242 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_4407242 : Nat := 118140960795 + 4407242 * 2 ^ 59
def prefixEnd_4407242 : Nat := 4983230072969 + 3 ^ 40 * 4407242 * 2
def baseEnd_4407242 : Nat := 251448167409194542122941

theorem tailTrace_4407242 : CollatzResearch.WordTrace tailWord_4407242 prefixEnd_4407242 251448167409194542122941 := by
  unfold tailWord_4407242
  simp only [CollatzResearch.WordTrace]
  refine ⟨40186330374830601463359995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107163547666214937235626653 40186330374830601463359995)
  ·
    refine ⟨60279495562245902195039993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40186330374830601463359995 60279495562245902195039993)
    ·
      refine ⟨45209621671684426646279995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60279495562245902195039993 45209621671684426646279995)
      ·
        refine ⟨67814432507526639969419993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45209621671684426646279995 67814432507526639969419993)
        ·
          refine ⟨50860824380644979977064995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67814432507526639969419993 50860824380644979977064995)
          ·
            refine ⟨76291236570967469965597493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50860824380644979977064995 76291236570967469965597493)
            ·
              refine ⟨7152303428528200309274765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76291236570967469965597493 7152303428528200309274765)
              ·
                refine ⟨2682113785698075115978037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7152303428528200309274765 2682113785698075115978037)
                ·
                  refine ⟨251448167409194542122941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2682113785698075115978037 251448167409194542122941)
                  ·
                    rfl

theorem cell23_4407242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_4407242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407242 prefixEnd_4407242 := by exact prefixLift 4407242
  have htrace : WordTrace (prefixWord ++ tailWord_4407242) baseStart_4407242 baseEnd_4407242 := by
    simpa [prefixWord, tailWord_4407242, baseEnd_4407242] using wordTrace_append hprefix tailTrace_4407242
  have hstable : (prefixWord ++ tailWord_4407242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407242).length < 2 ^ (prefixWord ++ tailWord_4407242).sum := by decide
  have hdescent : baseEnd_4407242 < baseStart_4407242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407255 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 2, 5]
def baseStart_4407255 : Nat := 118140960795 + 4407255 * 2 ^ 59
def prefixEnd_4407255 : Nat := 4983230072969 + 3 ^ 40 * 4407255 * 2
def baseEnd_4407255 : Nat := 754346727310419776081303

theorem tailTrace_4407255 : CollatzResearch.WordTrace tailWord_4407255 prefixEnd_4407255 754346727310419776081303 := by
  unfold tailWord_4407255
  simp only [CollatzResearch.WordTrace]
  refine ⟨160745795648275309073663219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107163863765516872715775479 160745795648275309073663219)
  ·
    refine ⟨241118693472412963610494829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160745795648275309073663219 241118693472412963610494829)
    ·
      refine ⟨90419510052154861353935561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241118693472412963610494829 90419510052154861353935561)
      ·
        refine ⟨67814632539116146015451671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90419510052154861353935561 67814632539116146015451671)
        ·
          refine ⟨101721948808674219023177507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67814632539116146015451671 101721948808674219023177507)
          ·
            refine ⟨152582923213011328534766261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101721948808674219023177507 152582923213011328534766261)
            ·
              refine ⟨14304649051219812050134337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152582923213011328534766261 14304649051219812050134337)
              ·
                refine ⟨10728486788414859037600753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14304649051219812050134337 10728486788414859037600753)
                ·
                  refine ⟨8046365091311144278200565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10728486788414859037600753 8046365091311144278200565)
                  ·
                    refine ⟨754346727310419776081303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8046365091311144278200565 754346727310419776081303)
                    ·
                      rfl

theorem cell23_4407255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_4407255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407255 prefixEnd_4407255 := by exact prefixLift 4407255
  have htrace : WordTrace (prefixWord ++ tailWord_4407255) baseStart_4407255 baseEnd_4407255 := by
    simpa [prefixWord, tailWord_4407255, baseEnd_4407255] using wordTrace_append hprefix tailTrace_4407255
  have hstable : (prefixWord ++ tailWord_4407255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407255).length < 2 ^ (prefixWord ++ tailWord_4407255).sum := by decide
  have hdescent : baseEnd_4407255 < baseStart_4407255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407292 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_4407292 : Nat := 118140960795 + 4407292 * 2 ^ 59
def prefixEnd_4407292 : Nat := 4983230072969 + 3 ^ 40 * 4407292 * 2
def baseEnd_4407292 : Nat := 2263059180715475683481239

theorem tailTrace_4407292 : CollatzResearch.WordTrace tailWord_4407292 prefixEnd_4407292 2263059180715475683481239 := by
  unfold tailWord_4407292
  simp only [CollatzResearch.WordTrace]
  refine ⟨80373572574570632196380065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107164763432760842928506753 80373572574570632196380065)
  ·
    refine ⟨60280179430927974147285049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80373572574570632196380065 60280179430927974147285049)
    ·
      refine ⟨45210134573195980610463787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60280179430927974147285049 45210134573195980610463787)
      ·
        refine ⟨67815201859793970915695681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45210134573195980610463787 67815201859793970915695681)
        ·
          refine ⟨50861401394845478186771761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67815201859793970915695681 50861401394845478186771761)
          ·
            refine ⟨38146051046134108640078821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50861401394845478186771761 38146051046134108640078821)
            ·
              refine ⟨7152384571150145370014779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38146051046134108640078821 7152384571150145370014779)
              ·
                refine ⟨10728576856725218055022169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7152384571150145370014779 10728576856725218055022169)
                ·
                  refine ⟨8046432642543913541266627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10728576856725218055022169 8046432642543913541266627)
                  ·
                    refine ⟨12069648963815870311899941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8046432642543913541266627 12069648963815870311899941)
                    ·
                      refine ⟨2263059180715475683481239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12069648963815870311899941 2263059180715475683481239)
                      ·
                        rfl

theorem cell23_4407292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_4407292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407292 prefixEnd_4407292 := by exact prefixLift 4407292
  have htrace : WordTrace (prefixWord ++ tailWord_4407292) baseStart_4407292 baseEnd_4407292 := by
    simpa [prefixWord, tailWord_4407292, baseEnd_4407292] using wordTrace_append hprefix tailTrace_4407292
  have hstable : (prefixWord ++ tailWord_4407292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407292).length < 2 ^ (prefixWord ++ tailWord_4407292).sum := by decide
  have hdescent : baseEnd_4407292 < baseStart_4407292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407295 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_4407295 : Nat := 118140960795 + 4407295 * 2 ^ 59
def prefixEnd_4407295 : Nat := 4983230072969 + 3 ^ 40 * 4407295 * 2
def baseEnd_4407295 : Nat := 2263060721157439171743725

theorem tailTrace_4407295 : CollatzResearch.WordTrace tailWord_4407295 prefixEnd_4407295 2263060721157439171743725 := by
  unfold tailWord_4407295
  simp only [CollatzResearch.WordTrace]
  refine ⟨160747254568130395905119339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107164836378753597270079559 160747254568130395905119339)
  ·
    refine ⟨241120881852195593857679009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160747254568130395905119339 241120881852195593857679009)
    ·
      refine ⟨180840661389146695393259257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241120881852195593857679009 180840661389146695393259257)
      ·
        refine ⟨135630496041860021544944443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180840661389146695393259257 135630496041860021544944443)
        ·
          refine ⟨203445744062790032317416665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135630496041860021544944443 203445744062790032317416665)
          ·
            refine ⟨152584308047092524238062499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203445744062790032317416665 152584308047092524238062499)
            ·
              refine ⟨228876462070638786357093749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152584308047092524238062499 228876462070638786357093749)
              ·
                refine ⟨21457168319122386220977539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228876462070638786357093749 21457168319122386220977539)
                ·
                  refine ⟨32185752478683579331466309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21457168319122386220977539 32185752478683579331466309)
                  ·
                    refine ⟨6034828589753171124649933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32185752478683579331466309 6034828589753171124649933)
                    ·
                      refine ⟨2263060721157439171743725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6034828589753171124649933 2263060721157439171743725)
                      ·
                        rfl

theorem cell23_4407295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_4407295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407295 prefixEnd_4407295 := by exact prefixLift 4407295
  have htrace : WordTrace (prefixWord ++ tailWord_4407295) baseStart_4407295 baseEnd_4407295 := by
    simpa [prefixWord, tailWord_4407295, baseEnd_4407295] using wordTrace_append hprefix tailTrace_4407295
  have hstable : (prefixWord ++ tailWord_4407295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407295).length < 2 ^ (prefixWord ++ tailWord_4407295).sum := by decide
  have hdescent : baseEnd_4407295 < baseStart_4407295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407315 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 6]
def baseStart_4407315 : Nat := 118140960795 + 4407315 * 2 ^ 59
def prefixEnd_4407315 : Nat := 4983230072969 + 3 ^ 40 * 4407315 * 2
def baseEnd_4407315 : Nat := 251452332307836565943737

theorem tailTrace_4407315 : CollatzResearch.WordTrace tailWord_4407315 prefixEnd_4407315 251452332307836565943737 := by
  unfold tailWord_4407315
  simp only [CollatzResearch.WordTrace]
  refine ⟨160747984028057939320847399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107165322685371959547231599 160747984028057939320847399)
  ·
    refine ⟨241121976042086908981271099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160747984028057939320847399 241121976042086908981271099)
    ·
      refine ⟨361682964063130363471906649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241121976042086908981271099 361682964063130363471906649)
      ·
        refine ⟨271262223047347772603929987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361682964063130363471906649 271262223047347772603929987)
        ·
          refine ⟨406893334571021658905894981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271262223047347772603929987 406893334571021658905894981)
          ·
            refine ⟨76292500232066561044855309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 406893334571021658905894981 76292500232066561044855309)
            ·
              refine ⟨28609687587024960391820741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76292500232066561044855309 28609687587024960391820741)
              ·
                refine ⟨5364316422567180073466389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28609687587024960391820741 5364316422567180073466389)
                ·
                  refine ⟨251452332307836565943737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5364316422567180073466389 251452332307836565943737)
                  ·
                    rfl

theorem cell23_4407315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 6].length) (baseStart_4407315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407315 prefixEnd_4407315 := by exact prefixLift 4407315
  have htrace : WordTrace (prefixWord ++ tailWord_4407315) baseStart_4407315 baseEnd_4407315 := by
    simpa [prefixWord, tailWord_4407315, baseEnd_4407315] using wordTrace_append hprefix tailTrace_4407315
  have hstable : (prefixWord ++ tailWord_4407315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407315).length < 2 ^ (prefixWord ++ tailWord_4407315).sum := by decide
  have hdescent : baseEnd_4407315 < baseStart_4407315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407336 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4407336 : Nat := 118140960795 + 4407336 * 2 ^ 59
def prefixEnd_4407336 : Nat := 4983230072969 + 3 ^ 40 * 4407336 * 2
def baseEnd_4407336 : Nat := 754360591288091170443679

theorem tailTrace_4407336 : CollatzResearch.WordTrace tailWord_4407336 prefixEnd_4407336 754360591288091170443679 := by
  unfold tailWord_4407336
  simp only [CollatzResearch.WordTrace]
  refine ⟨80374374980490929953680931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107165833307321239938241241 80374374980490929953680931)
  ·
    refine ⟨120561562470736394930521397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80374374980490929953680931 120561562470736394930521397)
    ·
      refine ⟨11302646481631537024736381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120561562470736394930521397 11302646481631537024736381)
      ·
        refine ⟨4238492430611826384276143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11302646481631537024736381 4238492430611826384276143)
        ·
          refine ⟨6357738645917739576414215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238492430611826384276143 6357738645917739576414215)
          ·
            refine ⟨9536607968876609364621323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6357738645917739576414215 9536607968876609364621323)
            ·
              refine ⟨14304911953314914046931985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9536607968876609364621323 14304911953314914046931985)
              ·
                refine ⟨10728683964986185535198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14304911953314914046931985 10728683964986185535198989)
                ·
                  refine ⟨4023256486869819575699621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10728683964986185535198989 4023256486869819575699621)
                  ·
                    refine ⟨754360591288091170443679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023256486869819575699621 754360591288091170443679)
                    ·
                      rfl

theorem cell23_4407336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4407336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407336 prefixEnd_4407336 := by exact prefixLift 4407336
  have htrace : WordTrace (prefixWord ++ tailWord_4407336) baseStart_4407336 baseEnd_4407336 := by
    simpa [prefixWord, tailWord_4407336, baseEnd_4407336] using wordTrace_append hprefix tailTrace_4407336
  have hstable : (prefixWord ++ tailWord_4407336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407336).length < 2 ^ (prefixWord ++ tailWord_4407336).sum := by decide
  have hdescent : baseEnd_4407336 < baseStart_4407336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407392 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 1, 6]
def baseStart_4407392 : Nat := 118140960795 + 4407392 * 2 ^ 59
def prefixEnd_4407392 : Nat := 4983230072969 + 3 ^ 40 * 4407392 * 2
def baseEnd_4407392 : Nat := 754370176260308430743593

theorem tailTrace_4407392 : CollatzResearch.WordTrace tailWord_4407392 prefixEnd_4407392 754370176260308430743593 := by
  unfold tailWord_4407392
  simp only [CollatzResearch.WordTrace]
  refine ⟨80375396224389490735700215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107167194965852654314266953 80375396224389490735700215)
  ·
    refine ⟨120563094336584236103550323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80375396224389490735700215 120563094336584236103550323)
    ·
      refine ⟨180844641504876354155325485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120563094336584236103550323 180844641504876354155325485)
      ·
        refine ⟨67816740564328632808247057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180844641504876354155325485 67816740564328632808247057)
        ·
          refine ⟨50862555423246474606185293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67816740564328632808247057 50862555423246474606185293)
          ·
            refine ⟨19073458283717427977319485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50862555423246474606185293 19073458283717427977319485)
            ·
              refine ⟨7152546856394035491494807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19073458283717427977319485 7152546856394035491494807)
              ·
                refine ⟨10728820284591053237242211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7152546856394035491494807 10728820284591053237242211)
                ·
                  refine ⟨16093230426886579855863317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10728820284591053237242211 16093230426886579855863317)
                  ·
                    refine ⟨754370176260308430743593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16093230426886579855863317 754370176260308430743593)
                    ·
                      rfl

theorem cell23_4407392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_4407392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407392 prefixEnd_4407392 := by exact prefixLift 4407392
  have htrace : WordTrace (prefixWord ++ tailWord_4407392) baseStart_4407392 baseEnd_4407392 := by
    simpa [prefixWord, tailWord_4407392, baseEnd_4407392] using wordTrace_append hprefix tailTrace_4407392
  have hstable : (prefixWord ++ tailWord_4407392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407392).length < 2 ^ (prefixWord ++ tailWord_4407392).sum := by decide
  have hdescent : baseEnd_4407392 < baseStart_4407392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407399 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_4407399 : Nat := 118140960795 + 4407399 * 2 ^ 59
def prefixEnd_4407399 : Nat := 4983230072969 + 3 ^ 40 * 4407399 * 2
def baseEnd_4407399 : Nat := 2263114123145506764843247

theorem tailTrace_4407399 : CollatzResearch.WordTrace tailWord_4407399 prefixEnd_4407399 2263114123145506764843247 := by
  unfold tailWord_4407399
  simp only [CollatzResearch.WordTrace]
  refine ⟨160751047759753621666905251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107167365173169081111270167 160751047759753621666905251)
  ·
    refine ⟨241126571639630432500357877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160751047759753621666905251 241126571639630432500357877)
    ·
      refine ⟨22605616091215353046908551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241126571639630432500357877 22605616091215353046908551)
      ·
        refine ⟨33908424136823029570362827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22605616091215353046908551 33908424136823029570362827)
        ·
          refine ⟨50862636205234544355544241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33908424136823029570362827 50862636205234544355544241)
          ·
            refine ⟨38146977153925908266658181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50862636205234544355544241 38146977153925908266658181)
            ·
              refine ⟨7152558216361107799998409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38146977153925908266658181 7152558216361107799998409)
              ·
                refine ⟨5364418662270830849998807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152558216361107799998409 5364418662270830849998807)
                ·
                  refine ⟨8046627993406246274998211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5364418662270830849998807 8046627993406246274998211)
                  ·
                    refine ⟨12069941990109369412497317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8046627993406246274998211 12069941990109369412497317)
                    ·
                      refine ⟨2263114123145506764843247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12069941990109369412497317 2263114123145506764843247)
                      ·
                        rfl

theorem cell23_4407399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_4407399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407399 prefixEnd_4407399 := by exact prefixLift 4407399
  have htrace : WordTrace (prefixWord ++ tailWord_4407399) baseStart_4407399 baseEnd_4407399 := by
    simpa [prefixWord, tailWord_4407399, baseEnd_4407399] using wordTrace_append hprefix tailTrace_4407399
  have hstable : (prefixWord ++ tailWord_4407399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407399).length < 2 ^ (prefixWord ++ tailWord_4407399).sum := by decide
  have hdescent : baseEnd_4407399 < baseStart_4407399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407442 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4407442 : Nat := 118140960795 + 4407442 * 2 ^ 59
def prefixEnd_4407442 : Nat := 4983230072969 + 3 ^ 40 * 4407442 * 2
def baseEnd_4407442 : Nat := 2263136202813650096605549

theorem tailTrace_4407442 : CollatzResearch.WordTrace tailWord_4407442 prefixEnd_4407442 2263136202813650096605549 := by
  unfold tailWord_4407442
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188154024649460002680145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107168410732398560007147053 40188154024649460002680145)
  ·
    refine ⟨30141115518487095002010109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40188154024649460002680145 30141115518487095002010109)
    ·
      refine ⟨11302918319432660625753791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30141115518487095002010109 11302918319432660625753791)
      ·
        refine ⟨16954377479148990938630687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11302918319432660625753791 16954377479148990938630687)
        ·
          refine ⟨25431566218723486407946031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16954377479148990938630687 25431566218723486407946031)
          ·
            refine ⟨38147349328085229611919047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25431566218723486407946031 38147349328085229611919047)
            ·
              refine ⟨57221023992127844417878571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38147349328085229611919047 57221023992127844417878571)
              ·
                refine ⟨85831535988191766626817857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57221023992127844417878571 85831535988191766626817857)
                ·
                  refine ⟨64373651991143824970113393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85831535988191766626817857 64373651991143824970113393)
                  ·
                    refine ⟨48280238993357868727585045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64373651991143824970113393 48280238993357868727585045)
                    ·
                      refine ⟨2263136202813650096605549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48280238993357868727585045 2263136202813650096605549)
                      ·
                        rfl

theorem cell23_4407442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4407442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407442 prefixEnd_4407442 := by exact prefixLift 4407442
  have htrace : WordTrace (prefixWord ++ tailWord_4407442) baseStart_4407442 baseEnd_4407442 := by
    simpa [prefixWord, tailWord_4407442, baseEnd_4407442] using wordTrace_append hprefix tailTrace_4407442
  have hstable : (prefixWord ++ tailWord_4407442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407442).length < 2 ^ (prefixWord ++ tailWord_4407442).sum := by decide
  have hdescent : baseEnd_4407442 < baseStart_4407442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407470 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4407470 : Nat := 118140960795 + 4407470 * 2 ^ 59
def prefixEnd_4407470 : Nat := 4983230072969 + 3 ^ 40 * 4407470 * 2
def baseEnd_4407470 : Nat := 2263150580271975987055421

theorem tailTrace_4407470 : CollatzResearch.WordTrace tailWord_4407470 prefixEnd_4407470 2263150580271975987055421 := by
  unfold tailWord_4407470
  simp only [CollatzResearch.WordTrace]
  refine ⟨20094204667812050099092483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107169091561664267195159909 20094204667812050099092483)
  ·
    refine ⟨30141307001718075148638725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20094204667812050099092483 30141307001718075148638725)
    ·
      refine ⟨5651495062822139090369761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30141307001718075148638725 5651495062822139090369761)
      ·
        refine ⟨4238621297116604317777321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5651495062822139090369761 4238621297116604317777321)
        ·
          refine ⟨3178965972837453238332991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4238621297116604317777321 3178965972837453238332991)
          ·
            refine ⟨4768448959256179857499487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178965972837453238332991 4768448959256179857499487)
            ·
              refine ⟨7152673438884269786249231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768448959256179857499487 7152673438884269786249231)
              ·
                refine ⟨10729010158326404679373847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7152673438884269786249231 10729010158326404679373847)
                ·
                  refine ⟨16093515237489607019060771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729010158326404679373847 16093515237489607019060771)
                  ·
                    refine ⟨24140272856234410528591157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16093515237489607019060771 24140272856234410528591157)
                    ·
                      refine ⟨2263150580271975987055421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24140272856234410528591157 2263150580271975987055421)
                      ·
                        rfl

theorem cell23_4407470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4407470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407470 prefixEnd_4407470 := by exact prefixLift 4407470
  have htrace : WordTrace (prefixWord ++ tailWord_4407470) baseStart_4407470 baseEnd_4407470 := by
    simpa [prefixWord, tailWord_4407470, baseEnd_4407470] using wordTrace_append hprefix tailTrace_4407470
  have hstable : (prefixWord ++ tailWord_4407470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407470).length < 2 ^ (prefixWord ++ tailWord_4407470).sum := by decide
  have hdescent : baseEnd_4407470 < baseStart_4407470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407484 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_4407484 : Nat := 118140960795 + 4407484 * 2 ^ 59
def prefixEnd_4407484 : Nat := 4983230072969 + 3 ^ 40 * 4407484 * 2
def baseEnd_4407484 : Nat := 2263157769001138932280357

theorem tailTrace_4407484 : CollatzResearch.WordTrace tailWord_4407484 prefixEnd_4407484 2263157769001138932280357 := by
  unfold tailWord_4407484
  simp only [CollatzResearch.WordTrace]
  refine ⟨80377073982222840591874753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107169431976297120789166337 80377073982222840591874753)
  ·
    refine ⟨60282805486667130443906065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80377073982222840591874753 60282805486667130443906065)
    ·
      refine ⟨45212104115000347832929549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60282805486667130443906065 45212104115000347832929549)
      ·
        refine ⟨16954539043125130437348581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45212104115000347832929549 16954539043125130437348581)
        ·
          refine ⟨3178976070585961957002859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16954539043125130437348581 3178976070585961957002859)
          ·
            refine ⟨4768464105878942935504289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178976070585961957002859 4768464105878942935504289)
            ·
              refine ⟨3576348079409207201628217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4768464105878942935504289 3576348079409207201628217)
              ·
                refine ⟨2682261059556905401221163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3576348079409207201628217 2682261059556905401221163)
                ·
                  refine ⟨4023391589335358101831745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682261059556905401221163 4023391589335358101831745)
                  ·
                    refine ⟨3017543692001518576373809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023391589335358101831745 3017543692001518576373809)
                    ·
                      refine ⟨2263157769001138932280357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017543692001518576373809 2263157769001138932280357)
                      ·
                        rfl

theorem cell23_4407484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_4407484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407484 prefixEnd_4407484 := by exact prefixLift 4407484
  have htrace : WordTrace (prefixWord ++ tailWord_4407484) baseStart_4407484 baseEnd_4407484 := by
    simpa [prefixWord, tailWord_4407484, baseEnd_4407484] using wordTrace_append hprefix tailTrace_4407484
  have hstable : (prefixWord ++ tailWord_4407484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407484).length < 2 ^ (prefixWord ++ tailWord_4407484).sum := by decide
  have hdescent : baseEnd_4407484 < baseStart_4407484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407506 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_4407506 : Nat := 118140960795 + 4407506 * 2 ^ 59
def prefixEnd_4407506 : Nat := 4983230072969 + 3 ^ 40 * 4407506 * 2
def baseEnd_4407506 : Nat := 2263169065575537846205255

theorem tailTrace_4407506 : CollatzResearch.WordTrace tailWord_4407506 prefixEnd_4407506 2263169065575537846205255 := by
  unfold tailWord_4407506
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188737592591494735262593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107169966913577319294033581 40188737592591494735262593)
  ·
    refine ⟨30141553194443621051446945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40188737592591494735262593 30141553194443621051446945)
    ·
      refine ⟨22606164895832715788585209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30141553194443621051446945 22606164895832715788585209)
      ·
        refine ⟨16954623671874536841438907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22606164895832715788585209 16954623671874536841438907)
        ·
          refine ⟨25431935507811805262158361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16954623671874536841438907 25431935507811805262158361)
          ·
            refine ⟨19073951630858853946618771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25431935507811805262158361 19073951630858853946618771)
            ·
              refine ⟨28610927446288280919928157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19073951630858853946618771 28610927446288280919928157)
              ·
                refine ⟨10729097792358105344973059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28610927446288280919928157 10729097792358105344973059)
                ·
                  refine ⟨16093646688537158017459589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729097792358105344973059 16093646688537158017459589)
                  ·
                    refine ⟨3017558754100717128273673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16093646688537158017459589 3017558754100717128273673)
                    ·
                      refine ⟨2263169065575537846205255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017558754100717128273673 2263169065575537846205255)
                      ·
                        rfl

theorem cell23_4407506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_4407506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407506 prefixEnd_4407506 := by exact prefixLift 4407506
  have htrace : WordTrace (prefixWord ++ tailWord_4407506) baseStart_4407506 baseEnd_4407506 := by
    simpa [prefixWord, tailWord_4407506, baseEnd_4407506] using wordTrace_append hprefix tailTrace_4407506
  have hstable : (prefixWord ++ tailWord_4407506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407506).length < 2 ^ (prefixWord ++ tailWord_4407506).sum := by decide
  have hdescent : baseEnd_4407506 < baseStart_4407506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407512 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 9]
def baseStart_4407512 : Nat := 118140960795 + 4407512 * 2 ^ 59
def prefixEnd_4407512 : Nat := 4983230072969 + 3 ^ 40 * 4407512 * 2
def baseEnd_4407512 : Nat := 251463571828829424747803

theorem tailTrace_4407512 : CollatzResearch.WordTrace tailWord_4407512 prefixEnd_4407512 251463571828829424747803 := by
  unfold tailWord_4407512
  simp only [CollatzResearch.WordTrace]
  refine ⟨80377584604172120982884395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107170112805562827977179193 80377584604172120982884395)
  ·
    refine ⟨120566376906258181474326593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80377584604172120982884395 120566376906258181474326593)
    ·
      refine ⟨90424782679693636105744945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120566376906258181474326593 90424782679693636105744945)
      ·
        refine ⟨67818587009770227079308709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90424782679693636105744945 67818587009770227079308709)
        ·
          refine ⟨12715985064331917577370383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67818587009770227079308709 12715985064331917577370383)
          ·
            refine ⟨19073977596497876366055575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12715985064331917577370383 19073977596497876366055575)
            ·
              refine ⟨28610966394746814549083363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19073977596497876366055575 28610966394746814549083363)
              ·
                refine ⟨42916449592120221823625045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28610966394746814549083363 42916449592120221823625045)
                ·
                  refine ⟨251463571828829424747803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42916449592120221823625045 251463571828829424747803)
                  ·
                    rfl

theorem cell23_4407512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_4407512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407512 prefixEnd_4407512 := by exact prefixLift 4407512
  have htrace : WordTrace (prefixWord ++ tailWord_4407512) baseStart_4407512 baseEnd_4407512 := by
    simpa [prefixWord, tailWord_4407512, baseEnd_4407512] using wordTrace_append hprefix tailTrace_4407512
  have hstable : (prefixWord ++ tailWord_4407512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407512).length < 2 ^ (prefixWord ++ tailWord_4407512).sum := by decide
  have hdescent : baseEnd_4407512 < baseStart_4407512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407549 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_4407549 : Nat := 118140960795 + 4407549 * 2 ^ 59
def prefixEnd_4407549 : Nat := 4983230072969 + 3 ^ 40 * 4407549 * 2
def baseEnd_4407549 : Nat := 2263191145243681177967557

theorem tailTrace_4407549 : CollatzResearch.WordTrace tailWord_4407549 prefixEnd_4407549 2263191145243681177967557 := by
  unfold tailWord_4407549
  simp only [CollatzResearch.WordTrace]
  refine ⟨160756518709210197284865701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107171012472806798189910467 160756518709210197284865701)
  ·
    refine ⟨30141847257976911990912319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160756518709210197284865701 30141847257976911990912319)
    ·
      refine ⟨45212770886965367986368479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30141847257976911990912319 45212770886965367986368479)
      ·
        refine ⟨67819156330448051979552719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45212770886965367986368479 67819156330448051979552719)
        ·
          refine ⟨101728734495672077969329079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67819156330448051979552719 101728734495672077969329079)
          ·
            refine ⟨152593101743508116953993619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101728734495672077969329079 152593101743508116953993619)
            ·
              refine ⟨228889652615262175430990429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152593101743508116953993619 228889652615262175430990429)
              ·
                refine ⟨85833619730723315786621411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228889652615262175430990429 85833619730723315786621411)
                ·
                  refine ⟨128750429596084973679932117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85833619730723315786621411 128750429596084973679932117)
                  ·
                    refine ⟨3017588193658241570623409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 128750429596084973679932117 3017588193658241570623409)
                    ·
                      refine ⟨2263191145243681177967557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017588193658241570623409 2263191145243681177967557)
                      ·
                        rfl

theorem cell23_4407549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_4407549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407549 prefixEnd_4407549 := by exact prefixLift 4407549
  have htrace : WordTrace (prefixWord ++ tailWord_4407549) baseStart_4407549 baseEnd_4407549 := by
    simpa [prefixWord, tailWord_4407549, baseEnd_4407549] using wordTrace_append hprefix tailTrace_4407549
  have hstable : (prefixWord ++ tailWord_4407549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407549).length < 2 ^ (prefixWord ++ tailWord_4407549).sum := by decide
  have hdescent : baseEnd_4407549 < baseStart_4407549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407552 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_4407552 : Nat := 118140960795 + 4407552 * 2 ^ 59
def prefixEnd_4407552 : Nat := 4983230072969 + 3 ^ 40 * 4407552 * 2
def baseEnd_4407552 : Nat := 2263192685685644666230043

theorem tailTrace_4407552 : CollatzResearch.WordTrace tailWord_4407552 prefixEnd_4407552 2263192685685644666230043 := by
  unfold tailWord_4407552
  simp only [CollatzResearch.WordTrace]
  refine ⟨80378314064099664398612455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107171085418799552531483273 80378314064099664398612455)
  ·
    refine ⟨120567471096149496597918683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80378314064099664398612455 120567471096149496597918683)
    ·
      refine ⟨180851206644224244896878025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120567471096149496597918683 180851206644224244896878025)
      ·
        refine ⟨135638404983168183672658519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180851206644224244896878025 135638404983168183672658519)
        ·
          refine ⟨203457607474752275508987779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135638404983168183672658519 203457607474752275508987779)
          ·
            refine ⟨305186411212128413263481669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203457607474752275508987779 305186411212128413263481669)
            ·
              refine ⟨57222452102274077486902813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305186411212128413263481669 57222452102274077486902813)
              ·
                refine ⟨21458419538352779057588555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57222452102274077486902813 21458419538352779057588555)
                ·
                  refine ⟨32187629307529168586382833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21458419538352779057588555 32187629307529168586382833)
                  ·
                    refine ⟨24140721980646876439787125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32187629307529168586382833 24140721980646876439787125)
                    ·
                      refine ⟨2263192685685644666230043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24140721980646876439787125 2263192685685644666230043)
                      ·
                        rfl

theorem cell23_4407552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_4407552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407552 prefixEnd_4407552 := by exact prefixLift 4407552
  have htrace : WordTrace (prefixWord ++ tailWord_4407552) baseStart_4407552 baseEnd_4407552 := by
    simpa [prefixWord, tailWord_4407552, baseEnd_4407552] using wordTrace_append hprefix tailTrace_4407552
  have hstable : (prefixWord ++ tailWord_4407552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407552).length < 2 ^ (prefixWord ++ tailWord_4407552).sum := by decide
  have hdescent : baseEnd_4407552 < baseStart_4407552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407579 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 6, 2]
def baseStart_4407579 : Nat := 118140960795 + 4407579 * 2 ^ 59
def prefixEnd_4407579 : Nat := 4983230072969 + 3 ^ 40 * 4407579 * 2
def baseEnd_4407579 : Nat := 2263206549663316060592419

theorem tailTrace_4407579 : CollatzResearch.WordTrace tailWord_4407579 prefixEnd_4407579 2263206549663316060592419 := by
  unfold tailWord_4407579
  simp only [CollatzResearch.WordTrace]
  refine ⟨160757612899101512408457791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107171741932734341605638527 160757612899101512408457791)
  ·
    refine ⟨241136419348652268612686687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160757612899101512408457791 241136419348652268612686687)
    ·
      refine ⟨361704629022978402919030031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241136419348652268612686687 361704629022978402919030031)
      ·
        refine ⟨542556943534467604378545047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361704629022978402919030031 542556943534467604378545047)
        ·
          refine ⟨813835415301701406567817571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542556943534467604378545047 813835415301701406567817571)
          ·
            refine ⟨1220753122952552109851726357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813835415301701406567817571 1220753122952552109851726357)
            ·
              refine ⟨57222802638400880149299673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1220753122952552109851726357 57222802638400880149299673)
              ·
                refine ⟨42917101978800660111974755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57222802638400880149299673 42917101978800660111974755)
                ·
                  refine ⟨64375652968200990167962133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42917101978800660111974755 64375652968200990167962133)
                  ·
                    refine ⟨3017608732884421414123225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64375652968200990167962133 3017608732884421414123225)
                    ·
                      refine ⟨2263206549663316060592419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017608732884421414123225 2263206549663316060592419)
                      ·
                        rfl

theorem cell23_4407579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6, 2].length) (baseStart_4407579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407579 prefixEnd_4407579 := by exact prefixLift 4407579
  have htrace : WordTrace (prefixWord ++ tailWord_4407579) baseStart_4407579 baseEnd_4407579 := by
    simpa [prefixWord, tailWord_4407579, baseEnd_4407579] using wordTrace_append hprefix tailTrace_4407579
  have hstable : (prefixWord ++ tailWord_4407579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407579).length < 2 ^ (prefixWord ++ tailWord_4407579).sum := by decide
  have hdescent : baseEnd_4407579 < baseStart_4407579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407599 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_4407599 : Nat := 118140960795 + 4407599 * 2 ^ 59
def prefixEnd_4407599 : Nat := 4983230072969 + 3 ^ 40 * 4407599 * 2
def baseEnd_4407599 : Nat := 2263216819276405982342327

theorem tailTrace_4407599 : CollatzResearch.WordTrace tailWord_4407599 prefixEnd_4407599 2263216819276405982342327 := by
  unfold tailWord_4407599
  simp only [CollatzResearch.WordTrace]
  refine ⟨160758342359029055824185851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107172228239352703882790567 160758342359029055824185851)
  ·
    refine ⟨241137513538543583736278777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160758342359029055824185851 241137513538543583736278777)
    ·
      refine ⟨180853135153907687802209083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241137513538543583736278777 180853135153907687802209083)
      ·
        refine ⟨271279702730861531703313625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180853135153907687802209083 271279702730861531703313625)
        ·
          refine ⟨203459777048146148777485219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271279702730861531703313625 203459777048146148777485219)
          ·
            refine ⟨305189665572219223166227829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203459777048146148777485219 305189665572219223166227829)
            ·
              refine ⟨28611531147395552171833859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 305189665572219223166227829 28611531147395552171833859)
              ·
                refine ⟨42917296721093328257750789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28611531147395552171833859 42917296721093328257750789)
                ·
                  refine ⟨8046993135204999048328273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42917296721093328257750789 8046993135204999048328273)
                  ·
                    refine ⟨6035244851403749286246205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8046993135204999048328273 6035244851403749286246205)
                    ·
                      refine ⟨2263216819276405982342327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6035244851403749286246205 2263216819276405982342327)
                      ·
                        rfl

theorem cell23_4407599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_4407599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407599 prefixEnd_4407599 := by exact prefixLift 4407599
  have htrace : WordTrace (prefixWord ++ tailWord_4407599) baseStart_4407599 baseEnd_4407599 := by
    simpa [prefixWord, tailWord_4407599, baseEnd_4407599] using wordTrace_append hprefix tailTrace_4407599
  have hstable : (prefixWord ++ tailWord_4407599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407599).length < 2 ^ (prefixWord ++ tailWord_4407599).sum := by decide
  have hdescent : baseEnd_4407599 < baseStart_4407599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407690 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4407690 : Nat := 118140960795 + 4407690 * 2 ^ 59
def prefixEnd_4407690 : Nat := 4983230072969 + 3 ^ 40 * 4407690 * 2
def baseEnd_4407690 : Nat := 2263263546015965126304409

theorem tailTrace_4407690 : CollatzResearch.WordTrace tailWord_4407690 prefixEnd_4407690 2263263546015965126304409 := by
  unfold tailWord_4407690
  simp only [CollatzResearch.WordTrace]
  refine ⟨40190415350424844591437131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107174440934466252243832349 40190415350424844591437131)
  ·
    refine ⟨60285623025637266887155697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40190415350424844591437131 60285623025637266887155697)
    ·
      refine ⟨45214217269227950165366773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60285623025637266887155697 45214217269227950165366773)
      ·
        refine ⟨4238832868990120328003135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45214217269227950165366773 4238832868990120328003135)
        ·
          refine ⟨6358249303485180492004703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238832868990120328003135 6358249303485180492004703)
          ·
            refine ⟨9537373955227770738007055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358249303485180492004703 9537373955227770738007055)
            ·
              refine ⟨14306060932841656107010583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537373955227770738007055 14306060932841656107010583)
              ·
                refine ⟨21459091399262484160515875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14306060932841656107010583 21459091399262484160515875)
                ·
                  refine ⟨32188637098893726240773813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21459091399262484160515875 32188637098893726240773813)
                  ·
                    refine ⟨3017684728021286835072545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32188637098893726240773813 3017684728021286835072545)
                    ·
                      refine ⟨2263263546015965126304409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017684728021286835072545 2263263546015965126304409)
                      ·
                        rfl

theorem cell23_4407690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4407690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407690 prefixEnd_4407690 := by exact prefixLift 4407690
  have htrace : WordTrace (prefixWord ++ tailWord_4407690) baseStart_4407690 baseEnd_4407690 := by
    simpa [prefixWord, tailWord_4407690, baseEnd_4407690] using wordTrace_append hprefix tailTrace_4407690
  have hstable : (prefixWord ++ tailWord_4407690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407690).length < 2 ^ (prefixWord ++ tailWord_4407690).sum := by decide
  have hdescent : baseEnd_4407690 < baseStart_4407690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407703 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 1, 1, 4]
def baseStart_4407703 : Nat := 118140960795 + 4407703 * 2 ^ 59
def prefixEnd_4407703 : Nat := 4983230072969 + 3 ^ 40 * 4407703 * 2
def baseEnd_4407703 : Nat := 2263270221264473575441849

theorem tailTrace_4407703 : CollatzResearch.WordTrace tailWord_4407703 prefixEnd_4407703 2263270221264473575441849 := by
  unfold tailWord_4407703
  simp only [CollatzResearch.WordTrace]
  refine ⟨160762135550652281585971763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107174757033768187723981175 160762135550652281585971763)
  ·
    refine ⟨241143203325978422378957645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160762135550652281585971763 241143203325978422378957645)
    ·
      refine ⟨90428701247241908392109117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241143203325978422378957645 90428701247241908392109117)
      ·
        refine ⟨33910762967715715647040919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90428701247241908392109117 33910762967715715647040919)
        ·
          refine ⟨50866144451573573470561379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33910762967715715647040919 50866144451573573470561379)
          ·
            refine ⟨76299216677360360205842069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50866144451573573470561379 76299216677360360205842069)
            ·
              refine ⟨3576525781751266884648847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76299216677360360205842069 3576525781751266884648847)
              ·
                refine ⟨5364788672626900326973271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576525781751266884648847 5364788672626900326973271)
                ·
                  refine ⟨8047183008940350490459907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5364788672626900326973271 8047183008940350490459907)
                  ·
                    refine ⟨12070774513410525735689861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8047183008940350490459907 12070774513410525735689861)
                    ·
                      refine ⟨2263270221264473575441849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12070774513410525735689861 2263270221264473575441849)
                      ·
                        rfl

theorem cell23_4407703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_4407703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407703 prefixEnd_4407703 := by exact prefixLift 4407703
  have htrace : WordTrace (prefixWord ++ tailWord_4407703) baseStart_4407703 baseEnd_4407703 := by
    simpa [prefixWord, tailWord_4407703, baseEnd_4407703] using wordTrace_append hprefix tailTrace_4407703
  have hstable : (prefixWord ++ tailWord_4407703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407703).length < 2 ^ (prefixWord ++ tailWord_4407703).sum := by decide
  have hdescent : baseEnd_4407703 < baseStart_4407703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407740 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4407740 : Nat := 118140960795 + 4407740 * 2 ^ 59
def prefixEnd_4407740 : Nat := 4983230072969 + 3 ^ 40 * 4407740 * 2
def baseEnd_4407740 : Nat := 2263289220048689930679179

theorem tailTrace_4407740 : CollatzResearch.WordTrace tailWord_4407740 prefixEnd_4407740 2263289220048689930679179 := by
  unfold tailWord_4407740
  simp only [CollatzResearch.WordTrace]
  refine ⟨80381742525759118452534337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107175656701012157936712449 80381742525759118452534337)
  ·
    refine ⟨60286306894319338839400753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80381742525759118452534337 60286306894319338839400753)
    ·
      refine ⟨45214730170739504129550565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60286306894319338839400753 45214730170739504129550565)
      ·
        refine ⟨8477761907013657024290731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45214730170739504129550565 8477761907013657024290731)
        ·
          refine ⟨12716642860520485536436097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8477761907013657024290731 12716642860520485536436097)
          ·
            refine ⟨9537482145390364152327073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12716642860520485536436097 9537482145390364152327073)
            ·
              refine ⟨7153111609042773114245305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9537482145390364152327073 7153111609042773114245305)
              ·
                refine ⟨5364833706782079835683979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7153111609042773114245305 5364833706782079835683979)
                ·
                  refine ⟨8047250560173119753525969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5364833706782079835683979 8047250560173119753525969)
                  ·
                    refine ⟨6035437920129839815144477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8047250560173119753525969 6035437920129839815144477)
                    ·
                      refine ⟨2263289220048689930679179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6035437920129839815144477 2263289220048689930679179)
                      ·
                        rfl

theorem cell23_4407740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4407740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407740 prefixEnd_4407740 := by exact prefixLift 4407740
  have htrace : WordTrace (prefixWord ++ tailWord_4407740) baseStart_4407740 baseEnd_4407740 := by
    simpa [prefixWord, tailWord_4407740, baseEnd_4407740] using wordTrace_append hprefix tailTrace_4407740
  have hstable : (prefixWord ++ tailWord_4407740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407740).length < 2 ^ (prefixWord ++ tailWord_4407740).sum := by decide
  have hdescent : baseEnd_4407740 < baseStart_4407740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407759 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_4407759 : Nat := 118140960795 + 4407759 * 2 ^ 59
def prefixEnd_4407759 : Nat := 4983230072969 + 3 ^ 40 * 4407759 * 2
def baseEnd_4407759 : Nat := 2263298976181125356341591

theorem tailTrace_4407759 : CollatzResearch.WordTrace tailWord_4407759 prefixEnd_4407759 2263298976181125356341591 := by
  unfold tailWord_4407759
  simp only [CollatzResearch.WordTrace]
  refine ⟨160764178038449403150010331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107176118692299602100006887 160764178038449403150010331)
  ·
    refine ⟨241146267057674104725015497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160764178038449403150010331 241146267057674104725015497)
    ·
      refine ⟨180859700293255578543761623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241146267057674104725015497 180859700293255578543761623)
      ·
        refine ⟨271289550439883367815642435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180859700293255578543761623 271289550439883367815642435)
        ·
          refine ⟨406934325659825051723463653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271289550439883367815642435 406934325659825051723463653)
          ·
            refine ⟨76300186061217197198149435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 406934325659825051723463653 76300186061217197198149435)
            ·
              refine ⟨114450279091825795797224153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76300186061217197198149435 114450279091825795797224153)
              ·
                refine ⟨85837709318869346847918115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114450279091825795797224153 85837709318869346847918115)
                ·
                  refine ⟨128756563978304020271877173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85837709318869346847918115 128756563978304020271877173)
                  ·
                    refine ⟨12070927872966001900488485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128756563978304020271877173 12070927872966001900488485)
                    ·
                      refine ⟨2263298976181125356341591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12070927872966001900488485 2263298976181125356341591)
                      ·
                        rfl

theorem cell23_4407759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_4407759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407759 prefixEnd_4407759 := by exact prefixLift 4407759
  have htrace : WordTrace (prefixWord ++ tailWord_4407759) baseStart_4407759 baseEnd_4407759 := by
    simpa [prefixWord, tailWord_4407759, baseEnd_4407759] using wordTrace_append hprefix tailTrace_4407759
  have hstable : (prefixWord ++ tailWord_4407759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407759).length < 2 ^ (prefixWord ++ tailWord_4407759).sum := by decide
  have hdescent : baseEnd_4407759 < baseStart_4407759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407793 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 1, 4, 2]
def baseStart_4407793 : Nat := 118140960795 + 4407793 * 2 ^ 59
def prefixEnd_4407793 : Nat := 4983230072969 + 3 ^ 40 * 4407793 * 2
def baseEnd_4407793 : Nat := 2263316434523378223316435

theorem tailTrace_4407793 : CollatzResearch.WordTrace tailWord_4407793 prefixEnd_4407793 2263316434523378223316435 := by
  unfold tailWord_4407793
  simp only [CollatzResearch.WordTrace]
  refine ⟨160765418120326226956748033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107176945413550817971165355 160765418120326226956748033)
  ·
    refine ⟨120574063590244670217561025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160765418120326226956748033 120574063590244670217561025)
    ·
      refine ⟨90430547692683502663170769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120574063590244670217561025 90430547692683502663170769)
      ·
        refine ⟨67822910769512626997378077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90430547692683502663170769 67822910769512626997378077)
        ·
          refine ⟨25433591538567235124016779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67822910769512626997378077 25433591538567235124016779)
          ·
            refine ⟨38150387307850852686025169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25433591538567235124016779 38150387307850852686025169)
            ·
              refine ⟨28612790480888139514518877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38150387307850852686025169 28612790480888139514518877)
              ·
                refine ⟨10729796430333052317944579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28612790480888139514518877 10729796430333052317944579)
                ·
                  refine ⟨16094694645499578476916869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729796430333052317944579 16094694645499578476916869)
                  ·
                    refine ⟨3017755246031170964421913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16094694645499578476916869 3017755246031170964421913)
                    ·
                      refine ⟨2263316434523378223316435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017755246031170964421913 2263316434523378223316435)
                      ·
                        rfl

theorem cell23_4407793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_4407793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407793 prefixEnd_4407793 := by exact prefixLift 4407793
  have htrace : WordTrace (prefixWord ++ tailWord_4407793) baseStart_4407793 baseEnd_4407793 := by
    simpa [prefixWord, tailWord_4407793, baseEnd_4407793] using wordTrace_append hprefix tailTrace_4407793
  have hstable : (prefixWord ++ tailWord_4407793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407793).length < 2 ^ (prefixWord ++ tailWord_4407793).sum := by decide
  have hdescent : baseEnd_4407793 < baseStart_4407793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407797 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4407797 : Nat := 118140960795 + 4407797 * 2 ^ 59
def prefixEnd_4407797 : Nat := 4983230072969 + 3 ^ 40 * 4407797 * 2
def baseEnd_4407797 : Nat := 2263318488445996207666417

theorem tailTrace_4407797 : CollatzResearch.WordTrace tailWord_4407797 prefixEnd_4407797 2263318488445996207666417 := by
  unfold tailWord_4407797
  simp only [CollatzResearch.WordTrace]
  refine ⟨160765564012311735639893645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107177042674874490426595763 160765564012311735639893645)
  ·
    refine ⟨60287086504616900864960117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160765564012311735639893645 60287086504616900864960117)
    ·
      refine ⟨5651914359807834456090011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60287086504616900864960117 5651914359807834456090011)
      ·
        refine ⟨8477871539711751684135017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651914359807834456090011 8477871539711751684135017)
        ·
          refine ⟨6358403654783813763101263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8477871539711751684135017 6358403654783813763101263)
          ·
            refine ⟨9537605482175720644651895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358403654783813763101263 9537605482175720644651895)
            ·
              refine ⟨14306408223263580966977843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537605482175720644651895 14306408223263580966977843)
              ·
                refine ⟨21459612334895371450466765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14306408223263580966977843 21459612334895371450466765)
                ·
                  refine ⟨8047354625585764293925037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21459612334895371450466765 8047354625585764293925037)
                  ·
                    refine ⟨3017757984594661610221889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8047354625585764293925037 3017757984594661610221889)
                    ·
                      refine ⟨2263318488445996207666417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017757984594661610221889 2263318488445996207666417)
                      ·
                        rfl

theorem cell23_4407797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4407797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407797 prefixEnd_4407797 := by exact prefixLift 4407797
  have htrace : WordTrace (prefixWord ++ tailWord_4407797) baseStart_4407797 baseEnd_4407797 := by
    simpa [prefixWord, tailWord_4407797, baseEnd_4407797] using wordTrace_append hprefix tailTrace_4407797
  have hstable : (prefixWord ++ tailWord_4407797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407797).length < 2 ^ (prefixWord ++ tailWord_4407797).sum := by decide
  have hdescent : baseEnd_4407797 < baseStart_4407797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407843 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 3]
def baseStart_4407843 : Nat := 118140960795 + 4407843 * 2 ^ 59
def prefixEnd_4407843 : Nat := 4983230072969 + 3 ^ 40 * 4407843 * 2
def baseEnd_4407843 : Nat := 2263342108556103027691205

theorem tailTrace_4407843 : CollatzResearch.WordTrace tailWord_4407843 prefixEnd_4407843 2263342108556103027691205 := by
  unfold tailWord_4407843
  simp only [CollatzResearch.WordTrace]
  refine ⟨160767241770145085496068183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107178161180096723664045455 160767241770145085496068183)
  ·
    refine ⟨241150862655217628244102275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160767241770145085496068183 241150862655217628244102275)
    ·
      refine ⟨361726293982826442366153413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241150862655217628244102275 361726293982826442366153413)
      ·
        refine ⟨67823680121779957943653765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 361726293982826442366153413 67823680121779957943653765)
        ·
          refine ⟨12716940022833742114435081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67823680121779957943653765 12716940022833742114435081)
          ·
            refine ⟨9537705017125306585826311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12716940022833742114435081 9537705017125306585826311)
            ·
              refine ⟨14306557525687959878739467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537705017125306585826311 14306557525687959878739467)
              ·
                refine ⟨21459836288531939818109201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14306557525687959878739467 21459836288531939818109201)
                ·
                  refine ⟨16094877216398954863581901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21459836288531939818109201 16094877216398954863581901)
                  ·
                    refine ⟨6035578956149608073843213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16094877216398954863581901 6035578956149608073843213)
                    ·
                      refine ⟨2263342108556103027691205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6035578956149608073843213 2263342108556103027691205)
                      ·
                        rfl

theorem cell23_4407843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_4407843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407843 prefixEnd_4407843 := by exact prefixLift 4407843
  have htrace : WordTrace (prefixWord ++ tailWord_4407843) baseStart_4407843 baseEnd_4407843 := by
    simpa [prefixWord, tailWord_4407843, baseEnd_4407843] using wordTrace_append hprefix tailTrace_4407843
  have hstable : (prefixWord ++ tailWord_4407843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407843).length < 2 ^ (prefixWord ++ tailWord_4407843).sum := by decide
  have hdescent : baseEnd_4407843 < baseStart_4407843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407883 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 2, 4, 2]
def baseStart_4407883 : Nat := 118140960795 + 4407883 * 2 ^ 59
def prefixEnd_4407883 : Nat := 4983230072969 + 3 ^ 40 * 4407883 * 2
def baseEnd_4407883 : Nat := 2263362647782282871191021

theorem tailTrace_4407883 : CollatzResearch.WordTrace tailWord_4407883 prefixEnd_4407883 2263362647782282871191021 := by
  unfold tailWord_4407883
  simp only [CollatzResearch.WordTrace]
  refine ⟨160768700690000172327524303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107179133793333448218349535 160768700690000172327524303)
  ·
    refine ⟨241153051035000258491286455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160768700690000172327524303 241153051035000258491286455)
    ·
      refine ⟨361729576552500387736929683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241153051035000258491286455 361729576552500387736929683)
      ·
        refine ⟨542594364828750581605394525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361729576552500387736929683 542594364828750581605394525)
        ·
          refine ⟨203472886810781468102022947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542594364828750581605394525 203472886810781468102022947)
          ·
            refine ⟨305209330216172202153034421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203472886810781468102022947 305209330216172202153034421)
            ·
              refine ⟨28613374707766143951846977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 305209330216172202153034421 28613374707766143951846977)
              ·
                refine ⟨21460031030824607963885233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28613374707766143951846977 21460031030824607963885233)
                ·
                  refine ⟨16095023273118455972913925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21460031030824607963885233 16095023273118455972913925)
                  ·
                    refine ⟨3017816863709710494921361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16095023273118455972913925 3017816863709710494921361)
                    ·
                      refine ⟨2263362647782282871191021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017816863709710494921361 2263362647782282871191021)
                      ·
                        rfl

theorem cell23_4407883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4, 2].length) (baseStart_4407883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407883 prefixEnd_4407883 := by exact prefixLift 4407883
  have htrace : WordTrace (prefixWord ++ tailWord_4407883) baseStart_4407883 baseEnd_4407883 := by
    simpa [prefixWord, tailWord_4407883, baseEnd_4407883] using wordTrace_append hprefix tailTrace_4407883
  have hstable : (prefixWord ++ tailWord_4407883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407883).length < 2 ^ (prefixWord ++ tailWord_4407883).sum := by decide
  have hdescent : baseEnd_4407883 < baseStart_4407883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407886 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4407886 : Nat := 118140960795 + 4407886 * 2 ^ 59
def prefixEnd_4407886 : Nat := 4983230072969 + 3 ^ 40 * 4407886 * 2
def baseEnd_4407886 : Nat := 2263364188224246359453507

theorem tailTrace_4407886 : CollatzResearch.WordTrace tailWord_4407886 prefixEnd_4407886 2263364188224246359453507 := by
  unfold tailWord_4407886
  simp only [CollatzResearch.WordTrace]
  refine ⟨20096101263623662979985439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107179206739326202559922341 20096101263623662979985439)
  ·
    refine ⟨30144151895435494469978159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20096101263623662979985439 30144151895435494469978159)
    ·
      refine ⟨45216227843153241704967239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30144151895435494469978159 45216227843153241704967239)
      ·
        refine ⟨67824341764729862557450859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45216227843153241704967239 67824341764729862557450859)
        ·
          refine ⟨101736512647094793836176289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67824341764729862557450859 101736512647094793836176289)
          ·
            refine ⟨76302384485321095377132217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101736512647094793836176289 76302384485321095377132217)
            ·
              refine ⟨57226788363990821532849163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76302384485321095377132217 57226788363990821532849163)
              ·
                refine ⟨85840182545986232299273745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57226788363990821532849163 85840182545986232299273745)
                ·
                  refine ⟨64380136909489674224455309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85840182545986232299273745 64380136909489674224455309)
                  ·
                    refine ⟨24142551341058627834170741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64380136909489674224455309 24142551341058627834170741)
                    ·
                      refine ⟨2263364188224246359453507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24142551341058627834170741 2263364188224246359453507)
                      ·
                        rfl

theorem cell23_4407886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4407886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407886 prefixEnd_4407886 := by exact prefixLift 4407886
  have htrace : WordTrace (prefixWord ++ tailWord_4407886) baseStart_4407886 baseEnd_4407886 := by
    simpa [prefixWord, tailWord_4407886, baseEnd_4407886] using wordTrace_append hprefix tailTrace_4407886
  have hstable : (prefixWord ++ tailWord_4407886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407886).length < 2 ^ (prefixWord ++ tailWord_4407886).sum := by decide
  have hdescent : baseEnd_4407886 < baseStart_4407886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407893 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_4407893 : Nat := 118140960795 + 4407893 * 2 ^ 59
def prefixEnd_4407893 : Nat := 4983230072969 + 3 ^ 40 * 4407893 * 2
def baseEnd_4407893 : Nat := 754455927529609277355325

theorem tailTrace_4407893 : CollatzResearch.WordTrace tailWord_4407893 prefixEnd_4407893 754455927529609277355325 := by
  unfold tailWord_4407893
  simp only [CollatzResearch.WordTrace]
  refine ⟨160769065419963944035388333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107179376946642629356925555 160769065419963944035388333)
  ·
    refine ⟨60288399532486479013270625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160769065419963944035388333 60288399532486479013270625)
    ·
      refine ⟨45216299649364859259952969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60288399532486479013270625 45216299649364859259952969)
      ·
        refine ⟨33912224737023644444964727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45216299649364859259952969 33912224737023644444964727)
        ·
          refine ⟨50868337105535466667447091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33912224737023644444964727 50868337105535466667447091)
          ·
            refine ⟨76302505658303200001170637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50868337105535466667447091 76302505658303200001170637)
            ·
              refine ⟨28613439621863700000438989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76302505658303200001170637 28613439621863700000438989)
              ·
                refine ⟨10730039858198887500164621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28613439621863700000438989 10730039858198887500164621)
                ·
                  refine ⟨4023764946824582812561733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10730039858198887500164621 4023764946824582812561733)
                  ·
                    refine ⟨754455927529609277355325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023764946824582812561733 754455927529609277355325)
                    ·
                      rfl

theorem cell23_4407893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_4407893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407893 prefixEnd_4407893 := by exact prefixLift 4407893
  have htrace : WordTrace (prefixWord ++ tailWord_4407893) baseStart_4407893 baseEnd_4407893 := by
    simpa [prefixWord, tailWord_4407893, baseEnd_4407893] using wordTrace_append hprefix tailTrace_4407893
  have hstable : (prefixWord ++ tailWord_4407893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407893).length < 2 ^ (prefixWord ++ tailWord_4407893).sum := by decide
  have hdescent : baseEnd_4407893 < baseStart_4407893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407960 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4407960 : Nat := 118140960795 + 4407960 * 2 ^ 59
def prefixEnd_4407960 : Nat := 4983230072969 + 3 ^ 40 * 4407960 * 2
def baseEnd_4407960 : Nat := 2263402185792679069928167

theorem tailTrace_4407960 : CollatzResearch.WordTrace tailWord_4407960 prefixEnd_4407960 2263402185792679069928167 := by
  unfold tailWord_4407960
  simp only [CollatzResearch.WordTrace]
  refine ⟨80385754555360607239038667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107181006073814142985384889 80385754555360607239038667)
  ·
    refine ⟨120578631833040910858558001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80385754555360607239038667 120578631833040910858558001)
    ·
      refine ⟨90433973874780683143918501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120578631833040910858558001 90433973874780683143918501)
      ·
        refine ⟨16956370101521378089484719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90433973874780683143918501 16956370101521378089484719)
        ·
          refine ⟨25434555152282067134227079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16956370101521378089484719 25434555152282067134227079)
          ·
            refine ⟨38151832728423100701340619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25434555152282067134227079 38151832728423100701340619)
            ·
              refine ⟨57227749092634651052010929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38151832728423100701340619 57227749092634651052010929)
              ·
                refine ⟨42920811819475988289008197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57227749092634651052010929 42920811819475988289008197)
                ·
                  refine ⟨8047652216151747804189037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42920811819475988289008197 8047652216151747804189037)
                  ·
                    refine ⟨3017869581056905426570889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8047652216151747804189037 3017869581056905426570889)
                    ·
                      refine ⟨2263402185792679069928167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017869581056905426570889 2263402185792679069928167)
                      ·
                        rfl

theorem cell23_4407960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4407960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407960 prefixEnd_4407960 := by exact prefixLift 4407960
  have htrace : WordTrace (prefixWord ++ tailWord_4407960) baseStart_4407960 baseEnd_4407960 := by
    simpa [prefixWord, tailWord_4407960, baseEnd_4407960] using wordTrace_append hprefix tailTrace_4407960
  have hstable : (prefixWord ++ tailWord_4407960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407960).length < 2 ^ (prefixWord ++ tailWord_4407960).sum := by decide
  have hdescent : baseEnd_4407960 < baseStart_4407960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4407983 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 1, 6]
def baseStart_4407983 : Nat := 118140960795 + 4407983 * 2 ^ 59
def prefixEnd_4407983 : Nat := 4983230072969 + 3 ^ 40 * 4407983 * 2
def baseEnd_4407983 : Nat := 754471331949244159980187

theorem tailTrace_4407983 : CollatzResearch.WordTrace tailWord_4407983 prefixEnd_4407983 754471331949244159980187 := by
  unfold tailWord_4407983
  simp only [CollatzResearch.WordTrace]
  refine ⟨160772347989637889406164603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107181565326425259604109735 160772347989637889406164603)
  ·
    refine ⟨241158521984456834109246905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160772347989637889406164603 241158521984456834109246905)
    ·
      refine ⟨180868891488342625581935179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241158521984456834109246905 180868891488342625581935179)
      ·
        refine ⟨271303337232513938372902769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180868891488342625581935179 271303337232513938372902769)
        ·
          refine ⟨203477502924385453779677077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271303337232513938372902769 203477502924385453779677077)
          ·
            refine ⟨9538007949580568145922363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203477502924385453779677077 9538007949580568145922363)
            ·
              refine ⟨14307011924370852218883545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9538007949580568145922363 14307011924370852218883545)
              ·
                refine ⟨10730258943278139164162659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14307011924370852218883545 10730258943278139164162659)
                ·
                  refine ⟨16095388414917208746243989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10730258943278139164162659 16095388414917208746243989)
                  ·
                    refine ⟨754471331949244159980187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16095388414917208746243989 754471331949244159980187)
                    ·
                      rfl

theorem cell23_4407983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_4407983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4407983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4407983 prefixEnd_4407983 := by exact prefixLift 4407983
  have htrace : WordTrace (prefixWord ++ tailWord_4407983) baseStart_4407983 baseEnd_4407983 := by
    simpa [prefixWord, tailWord_4407983, baseEnd_4407983] using wordTrace_append hprefix tailTrace_4407983
  have hstable : (prefixWord ++ tailWord_4407983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4407983).length < 2 ^ (prefixWord ++ tailWord_4407983).sum := by decide
  have hdescent : baseEnd_4407983 < baseStart_4407983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4407983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408000 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 2, 4]
def baseStart_4408000 : Nat := 118140960795 + 4408000 * 2 ^ 59
def prefixEnd_4408000 : Nat := 4983230072969 + 3 ^ 40 * 4408000 * 2
def baseEnd_4408000 : Nat := 754474241672952971142661

theorem tailTrace_4408000 : CollatzResearch.WordTrace tailWord_4408000 prefixEnd_4408000 754474241672952971142661 := by
  unfold tailWord_4408000
  simp only [CollatzResearch.WordTrace]
  refine ⟨80386484015288150654766727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107181978687050867539688969 80386484015288150654766727)
  ·
    refine ⟨120579726022932225982150091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80386484015288150654766727 120579726022932225982150091)
    ·
      refine ⟨180869589034398338973225137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120579726022932225982150091 180869589034398338973225137)
      ·
        refine ⟨135652191775798754229918853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180869589034398338973225137 135652191775798754229918853)
        ·
          refine ⟨25434785957962266418109785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135652191775798754229918853 25434785957962266418109785)
          ·
            refine ⟨19076089468471699813582339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25434785957962266418109785 19076089468471699813582339)
            ·
              refine ⟨28614134202707549720373509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19076089468471699813582339 28614134202707549720373509)
              ·
                refine ⟨5365150163007665572570033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28614134202707549720373509 5365150163007665572570033)
                ·
                  refine ⟨4023862622255749179427525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5365150163007665572570033 4023862622255749179427525)
                  ·
                    refine ⟨754474241672952971142661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023862622255749179427525 754474241672952971142661)
                    ·
                      rfl

theorem cell23_4408000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_4408000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408000 prefixEnd_4408000 := by exact prefixLift 4408000
  have htrace : WordTrace (prefixWord ++ tailWord_4408000) baseStart_4408000 baseEnd_4408000 := by
    simpa [prefixWord, tailWord_4408000, baseEnd_4408000] using wordTrace_append hprefix tailTrace_4408000
  have hstable : (prefixWord ++ tailWord_4408000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408000).length < 2 ^ (prefixWord ++ tailWord_4408000).sum := by decide
  have hdescent : baseEnd_4408000 < baseStart_4408000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408010 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_4408010 : Nat := 118140960795 + 4408010 * 2 ^ 59
def prefixEnd_4408010 : Nat := 4983230072969 + 3 ^ 40 * 4408010 * 2
def baseEnd_4408010 : Nat := 2263427859825403874302937

theorem tailTrace_4408010 : CollatzResearch.WordTrace tailWord_4408010 prefixEnd_4408010 2263427859825403874302937 := by
  unfold tailWord_4408010
  simp only [CollatzResearch.WordTrace]
  refine ⟨40193333190135018254349371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107182221840360048678264989 40193333190135018254349371)
  ·
    refine ⟨60289999785202527381524057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40193333190135018254349371 60289999785202527381524057)
    ·
      refine ⟨45217499838901895536143043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60289999785202527381524057 45217499838901895536143043)
      ·
        refine ⟨67826249758352843304214565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45217499838901895536143043 67826249758352843304214565)
        ·
          refine ⟨12717421829691158119540231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67826249758352843304214565 12717421829691158119540231)
          ·
            refine ⟨19076132744536737179310347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12717421829691158119540231 19076132744536737179310347)
            ·
              refine ⟨28614199116805105768965521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19076132744536737179310347 28614199116805105768965521)
              ·
                refine ⟨21460649337603829326724141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28614199116805105768965521 21460649337603829326724141)
                ·
                  refine ⟨8047743501601435997521553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21460649337603829326724141 8047743501601435997521553)
                  ·
                    refine ⟨6035807626201076998141165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8047743501601435997521553 6035807626201076998141165)
                    ·
                      refine ⟨2263427859825403874302937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6035807626201076998141165 2263427859825403874302937)
                      ·
                        rfl

theorem cell23_4408010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_4408010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408010 prefixEnd_4408010 := by exact prefixLift 4408010
  have htrace : WordTrace (prefixWord ++ tailWord_4408010) baseStart_4408010 baseEnd_4408010 := by
    simpa [prefixWord, tailWord_4408010, baseEnd_4408010] using wordTrace_append hprefix tailTrace_4408010
  have hstable : (prefixWord ++ tailWord_4408010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408010).length < 2 ^ (prefixWord ++ tailWord_4408010).sum := by decide
  have hdescent : baseEnd_4408010 < baseStart_4408010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408073 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_4408073 : Nat := 118140960795 + 4408073 * 2 ^ 59
def prefixEnd_4408073 : Nat := 4983230072969 + 3 ^ 40 * 4408073 * 2
def baseEnd_4408073 : Nat := 754486736368879042605049

theorem tailTrace_4408073 : CollatzResearch.WordTrace tailWord_4408073 prefixEnd_4408073 754486736368879042605049 := by
  unfold tailWord_4408073
  simp only [CollatzResearch.WordTrace]
  refine ⟨160775630559311834776940873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107183753706207889851293915 160775630559311834776940873)
  ·
    refine ⟨120581722919483876082705655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160775630559311834776940873 120581722919483876082705655)
    ·
      refine ⟨180872584379225814124058483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120581722919483876082705655 180872584379225814124058483)
      ·
        refine ⟨271308876568838721186087725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180872584379225814124058483 271308876568838721186087725)
        ·
          refine ⟨101740828713314520444782897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271308876568838721186087725 101740828713314520444782897)
          ·
            refine ⟨76305621534985890333587173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101740828713314520444782897 76305621534985890333587173)
            ·
              refine ⟨14307304037809854437547595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76305621534985890333587173 14307304037809854437547595)
              ·
                refine ⟨21460956056714781656321393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14307304037809854437547595 21460956056714781656321393)
                ·
                  refine ⟨16095717042536086242241045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21460956056714781656321393 16095717042536086242241045)
                  ·
                    refine ⟨754486736368879042605049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16095717042536086242241045 754486736368879042605049)
                    ·
                      rfl

theorem cell23_4408073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_4408073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408073 prefixEnd_4408073 := by exact prefixLift 4408073
  have htrace : WordTrace (prefixWord ++ tailWord_4408073) baseStart_4408073 baseEnd_4408073 := by
    simpa [prefixWord, tailWord_4408073, baseEnd_4408073] using wordTrace_append hprefix tailTrace_4408073
  have hstable : (prefixWord ++ tailWord_4408073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408073).length < 2 ^ (prefixWord ++ tailWord_4408073).sum := by decide
  have hdescent : baseEnd_4408073 < baseStart_4408073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408074 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_4408074 : Nat := 118140960795 + 4408074 * 2 ^ 59
def prefixEnd_4408074 : Nat := 4983230072969 + 3 ^ 40 * 4408074 * 2
def baseEnd_4408074 : Nat := 2263460722587291623902643

theorem tailTrace_4408074 : CollatzResearch.WordTrace tailWord_4408074 prefixEnd_4408074 2263460722587291623902643 := by
  unfold tailWord_4408074
  simp only [CollatzResearch.WordTrace]
  refine ⟨40193916758077052986931819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107183778021538807965151517 40193916758077052986931819)
  ·
    refine ⟨60290875137115579480397729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40193916758077052986931819 60290875137115579480397729)
    ·
      refine ⟨45218156352836684610298297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60290875137115579480397729 45218156352836684610298297)
      ·
        refine ⟨33913617264627513457723723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45218156352836684610298297 33913617264627513457723723)
        ·
          refine ⟨50870425896941270186585585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33913617264627513457723723 50870425896941270186585585)
          ·
            refine ⟨38152819422705952639939189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50870425896941270186585585 38152819422705952639939189)
            ·
              refine ⟨3576826820878683059994299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38152819422705952639939189 3576826820878683059994299)
              ·
                refine ⟨5365240231318024589991449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576826820878683059994299 5365240231318024589991449)
                ·
                  refine ⟨4023930173488518442493587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5365240231318024589991449 4023930173488518442493587)
                  ·
                    refine ⟨6035895260232777663740381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023930173488518442493587 6035895260232777663740381)
                    ·
                      refine ⟨2263460722587291623902643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6035895260232777663740381 2263460722587291623902643)
                      ·
                        rfl

theorem cell23_4408074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_4408074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408074 prefixEnd_4408074 := by exact prefixLift 4408074
  have htrace : WordTrace (prefixWord ++ tailWord_4408074) baseStart_4408074 baseEnd_4408074 := by
    simpa [prefixWord, tailWord_4408074, baseEnd_4408074] using wordTrace_append hprefix tailTrace_4408074
  have hstable : (prefixWord ++ tailWord_4408074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408074).length < 2 ^ (prefixWord ++ tailWord_4408074).sum := by decide
  have hdescent : baseEnd_4408074 < baseStart_4408074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408083 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5]
def baseStart_4408083 : Nat := 118140960795 + 4408083 * 2 ^ 59
def prefixEnd_4408083 : Nat := 4983230072969 + 3 ^ 40 * 4408083 * 2
def baseEnd_4408083 : Nat := 2263465343913182088690101

theorem tailTrace_4408083 : CollatzResearch.WordTrace tailWord_4408083 prefixEnd_4408083 2263465343913182088690101 := by
  unfold tailWord_4408083
  simp only [CollatzResearch.WordTrace]
  refine ⟨160775995289275606484804903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107183996859517070989869935 160775995289275606484804903)
  ·
    refine ⟨241163992933913409727207355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160775995289275606484804903 241163992933913409727207355)
    ·
      refine ⟨361745989400870114590811033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241163992933913409727207355 361745989400870114590811033)
      ·
        refine ⟨271309492050652585943108275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361745989400870114590811033 271309492050652585943108275)
        ·
          refine ⟨406964238075978878914662413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271309492050652585943108275 406964238075978878914662413)
          ·
            refine ⟨152611589278492079592998405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406964238075978878914662413 152611589278492079592998405)
            ·
              refine ⟨28614672989717264923687201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152611589278492079592998405 28614672989717264923687201)
              ·
                refine ⟨21461004742287948692765401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28614672989717264923687201 21461004742287948692765401)
                ·
                  refine ⟨16095753556715961519574051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21461004742287948692765401 16095753556715961519574051)
                  ·
                    refine ⟨24143630335073942279361077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16095753556715961519574051 24143630335073942279361077)
                    ·
                      refine ⟨2263465343913182088690101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24143630335073942279361077 2263465343913182088690101)
                      ·
                        rfl

theorem cell23_4408083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_4408083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408083 prefixEnd_4408083 := by exact prefixLift 4408083
  have htrace : WordTrace (prefixWord ++ tailWord_4408083) baseStart_4408083 baseEnd_4408083 := by
    simpa [prefixWord, tailWord_4408083, baseEnd_4408083] using wordTrace_append hprefix tailTrace_4408083
  have hstable : (prefixWord ++ tailWord_4408083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408083).length < 2 ^ (prefixWord ++ tailWord_4408083).sum := by decide
  have hdescent : baseEnd_4408083 < baseStart_4408083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408097 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_4408097 : Nat := 118140960795 + 4408097 * 2 ^ 59
def prefixEnd_4408097 : Nat := 4983230072969 + 3 ^ 40 * 4408097 * 2
def baseEnd_4408097 : Nat := 2263472532642345033915037

theorem tailTrace_4408097 : CollatzResearch.WordTrace tailWord_4408097 prefixEnd_4408097 2263472532642345033915037 := by
  unfold tailWord_4408097
  simp only [CollatzResearch.WordTrace]
  refine ⟨160776505911224886875814545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107184337274149924583876363 160776505911224886875814545)
  ·
    refine ⟨120582379433418665156860909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160776505911224886875814545 120582379433418665156860909)
    ·
      refine ⟨45218392287531999433822841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120582379433418665156860909 45218392287531999433822841)
      ·
        refine ⟨33913794215648999575367131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45218392287531999433822841 33913794215648999575367131)
        ·
          refine ⟨50870691323473499363050697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33913794215648999575367131 50870691323473499363050697)
          ·
            refine ⟨38153018492605124522288023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50870691323473499363050697 38153018492605124522288023)
            ·
              refine ⟨57229527738907686783432035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38153018492605124522288023 57229527738907686783432035)
              ·
                refine ⟨85844291608361530175148053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57229527738907686783432035 85844291608361530175148053)
                ·
                  refine ⟨4023951169141946726960065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85844291608361530175148053 4023951169141946726960065)
                  ·
                    refine ⟨3017963376856460045220049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023951169141946726960065 3017963376856460045220049)
                    ·
                      refine ⟨2263472532642345033915037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017963376856460045220049 2263472532642345033915037)
                      ·
                        rfl

theorem cell23_4408097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_4408097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408097 prefixEnd_4408097 := by exact prefixLift 4408097
  have htrace : WordTrace (prefixWord ++ tailWord_4408097) baseStart_4408097 baseEnd_4408097 := by
    simpa [prefixWord, tailWord_4408097, baseEnd_4408097] using wordTrace_append hprefix tailTrace_4408097
  have hstable : (prefixWord ++ tailWord_4408097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408097).length < 2 ^ (prefixWord ++ tailWord_4408097).sum := by decide
  have hdescent : baseEnd_4408097 < baseStart_4408097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408113 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4408113 : Nat := 118140960795 + 4408113 * 2 ^ 59
def prefixEnd_4408113 : Nat := 4983230072969 + 3 ^ 40 * 4408113 * 2
def baseEnd_4408113 : Nat := 2263480748332816971314963

theorem tailTrace_4408113 : CollatzResearch.WordTrace tailWord_4408113 prefixEnd_4408113 2263480748332816971314963 := by
  unfold tailWord_4408113
  simp only [CollatzResearch.WordTrace]
  refine ⟨160777089479166921608396993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107184726319444614405597995 160777089479166921608396993)
  ·
    refine ⟨120582817109375191206297745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160777089479166921608396993 120582817109375191206297745)
    ·
      refine ⟨90437112832031393404723309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120582817109375191206297745 90437112832031393404723309)
      ·
        refine ⟨33913917312011772526771241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90437112832031393404723309 33913917312011772526771241)
        ·
          refine ⟨25435437984008829395078431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33913917312011772526771241 25435437984008829395078431)
          ·
            refine ⟨38153156976013244092617647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25435437984008829395078431 38153156976013244092617647)
            ·
              refine ⟨57229735464019866138926471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38153156976013244092617647 57229735464019866138926471)
              ·
                refine ⟨85844603196029799208389707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57229735464019866138926471 85844603196029799208389707)
                ·
                  refine ⟨128766904794044698812584561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85844603196029799208389707 128766904794044698812584561)
                  ·
                    refine ⟨96575178595533524109438421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128766904794044698812584561 96575178595533524109438421)
                    ·
                      refine ⟨2263480748332816971314963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96575178595533524109438421 2263480748332816971314963)
                      ·
                        rfl

theorem cell23_4408113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4408113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408113 prefixEnd_4408113 := by exact prefixLift 4408113
  have htrace : WordTrace (prefixWord ++ tailWord_4408113) baseStart_4408113 baseEnd_4408113 := by
    simpa [prefixWord, tailWord_4408113, baseEnd_4408113] using wordTrace_append hprefix tailTrace_4408113
  have hstable : (prefixWord ++ tailWord_4408113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408113).length < 2 ^ (prefixWord ++ tailWord_4408113).sum := by decide
  have hdescent : baseEnd_4408113 < baseStart_4408113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408114 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_4408114 : Nat := 118140960795 + 4408114 * 2 ^ 59
def prefixEnd_4408114 : Nat := 4983230072969 + 3 ^ 40 * 4408114 * 2
def baseEnd_4408114 : Nat := 2263481261813471467402459

theorem tailTrace_4408114 : CollatzResearch.WordTrace tailWord_4408114 prefixEnd_4408114 2263481261813471467402459 := by
  unfold tailWord_4408114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40194281488040824694795849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107184750634775532519455597 40194281488040824694795849)
  ·
    refine ⟨30145711116030618521096887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40194281488040824694795849 30145711116030618521096887)
    ·
      refine ⟨45218566674045927781645331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30145711116030618521096887 45218566674045927781645331)
      ·
        refine ⟨67827850011068891672467997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45218566674045927781645331 67827850011068891672467997)
        ·
          refine ⟨25435443754150834377175499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67827850011068891672467997 25435443754150834377175499)
          ·
            refine ⟨38153165631226251565763249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25435443754150834377175499 38153165631226251565763249)
            ·
              refine ⟨28614874223419688674322437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38153165631226251565763249 28614874223419688674322437)
              ·
                refine ⟨5365288916891191626435457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28614874223419688674322437 5365288916891191626435457)
                ·
                  refine ⟨4023966687668393719826593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5365288916891191626435457 4023966687668393719826593)
                  ·
                    refine ⟨3017975015751295289869945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023966687668393719826593 3017975015751295289869945)
                    ·
                      refine ⟨2263481261813471467402459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3017975015751295289869945 2263481261813471467402459)
                      ·
                        rfl

theorem cell23_4408114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_4408114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408114 prefixEnd_4408114 := by exact prefixLift 4408114
  have htrace : WordTrace (prefixWord ++ tailWord_4408114) baseStart_4408114 baseEnd_4408114 := by
    simpa [prefixWord, tailWord_4408114, baseEnd_4408114] using wordTrace_append hprefix tailTrace_4408114
  have hstable : (prefixWord ++ tailWord_4408114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408114).length < 2 ^ (prefixWord ++ tailWord_4408114).sum := by decide
  have hdescent : baseEnd_4408114 < baseStart_4408114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408133 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_4408133 : Nat := 118140960795 + 4408133 * 2 ^ 59
def prefixEnd_4408133 : Nat := 4983230072969 + 3 ^ 40 * 4408133 * 2
def baseEnd_4408133 : Nat := 754497005981968964354957

theorem tailTrace_4408133 : CollatzResearch.WordTrace tailWord_4408133 prefixEnd_4408133 754497005981968964354957 := by
  unfold tailWord_4408133
  simp only [CollatzResearch.WordTrace]
  refine ⟨160777818939094465024125053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107185212626062976682750035 160777818939094465024125053)
  ·
    refine ⟨60291682102160424384046895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160777818939094465024125053 60291682102160424384046895)
    ·
      refine ⟨90437523153240636576070343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60291682102160424384046895 90437523153240636576070343)
      ·
        refine ⟨135656284729860954864105515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90437523153240636576070343 135656284729860954864105515)
        ·
          refine ⟨203484427094791432296158273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135656284729860954864105515 203484427094791432296158273)
          ·
            refine ⟨152613320321093574222118705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203484427094791432296158273 152613320321093574222118705)
            ·
              refine ⟨114459990240820180666589029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152613320321093574222118705 114459990240820180666589029)
              ·
                refine ⟨21461248170153783874985443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114459990240820180666589029 21461248170153783874985443)
                ·
                  refine ⟨32191872255230675812478165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21461248170153783874985443 32191872255230675812478165)
                  ·
                    refine ⟨754497005981968964354957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32191872255230675812478165 754497005981968964354957)
                    ·
                      rfl

theorem cell23_4408133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_4408133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408133 prefixEnd_4408133 := by exact prefixLift 4408133
  have htrace : WordTrace (prefixWord ++ tailWord_4408133) baseStart_4408133 baseEnd_4408133 := by
    simpa [prefixWord, tailWord_4408133, baseEnd_4408133] using wordTrace_append hprefix tailTrace_4408133
  have hstable : (prefixWord ++ tailWord_4408133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408133).length < 2 ^ (prefixWord ++ tailWord_4408133).sum := by decide
  have hdescent : baseEnd_4408133 < baseStart_4408133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408197 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_4408197 : Nat := 118140960795 + 4408197 * 2 ^ 59
def prefixEnd_4408197 : Nat := 4983230072969 + 3 ^ 40 * 4408197 * 2
def baseEnd_4408197 : Nat := 754507960235931547554859

theorem tailTrace_4408197 : CollatzResearch.WordTrace tailWord_4408197 prefixEnd_4408197 754507960235931547554859 := by
  unfold tailWord_4408197
  simp only [CollatzResearch.WordTrace]
  refine ⟨160780153210862603954454845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107186768807241735969636563 160780153210862603954454845)
  ·
    refine ⟨60292557454073476482920567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160780153210862603954454845 60292557454073476482920567)
    ·
      refine ⟨90438836181110214724380851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60292557454073476482920567 90438836181110214724380851)
      ·
        refine ⟨135658254271665322086571277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90438836181110214724380851 135658254271665322086571277)
        ·
          refine ⟨50871845351874495782464229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135658254271665322086571277 50871845351874495782464229)
          ·
            refine ⟨9538471003476467959212043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50871845351874495782464229 9538471003476467959212043)
            ·
              refine ⟨14307706505214701938818065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9538471003476467959212043 14307706505214701938818065)
              ·
                refine ⟨10730779878911026454113549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14307706505214701938818065 10730779878911026454113549)
                ·
                  refine ⟨4024042454591634920292581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10730779878911026454113549 4024042454591634920292581)
                  ·
                    refine ⟨754507960235931547554859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024042454591634920292581 754507960235931547554859)
                    ·
                      rfl

theorem cell23_4408197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_4408197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408197 prefixEnd_4408197 := by exact prefixLift 4408197
  have htrace : WordTrace (prefixWord ++ tailWord_4408197) baseStart_4408197 baseEnd_4408197 := by
    simpa [prefixWord, tailWord_4408197, baseEnd_4408197] using wordTrace_append hprefix tailTrace_4408197
  have hstable : (prefixWord ++ tailWord_4408197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408197).length < 2 ^ (prefixWord ++ tailWord_4408197).sum := by decide
  have hdescent : baseEnd_4408197 < baseStart_4408197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408247 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 1, 5, 2]
def baseStart_4408247 : Nat := 118140960795 + 4408247 * 2 ^ 59
def prefixEnd_4408247 : Nat := 4983230072969 + 3 ^ 40 * 4408247 * 2
def baseEnd_4408247 : Nat := 2263549554740519447039347

theorem tailTrace_4408247 : CollatzResearch.WordTrace tailWord_4408247 prefixEnd_4408247 2263549554740519447039347 := by
  unfold tailWord_4408247
  simp only [CollatzResearch.WordTrace]
  refine ⟨160781976860681462493774995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107187984573787641662516663 160781976860681462493774995)
  ·
    refine ⟨241172965291022193740662493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160781976860681462493774995 241172965291022193740662493)
    ·
      refine ⟨90439861984133322652748435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241172965291022193740662493 90439861984133322652748435)
      ·
        refine ⟨135659792976199983979122653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90439861984133322652748435 135659792976199983979122653)
        ·
          refine ⟨50872422366074993992170995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135659792976199983979122653 50872422366074993992170995)
          ·
            refine ⟨76308633549112490988256493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50872422366074993992170995 76308633549112490988256493)
            ·
              refine ⟨28615737580917184120596185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76308633549112490988256493 28615737580917184120596185)
              ·
                refine ⟨21461803185687888090447139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28615737580917184120596185 21461803185687888090447139)
                ·
                  refine ⟨32192704778531832135670709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21461803185687888090447139 32192704778531832135670709)
                  ·
                    refine ⟨3018066072987359262719129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32192704778531832135670709 3018066072987359262719129)
                    ·
                      refine ⟨2263549554740519447039347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018066072987359262719129 2263549554740519447039347)
                      ·
                        rfl

theorem cell23_4408247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_4408247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408247 prefixEnd_4408247 := by exact prefixLift 4408247
  have htrace : WordTrace (prefixWord ++ tailWord_4408247) baseStart_4408247 baseEnd_4408247 := by
    simpa [prefixWord, tailWord_4408247, baseEnd_4408247] using wordTrace_append hprefix tailTrace_4408247
  have hstable : (prefixWord ++ tailWord_4408247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408247).length < 2 ^ (prefixWord ++ tailWord_4408247).sum := by decide
  have hdescent : baseEnd_4408247 < baseStart_4408247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408254 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_4408254 : Nat := 118140960795 + 4408254 * 2 ^ 59
def prefixEnd_4408254 : Nat := 4983230072969 + 3 ^ 40 * 4408254 * 2
def baseEnd_4408254 : Nat := 2263553149105100919651815

theorem tailTrace_4408254 : CollatzResearch.WordTrace tailWord_4408254 prefixEnd_4408254 2263553149105100919651815 := by
  unfold tailWord_4408254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20097779021457012836159977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107188154781104068459519877 20097779021457012836159977)
  ·
    refine ⟨15073334266092759627119983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20097779021457012836159977 15073334266092759627119983)
    ·
      refine ⟨22610001399139139440679975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15073334266092759627119983 22610001399139139440679975)
      ·
        refine ⟨33915002098708709161019963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22610001399139139440679975 33915002098708709161019963)
        ·
          refine ⟨50872503148063063741529945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33915002098708709161019963 50872503148063063741529945)
          ·
            refine ⟨38154377361047297806147459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50872503148063063741529945 38154377361047297806147459)
            ·
              refine ⟨57231566041570946709221189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38154377361047297806147459 57231566041570946709221189)
              ·
                refine ⟨10730918632794552507978973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57231566041570946709221189 10730918632794552507978973)
                ·
                  refine ⟨4024094487297957190492115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10730918632794552507978973 4024094487297957190492115)
                  ·
                    refine ⟨6036141730946935785738173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024094487297957190492115 6036141730946935785738173)
                    ·
                      refine ⟨2263553149105100919651815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6036141730946935785738173 2263553149105100919651815)
                      ·
                        rfl

theorem cell23_4408254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_4408254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408254 prefixEnd_4408254 := by exact prefixLift 4408254
  have htrace : WordTrace (prefixWord ++ tailWord_4408254) baseStart_4408254 baseEnd_4408254 := by
    simpa [prefixWord, tailWord_4408254, baseEnd_4408254] using wordTrace_append hprefix tailTrace_4408254
  have hstable : (prefixWord ++ tailWord_4408254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408254).length < 2 ^ (prefixWord ++ tailWord_4408254).sum := by decide
  have hdescent : baseEnd_4408254 < baseStart_4408254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408271 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 1, 1, 3]
def baseStart_4408271 : Nat := 118140960795 + 4408271 * 2 ^ 59
def prefixEnd_4408271 : Nat := 4983230072969 + 3 ^ 40 * 4408271 * 2
def baseEnd_4408271 : Nat := 2263561878276227353139237

theorem tailTrace_4408271 : CollatzResearch.WordTrace tailWord_4408271 prefixEnd_4408271 2263561878276227353139237 := by
  unfold tailWord_4408271
  simp only [CollatzResearch.WordTrace]
  refine ⟨160782852212594514592648667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107188568141729676395099111 160782852212594514592648667)
  ·
    refine ⟨241174278318891771888973001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160782852212594514592648667 241174278318891771888973001)
    ·
      refine ⟨180880708739168828916729751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241174278318891771888973001 180880708739168828916729751)
      ·
        refine ⟨271321063108753243375094627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180880708739168828916729751 271321063108753243375094627)
        ·
          refine ⟨406981594663129865062641941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271321063108753243375094627 406981594663129865062641941)
          ·
            refine ⟨19077262249834212424811341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 406981594663129865062641941 19077262249834212424811341)
            ·
              refine ⟨7153973343687829659304253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19077262249834212424811341 7153973343687829659304253)
              ·
                refine ⟨2682740003882936122239095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7153973343687829659304253 2682740003882936122239095)
                ·
                  refine ⟨4024110005824404183358643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682740003882936122239095 4024110005824404183358643)
                  ·
                    refine ⟨6036165008736606275037965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024110005824404183358643 6036165008736606275037965)
                    ·
                      refine ⟨2263561878276227353139237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6036165008736606275037965 2263561878276227353139237)
                      ·
                        rfl

theorem cell23_4408271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 1, 3].length) (baseStart_4408271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408271 prefixEnd_4408271 := by exact prefixLift 4408271
  have htrace : WordTrace (prefixWord ++ tailWord_4408271) baseStart_4408271 baseEnd_4408271 := by
    simpa [prefixWord, tailWord_4408271, baseEnd_4408271] using wordTrace_append hprefix tailTrace_4408271
  have hstable : (prefixWord ++ tailWord_4408271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408271).length < 2 ^ (prefixWord ++ tailWord_4408271).sum := by decide
  have hdescent : baseEnd_4408271 < baseStart_4408271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408274 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_4408274 : Nat := 118140960795 + 4408274 * 2 ^ 59
def prefixEnd_4408274 : Nat := 4983230072969 + 3 ^ 40 * 4408274 * 2
def baseEnd_4408274 : Nat := 754521139572730280467241

theorem tailTrace_4408274 : CollatzResearch.WordTrace tailWord_4408274 prefixEnd_4408274 754521139572730280467241 := by
  unfold tailWord_4408274
  simp only [CollatzResearch.WordTrace]
  refine ⟨40195740407895911526251969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107188641087722430736671917 40195740407895911526251969)
  ·
    refine ⟨30146805305921933644688977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40195740407895911526251969 30146805305921933644688977)
    ·
      refine ⟨22610103979441450233516733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30146805305921933644688977 22610103979441450233516733)
      ·
        refine ⟨8478788992290543837568775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22610103979441450233516733 8478788992290543837568775)
        ·
          refine ⟨12718183488435815756353163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8478788992290543837568775 12718183488435815756353163)
          ·
            refine ⟨19077275232653723634529745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12718183488435815756353163 19077275232653723634529745)
            ·
              refine ⟨14307956424490292725897309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19077275232653723634529745 14307956424490292725897309)
              ·
                refine ⟨5365483659183859772211491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14307956424490292725897309 5365483659183859772211491)
                ·
                  refine ⟨8048225488775789658317237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5365483659183859772211491 8048225488775789658317237)
                  ·
                    refine ⟨754521139572730280467241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8048225488775789658317237 754521139572730280467241)
                    ·
                      rfl

theorem cell23_4408274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_4408274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408274 prefixEnd_4408274 := by exact prefixLift 4408274
  have htrace : WordTrace (prefixWord ++ tailWord_4408274) baseStart_4408274 baseEnd_4408274 := by
    simpa [prefixWord, tailWord_4408274, baseEnd_4408274] using wordTrace_append hprefix tailTrace_4408274
  have hstable : (prefixWord ++ tailWord_4408274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408274).length < 2 ^ (prefixWord ++ tailWord_4408274).sum := by decide
  have hdescent : baseEnd_4408274 < baseStart_4408274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408331 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 1, 2, 3]
def baseStart_4408331 : Nat := 118140960795 + 4408331 * 2 ^ 59
def prefixEnd_4408331 : Nat := 4983230072969 + 3 ^ 40 * 4408331 * 2
def baseEnd_4408331 : Nat := 2263592687115497118388961

theorem tailTrace_4408331 : CollatzResearch.WordTrace tailWord_4408331 prefixEnd_4408331 2263592687115497118388961 := by
  unfold tailWord_4408331
  simp only [CollatzResearch.WordTrace]
  refine ⟨160785040592377144839832847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107190027061584763226555231 160785040592377144839832847)
  ·
    refine ⟨241177560888565717259749271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160785040592377144839832847 241177560888565717259749271)
    ·
      refine ⟨361766341332848575889623907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241177560888565717259749271 361766341332848575889623907)
      ·
        refine ⟨542649511999272863834435861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361766341332848575889623907 542649511999272863834435861)
        ·
          refine ⟨25436695874965915492239181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 542649511999272863834435861 25436695874965915492239181)
          ·
            refine ⟨9538760953112218309589693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25436695874965915492239181 9538760953112218309589693)
            ·
              refine ⟨3577035357417081866096135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9538760953112218309589693 3577035357417081866096135)
              ·
                refine ⟨5365553036125622799144203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3577035357417081866096135 5365553036125622799144203)
                ·
                  refine ⟨8048329554188434198716305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5365553036125622799144203 8048329554188434198716305)
                  ·
                    refine ⟨6036247165641325649037229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8048329554188434198716305 6036247165641325649037229)
                    ·
                      refine ⟨2263592687115497118388961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6036247165641325649037229 2263592687115497118388961)
                      ·
                        rfl

theorem cell23_4408331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 2, 3].length) (baseStart_4408331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408331 prefixEnd_4408331 := by exact prefixLift 4408331
  have htrace : WordTrace (prefixWord ++ tailWord_4408331) baseStart_4408331 baseEnd_4408331 := by
    simpa [prefixWord, tailWord_4408331, baseEnd_4408331] using wordTrace_append hprefix tailTrace_4408331
  have hstable : (prefixWord ++ tailWord_4408331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408331).length < 2 ^ (prefixWord ++ tailWord_4408331).sum := by decide
  have hdescent : baseEnd_4408331 < baseStart_4408331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408384 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 1, 4, 2]
def baseStart_4408384 : Nat := 118140960795 + 4408384 * 2 ^ 59
def prefixEnd_4408384 : Nat := 4983230072969 + 3 ^ 40 * 4408384 * 2
def baseEnd_4408384 : Nat := 2263619901590185411026217

theorem tailTrace_4408384 : CollatzResearch.WordTrace tailWord_4408384 prefixEnd_4408384 2263619901590185411026217 := by
  unfold tailWord_4408384
  simp only [CollatzResearch.WordTrace]
  refine ⟨80393486830592567445756103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107191315774123423261008137 80393486830592567445756103)
  ·
    refine ⟨120590230245888851168634155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80393486830592567445756103 120590230245888851168634155)
    ·
      refine ⟨180885345368833276752951233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120590230245888851168634155 180885345368833276752951233)
      ·
        refine ⟨135664009026624957564713425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180885345368833276752951233 135664009026624957564713425)
        ·
          refine ⟨101748006769968718173535069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135664009026624957564713425 101748006769968718173535069)
          ·
            refine ⟨38155502538738269315075651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101748006769968718173535069 38155502538738269315075651)
            ·
              refine ⟨57233253808107403972613477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38155502538738269315075651 57233253808107403972613477)
              ·
                refine ⟨10731235089020138244865027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57233253808107403972613477 10731235089020138244865027)
                ·
                  refine ⟨16096852633530207367297541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10731235089020138244865027 16096852633530207367297541)
                  ·
                    refine ⟨3018159868786913881368289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16096852633530207367297541 3018159868786913881368289)
                    ·
                      refine ⟨2263619901590185411026217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018159868786913881368289 2263619901590185411026217)
                      ·
                        rfl

theorem cell23_4408384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_4408384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408384 prefixEnd_4408384 := by exact prefixLift 4408384
  have htrace : WordTrace (prefixWord ++ tailWord_4408384) baseStart_4408384 baseEnd_4408384 := by
    simpa [prefixWord, tailWord_4408384, baseEnd_4408384] using wordTrace_append hprefix tailTrace_4408384
  have hstable : (prefixWord ++ tailWord_4408384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408384).length < 2 ^ (prefixWord ++ tailWord_4408384).sum := by decide
  have hdescent : baseEnd_4408384 < baseStart_4408384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408418 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4408418 : Nat := 118140960795 + 4408418 * 2 ^ 59
def prefixEnd_4408418 : Nat := 4983230072969 + 3 ^ 40 * 4408418 * 2
def baseEnd_4408418 : Nat := 2263637359932438278001061

theorem tailTrace_4408418 : CollatzResearch.WordTrace tailWord_4408418 prefixEnd_4408418 2263637359932438278001061 := by
  unfold tailWord_4408418
  simp only [CollatzResearch.WordTrace]
  refine ⟨40197053435765489674562477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107192142495374639132166605 40197053435765489674562477)
  ·
    refine ⟨15073895038412058627960929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40197053435765489674562477 15073895038412058627960929)
    ·
      refine ⟨11305421278809043970970697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15073895038412058627960929 11305421278809043970970697)
      ·
        refine ⟨8479065959106782978228023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11305421278809043970970697 8479065959106782978228023)
        ·
          refine ⟨12718598938660174467342035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8479065959106782978228023 12718598938660174467342035)
          ·
            refine ⟨19077898407990261701013053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12718598938660174467342035 19077898407990261701013053)
            ·
              refine ⟨7154211902996348137879895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19077898407990261701013053 7154211902996348137879895)
              ·
                refine ⟨10731317854494522206819843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7154211902996348137879895 10731317854494522206819843)
                ·
                  refine ⟨16096976781741783310229765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10731317854494522206819843 16096976781741783310229765)
                  ·
                    refine ⟨3018183146576584370668081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16096976781741783310229765 3018183146576584370668081)
                    ·
                      refine ⟨2263637359932438278001061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018183146576584370668081 2263637359932438278001061)
                      ·
                        rfl

theorem cell23_4408418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4408418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408418 prefixEnd_4408418 := by exact prefixLift 4408418
  have htrace : WordTrace (prefixWord ++ tailWord_4408418) baseStart_4408418 baseEnd_4408418 := by
    simpa [prefixWord, tailWord_4408418, baseEnd_4408418] using wordTrace_append hprefix tailTrace_4408418
  have hstable : (prefixWord ++ tailWord_4408418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408418).length < 2 ^ (prefixWord ++ tailWord_4408418).sum := by decide
  have hdescent : baseEnd_4408418 < baseStart_4408418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408517 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_4408517 : Nat := 118140960795 + 4408517 * 2 ^ 59
def prefixEnd_4408517 : Nat := 4983230072969 + 3 ^ 40 * 4408517 * 2
def baseEnd_4408517 : Nat := 2263688194517233390663105

theorem tailTrace_4408517 : CollatzResearch.WordTrace tailWord_4408517 prefixEnd_4408517 2263688194517233390663105 := by
  unfold tailWord_4408517
  simp only [CollatzResearch.WordTrace]
  refine ⟨160791824569703298606103805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107194549713135532404069203 160791824569703298606103805)
  ·
    refine ⟨60296934213638736977288927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160791824569703298606103805 60296934213638736977288927)
    ·
      refine ⟨90445401320458105465933391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60296934213638736977288927 90445401320458105465933391)
      ·
        refine ⟨135668101980687158198900087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90445401320458105465933391 135668101980687158198900087)
        ·
          refine ⟨203502152971030737298350131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135668101980687158198900087 203502152971030737298350131)
          ·
            refine ⟨305253229456546105947525197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203502152971030737298350131 305253229456546105947525197)
            ·
              refine ⟨114469961046204789730321949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305253229456546105947525197 114469961046204789730321949)
              ·
                refine ⟨42926235392326796148870731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114469961046204789730321949 42926235392326796148870731)
                ·
                  refine ⟨64389353088490194223306097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42926235392326796148870731 64389353088490194223306097)
                  ·
                    refine ⟨48292014816367645667479573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64389353088490194223306097 48292014816367645667479573)
                    ·
                      refine ⟨2263688194517233390663105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48292014816367645667479573 2263688194517233390663105)
                      ·
                        rfl

theorem cell23_4408517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_4408517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408517 prefixEnd_4408517 := by exact prefixLift 4408517
  have htrace : WordTrace (prefixWord ++ tailWord_4408517) baseStart_4408517 baseEnd_4408517 := by
    simpa [prefixWord, tailWord_4408517, baseEnd_4408517] using wordTrace_append hprefix tailTrace_4408517
  have hstable : (prefixWord ++ tailWord_4408517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408517).length < 2 ^ (prefixWord ++ tailWord_4408517).sum := by decide
  have hdescent : baseEnd_4408517 < baseStart_4408517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408537 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_4408537 : Nat := 118140960795 + 4408537 * 2 ^ 59
def prefixEnd_4408537 : Nat := 4983230072969 + 3 ^ 40 * 4408537 * 2
def baseEnd_4408537 : Nat := 2263698464130323312413013

theorem tailTrace_4408537 : CollatzResearch.WordTrace tailWord_4408537 prefixEnd_4408537 2263698464130323312413013 := by
  unfold tailWord_4408537
  simp only [CollatzResearch.WordTrace]
  refine ⟨160792554029630842021831865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107195036019753894681221243 160792554029630842021831865)
  ·
    refine ⟨120594415522223131516373899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160792554029630842021831865 120594415522223131516373899)
    ·
      refine ⟨180891623283334697274560849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120594415522223131516373899 180891623283334697274560849)
      ·
        refine ⟨135668717462501022955920637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180891623283334697274560849 135668717462501022955920637)
        ·
          refine ⟨50875769048437883608470239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135668717462501022955920637 50875769048437883608470239)
          ·
            refine ⟨76313653572656825412705359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50875769048437883608470239 76313653572656825412705359)
            ·
              refine ⟨114470480358985238119058039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76313653572656825412705359 114470480358985238119058039)
              ·
                refine ⟨171705720538477857178587059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114470480358985238119058039 171705720538477857178587059)
                ·
                  refine ⟨257558580807716785767880589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171705720538477857178587059 257558580807716785767880589)
                  ·
                    refine ⟨96584467802893794662955221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 257558580807716785767880589 96584467802893794662955221)
                    ·
                      refine ⟨2263698464130323312413013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96584467802893794662955221 2263698464130323312413013)
                      ·
                        rfl

theorem cell23_4408537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_4408537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408537 prefixEnd_4408537 := by exact prefixLift 4408537
  have htrace : WordTrace (prefixWord ++ tailWord_4408537) baseStart_4408537 baseEnd_4408537 := by
    simpa [prefixWord, tailWord_4408537, baseEnd_4408537] using wordTrace_append hprefix tailTrace_4408537
  have hstable : (prefixWord ++ tailWord_4408537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408537).length < 2 ^ (prefixWord ++ tailWord_4408537).sum := by decide
  have hdescent : baseEnd_4408537 < baseStart_4408537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408544 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_4408544 : Nat := 118140960795 + 4408544 * 2 ^ 59
def prefixEnd_4408544 : Nat := 4983230072969 + 3 ^ 40 * 4408544 * 2
def baseEnd_4408544 : Nat := 754567352831634928341827

theorem tailTrace_4408544 : CollatzResearch.WordTrace tailWord_4408544 prefixEnd_4408544 754567352831634928341827 := by
  unfold tailWord_4408544
  simp only [CollatzResearch.WordTrace]
  refine ⟨80396404670302741108668343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107195206227070321478224457 80396404670302741108668343)
  ·
    refine ⟨120594607005454111663002515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80396404670302741108668343 120594607005454111663002515)
    ·
      refine ⟨180891910508181167494503773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120594607005454111663002515 180891910508181167494503773)
      ·
        refine ⟨67834466440567937810438915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180891910508181167494503773 67834466440567937810438915)
        ·
          refine ⟨101751699660851906715658373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67834466440567937810438915 101751699660851906715658373)
          ·
            refine ⟨19078443686409732509185945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101751699660851906715658373 19078443686409732509185945)
            ·
              refine ⟨14308832764807299381889459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19078443686409732509185945 14308832764807299381889459)
              ·
                refine ⟨21463249147210949072834189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14308832764807299381889459 21463249147210949072834189)
                ·
                  refine ⟨8048718430204105902312821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21463249147210949072834189 8048718430204105902312821)
                  ·
                    refine ⟨754567352831634928341827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8048718430204105902312821 754567352831634928341827)
                    ·
                      rfl

theorem cell23_4408544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_4408544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408544 prefixEnd_4408544 := by exact prefixLift 4408544
  have htrace : WordTrace (prefixWord ++ tailWord_4408544) baseStart_4408544 baseEnd_4408544 := by
    simpa [prefixWord, tailWord_4408544, baseEnd_4408544] using wordTrace_append hprefix tailTrace_4408544
  have hstable : (prefixWord ++ tailWord_4408544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408544).length < 2 ^ (prefixWord ++ tailWord_4408544).sum := by decide
  have hdescent : baseEnd_4408544 < baseStart_4408544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408618 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4408618 : Nat := 118140960795 + 4408618 * 2 ^ 59
def prefixEnd_4408618 : Nat := 4983230072969 + 3 ^ 40 * 4408618 * 2
def baseEnd_4408618 : Nat := 2263740056063337495500141

theorem tailTrace_4408618 : CollatzResearch.WordTrace tailWord_4408618 prefixEnd_4408618 2263740056063337495500141 := by
  unfold tailWord_4408618
  simp only [CollatzResearch.WordTrace]
  refine ⟨40198877085584348213882627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107197005561558261903687005 40198877085584348213882627)
  ·
    refine ⟨60298315628376522320823941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40198877085584348213882627 60298315628376522320823941)
    ·
      refine ⟨11305934180320597935154489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60298315628376522320823941 11305934180320597935154489)
      ·
        refine ⟨8479450635240448451365867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11305934180320597935154489 8479450635240448451365867)
        ·
          refine ⟨12719175952860672677048801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8479450635240448451365867 12719175952860672677048801)
          ·
            refine ⟨9539381964645504507786601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12719175952860672677048801 9539381964645504507786601)
            ·
              refine ⟨7154536473484128380839951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9539381964645504507786601 7154536473484128380839951)
              ·
                refine ⟨10731804710226192571259927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7154536473484128380839951 10731804710226192571259927)
                ·
                  refine ⟨16097707065339288856889891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10731804710226192571259927 16097707065339288856889891)
                  ·
                    refine ⟨24146560598008933285334837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16097707065339288856889891 24146560598008933285334837)
                    ·
                      refine ⟨2263740056063337495500141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24146560598008933285334837 2263740056063337495500141)
                      ·
                        rfl

theorem cell23_4408618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4408618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408618 prefixEnd_4408618 := by exact prefixLift 4408618
  have htrace : WordTrace (prefixWord ++ tailWord_4408618) baseStart_4408618 baseEnd_4408618 := by
    simpa [prefixWord, tailWord_4408618, baseEnd_4408618] using wordTrace_append hprefix tailTrace_4408618
  have hstable : (prefixWord ++ tailWord_4408618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408618).length < 2 ^ (prefixWord ++ tailWord_4408618).sum := by decide
  have hdescent : baseEnd_4408618 < baseStart_4408618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408621 : List Nat := [1, 5, 3, 1, 1, 1, 11]
def baseStart_4408621 : Nat := 118140960795 + 4408621 * 2 ^ 59
def prefixEnd_4408621 : Nat := 4983230072969 + 3 ^ 40 * 4408621 * 2
def baseEnd_4408621 : Nat := 27947427117349394861267

theorem tailTrace_4408621 : CollatzResearch.WordTrace tailWord_4408621 prefixEnd_4408621 27947427117349394861267 := by
  unfold tailWord_4408621
  simp only [CollatzResearch.WordTrace]
  refine ⟨160795617761326524367889717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107197078507551016245259811 160795617761326524367889717)
  ·
    refine ⟨15074589165124361659489661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160795617761326524367889717 15074589165124361659489661)
    ·
      refine ⟨5652970936921635622308623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15074589165124361659489661 5652970936921635622308623)
      ·
        refine ⟨8479456405382453433462935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5652970936921635622308623 8479456405382453433462935)
        ·
          refine ⟨12719184608073680150194403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8479456405382453433462935 12719184608073680150194403)
          ·
            refine ⟨19078776912110520225291605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12719184608073680150194403 19078776912110520225291605)
            ·
              refine ⟨27947427117349394861267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19078776912110520225291605 27947427117349394861267)
              ·
                rfl

theorem cell23_4408621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 11].length) (baseStart_4408621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408621 prefixEnd_4408621 := by exact prefixLift 4408621
  have htrace : WordTrace (prefixWord ++ tailWord_4408621) baseStart_4408621 baseEnd_4408621 := by
    simpa [prefixWord, tailWord_4408621, baseEnd_4408621] using wordTrace_append hprefix tailTrace_4408621
  have hstable : (prefixWord ++ tailWord_4408621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408621).length < 2 ^ (prefixWord ++ tailWord_4408621).sum := by decide
  have hdescent : baseEnd_4408621 < baseStart_4408621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408634 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_4408634 : Nat := 118140960795 + 4408634 * 2 ^ 59
def prefixEnd_4408634 : Nat := 4983230072969 + 3 ^ 40 * 4408634 * 2
def baseEnd_4408634 : Nat := 754582757251269810966689

theorem tailTrace_4408634 : CollatzResearch.WordTrace tailWord_4408634 prefixEnd_4408634 754582757251269810966689 := by
  unfold tailWord_4408634
  simp only [CollatzResearch.WordTrace]
  refine ⟨40199022977569856897028239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107197394606852951725408637 40199022977569856897028239)
  ·
    refine ⟨60298534466354785345542359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40199022977569856897028239 60298534466354785345542359)
    ·
      refine ⟨90447801699532178018313539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60298534466354785345542359 90447801699532178018313539)
      ·
        refine ⟨135671702549298267027470309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90447801699532178018313539 135671702549298267027470309)
        ·
          refine ⟨25438444227993425067650683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135671702549298267027470309 25438444227993425067650683)
          ·
            refine ⟨38157666341990137601476025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25438444227993425067650683 38157666341990137601476025)
            ·
              refine ⟨28618249756492603201107019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38157666341990137601476025 28618249756492603201107019)
              ·
                refine ⟨42927374634738904801660529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28618249756492603201107019 42927374634738904801660529)
                ·
                  refine ⟨32195530976054178601245397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42927374634738904801660529 32195530976054178601245397)
                  ·
                    refine ⟨754582757251269810966689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32195530976054178601245397 754582757251269810966689)
                    ·
                      rfl

theorem cell23_4408634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_4408634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408634 prefixEnd_4408634 := by exact prefixLift 4408634
  have htrace : WordTrace (prefixWord ++ tailWord_4408634) baseStart_4408634 baseEnd_4408634 := by
    simpa [prefixWord, tailWord_4408634, baseEnd_4408634] using wordTrace_append hprefix tailTrace_4408634
  have hstable : (prefixWord ++ tailWord_4408634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408634).length < 2 ^ (prefixWord ++ tailWord_4408634).sum := by decide
  have hdescent : baseEnd_4408634 < baseStart_4408634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408669 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4408669 : Nat := 118140960795 + 4408669 * 2 ^ 59
def prefixEnd_4408669 : Nat := 4983230072969 + 3 ^ 40 * 4408669 * 2
def baseEnd_4408669 : Nat := 2263766243576716795962407

theorem tailTrace_4408669 : CollatzResearch.WordTrace tailWord_4408669 prefixEnd_4408669 2263766243576716795962407 := by
  unfold tailWord_4408669
  simp only [CollatzResearch.WordTrace]
  refine ⟨160797368465152628565637061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107198245643435085710424707 160797368465152628565637061)
  ·
    refine ⟨30149506587216117856056949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160797368465152628565637061 30149506587216117856056949)
    ·
      refine ⟨2826516242551511049005339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30149506587216117856056949 2826516242551511049005339)
      ·
        refine ⟨4239774363827266573508009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826516242551511049005339 4239774363827266573508009)
        ·
          refine ⟨3179830772870449930131007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4239774363827266573508009 3179830772870449930131007)
          ·
            refine ⟨4769746159305674895196511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179830772870449930131007 4769746159305674895196511)
            ·
              refine ⟨7154619238958512342794767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4769746159305674895196511 7154619238958512342794767)
              ·
                refine ⟨10731928858437768514192151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7154619238958512342794767 10731928858437768514192151)
                ·
                  refine ⟨16097893287656652771288227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10731928858437768514192151 16097893287656652771288227)
                  ·
                    refine ⟨24146839931484979156932341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16097893287656652771288227 24146839931484979156932341)
                    ·
                      refine ⟨2263766243576716795962407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24146839931484979156932341 2263766243576716795962407)
                      ·
                        rfl

theorem cell23_4408669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4408669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408669 prefixEnd_4408669 := by exact prefixLift 4408669
  have htrace : WordTrace (prefixWord ++ tailWord_4408669) baseStart_4408669 baseEnd_4408669 := by
    simpa [prefixWord, tailWord_4408669, baseEnd_4408669] using wordTrace_append hprefix tailTrace_4408669
  have hstable : (prefixWord ++ tailWord_4408669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408669).length < 2 ^ (prefixWord ++ tailWord_4408669).sum := by decide
  have hdescent : baseEnd_4408669 < baseStart_4408669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408682 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4408682 : Nat := 118140960795 + 4408682 * 2 ^ 59
def prefixEnd_4408682 : Nat := 4983230072969 + 3 ^ 40 * 4408682 * 2
def baseEnd_4408682 : Nat := 2263772918825225245099847

theorem tailTrace_4408682 : CollatzResearch.WordTrace tailWord_4408682 prefixEnd_4408682 2263772918825225245099847 := by
  unfold tailWord_4408682
  simp only [CollatzResearch.WordTrace]
  refine ⟨40199460653526382946465075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107198561742737021190573533 40199460653526382946465075)
  ·
    refine ⟨60299190980289574419697613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40199460653526382946465075 60299190980289574419697613)
    ·
      refine ⟨22612196617608590407386605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60299190980289574419697613 22612196617608590407386605)
      ·
        refine ⟨8479573731603221402769977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22612196617608590407386605 8479573731603221402769977)
        ·
          refine ⟨6359680298702416052077483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8479573731603221402769977 6359680298702416052077483)
          ·
            refine ⟨9539520448053624078116225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359680298702416052077483 9539520448053624078116225)
            ·
              refine ⟨7154640336040218058587169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9539520448053624078116225 7154640336040218058587169)
              ·
                refine ⟨5365980252030163543940377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7154640336040218058587169 5365980252030163543940377)
                ·
                  refine ⟨4024485189022622657955283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5365980252030163543940377 4024485189022622657955283)
                  ·
                    refine ⟨6036727783533933986932925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024485189022622657955283 6036727783533933986932925)
                    ·
                      refine ⟨2263772918825225245099847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6036727783533933986932925 2263772918825225245099847)
                      ·
                        rfl

theorem cell23_4408682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4408682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408682 prefixEnd_4408682 := by exact prefixLift 4408682
  have htrace : WordTrace (prefixWord ++ tailWord_4408682) baseStart_4408682 baseEnd_4408682 := by
    simpa [prefixWord, tailWord_4408682, baseEnd_4408682] using wordTrace_append hprefix tailTrace_4408682
  have hstable : (prefixWord ++ tailWord_4408682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408682).length < 2 ^ (prefixWord ++ tailWord_4408682).sum := by decide
  have hdescent : baseEnd_4408682 < baseStart_4408682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408701 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_4408701 : Nat := 118140960795 + 4408701 * 2 ^ 59
def prefixEnd_4408701 : Nat := 4983230072969 + 3 ^ 40 * 4408701 * 2
def baseEnd_4408701 : Nat := 2263782674957660670762259

theorem tailTrace_4408701 : CollatzResearch.WordTrace tailWord_4408701 prefixEnd_4408701 2263782674957660670762259 := by
  unfold tailWord_4408701
  simp only [CollatzResearch.WordTrace]
  refine ⟨160798535601036698030801957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107199023734024465353867971 160798535601036698030801957)
  ·
    refine ⟨30149725425194380880775367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160798535601036698030801957 30149725425194380880775367)
    ·
      refine ⟨45224588137791571321163051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30149725425194380880775367 45224588137791571321163051)
      ·
        refine ⟨67836882206687356981744577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45224588137791571321163051 67836882206687356981744577)
        ·
          refine ⟨50877661655015517736308433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67836882206687356981744577 50877661655015517736308433)
          ·
            refine ⟨38158246241261638302231325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50877661655015517736308433 38158246241261638302231325)
            ·
              refine ⟨14309342340473114363336747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38158246241261638302231325 14309342340473114363336747)
              ·
                refine ⟨21464013510709671545005121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14309342340473114363336747 21464013510709671545005121)
                ·
                  refine ⟨16098010133032253658753841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21464013510709671545005121 16098010133032253658753841)
                  ·
                    refine ⟨12073507599774190244065381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16098010133032253658753841 12073507599774190244065381)
                    ·
                      refine ⟨2263782674957660670762259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12073507599774190244065381 2263782674957660670762259)
                      ·
                        rfl

theorem cell23_4408701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_4408701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408701 prefixEnd_4408701 := by exact prefixLift 4408701
  have htrace : WordTrace (prefixWord ++ tailWord_4408701) baseStart_4408701 baseEnd_4408701 := by
    simpa [prefixWord, tailWord_4408701, baseEnd_4408701] using wordTrace_append hprefix tailTrace_4408701
  have hstable : (prefixWord ++ tailWord_4408701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408701).length < 2 ^ (prefixWord ++ tailWord_4408701).sum := by decide
  have hdescent : baseEnd_4408701 < baseStart_4408701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408711 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 7]
def baseStart_4408711 : Nat := 118140960795 + 4408711 * 2 ^ 59
def prefixEnd_4408711 : Nat := 4983230072969 + 3 ^ 40 * 4408711 * 2
def baseEnd_4408711 : Nat := 251531978862689514626357

theorem tailTrace_4408711 : CollatzResearch.WordTrace tailWord_4408711 prefixEnd_4408711 251531978862689514626357 := by
  unfold tailWord_4408711
  simp only [CollatzResearch.WordTrace]
  refine ⟨160798900331000469738665987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107199266887333646492443991 160798900331000469738665987)
  ·
    refine ⟨241198350496500704607998981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160798900331000469738665987 241198350496500704607998981)
    ·
      refine ⟨45224690718093882113999809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241198350496500704607998981 45224690718093882113999809)
      ·
        refine ⟨33918518038570411585499857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45224690718093882113999809 33918518038570411585499857)
        ·
          refine ⟨25438888528927808689124893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33918518038570411585499857 25438888528927808689124893)
          ·
            refine ⟨9539583198347928258421835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25438888528927808689124893 9539583198347928258421835)
            ·
              refine ⟨14309374797521892387632753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9539583198347928258421835 14309374797521892387632753)
              ·
                refine ⟨10732031098141419290724565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14309374797521892387632753 10732031098141419290724565)
                ·
                  refine ⟨251531978862689514626357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10732031098141419290724565 251531978862689514626357)
                  ·
                    rfl

theorem cell23_4408711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 7].length) (baseStart_4408711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408711 prefixEnd_4408711 := by exact prefixLift 4408711
  have htrace : WordTrace (prefixWord ++ tailWord_4408711) baseStart_4408711 baseEnd_4408711 := by
    simpa [prefixWord, tailWord_4408711, baseEnd_4408711] using wordTrace_append hprefix tailTrace_4408711
  have hstable : (prefixWord ++ tailWord_4408711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408711).length < 2 ^ (prefixWord ++ tailWord_4408711).sum := by decide
  have hdescent : baseEnd_4408711 < baseStart_4408711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408738 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_4408738 : Nat := 118140960795 + 4408738 * 2 ^ 59
def prefixEnd_4408738 : Nat := 4983230072969 + 3 ^ 40 * 4408738 * 2
def baseEnd_4408738 : Nat := 2263801673741877025999589

theorem tailTrace_4408738 : CollatzResearch.WordTrace tailWord_4408738 prefixEnd_4408738 2263801673741877025999589 := by
  unfold tailWord_4408738
  simp only [CollatzResearch.WordTrace]
  refine ⟨40199971275475663337474717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107199923401268435566599245 40199971275475663337474717)
  ·
    refine ⟨15074989228303373751553019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40199971275475663337474717 15074989228303373751553019)
    ·
      refine ⟨22612483842455060627329529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15074989228303373751553019 22612483842455060627329529)
      ·
        refine ⟨16959362881841295470497147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22612483842455060627329529 16959362881841295470497147)
        ·
          refine ⟨25439044322761943205745721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16959362881841295470497147 25439044322761943205745721)
          ·
            refine ⟨19079283242071457404309291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25439044322761943205745721 19079283242071457404309291)
            ·
              refine ⟨28618924863107186106463937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19079283242071457404309291 28618924863107186106463937)
              ·
                refine ⟨21464193647330389579847953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28618924863107186106463937 21464193647330389579847953)
                ·
                  refine ⟨16098145235497792184885965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21464193647330389579847953 16098145235497792184885965)
                  ·
                    refine ⟨6036804463311672069332237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16098145235497792184885965 6036804463311672069332237)
                    ·
                      refine ⟨2263801673741877025999589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6036804463311672069332237 2263801673741877025999589)
                      ·
                        rfl

theorem cell23_4408738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_4408738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408738 prefixEnd_4408738 := by exact prefixLift 4408738
  have htrace : WordTrace (prefixWord ++ tailWord_4408738) baseStart_4408738 baseEnd_4408738 := by
    simpa [prefixWord, tailWord_4408738, baseEnd_4408738] using wordTrace_append hprefix tailTrace_4408738
  have hstable : (prefixWord ++ tailWord_4408738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408738).length < 2 ^ (prefixWord ++ tailWord_4408738).sum := by decide
  have hdescent : baseEnd_4408738 < baseStart_4408738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408801 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 8]
def baseStart_4408801 : Nat := 118140960795 + 4408801 * 2 ^ 59
def prefixEnd_4408801 : Nat := 4983230072969 + 3 ^ 40 * 4408801 * 2
def baseEnd_4408801 : Nat := 251537113669234475501311

theorem tailTrace_4408801 : CollatzResearch.WordTrace tailWord_4408801 prefixEnd_4408801 251537113669234475501311 := by
  unfold tailWord_4408801
  simp only [CollatzResearch.WordTrace]
  refine ⟨160802182900674415109442257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107201455267116276739628171 160802182900674415109442257)
  ·
    refine ⟨120601637175505811332081693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160802182900674415109442257 120601637175505811332081693)
    ·
      refine ⟨45225613940814679249530635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120601637175505811332081693 45225613940814679249530635)
      ·
        refine ⟨67838420911222018874295953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45225613940814679249530635 67838420911222018874295953)
        ·
          refine ⟨50878815683416514155721965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67838420911222018874295953 50878815683416514155721965)
          ·
            refine ⟨19079555881281192808395737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50878815683416514155721965 19079555881281192808395737)
            ·
              refine ⟨14309666910960894606296803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19079555881281192808395737 14309666910960894606296803)
              ·
                refine ⟨21464500366441341909445205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14309666910960894606296803 21464500366441341909445205)
                ·
                  refine ⟨251537113669234475501311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21464500366441341909445205 251537113669234475501311)
                  ·
                    rfl

theorem cell23_4408801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_4408801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408801 prefixEnd_4408801 := by exact prefixLift 4408801
  have htrace : WordTrace (prefixWord ++ tailWord_4408801) baseStart_4408801 baseEnd_4408801 := by
    simpa [prefixWord, tailWord_4408801, baseEnd_4408801] using wordTrace_append hprefix tailTrace_4408801
  have hstable : (prefixWord ++ tailWord_4408801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408801).length < 2 ^ (prefixWord ++ tailWord_4408801).sum := by decide
  have hdescent : baseEnd_4408801 < baseStart_4408801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408805 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_4408805 : Nat := 118140960795 + 4408805 * 2 ^ 59
def prefixEnd_4408805 : Nat := 4983230072969 + 3 ^ 40 * 4408805 * 2
def baseEnd_4408805 : Nat := 754612025648576087953927

theorem tailTrace_4408805 : CollatzResearch.WordTrace tailWord_4408805 prefixEnd_4408805 754612025648576087953927 := by
  unfold tailWord_4408805
  simp only [CollatzResearch.WordTrace]
  refine ⟨160802328792659923792587869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107201552528439949195058579 160802328792659923792587869)
  ·
    refine ⟨60300873297247471422220451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160802328792659923792587869 60300873297247471422220451)
    ·
      refine ⟨90451309945871207133330677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60300873297247471422220451 90451309945871207133330677)
      ·
        refine ⟨8479810307425425668749751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90451309945871207133330677 8479810307425425668749751)
        ·
          refine ⟨12719715461138138503124627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8479810307425425668749751 12719715461138138503124627)
          ·
            refine ⟨19079573191707207754686941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12719715461138138503124627 19079573191707207754686941)
            ·
              refine ⟨7154839946890202908007603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19079573191707207754686941 7154839946890202908007603)
              ·
                refine ⟨10732259920335304362011405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7154839946890202908007603 10732259920335304362011405)
                ·
                  refine ⟨4024597470125739135754277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10732259920335304362011405 4024597470125739135754277)
                  ·
                    refine ⟨754612025648576087953927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024597470125739135754277 754612025648576087953927)
                    ·
                      rfl

theorem cell23_4408805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_4408805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408805 prefixEnd_4408805 := by exact prefixLift 4408805
  have htrace : WordTrace (prefixWord ++ tailWord_4408805) baseStart_4408805 baseEnd_4408805 := by
    simpa [prefixWord, tailWord_4408805, baseEnd_4408805] using wordTrace_append hprefix tailTrace_4408805
  have hstable : (prefixWord ++ tailWord_4408805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408805).length < 2 ^ (prefixWord ++ tailWord_4408805).sum := by decide
  have hdescent : baseEnd_4408805 < baseStart_4408805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408811 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 3]
def baseStart_4408811 : Nat := 118140960795 + 4408811 * 2 ^ 59
def prefixEnd_4408811 : Nat := 4983230072969 + 3 ^ 40 * 4408811 * 2
def baseEnd_4408811 : Nat := 2263839157829655240386753

theorem tailTrace_4408811 : CollatzResearch.WordTrace tailWord_4408811 prefixEnd_4408811 2263839157829655240386753 := by
  unfold tailWord_4408811
  simp only [CollatzResearch.WordTrace]
  refine ⟨160802547630638186817306287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107201698420425457878204191 160802547630638186817306287)
  ·
    refine ⟨241203821445957280225959431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160802547630638186817306287 241203821445957280225959431)
    ·
      refine ⟨361805732168935920338939147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241203821445957280225959431 361805732168935920338939147)
      ·
        refine ⟨542708598253403880508408721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361805732168935920338939147 542708598253403880508408721)
        ·
          refine ⟨407031448690052910381306541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542708598253403880508408721 407031448690052910381306541)
          ·
            refine ⟨152636793258769841392989953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 407031448690052910381306541 152636793258769841392989953)
            ·
              refine ⟨114477594944077381044742465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152636793258769841392989953 114477594944077381044742465)
              ·
                refine ⟨85858196208058035783556849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114477594944077381044742465 85858196208058035783556849)
                ·
                  refine ⟨64393647156043526837667637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85858196208058035783556849 64393647156043526837667637)
                  ·
                    refine ⟨6036904420879080641031341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64393647156043526837667637 6036904420879080641031341)
                    ·
                      refine ⟨2263839157829655240386753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6036904420879080641031341 2263839157829655240386753)
                      ·
                        rfl

theorem cell23_4408811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 3].length) (baseStart_4408811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408811 prefixEnd_4408811 := by exact prefixLift 4408811
  have htrace : WordTrace (prefixWord ++ tailWord_4408811) baseStart_4408811 baseEnd_4408811 := by
    simpa [prefixWord, tailWord_4408811, baseEnd_4408811] using wordTrace_append hprefix tailTrace_4408811
  have hstable : (prefixWord ++ tailWord_4408811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408811).length < 2 ^ (prefixWord ++ tailWord_4408811).sum := by decide
  have hdescent : baseEnd_4408811 < baseStart_4408811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408852 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 6]
def baseStart_4408852 : Nat := 118140960795 + 4408852 * 2 ^ 59
def prefixEnd_4408852 : Nat := 4983230072969 + 3 ^ 40 * 4408852 * 2
def baseEnd_4408852 : Nat := 251540023392943286663785

theorem tailTrace_4408852 : CollatzResearch.WordTrace tailWord_4408852 prefixEnd_4408852 251540023392943286663785 := by
  unfold tailWord_4408852
  simp only [CollatzResearch.WordTrace]
  refine ⟨80402021511744825409774405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107202695348993100546365873 80402021511744825409774405)
  ·
    refine ⟨15075379033452154764332701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80402021511744825409774405 15075379033452154764332701)
    ·
      refine ⟨5653267137544558036624763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15075379033452154764332701 5653267137544558036624763)
      ·
        refine ⟨8479900706316837054937145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5653267137544558036624763 8479900706316837054937145)
        ·
          refine ⟨6359925529737627791202859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8479900706316837054937145 6359925529737627791202859)
          ·
            refine ⟨9539888294606441686804289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359925529737627791202859 9539888294606441686804289)
            ·
              refine ⟨7154916220954831265103217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9539888294606441686804289 7154916220954831265103217)
              ·
                refine ⟨5366187165716123448827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7154916220954831265103217 5366187165716123448827413)
                ·
                  refine ⟨251540023392943286663785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5366187165716123448827413 251540023392943286663785)
                  ·
                    rfl

theorem cell23_4408852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_4408852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408852 prefixEnd_4408852 := by exact prefixLift 4408852
  have htrace : WordTrace (prefixWord ++ tailWord_4408852) baseStart_4408852 baseEnd_4408852 := by
    simpa [prefixWord, tailWord_4408852, baseEnd_4408852] using wordTrace_append hprefix tailTrace_4408852
  have hstable : (prefixWord ++ tailWord_4408852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408852).length < 2 ^ (prefixWord ++ tailWord_4408852).sum := by decide
  have hdescent : baseEnd_4408852 < baseStart_4408852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408856 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 1, 4]
def baseStart_4408856 : Nat := 118140960795 + 4408856 * 2 ^ 59
def prefixEnd_4408856 : Nat := 4983230072969 + 3 ^ 40 * 4408856 * 2
def baseEnd_4408856 : Nat := 754620754819702521441349

theorem tailTrace_4408856 : CollatzResearch.WordTrace tailWord_4408856 prefixEnd_4408856 754620754819702521441349 := by
  unfold tailWord_4408856
  simp only [CollatzResearch.WordTrace]
  refine ⟨80402094457737579751347211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107202792610316773001796281 80402094457737579751347211)
  ·
    refine ⟨120603141686606369627020817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80402094457737579751347211 120603141686606369627020817)
    ·
      refine ⟨90452356264954777220265613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120603141686606369627020817 90452356264954777220265613)
      ·
        refine ⟨33919633599358041457599605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90452356264954777220265613 33919633599358041457599605)
        ·
          refine ⟨3179965649939816386649963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33919633599358041457599605 3179965649939816386649963)
          ·
            refine ⟨4769948474909724579974945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179965649939816386649963 4769948474909724579974945)
            ·
              refine ⟨3577461356182293434981209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4769948474909724579974945 3577461356182293434981209)
              ·
                refine ⟨2683096017136720076235907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3577461356182293434981209 2683096017136720076235907)
                ·
                  refine ⟨4024644025705080114353861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683096017136720076235907 4024644025705080114353861)
                  ·
                    refine ⟨754620754819702521441349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024644025705080114353861 754620754819702521441349)
                    ·
                      rfl

theorem cell23_4408856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_4408856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408856 prefixEnd_4408856 := by exact prefixLift 4408856
  have htrace : WordTrace (prefixWord ++ tailWord_4408856) baseStart_4408856 baseEnd_4408856 := by
    simpa [prefixWord, tailWord_4408856, baseEnd_4408856] using wordTrace_append hprefix tailTrace_4408856
  have hstable : (prefixWord ++ tailWord_4408856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408856).length < 2 ^ (prefixWord ++ tailWord_4408856).sum := by decide
  have hdescent : baseEnd_4408856 < baseStart_4408856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408911 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_4408911 : Nat := 118140960795 + 4408911 * 2 ^ 59
def prefixEnd_4408911 : Nat := 4983230072969 + 3 ^ 40 * 4408911 * 2
def baseEnd_4408911 : Nat := 2263890505895104849136293

theorem tailTrace_4408911 : CollatzResearch.WordTrace tailWord_4408911 prefixEnd_4408911 2263890505895104849136293 := by
  unfold tailWord_4408911
  simp only [CollatzResearch.WordTrace]
  refine ⟨160806194930275903895946587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107204129953517269263964391 160806194930275903895946587)
  ·
    refine ⟨241209292395413855843919881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160806194930275903895946587 241209292395413855843919881)
    ·
      refine ⟨180906969296560391882939911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241209292395413855843919881 180906969296560391882939911)
      ·
        refine ⟨271360453944840587824409867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180906969296560391882939911 271360453944840587824409867)
        ·
          refine ⟨407040680917260881736614801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271360453944840587824409867 407040680917260881736614801)
          ·
            refine ⟨305280510687945661302461101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407040680917260881736614801 305280510687945661302461101)
            ·
              refine ⟨114480191507979622988422913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305280510687945661302461101 114480191507979622988422913)
              ·
                refine ⟨85860143630984717241317185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114480191507979622988422913 85860143630984717241317185)
                ·
                  refine ⟨64395107723238537930987889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85860143630984717241317185 64395107723238537930987889)
                  ·
                    refine ⟨48296330792428903448240917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64395107723238537930987889 48296330792428903448240917)
                    ·
                      refine ⟨2263890505895104849136293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48296330792428903448240917 2263890505895104849136293)
                      ·
                        rfl

theorem cell23_4408911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_4408911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408911 prefixEnd_4408911 := by exact prefixLift 4408911
  have htrace : WordTrace (prefixWord ++ tailWord_4408911) baseStart_4408911 baseEnd_4408911 := by
    simpa [prefixWord, tailWord_4408911, baseEnd_4408911] using wordTrace_append hprefix tailTrace_4408911
  have hstable : (prefixWord ++ tailWord_4408911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408911).length < 2 ^ (prefixWord ++ tailWord_4408911).sum := by decide
  have hdescent : baseEnd_4408911 < baseStart_4408911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408919 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 1, 2, 2]
def baseStart_4408919 : Nat := 118140960795 + 4408919 * 2 ^ 59
def prefixEnd_4408919 : Nat := 4983230072969 + 3 ^ 40 * 4408919 * 2
def baseEnd_4408919 : Nat := 2263894613740340817836257

theorem tailTrace_4408919 : CollatzResearch.WordTrace tailWord_4408919 prefixEnd_4408919 2263894613740340817836257 := by
  unfold tailWord_4408919
  simp only [CollatzResearch.WordTrace]
  refine ⟨160806486714246921262237811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107204324476164614174825207 160806486714246921262237811)
  ·
    refine ⟨241209730071370381893356717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160806486714246921262237811 241209730071370381893356717)
    ·
      refine ⟨90453648776763893210008769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241209730071370381893356717 90453648776763893210008769)
      ·
        refine ⟨67840236582572919907506577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90453648776763893210008769 67840236582572919907506577)
        ·
          refine ⟨50880177436929689930629933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67840236582572919907506577 50880177436929689930629933)
          ·
            refine ⟨19080066538848633723986225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50880177436929689930629933 19080066538848633723986225)
            ·
              refine ⟨14310049904136475292989669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19080066538848633723986225 14310049904136475292989669)
              ·
                refine ⟨2683134357025589117435563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14310049904136475292989669 2683134357025589117435563)
                ·
                  refine ⟨4024701535538383676153345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683134357025589117435563 4024701535538383676153345)
                  ·
                    refine ⟨3018526151653787757115009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4024701535538383676153345 3018526151653787757115009)
                    ·
                      refine ⟨2263894613740340817836257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018526151653787757115009 2263894613740340817836257)
                      ·
                        rfl

theorem cell23_4408919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_4408919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408919 prefixEnd_4408919 := by exact prefixLift 4408919
  have htrace : WordTrace (prefixWord ++ tailWord_4408919) baseStart_4408919 baseEnd_4408919 := by
    simpa [prefixWord, tailWord_4408919, baseEnd_4408919] using wordTrace_append hprefix tailTrace_4408919
  have hstable : (prefixWord ++ tailWord_4408919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408919).length < 2 ^ (prefixWord ++ tailWord_4408919).sum := by decide
  have hdescent : baseEnd_4408919 < baseStart_4408919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408921 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_4408921 : Nat := 118140960795 + 4408921 * 2 ^ 59
def prefixEnd_4408921 : Nat := 4983230072969 + 3 ^ 40 * 4408921 * 2
def baseEnd_4408921 : Nat := 754631880233883270003749

theorem tailTrace_4408921 : CollatzResearch.WordTrace tailWord_4408921 prefixEnd_4408921 754631880233883270003749 := by
  unfold tailWord_4408921
  simp only [CollatzResearch.WordTrace]
  refine ⟨160806559660239675603810617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107204373106826450402540411 160806559660239675603810617)
  ·
    refine ⟨120604919745179756702857963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160806559660239675603810617 120604919745179756702857963)
    ·
      refine ⟨180907379617769635054286945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120604919745179756702857963 180907379617769635054286945)
      ·
        refine ⟨135680534713327226290715209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180907379617769635054286945 135680534713327226290715209)
        ·
          refine ⟨101760401034995419718036407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135680534713327226290715209 101760401034995419718036407)
          ·
            refine ⟨152640601552493129577054611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101760401034995419718036407 152640601552493129577054611)
            ·
              refine ⟨228960902328739694365581917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152640601552493129577054611 228960902328739694365581917)
              ·
                refine ⟨85860338373277385387093219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228960902328739694365581917 85860338373277385387093219)
                ·
                  refine ⟨128790507559916078080639829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85860338373277385387093219 128790507559916078080639829)
                  ·
                    refine ⟨754631880233883270003749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128790507559916078080639829 754631880233883270003749)
                    ·
                      rfl

theorem cell23_4408921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_4408921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408921 prefixEnd_4408921 := by exact prefixLift 4408921
  have htrace : WordTrace (prefixWord ++ tailWord_4408921) baseStart_4408921 baseEnd_4408921 := by
    simpa [prefixWord, tailWord_4408921, baseEnd_4408921] using wordTrace_append hprefix tailTrace_4408921
  have hstable : (prefixWord ++ tailWord_4408921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408921).length < 2 ^ (prefixWord ++ tailWord_4408921).sum := by decide
  have hdescent : baseEnd_4408921 < baseStart_4408921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408935 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_4408935 : Nat := 118140960795 + 4408935 * 2 ^ 59
def prefixEnd_4408935 : Nat := 4983230072969 + 3 ^ 40 * 4408935 * 2
def baseEnd_4408935 : Nat := 2263902829430812755236183

theorem tailTrace_4408935 : CollatzResearch.WordTrace tailWord_4408935 prefixEnd_4408935 2263902829430812755236183 := by
  unfold tailWord_4408935
  simp only [CollatzResearch.WordTrace]
  refine ⟨160807070282188955994820259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107204713521459303996546839 160807070282188955994820259)
  ·
    refine ⟨241210605423283433992230389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160807070282188955994820259 241210605423283433992230389)
    ·
      refine ⟨22613494258432821936771599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241210605423283433992230389 22613494258432821936771599)
      ·
        refine ⟨33920241387649232905157399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22613494258432821936771599 33920241387649232905157399)
        ·
          refine ⟨50880362081473849357736099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33920241387649232905157399 50880362081473849357736099)
          ·
            refine ⟨76320543122210774036604149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50880362081473849357736099 76320543122210774036604149)
            ·
              refine ⟨7155050917707260065931639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76320543122210774036604149 7155050917707260065931639)
              ·
                refine ⟨10732576376560890098897459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7155050917707260065931639 10732576376560890098897459)
                ·
                  refine ⟨16098864564841335148346189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10732576376560890098897459 16098864564841335148346189)
                  ·
                    refine ⟨6037074211815500680629821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16098864564841335148346189 6037074211815500680629821)
                    ·
                      refine ⟨2263902829430812755236183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6037074211815500680629821 2263902829430812755236183)
                      ·
                        rfl

theorem cell23_4408935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_4408935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408935 prefixEnd_4408935 := by exact prefixLift 4408935
  have htrace : WordTrace (prefixWord ++ tailWord_4408935) baseStart_4408935 baseEnd_4408935 := by
    simpa [prefixWord, tailWord_4408935, baseEnd_4408935] using wordTrace_append hprefix tailTrace_4408935
  have hstable : (prefixWord ++ tailWord_4408935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408935).length < 2 ^ (prefixWord ++ tailWord_4408935).sum := by decide
  have hdescent : baseEnd_4408935 < baseStart_4408935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408942 : List Nat := [4, 1, 2, 2, 3, 2, 2, 7]
def baseStart_4408942 : Nat := 118140960795 + 4408942 * 2 ^ 59
def prefixEnd_4408942 : Nat := 4983230072969 + 3 ^ 40 * 4408942 * 2
def baseEnd_4408942 : Nat := 83848386066496082512913

theorem tailTrace_4408942 : CollatzResearch.WordTrace tailWord_4408942 prefixEnd_4408942 83848386066496082512913 := by
  unfold tailWord_4408942
  simp only [CollatzResearch.WordTrace]
  refine ⟨20100915699145449523790635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107204883728775730793550053 20100915699145449523790635)
  ·
    refine ⟨30151373548718174285685953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20100915699145449523790635 30151373548718174285685953)
    ·
      refine ⟨22613530161538630714264465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30151373548718174285685953 22613530161538630714264465)
      ·
        refine ⟨16960147621153973035698349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22613530161538630714264465 16960147621153973035698349)
        ·
          refine ⟨6360055357932739888386881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16960147621153973035698349 6360055357932739888386881)
          ·
            refine ⟨4770041518449554916290161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6360055357932739888386881 4770041518449554916290161)
            ·
              refine ⟨3577531138837166187217621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4770041518449554916290161 3577531138837166187217621)
              ·
                refine ⟨83848386066496082512913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3577531138837166187217621 83848386066496082512913)
                ·
                  rfl

theorem cell23_4408942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_4408942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408942 prefixEnd_4408942 := by exact prefixLift 4408942
  have htrace : WordTrace (prefixWord ++ tailWord_4408942) baseStart_4408942 baseEnd_4408942 := by
    simpa [prefixWord, tailWord_4408942, baseEnd_4408942] using wordTrace_append hprefix tailTrace_4408942
  have hstable : (prefixWord ++ tailWord_4408942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408942).length < 2 ^ (prefixWord ++ tailWord_4408942).sum := by decide
  have hdescent : baseEnd_4408942 < baseStart_4408942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4408945 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 3, 3, 2]
def baseStart_4408945 : Nat := 118140960795 + 4408945 * 2 ^ 59
def prefixEnd_4408945 : Nat := 4983230072969 + 3 ^ 40 * 4408945 * 2
def baseEnd_4408945 : Nat := 2263907964237357716111137

theorem tailTrace_4408945 : CollatzResearch.WordTrace tailWord_4408945 prefixEnd_4408945 2263907964237357716111137 := by
  unfold tailWord_4408945
  simp only [CollatzResearch.WordTrace]
  refine ⟨160807435012152727702684289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107204956674768485135122859 160807435012152727702684289)
  ·
    refine ⟨120605576259114545777013217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160807435012152727702684289 120605576259114545777013217)
    ·
      refine ⟨90454182194335909332759913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120605576259114545777013217 90454182194335909332759913)
      ·
        refine ⟨67840636645751931999569935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90454182194335909332759913 67840636645751931999569935)
        ·
          refine ⟨101760954968627897999354903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67840636645751931999569935 101760954968627897999354903)
          ·
            refine ⟨152641432452941846999032355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101760954968627897999354903 152641432452941846999032355)
            ·
              refine ⟨228962148679412770498548533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152641432452941846999032355 228962148679412770498548533)
              ·
                refine ⟨21465201438694947234238925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228962148679412770498548533 21465201438694947234238925)
                ·
                  refine ⟨8049450539510605212839597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21465201438694947234238925 8049450539510605212839597)
                  ·
                    refine ⟨3018543952316476954814849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8049450539510605212839597 3018543952316476954814849)
                    ·
                      refine ⟨2263907964237357716111137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018543952316476954814849 2263907964237357716111137)
                      ·
                        rfl

theorem cell23_4408945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_4408945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4408945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4408945 prefixEnd_4408945 := by exact prefixLift 4408945
  have htrace : WordTrace (prefixWord ++ tailWord_4408945) baseStart_4408945 baseEnd_4408945 := by
    simpa [prefixWord, tailWord_4408945, baseEnd_4408945] using wordTrace_append hprefix tailTrace_4408945
  have hstable : (prefixWord ++ tailWord_4408945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4408945).length < 2 ^ (prefixWord ++ tailWord_4408945).sum := by decide
  have hdescent : baseEnd_4408945 < baseStart_4408945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4408945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409042 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_4409042 : Nat := 118140960795 + 4409042 * 2 ^ 59
def prefixEnd_4409042 : Nat := 4983230072969 + 3 ^ 40 * 4409042 * 2
def baseEnd_4409042 : Nat := 2263957771860843836598191

theorem tailTrace_4409042 : CollatzResearch.WordTrace tailWord_4409042 prefixEnd_4409042 2263957771860843836598191 := by
  unfold tailWord_4409042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40202743223200328317241345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107207315261867542179310253 40202743223200328317241345)
  ·
    refine ⟨30152057417400246237931009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40202743223200328317241345 30152057417400246237931009)
    ·
      refine ⟨22614043063050184678448257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30152057417400246237931009 22614043063050184678448257)
      ·
        refine ⟨16960532297287638508836193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22614043063050184678448257 16960532297287638508836193)
        ·
          refine ⟨12720399222965728881627145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16960532297287638508836193 12720399222965728881627145)
          ·
            refine ⟨9540299417224296661220359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12720399222965728881627145 9540299417224296661220359)
            ·
              refine ⟨14310449125836444991830539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9540299417224296661220359 14310449125836444991830539)
              ·
                refine ⟨21465673688754667487745809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14310449125836444991830539 21465673688754667487745809)
                ·
                  refine ⟨16099255266566000615809357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21465673688754667487745809 16099255266566000615809357)
                  ·
                    refine ⟨6037220724962250230928509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16099255266566000615809357 6037220724962250230928509)
                    ·
                      refine ⟨2263957771860843836598191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6037220724962250230928509 2263957771860843836598191)
                      ·
                        rfl

theorem cell23_4409042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_4409042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409042 prefixEnd_4409042 := by exact prefixLift 4409042
  have htrace : WordTrace (prefixWord ++ tailWord_4409042) baseStart_4409042 baseEnd_4409042 := by
    simpa [prefixWord, tailWord_4409042, baseEnd_4409042] using wordTrace_append hprefix tailTrace_4409042
  have hstable : (prefixWord ++ tailWord_4409042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409042).length < 2 ^ (prefixWord ++ tailWord_4409042).sum := by decide
  have hdescent : baseEnd_4409042 < baseStart_4409042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409065 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 6, 2]
def baseStart_4409065 : Nat := 118140960795 + 4409065 * 2 ^ 59
def prefixEnd_4409065 : Nat := 4983230072969 + 3 ^ 40 * 4409065 * 2
def baseEnd_4409065 : Nat := 2263969581915897246610585

theorem tailTrace_4409065 : CollatzResearch.WordTrace tailWord_4409065 prefixEnd_4409065 2263969581915897246610585 := by
  unfold tailWord_4409065
  simp only [CollatzResearch.WordTrace]
  refine ⟨160811811771717988197052649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107207874514478658798035099 160811811771717988197052649)
  ·
    refine ⟨120608858828788491147789487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160811811771717988197052649 120608858828788491147789487)
    ·
      refine ⟨180913288243182736721684231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120608858828788491147789487 180913288243182736721684231)
      ·
        refine ⟨271369932364774105082526347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180913288243182736721684231 271369932364774105082526347)
        ·
          refine ⟨407054898547161157623789521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271369932364774105082526347 407054898547161157623789521)
          ·
            refine ⟨305291173910370868217842141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407054898547161157623789521 305291173910370868217842141)
            ·
              refine ⟨114484190216389075581690803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305291173910370868217842141 114484190216389075581690803)
              ·
                refine ⟨171726285324583613372536205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114484190216389075581690803 171726285324583613372536205)
                ·
                  refine ⟨64397356996718855014701077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171726285324583613372536205 64397356996718855014701077)
                  ·
                    refine ⟨3018626109221196328814113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64397356996718855014701077 3018626109221196328814113)
                    ·
                      refine ⟨2263969581915897246610585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018626109221196328814113 2263969581915897246610585)
                      ·
                        rfl

theorem cell23_4409065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 6, 2].length) (baseStart_4409065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409065 prefixEnd_4409065 := by exact prefixLift 4409065
  have htrace : WordTrace (prefixWord ++ tailWord_4409065) baseStart_4409065 baseEnd_4409065 := by
    simpa [prefixWord, tailWord_4409065, baseEnd_4409065] using wordTrace_append hprefix tailTrace_4409065
  have hstable : (prefixWord ++ tailWord_4409065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409065).length < 2 ^ (prefixWord ++ tailWord_4409065).sum := by decide
  have hdescent : baseEnd_4409065 < baseStart_4409065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409088 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 8]
def baseStart_4409088 : Nat := 118140960795 + 4409088 * 2 ^ 59
def prefixEnd_4409088 : Nat := 4983230072969 + 3 ^ 40 * 4409088 * 2
def baseEnd_4409088 : Nat := 251553487996772295180331

theorem tailTrace_4409088 : CollatzResearch.WordTrace tailWord_4409088 prefixEnd_4409088 251553487996772295180331 := by
  unfold tailWord_4409088
  simp only [CollatzResearch.WordTrace]
  refine ⟨80406325325317331562569959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107208433767089775416759945 80406325325317331562569959)
  ·
    refine ⟨120609487987975997343854939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80406325325317331562569959 120609487987975997343854939)
    ·
      refine ⟨180914231981963996015782409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120609487987975997343854939 180914231981963996015782409)
      ·
        refine ⟨135685673986472997011836807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180914231981963996015782409 135685673986472997011836807)
        ·
          refine ⟨203528510979709495517755211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135685673986472997011836807 203528510979709495517755211)
          ·
            refine ⟨305292766469564243276632817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203528510979709495517755211 305292766469564243276632817)
            ·
              refine ⟨228969574852173182457474613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305292766469564243276632817 228969574852173182457474613)
              ·
                refine ⟨21465897642391235855388245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228969574852173182457474613 21465897642391235855388245)
                ·
                  refine ⟨251553487996772295180331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21465897642391235855388245 251553487996772295180331)
                  ·
                    rfl

theorem cell23_4409088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_4409088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409088 prefixEnd_4409088 := by exact prefixLift 4409088
  have htrace : WordTrace (prefixWord ++ tailWord_4409088) baseStart_4409088 baseEnd_4409088 := by
    simpa [prefixWord, tailWord_4409088, baseEnd_4409088] using wordTrace_append hprefix tailTrace_4409088
  have hstable : (prefixWord ++ tailWord_4409088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409088).length < 2 ^ (prefixWord ++ tailWord_4409088).sum := by decide
  have hdescent : baseEnd_4409088 < baseStart_4409088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409092 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_4409092 : Nat := 118140960795 + 4409092 * 2 ^ 59
def prefixEnd_4409092 : Nat := 4983230072969 + 3 ^ 40 * 4409092 * 2
def baseEnd_4409092 : Nat := 754661148631189546990987

theorem tailTrace_4409092 : CollatzResearch.WordTrace tailWord_4409092 prefixEnd_4409092 754661148631189546990987 := by
  unfold tailWord_4409092
  simp only [CollatzResearch.WordTrace]
  refine ⟨80406398271310085904142765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107208531028413447872190353 80406398271310085904142765)
  ·
    refine ⟨30152399351741282214053537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80406398271310085904142765 30152399351741282214053537)
    ·
      refine ⟨22614299513805961660540153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30152399351741282214053537 22614299513805961660540153)
      ·
        refine ⟨16960724635354471245405115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22614299513805961660540153 16960724635354471245405115)
        ·
          refine ⟨25441086953031706868107673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16960724635354471245405115 25441086953031706868107673)
          ·
            refine ⟨19080815214773780151080755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25441086953031706868107673 19080815214773780151080755)
            ·
              refine ⟨28621222822160670226621133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19080815214773780151080755 28621222822160670226621133)
              ·
                refine ⟨10732958558310251334982925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28621222822160670226621133 10732958558310251334982925)
                ·
                  refine ⟨4024859459366344250618597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10732958558310251334982925 4024859459366344250618597)
                  ·
                    refine ⟨754661148631189546990987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024859459366344250618597 754661148631189546990987)
                    ·
                      rfl

theorem cell23_4409092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_4409092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409092 prefixEnd_4409092 := by exact prefixLift 4409092
  have htrace : WordTrace (prefixWord ++ tailWord_4409092) baseStart_4409092 baseEnd_4409092 := by
    simpa [prefixWord, tailWord_4409092, baseEnd_4409092] using wordTrace_append hprefix tailTrace_4409092
  have hstable : (prefixWord ++ tailWord_4409092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409092).length < 2 ^ (prefixWord ++ tailWord_4409092).sum := by decide
  have hdescent : baseEnd_4409092 < baseStart_4409092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409094 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4409094 : Nat := 118140960795 + 4409094 * 2 ^ 59
def prefixEnd_4409094 : Nat := 4983230072969 + 3 ^ 40 * 4409094 * 2
def baseEnd_4409094 : Nat := 2263984472854877633147953

theorem tailTrace_4409094 : CollatzResearch.WordTrace tailWord_4409094 prefixEnd_4409094 2263984472854877633147953 := by
  unfold tailWord_4409094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025402171519153942183073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107208579659075284099905557 5025402171519153942183073)
  ·
    refine ⟨3769051628639365456637305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5025402171519153942183073 3769051628639365456637305)
    ·
      refine ⟨2826788721479524092477979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3769051628639365456637305 2826788721479524092477979)
      ·
        refine ⟨4240183082219286138716969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826788721479524092477979 4240183082219286138716969)
        ·
          refine ⟨3180137311664464604037727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4240183082219286138716969 3180137311664464604037727)
          ·
            refine ⟨4770205967496696906056591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180137311664464604037727 4770205967496696906056591)
            ·
              refine ⟨7155308951245045359084887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770205967496696906056591 7155308951245045359084887)
              ·
                refine ⟨10732963426867568038627331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7155308951245045359084887 10732963426867568038627331)
                ·
                  refine ⟨16099445140301352057940997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10732963426867568038627331 16099445140301352057940997)
                  ·
                    refine ⟨3018645963806503510863937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16099445140301352057940997 3018645963806503510863937)
                    ·
                      refine ⟨2263984472854877633147953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018645963806503510863937 2263984472854877633147953)
                      ·
                        rfl

theorem cell23_4409094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4409094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409094 prefixEnd_4409094 := by exact prefixLift 4409094
  have htrace : WordTrace (prefixWord ++ tailWord_4409094) baseStart_4409094 baseEnd_4409094 := by
    simpa [prefixWord, tailWord_4409094, baseEnd_4409094] using wordTrace_append hprefix tailTrace_4409094
  have hstable : (prefixWord ++ tailWord_4409094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409094).length < 2 ^ (prefixWord ++ tailWord_4409094).sum := by decide
  have hdescent : baseEnd_4409094 < baseStart_4409094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409169 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 1, 5]
def baseStart_4409169 : Nat := 118140960795 + 4409169 * 2 ^ 59
def prefixEnd_4409169 : Nat := 4983230072969 + 3 ^ 40 * 4409169 * 2
def baseEnd_4409169 : Nat := 754674327967988279903369

theorem tailTrace_4409169 : CollatzResearch.WordTrace tailWord_4409169 prefixEnd_4409169 754674327967988279903369 := by
  unfold tailWord_4409169
  simp only [CollatzResearch.WordTrace]
  refine ⟨160815604963341213958838561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107210403308894142639225707 160815604963341213958838561)
  ·
    refine ⟨120611703722505910469128921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160815604963341213958838561 120611703722505910469128921)
    ·
      refine ⟨90458777791879432851846691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120611703722505910469128921 90458777791879432851846691)
      ·
        refine ⟨135688166687819149277770037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90458777791879432851846691 135688166687819149277770037)
        ·
          refine ⟨12720765626983045244790941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135688166687819149277770037 12720765626983045244790941)
          ·
            refine ⟨4770287110118641966796603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12720765626983045244790941 4770287110118641966796603)
            ·
              refine ⟨7155430665177962950194905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770287110118641966796603 7155430665177962950194905)
              ·
                refine ⟨5366572998883472212646179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7155430665177962950194905 5366572998883472212646179)
                ·
                  refine ⟨8049859498325208318969269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5366572998883472212646179 8049859498325208318969269)
                  ·
                    refine ⟨754674327967988279903369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8049859498325208318969269 754674327967988279903369)
                    ·
                      rfl

theorem cell23_4409169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_4409169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409169 prefixEnd_4409169 := by exact prefixLift 4409169
  have htrace : WordTrace (prefixWord ++ tailWord_4409169) baseStart_4409169 baseEnd_4409169 := by
    simpa [prefixWord, tailWord_4409169, baseEnd_4409169] using wordTrace_append hprefix tailTrace_4409169
  have hstable : (prefixWord ++ tailWord_4409169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409169).length < 2 ^ (prefixWord ++ tailWord_4409169).sum := by decide
  have hdescent : baseEnd_4409169 < baseStart_4409169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409186 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4409186 : Nat := 118140960795 + 4409186 * 2 ^ 59
def prefixEnd_4409186 : Nat := 4983230072969 + 3 ^ 40 * 4409186 * 2
def baseEnd_4409186 : Nat := 754677237691697091065843

theorem tailTrace_4409186 : CollatzResearch.WordTrace tailWord_4409186 prefixEnd_4409186 754677237691697091065843 := by
  unfold tailWord_4409186
  simp only [CollatzResearch.WordTrace]
  refine ⟨40204056251069906465551853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107210816669519750574804941 40204056251069906465551853)
  ·
    refine ⟨15076521094151214924581945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40204056251069906465551853 15076521094151214924581945)
    ·
      refine ⟨11307390820613411193436459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15076521094151214924581945 11307390820613411193436459)
      ·
        refine ⟨16961086230920116790154689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11307390820613411193436459 16961086230920116790154689)
        ·
          refine ⟨12720814673190087592616017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16961086230920116790154689 12720814673190087592616017)
          ·
            refine ⟨9540611004892565694462013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12720814673190087592616017 9540611004892565694462013)
            ·
              refine ⟨3577729126834712135423255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9540611004892565694462013 3577729126834712135423255)
              ·
                refine ⟨5366593690252068203134883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3577729126834712135423255 5366593690252068203134883)
                ·
                  refine ⟨8049890535378102304702325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5366593690252068203134883 8049890535378102304702325)
                  ·
                    refine ⟨754677237691697091065843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8049890535378102304702325 754677237691697091065843)
                    ·
                      rfl

theorem cell23_4409186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4409186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409186 prefixEnd_4409186 := by exact prefixLift 4409186
  have htrace : WordTrace (prefixWord ++ tailWord_4409186) baseStart_4409186 baseEnd_4409186 := by
    simpa [prefixWord, tailWord_4409186, baseEnd_4409186] using wordTrace_append hprefix tailTrace_4409186
  have hstable : (prefixWord ++ tailWord_4409186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409186).length < 2 ^ (prefixWord ++ tailWord_4409186).sum := by decide
  have hdescent : baseEnd_4409186 < baseStart_4409186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409225 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_4409225 : Nat := 118140960795 + 4409225 * 2 ^ 59
def prefixEnd_4409225 : Nat := 4983230072969 + 3 ^ 40 * 4409225 * 2
def baseEnd_4409225 : Nat := 754683912940205540203283

theorem tailTrace_4409225 : CollatzResearch.WordTrace tailWord_4409225 prefixEnd_4409225 754683912940205540203283 := by
  unfold tailWord_4409225
  simp only [CollatzResearch.WordTrace]
  refine ⟨160817647451138335522877129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107211764967425557015251419 160817647451138335522877129)
  ·
    refine ⟨120613235588353751642157847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160817647451138335522877129 120613235588353751642157847)
    ·
      refine ⟨180919853382530627463236771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120613235588353751642157847 180919853382530627463236771)
      ·
        refine ⟨271379780073795941194855157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180919853382530627463236771 271379780073795941194855157)
        ·
          refine ⟨25441854381918369487017671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 271379780073795941194855157 25441854381918369487017671)
          ·
            refine ⟨38162781572877554230526507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25441854381918369487017671 38162781572877554230526507)
            ·
              refine ⟨57244172359316331345789761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38162781572877554230526507 57244172359316331345789761)
              ·
                refine ⟨42933129269487248509342321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57244172359316331345789761 42933129269487248509342321)
                ·
                  refine ⟨32199846952115436382006741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42933129269487248509342321 32199846952115436382006741)
                  ·
                    refine ⟨754683912940205540203283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32199846952115436382006741 754683912940205540203283)
                    ·
                      rfl

theorem cell23_4409225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_4409225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409225 prefixEnd_4409225 := by exact prefixLift 4409225
  have htrace : WordTrace (prefixWord ++ tailWord_4409225) baseStart_4409225 baseEnd_4409225 := by
    simpa [prefixWord, tailWord_4409225, baseEnd_4409225] using wordTrace_append hprefix tailTrace_4409225
  have hstable : (prefixWord ++ tailWord_4409225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409225).length < 2 ^ (prefixWord ++ tailWord_4409225).sum := by decide
  have hdescent : baseEnd_4409225 < baseStart_4409225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409240 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4409240 : Nat := 118140960795 + 4409240 * 2 ^ 59
def prefixEnd_4409240 : Nat := 4983230072969 + 3 ^ 40 * 4409240 * 2
def baseEnd_4409240 : Nat := 2264059441030434061922281

theorem tailTrace_4409240 : CollatzResearch.WordTrace tailWord_4409240 prefixEnd_4409240 2264059441030434061922281 := by
  unfold tailWord_4409240
  simp only [CollatzResearch.WordTrace]
  refine ⟨80409097273041996542336587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107212129697389328723115449 80409097273041996542336587)
  ·
    refine ⟨120613645909562994813504881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80409097273041996542336587 120613645909562994813504881)
    ·
      refine ⟨90460234432172246110128661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120613645909562994813504881 90460234432172246110128661)
      ·
        refine ⟨4240323489008074036412281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90460234432172246110128661 4240323489008074036412281)
        ·
          refine ⟨3180242616756055527309211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4240323489008074036412281 3180242616756055527309211)
          ·
            refine ⟨4770363925134083290963817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180242616756055527309211 4770363925134083290963817)
            ·
              refine ⟨3577772943850562468222863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4770363925134083290963817 3577772943850562468222863)
              ·
                refine ⟨5366659415775843702334295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3577772943850562468222863 5366659415775843702334295)
                ·
                  refine ⟨8049989123663765553501443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5366659415775843702334295 8049989123663765553501443)
                  ·
                    refine ⟨12074983685495648330252165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8049989123663765553501443 12074983685495648330252165)
                    ·
                      refine ⟨2264059441030434061922281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12074983685495648330252165 2264059441030434061922281)
                      ·
                        rfl

theorem cell23_4409240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4409240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409240 prefixEnd_4409240 := by exact prefixLift 4409240
  have htrace : WordTrace (prefixWord ++ tailWord_4409240) baseStart_4409240 baseEnd_4409240 := by
    simpa [prefixWord, tailWord_4409240, baseEnd_4409240] using wordTrace_append hprefix tailTrace_4409240
  have hstable : (prefixWord ++ tailWord_4409240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409240).length < 2 ^ (prefixWord ++ tailWord_4409240).sum := by decide
  have hdescent : baseEnd_4409240 < baseStart_4409240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409285 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 9]
def baseStart_4409285 : Nat := 118140960795 + 4409285 * 2 ^ 59
def prefixEnd_4409285 : Nat := 4983230072969 + 3 ^ 40 * 4409285 * 2
def baseEnd_4409285 : Nat := 251564727517765153984397

theorem tailTrace_4409285 : CollatzResearch.WordTrace tailWord_4409285 prefixEnd_4409285 251564727517765153984397 := by
  unfold tailWord_4409285
  simp only [CollatzResearch.WordTrace]
  refine ⟨160819835830920965770061309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107213223887280643846707539 160819835830920965770061309)
  ·
    refine ⟨60307438436595362163772991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160819835830920965770061309 60307438436595362163772991)
    ·
      refine ⟨90461157654893043245659487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60307438436595362163772991 90461157654893043245659487)
      ·
        refine ⟨135691736482339564868489231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90461157654893043245659487 135691736482339564868489231)
        ·
          refine ⟨203537604723509347302733847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135691736482339564868489231 203537604723509347302733847)
          ·
            refine ⟨305306407085264020954100771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203537604723509347302733847 305306407085264020954100771)
            ·
              refine ⟨457959610627896031431151157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305306407085264020954100771 457959610627896031431151157)
              ·
                refine ⟨42933713496365252946670421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457959610627896031431151157 42933713496365252946670421)
                ·
                  refine ⟨251564727517765153984397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42933713496365252946670421 251564727517765153984397)
                  ·
                    rfl

theorem cell23_4409285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_4409285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409285 prefixEnd_4409285 := by exact prefixLift 4409285
  have htrace : WordTrace (prefixWord ++ tailWord_4409285) baseStart_4409285 baseEnd_4409285 := by
    simpa [prefixWord, tailWord_4409285, baseEnd_4409285] using wordTrace_append hprefix tailTrace_4409285
  have hstable : (prefixWord ++ tailWord_4409285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409285).length < 2 ^ (prefixWord ++ tailWord_4409285).sum := by decide
  have hdescent : baseEnd_4409285 < baseStart_4409285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409312 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_4409312 : Nat := 118140960795 + 4409312 * 2 ^ 59
def prefixEnd_4409312 : Nat := 4983230072969 + 3 ^ 40 * 4409312 * 2
def baseEnd_4409312 : Nat := 2264096411637557780221949

theorem tailTrace_4409312 : CollatzResearch.WordTrace tailWord_4409312 prefixEnd_4409312 2264096411637557780221949 := by
  unfold tailWord_4409312
  simp only [CollatzResearch.WordTrace]
  refine ⟨80410410300911574690647095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107213880401215432920862793 80410410300911574690647095)
  ·
    refine ⟨120615615451367362035970643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80410410300911574690647095 120615615451367362035970643)
    ·
      refine ⟨180923423177051043053955965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120615615451367362035970643 180923423177051043053955965)
      ·
        refine ⟨67846283691394141145233487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180923423177051043053955965 67846283691394141145233487)
        ·
          refine ⟨101769425537091211717850231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67846283691394141145233487 101769425537091211717850231)
          ·
            refine ⟨152654138305636817576775347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101769425537091211717850231 152654138305636817576775347)
            ·
              refine ⟨228981207458455226365163021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152654138305636817576775347 228981207458455226365163021)
              ·
                refine ⟨85867952796920709886936133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228981207458455226365163021 85867952796920709886936133)
                ·
                  refine ⟨16100241149422633103800525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85867952796920709886936133 16100241149422633103800525)
                  ·
                    refine ⟨6037590431033487413925197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16100241149422633103800525 6037590431033487413925197)
                    ·
                      refine ⟨2264096411637557780221949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6037590431033487413925197 2264096411637557780221949)
                      ·
                        rfl

theorem cell23_4409312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_4409312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409312 prefixEnd_4409312 := by exact prefixLift 4409312
  have htrace : WordTrace (prefixWord ++ tailWord_4409312) baseStart_4409312 baseEnd_4409312 := by
    simpa [prefixWord, tailWord_4409312, baseEnd_4409312] using wordTrace_append hprefix tailTrace_4409312
  have hstable : (prefixWord ++ tailWord_4409312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409312).length < 2 ^ (prefixWord ++ tailWord_4409312).sum := by decide
  have hdescent : baseEnd_4409312 < baseStart_4409312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409349 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_4409349 : Nat := 118140960795 + 4409349 * 2 ^ 59
def prefixEnd_4409349 : Nat := 4983230072969 + 3 ^ 40 * 4409349 * 2
def baseEnd_4409349 : Nat := 754705136807258045153093

theorem tailTrace_4409349 : CollatzResearch.WordTrace tailWord_4409349 prefixEnd_4409349 754705136807258045153093 := by
  unfold tailWord_4409349
  simp only [CollatzResearch.WordTrace]
  refine ⟨160822170102689104700391101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107214780068459403133594067 160822170102689104700391101)
  ·
    refine ⟨60308313788508414262646663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160822170102689104700391101 60308313788508414262646663)
    ·
      refine ⟨90462470682762621393969995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60308313788508414262646663 90462470682762621393969995)
      ·
        refine ⟨135693706024143932090954993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90462470682762621393969995 135693706024143932090954993)
        ·
          refine ⟨101770279518107949068216245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135693706024143932090954993 101770279518107949068216245)
          ·
            refine ⟨9540963704822620225145273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101770279518107949068216245 9540963704822620225145273)
            ·
              refine ⟨7155722778616965168858955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9540963704822620225145273 7155722778616965168858955)
              ·
                refine ⟨10733584167925447753288433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7155722778616965168858955 10733584167925447753288433)
                ·
                  refine ⟨8050188125944085814966325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10733584167925447753288433 8050188125944085814966325)
                  ·
                    refine ⟨754705136807258045153093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8050188125944085814966325 754705136807258045153093)
                    ·
                      rfl

theorem cell23_4409349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_4409349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409349 prefixEnd_4409349 := by exact prefixLift 4409349
  have htrace : WordTrace (prefixWord ++ tailWord_4409349) baseStart_4409349 baseEnd_4409349 := by
    simpa [prefixWord, tailWord_4409349, baseEnd_4409349] using wordTrace_append hprefix tailTrace_4409349
  have hstable : (prefixWord ++ tailWord_4409349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409349).length < 2 ^ (prefixWord ++ tailWord_4409349).sum := by decide
  have hdescent : baseEnd_4409349 < baseStart_4409349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409369 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 2, 4, 2]
def baseStart_4409369 : Nat := 118140960795 + 4409369 * 2 ^ 59
def prefixEnd_4409369 : Nat := 4983230072969 + 3 ^ 40 * 4409369 * 2
def baseEnd_4409369 : Nat := 2264125680034864057209187

theorem tailTrace_4409369 : CollatzResearch.WordTrace tailWord_4409369 prefixEnd_4409369 2264125680034864057209187 := by
  unfold tailWord_4409369
  simp only [CollatzResearch.WordTrace]
  refine ⟨160822899562616648116119161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107215266375077765410746107 160822899562616648116119161)
  ·
    refine ⟨120617174671962486087089371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160822899562616648116119161 120617174671962486087089371)
    ·
      refine ⟨180925762007943729130634057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120617174671962486087089371 180925762007943729130634057)
      ·
        refine ⟨135694321505957796847975543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180925762007943729130634057 135694321505957796847975543)
        ·
          refine ⟨203541482258936695271963315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135694321505957796847975543 203541482258936695271963315)
          ·
            refine ⟨305312223388405042907944973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203541482258936695271963315 305312223388405042907944973)
            ·
              refine ⟨114492083770651891090479365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305312223388405042907944973 114492083770651891090479365)
              ·
                refine ⟨21467265706997229579464881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114492083770651891090479365 21467265706997229579464881)
                ·
                  refine ⟨16100449280247922184598661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21467265706997229579464881 16100449280247922184598661)
                  ·
                    refine ⟨3018834240046485409612249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16100449280247922184598661 3018834240046485409612249)
                    ·
                      refine ⟨2264125680034864057209187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018834240046485409612249 2264125680034864057209187)
                      ·
                        rfl

theorem cell23_4409369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_4409369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409369 prefixEnd_4409369 := by exact prefixLift 4409369
  have htrace : WordTrace (prefixWord ++ tailWord_4409369) baseStart_4409369 baseEnd_4409369 := by
    simpa [prefixWord, tailWord_4409369, baseEnd_4409369] using wordTrace_append hprefix tailTrace_4409369
  have hstable : (prefixWord ++ tailWord_4409369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409369).length < 2 ^ (prefixWord ++ tailWord_4409369).sum := by decide
  have hdescent : baseEnd_4409369 < baseStart_4409369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409379 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 3, 4]
def baseStart_4409379 : Nat := 118140960795 + 4409379 * 2 ^ 59
def prefixEnd_4409379 : Nat := 4983230072969 + 3 ^ 40 * 4409379 * 2
def baseEnd_4409379 : Nat := 754710271613803006028047

theorem tailTrace_4409379 : CollatzResearch.WordTrace tailWord_4409379 prefixEnd_4409379 754710271613803006028047 := by
  unfold tailWord_4409379
  simp only [CollatzResearch.WordTrace]
  refine ⟨160823264292580419823983191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107215509528386946549322127 160823264292580419823983191)
  ·
    refine ⟨241234896438870629735974787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160823264292580419823983191 241234896438870629735974787)
    ·
      refine ⟨361852344658305944603962181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241234896438870629735974787 361852344658305944603962181)
      ·
        refine ⟨67847314623432364613242909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 361852344658305944603962181 67847314623432364613242909)
        ·
          refine ⟨25442742983787136729966091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67847314623432364613242909 25442742983787136729966091)
          ·
            refine ⟨38164114475680705094949137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25442742983787136729966091 38164114475680705094949137)
            ·
              refine ⟨28623085856760528821211853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38164114475680705094949137 28623085856760528821211853)
              ·
                refine ⟨10733657196285198307954445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28623085856760528821211853 10733657196285198307954445)
                ·
                  refine ⟨4025121448606949365482917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10733657196285198307954445 4025121448606949365482917)
                  ·
                    refine ⟨754710271613803006028047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025121448606949365482917 754710271613803006028047)
                    ·
                      rfl

theorem cell23_4409379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 4].length) (baseStart_4409379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409379 prefixEnd_4409379 := by exact prefixLift 4409379
  have htrace : WordTrace (prefixWord ++ tailWord_4409379) baseStart_4409379 baseEnd_4409379 := by
    simpa [prefixWord, tailWord_4409379, baseEnd_4409379] using wordTrace_append hprefix tailTrace_4409379
  have hstable : (prefixWord ++ tailWord_4409379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409379).length < 2 ^ (prefixWord ++ tailWord_4409379).sum := by decide
  have hdescent : baseEnd_4409379 < baseStart_4409379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409386 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4409386 : Nat := 118140960795 + 4409386 * 2 ^ 59
def prefixEnd_4409386 : Nat := 4983230072969 + 3 ^ 40 * 4409386 * 2
def baseEnd_4409386 : Nat := 2264134409205990490696609

theorem tailTrace_4409386 : CollatzResearch.WordTrace tailWord_4409386 prefixEnd_4409386 2264134409205990490696609 := by
  unfold tailWord_4409386
  simp only [CollatzResearch.WordTrace]
  refine ⟨40205879900888765004872003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107215679735703373346325341 40205879900888765004872003)
  ·
    refine ⟨60308819851333147507308005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40205879900888765004872003 60308819851333147507308005)
    ·
      refine ⟨11307903722124965157620251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60308819851333147507308005 11307903722124965157620251)
      ·
        refine ⟨16961855583187447736430377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11307903722124965157620251 16961855583187447736430377)
        ·
          refine ⟨12721391687390585802322783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16961855583187447736430377 12721391687390585802322783)
          ·
            refine ⟨19082087531085878703484175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12721391687390585802322783 19082087531085878703484175)
            ·
              refine ⟨28623131296628818055226263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19082087531085878703484175 28623131296628818055226263)
              ·
                refine ⟨42934696944943227082839395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28623131296628818055226263 42934696944943227082839395)
                ·
                  refine ⟨64402045417414840624259093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42934696944943227082839395 64402045417414840624259093)
                  ·
                    refine ⟨3018845878941320654262145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64402045417414840624259093 3018845878941320654262145)
                    ·
                      refine ⟨2264134409205990490696609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018845878941320654262145 2264134409205990490696609)
                      ·
                        rfl

theorem cell23_4409386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4409386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409386 prefixEnd_4409386 := by exact prefixLift 4409386
  have htrace : WordTrace (prefixWord ++ tailWord_4409386) baseStart_4409386 baseEnd_4409386 := by
    simpa [prefixWord, tailWord_4409386, baseEnd_4409386] using wordTrace_append hprefix tailTrace_4409386
  have hstable : (prefixWord ++ tailWord_4409386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409386).length < 2 ^ (prefixWord ++ tailWord_4409386).sum := by decide
  have hdescent : baseEnd_4409386 < baseStart_4409386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409430 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4409430 : Nat := 118140960795 + 4409430 * 2 ^ 59
def prefixEnd_4409430 : Nat := 4983230072969 + 3 ^ 40 * 4409430 * 2
def baseEnd_4409430 : Nat := 754719000784929439515469

theorem tailTrace_4409430 : CollatzResearch.WordTrace tailWord_4409430 prefixEnd_4409430 754719000784929439515469 := by
  unfold tailWord_4409430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051570275962228470880609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107216749610263770356059829 10051570275962228470880609)
  ·
    refine ⟨7538677706971671353160457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10051570275962228470880609 7538677706971671353160457)
    ·
      refine ⟨5654008280228753514870343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7538677706971671353160457 5654008280228753514870343)
      ·
        refine ⟨8481012420343130272305515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5654008280228753514870343 8481012420343130272305515)
        ·
          refine ⟨12721518630514695408458273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8481012420343130272305515 12721518630514695408458273)
          ·
            refine ⟨9541138972886021556343705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12721518630514695408458273 9541138972886021556343705)
            ·
              refine ⟨7155854229664516167257779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9541138972886021556343705 7155854229664516167257779)
              ·
                refine ⟨10733781344496774250886669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7155854229664516167257779 10733781344496774250886669)
                ·
                  refine ⟨4025168004186290344082501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10733781344496774250886669 4025168004186290344082501)
                  ·
                    refine ⟨754719000784929439515469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025168004186290344082501 754719000784929439515469)
                    ·
                      rfl

theorem cell23_4409430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4409430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409430 prefixEnd_4409430 := by exact prefixLift 4409430
  have htrace : WordTrace (prefixWord ++ tailWord_4409430) baseStart_4409430 baseEnd_4409430 := by
    simpa [prefixWord, tailWord_4409430, baseEnd_4409430] using wordTrace_append hprefix tailTrace_4409430
  have hstable : (prefixWord ++ tailWord_4409430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409430).length < 2 ^ (prefixWord ++ tailWord_4409430).sum := by decide
  have hdescent : baseEnd_4409430 < baseStart_4409430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409456 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 1, 5]
def baseStart_4409456 : Nat := 118140960795 + 4409456 * 2 ^ 59
def prefixEnd_4409456 : Nat := 4983230072969 + 3 ^ 40 * 4409456 * 2
def baseEnd_4409456 : Nat := 754723450950601738940429

theorem tailTrace_4409456 : CollatzResearch.WordTrace tailWord_4409456 prefixEnd_4409456 754723450950601738940429 := by
  unfold tailWord_4409456
  simp only [CollatzResearch.WordTrace]
  refine ⟨80413036356650730987268111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107217381808867641316357481 80413036356650730987268111)
  ·
    refine ⟨120619554534976096480902167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80413036356650730987268111 120619554534976096480902167)
    ·
      refine ⟨180929331802464144721353251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120619554534976096480902167 180929331802464144721353251)
      ·
        refine ⟨271393997703696217082029877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180929331802464144721353251 271393997703696217082029877)
        ·
          refine ⟨25443187284721520351440301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 271393997703696217082029877 25443187284721520351440301)
          ·
            refine ⟨9541195231770570131790113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25443187284721520351440301 9541195231770570131790113)
            ·
              refine ⟨7155896423827927598842585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9541195231770570131790113 7155896423827927598842585)
              ·
                refine ⟨5366922317870945699131939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7155896423827927598842585 5366922317870945699131939)
                ·
                  refine ⟨8050383476806418548697909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5366922317870945699131939 8050383476806418548697909)
                  ·
                    refine ⟨754723450950601738940429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8050383476806418548697909 754723450950601738940429)
                    ·
                      rfl

theorem cell23_4409456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_4409456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409456 prefixEnd_4409456 := by exact prefixLift 4409456
  have htrace : WordTrace (prefixWord ++ tailWord_4409456) baseStart_4409456 baseEnd_4409456 := by
    simpa [prefixWord, tailWord_4409456, baseEnd_4409456] using wordTrace_append hprefix tailTrace_4409456
  have hstable : (prefixWord ++ tailWord_4409456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409456).length < 2 ^ (prefixWord ++ tailWord_4409456).sum := by decide
  have hdescent : baseEnd_4409456 < baseStart_4409456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409476 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_4409476 : Nat := 118140960795 + 4409476 * 2 ^ 59
def prefixEnd_4409476 : Nat := 4983230072969 + 3 ^ 40 * 4409476 * 2
def baseEnd_4409476 : Nat := 2264180622464895138571195

theorem tailTrace_4409476 : CollatzResearch.WordTrace tailWord_4409476 prefixEnd_4409476 2264180622464895138571195 := by
  unfold tailWord_4409476
  simp only [CollatzResearch.WordTrace]
  refine ⟨80413401086614502695132141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107217868115486003593509521 80413401086614502695132141)
  ·
    refine ⟨30155025407480438510674553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80413401086614502695132141 30155025407480438510674553)
    ·
      refine ⟨22616269055610328883005915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30155025407480438510674553 22616269055610328883005915)
      ·
        refine ⟨33924403583415493324508873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22616269055610328883005915 33924403583415493324508873)
        ·
          refine ⟨25443302687561619993381655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33924403583415493324508873 25443302687561619993381655)
          ·
            refine ⟨38164954031342429990072483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25443302687561619993381655 38164954031342429990072483)
            ·
              refine ⟨57247431047013644985108725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38164954031342429990072483 57247431047013644985108725)
              ·
                refine ⟨5366946660657529217353943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57247431047013644985108725 5366946660657529217353943)
                ·
                  refine ⟨8050419990986293826030915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5366946660657529217353943 8050419990986293826030915)
                  ·
                    refine ⟨12075629986479440739046373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8050419990986293826030915 12075629986479440739046373)
                    ·
                      refine ⟨2264180622464895138571195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12075629986479440739046373 2264180622464895138571195)
                      ·
                        rfl

theorem cell23_4409476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_4409476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409476 prefixEnd_4409476 := by exact prefixLift 4409476
  have htrace : WordTrace (prefixWord ++ tailWord_4409476) baseStart_4409476 baseEnd_4409476 := by
    simpa [prefixWord, tailWord_4409476, baseEnd_4409476] using wordTrace_append hprefix tailTrace_4409476
  have hstable : (prefixWord ++ tailWord_4409476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409476).length < 2 ^ (prefixWord ++ tailWord_4409476).sum := by decide
  have hdescent : baseEnd_4409476 < baseStart_4409476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409479 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_4409479 : Nat := 118140960795 + 4409479 * 2 ^ 59
def prefixEnd_4409479 : Nat := 4983230072969 + 3 ^ 40 * 4409479 * 2
def baseEnd_4409479 : Nat := 2264182162906858626833681

theorem tailTrace_4409479 : CollatzResearch.WordTrace tailWord_4409479 prefixEnd_4409479 2264182162906858626833681 := by
  unfold tailWord_4409479
  simp only [CollatzResearch.WordTrace]
  refine ⟨160826911592218136902623491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107217941061478757935082327 160826911592218136902623491)
  ·
    refine ⟨241240367388327205353935237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160826911592218136902623491 241240367388327205353935237)
    ·
      refine ⟨45232568885311351003862857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241240367388327205353935237 45232568885311351003862857)
      ·
        refine ⟨33924426663983513252897143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45232568885311351003862857 33924426663983513252897143)
        ·
          refine ⟨50886639995975269879345715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33924426663983513252897143 50886639995975269879345715)
          ·
            refine ⟨76329959993962904819018573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50886639995975269879345715 76329959993962904819018573)
            ·
              refine ⟨28623734997736089307131965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76329959993962904819018573 28623734997736089307131965)
              ·
                refine ⟨10733900624151033490174487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28623734997736089307131965 10733900624151033490174487)
                ·
                  refine ⟨16100850936226550235261731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10733900624151033490174487 16100850936226550235261731)
                  ·
                    refine ⟨24151276404339825352892597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16100850936226550235261731 24151276404339825352892597)
                    ·
                      refine ⟨2264182162906858626833681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24151276404339825352892597 2264182162906858626833681)
                      ·
                        rfl

theorem cell23_4409479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_4409479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409479 prefixEnd_4409479 := by exact prefixLift 4409479
  have htrace : WordTrace (prefixWord ++ tailWord_4409479) baseStart_4409479 baseEnd_4409479 := by
    simpa [prefixWord, tailWord_4409479, baseEnd_4409479] using wordTrace_append hprefix tailTrace_4409479
  have hstable : (prefixWord ++ tailWord_4409479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409479).length < 2 ^ (prefixWord ++ tailWord_4409479).sum := by decide
  have hdescent : baseEnd_4409479 < baseStart_4409479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409503 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 2, 4]
def baseStart_4409503 : Nat := 118140960795 + 4409503 * 2 ^ 59
def prefixEnd_4409503 : Nat := 4983230072969 + 3 ^ 40 * 4409503 * 2
def baseEnd_4409503 : Nat := 754731495480855510977857

theorem tailTrace_4409503 : CollatzResearch.WordTrace tailWord_4409503 prefixEnd_4409503 754731495480855510977857 := by
  unfold tailWord_4409503
  simp only [CollatzResearch.WordTrace]
  refine ⟨160827786944131189001497163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107218524629420792667664775 160827786944131189001497163)
  ·
    refine ⟨241241680416196783502245745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160827786944131189001497163 241241680416196783502245745)
    ·
      refine ⟨180931260312147587626684309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241241680416196783502245745 180931260312147587626684309)
      ·
        refine ⟨8481152827131918170000827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180931260312147587626684309 8481152827131918170000827)
        ·
          refine ⟨12721729240697877255001241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8481152827131918170000827 12721729240697877255001241)
          ·
            refine ⟨9541296930523407941250931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12721729240697877255001241 9541296930523407941250931)
            ·
              refine ⟨14311945395785111911876397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9541296930523407941250931 14311945395785111911876397)
              ·
                refine ⟨5366979523419416966953649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14311945395785111911876397 5366979523419416966953649)
                ·
                  refine ⟨4025234642564562725215237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5366979523419416966953649 4025234642564562725215237)
                  ·
                    refine ⟨754731495480855510977857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025234642564562725215237 754731495480855510977857)
                    ·
                      rfl

theorem cell23_4409503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_4409503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409503 prefixEnd_4409503 := by exact prefixLift 4409503
  have htrace : WordTrace (prefixWord ++ tailWord_4409503) baseStart_4409503 baseEnd_4409503 := by
    simpa [prefixWord, tailWord_4409503, baseEnd_4409503] using wordTrace_append hprefix tailTrace_4409503
  have hstable : (prefixWord ++ tailWord_4409503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409503).length < 2 ^ (prefixWord ++ tailWord_4409503).sum := by decide
  have hdescent : baseEnd_4409503 < baseStart_4409503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409506 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4409506 : Nat := 118140960795 + 4409506 * 2 ^ 59
def prefixEnd_4409506 : Nat := 4983230072969 + 3 ^ 40 * 4409506 * 2
def baseEnd_4409506 : Nat := 2264196026884530021196057

theorem tailTrace_4409506 : CollatzResearch.WordTrace tailWord_4409506 prefixEnd_4409506 2264196026884530021196057 := by
  unfold tailWord_4409506
  simp only [CollatzResearch.WordTrace]
  refine ⟨40206974090780080128464093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107218597575413547009237581 40206974090780080128464093)
  ·
    refine ⟨15077615284042530048174035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40206974090780080128464093 15077615284042530048174035)
    ·
      refine ⟨22616422926063795072261053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15077615284042530048174035 22616422926063795072261053)
      ·
        refine ⟨8481158597273923152097895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22616422926063795072261053 8481158597273923152097895)
        ·
          refine ⟨12721737895910884728146843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8481158597273923152097895 12721737895910884728146843)
          ·
            refine ⟨19082606843866327092220265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12721737895910884728146843 19082606843866327092220265)
            ·
              refine ⟨14311955132899745319165199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19082606843866327092220265 14311955132899745319165199)
              ·
                refine ⟨21467932699349617978747799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14311955132899745319165199 21467932699349617978747799)
                ·
                  refine ⟨32201899049024426968121699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21467932699349617978747799 32201899049024426968121699)
                  ·
                    refine ⟨48302848573536640452182549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32201899049024426968121699 48302848573536640452182549)
                    ·
                      refine ⟨2264196026884530021196057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48302848573536640452182549 2264196026884530021196057)
                      ·
                        rfl

theorem cell23_4409506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4409506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409506 prefixEnd_4409506 := by exact prefixLift 4409506
  have htrace : WordTrace (prefixWord ++ tailWord_4409506) baseStart_4409506 baseEnd_4409506 := by
    simpa [prefixWord, tailWord_4409506, baseEnd_4409506] using wordTrace_append hprefix tailTrace_4409506
  have hstable : (prefixWord ++ tailWord_4409506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409506).length < 2 ^ (prefixWord ++ tailWord_4409506).sum := by decide
  have hdescent : baseEnd_4409506 < baseStart_4409506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409524 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4409524 : Nat := 118140960795 + 4409524 * 2 ^ 59
def prefixEnd_4409524 : Nat := 4983230072969 + 3 ^ 40 * 4409524 * 2
def baseEnd_4409524 : Nat := 754735089845436983590325

theorem tailTrace_4409524 : CollatzResearch.WordTrace tailWord_4409524 prefixEnd_4409524 754735089845436983590325 := by
  unfold tailWord_4409524
  simp only [CollatzResearch.WordTrace]
  refine ⟨80414276438527554794005813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107219035251370073058674417 80414276438527554794005813)
  ·
    refine ⟨7538838416111958261938045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80414276438527554794005813 7538838416111958261938045)
    ·
      refine ⟨2827064406041984348226767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7538838416111958261938045 2827064406041984348226767)
      ·
        refine ⟨4240596609062976522340151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827064406041984348226767 4240596609062976522340151)
        ·
          refine ⟨6360894913594464783510227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240596609062976522340151 6360894913594464783510227)
          ·
            refine ⟨9541342370391697175265341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6360894913594464783510227 9541342370391697175265341)
            ·
              refine ⟨3578003388896886440724503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9541342370391697175265341 3578003388896886440724503)
              ·
                refine ⟨5367005083345329661086755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3578003388896886440724503 5367005083345329661086755)
                ·
                  refine ⟨8050507625017994491630133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5367005083345329661086755 8050507625017994491630133)
                  ·
                    refine ⟨754735089845436983590325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8050507625017994491630133 754735089845436983590325)
                    ·
                      rfl

theorem cell23_4409524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4409524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409524 prefixEnd_4409524 := by exact prefixLift 4409524
  have htrace : WordTrace (prefixWord ++ tailWord_4409524) baseStart_4409524 baseEnd_4409524 := by
    simpa [prefixWord, tailWord_4409524, baseEnd_4409524] using wordTrace_append hprefix tailTrace_4409524
  have hstable : (prefixWord ++ tailWord_4409524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409524).length < 2 ^ (prefixWord ++ tailWord_4409524).sum := by decide
  have hdescent : baseEnd_4409524 < baseStart_4409524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409579 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4]
def baseStart_4409579 : Nat := 118140960795 + 4409579 * 2 ^ 59
def prefixEnd_4409579 : Nat := 4983230072969 + 3 ^ 40 * 4409579 * 2
def baseEnd_4409579 : Nat := 2264233510972308235583221

theorem tailTrace_4409579 : CollatzResearch.WordTrace tailWord_4409579 prefixEnd_4409579 2264233510972308235583221 := by
  unfold tailWord_4409579
  simp only [CollatzResearch.WordTrace]
  refine ⟨160830558891855853981263791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107220372594570569320842527 160830558891855853981263791)
  ·
    refine ⟨241245838337783780971895687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160830558891855853981263791 241245838337783780971895687)
    ·
      refine ⟨361868757506675671457843531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241245838337783780971895687 361868757506675671457843531)
      ·
        refine ⟨542803136260013507186765297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361868757506675671457843531 542803136260013507186765297)
        ·
          refine ⟨407102352195010130390073973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542803136260013507186765297 407102352195010130390073973)
          ·
            refine ⟨38165845518282199724069435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 407102352195010130390073973 38165845518282199724069435)
            ·
              refine ⟨57248768277423299586104153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38165845518282199724069435 57248768277423299586104153)
              ·
                refine ⟨42936576208067474689578115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57248768277423299586104153 42936576208067474689578115)
                ·
                  refine ⟨64404864312101212034367173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42936576208067474689578115 64404864312101212034367173)
                  ·
                    refine ⟨12075912058518977256443845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64404864312101212034367173 12075912058518977256443845)
                    ·
                      refine ⟨2264233510972308235583221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12075912058518977256443845 2264233510972308235583221)
                      ·
                        rfl

theorem cell23_4409579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_4409579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409579 prefixEnd_4409579 := by exact prefixLift 4409579
  have htrace : WordTrace (prefixWord ++ tailWord_4409579) baseStart_4409579 baseEnd_4409579 := by
    simpa [prefixWord, tailWord_4409579, baseEnd_4409579] using wordTrace_append hprefix tailTrace_4409579
  have hstable : (prefixWord ++ tailWord_4409579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409579).length < 2 ^ (prefixWord ++ tailWord_4409579).sum := by decide
  have hdescent : baseEnd_4409579 < baseStart_4409579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409583 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 1, 4, 2]
def baseStart_4409583 : Nat := 118140960795 + 4409583 * 2 ^ 59
def prefixEnd_4409583 : Nat := 4983230072969 + 3 ^ 40 * 4409583 * 2
def baseEnd_4409583 : Nat := 2264235564894926219933203

theorem tailTrace_4409583 : CollatzResearch.WordTrace tailWord_4409583 prefixEnd_4409583 2264235564894926219933203 := by
  unfold tailWord_4409583
  simp only [CollatzResearch.WordTrace]
  refine ⟨160830704783841362664409403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107220469855894241776272935 160830704783841362664409403)
  ·
    refine ⟨241246057175762043996614105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160830704783841362664409403 241246057175762043996614105)
    ·
      refine ⟨180934542881821532997460579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241246057175762043996614105 180934542881821532997460579)
      ·
        refine ⟨271401814322732299496190869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180934542881821532997460579 271401814322732299496190869)
        ·
          refine ⟨12721960046378076538883947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 271401814322732299496190869 12721960046378076538883947)
          ·
            refine ⟨19082940069567114808325921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12721960046378076538883947 19082940069567114808325921)
            ·
              refine ⟨14312205052175336106244441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19082940069567114808325921 14312205052175336106244441)
              ·
                refine ⟨10734153789131502079683331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14312205052175336106244441 10734153789131502079683331)
                ·
                  refine ⟨16101230683697253119524997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10734153789131502079683331 16101230683697253119524997)
                  ·
                    refine ⟨3018980753193234959910937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16101230683697253119524997 3018980753193234959910937)
                    ·
                      refine ⟨2264235564894926219933203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018980753193234959910937 2264235564894926219933203)
                      ·
                        rfl

theorem cell23_4409583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4, 2].length) (baseStart_4409583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409583 prefixEnd_4409583 := by exact prefixLift 4409583
  have htrace : WordTrace (prefixWord ++ tailWord_4409583) baseStart_4409583 baseEnd_4409583 := by
    simpa [prefixWord, tailWord_4409583, baseEnd_4409583] using wordTrace_append hprefix tailTrace_4409583
  have hstable : (prefixWord ++ tailWord_4409583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409583).length < 2 ^ (prefixWord ++ tailWord_4409583).sum := by decide
  have hdescent : baseEnd_4409583 < baseStart_4409583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409596 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_4409596 : Nat := 118140960795 + 4409596 * 2 ^ 59
def prefixEnd_4409596 : Nat := 4983230072969 + 3 ^ 40 * 4409596 * 2
def baseEnd_4409596 : Nat := 2264242240143434669070643

theorem tailTrace_4409596 : CollatzResearch.WordTrace tailWord_4409596 prefixEnd_4409596 2264242240143434669070643 := by
  unfold tailWord_4409596
  simp only [CollatzResearch.WordTrace]
  refine ⟨80415589466397132942316321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107220785955196177256421761 80415589466397132942316321)
  ·
    refine ⟨60311692099797849706737241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80415589466397132942316321 60311692099797849706737241)
    ·
      refine ⟨45233769074848387280052931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60311692099797849706737241 45233769074848387280052931)
      ·
        refine ⟨67850653612272580920079397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45233769074848387280052931 67850653612272580920079397)
        ·
          refine ⟨12721997552301108922514887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67850653612272580920079397 12721997552301108922514887)
          ·
            refine ⟨19082996328451663383772331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12721997552301108922514887 19082996328451663383772331)
            ·
              refine ⟨28624494492677495075658497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19082996328451663383772331 28624494492677495075658497)
              ·
                refine ⟨21468370869508121306743873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28624494492677495075658497 21468370869508121306743873)
                ·
                  refine ⟨16101278152131090980057905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21468370869508121306743873 16101278152131090980057905)
                  ·
                    refine ⟨12075958614098318235043429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16101278152131090980057905 12075958614098318235043429)
                    ·
                      refine ⟨2264242240143434669070643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12075958614098318235043429 2264242240143434669070643)
                      ·
                        rfl

theorem cell23_4409596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_4409596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409596 prefixEnd_4409596 := by exact prefixLift 4409596
  have htrace : WordTrace (prefixWord ++ tailWord_4409596) baseStart_4409596 baseEnd_4409596 := by
    simpa [prefixWord, tailWord_4409596, baseEnd_4409596] using wordTrace_append hprefix tailTrace_4409596
  have hstable : (prefixWord ++ tailWord_4409596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409596).length < 2 ^ (prefixWord ++ tailWord_4409596).sum := by decide
  have hdescent : baseEnd_4409596 < baseStart_4409596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409600 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 2, 2, 2]
def baseStart_4409600 : Nat := 118140960795 + 4409600 * 2 ^ 59
def prefixEnd_4409600 : Nat := 4983230072969 + 3 ^ 40 * 4409600 * 2
def baseEnd_4409600 : Nat := 2264244294066052653420625

theorem tailTrace_4409600 : CollatzResearch.WordTrace tailWord_4409600 prefixEnd_4409600 2264244294066052653420625 := by
  unfold tailWord_4409600
  simp only [CollatzResearch.WordTrace]
  refine ⟨80415662412389887283889127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107220883216519849711852169 80415662412389887283889127)
  ·
    refine ⟨120623493618584830925833691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80415662412389887283889127 120623493618584830925833691)
    ·
      refine ⟨180935240427877246388750537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120623493618584830925833691 180935240427877246388750537)
      ·
        refine ⟨135701430320907934791562903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180935240427877246388750537 135701430320907934791562903)
        ·
          refine ⟨203552145481361902187344355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135701430320907934791562903 203552145481361902187344355)
          ·
            refine ⟨305328218222042853281016533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203552145481361902187344355 305328218222042853281016533)
            ·
              refine ⟨7156130114579129373773825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 305328218222042853281016533 7156130114579129373773825)
              ·
                refine ⟨5367097585934347030330369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156130114579129373773825 5367097585934347030330369)
                ·
                  refine ⟨4025323189450760272747777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367097585934347030330369 4025323189450760272747777)
                  ·
                    refine ⟨3018992392088070204560833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025323189450760272747777 3018992392088070204560833)
                    ·
                      refine ⟨2264244294066052653420625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3018992392088070204560833 2264244294066052653420625)
                      ·
                        rfl

theorem cell23_4409600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_4409600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409600 prefixEnd_4409600 := by exact prefixLift 4409600
  have htrace : WordTrace (prefixWord ++ tailWord_4409600) baseStart_4409600 baseEnd_4409600 := by
    simpa [prefixWord, tailWord_4409600, baseEnd_4409600] using wordTrace_append hprefix tailTrace_4409600
  have hstable : (prefixWord ++ tailWord_4409600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409600).length < 2 ^ (prefixWord ++ tailWord_4409600).sum := by decide
  have hdescent : baseEnd_4409600 < baseStart_4409600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409617 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 2, 2, 2]
def baseStart_4409617 : Nat := 118140960795 + 4409617 * 2 ^ 59
def prefixEnd_4409617 : Nat := 4983230072969 + 3 ^ 40 * 4409617 * 2
def baseEnd_4409617 : Nat := 2264253023237179086908047

theorem tailTrace_4409617 : CollatzResearch.WordTrace tailWord_4409617 prefixEnd_4409617 2264253023237179086908047 := by
  unfold tailWord_4409617
  simp only [CollatzResearch.WordTrace]
  refine ⟨160831944865718186471147105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107221296577145457647431403 160831944865718186471147105)
  ·
    refine ⟨120623958649288639853360329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160831944865718186471147105 120623958649288639853360329)
    ·
      refine ⟨90467968986966479890020247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120623958649288639853360329 90467968986966479890020247)
      ·
        refine ⟨135701953480449719835030371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90467968986966479890020247 135701953480449719835030371)
        ·
          refine ⟨203552930220674579752545557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135701953480449719835030371 203552930220674579752545557)
          ·
            refine ⟨9541543604094120925900573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203552930220674579752545557 9541543604094120925900573)
            ·
              refine ⟨3578078851535295347212715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9541543604094120925900573 3578078851535295347212715)
              ·
                refine ⟨5367118277302943020819073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3578078851535295347212715 5367118277302943020819073)
                ·
                  refine ⟨4025338707977207265614305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367118277302943020819073 4025338707977207265614305)
                  ·
                    refine ⟨3019004030982905449210729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025338707977207265614305 3019004030982905449210729)
                    ·
                      refine ⟨2264253023237179086908047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019004030982905449210729 2264253023237179086908047)
                      ·
                        rfl

theorem cell23_4409617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_4409617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409617 prefixEnd_4409617 := by exact prefixLift 4409617
  have htrace : WordTrace (prefixWord ++ tailWord_4409617) baseStart_4409617 baseEnd_4409617 := by
    simpa [prefixWord, tailWord_4409617, baseEnd_4409617] using wordTrace_append hprefix tailTrace_4409617
  have hstable : (prefixWord ++ tailWord_4409617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409617).length < 2 ^ (prefixWord ++ tailWord_4409617).sum := by decide
  have hdescent : baseEnd_4409617 < baseStart_4409617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409636 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_4409636 : Nat := 118140960795 + 4409636 * 2 ^ 59
def prefixEnd_4409636 : Nat := 4983230072969 + 3 ^ 40 * 4409636 * 2
def baseEnd_4409636 : Nat := 754754259789871504190153

theorem tailTrace_4409636 : CollatzResearch.WordTrace tailWord_4409636 prefixEnd_4409636 754754259789871504190153 := by
  unfold tailWord_4409636
  simp only [CollatzResearch.WordTrace]
  refine ⟨80416318926324676358044381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107221758568432901810725841 80416318926324676358044381)
  ·
    refine ⟨30156119597371753634266643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80416318926324676358044381 30156119597371753634266643)
    ·
      refine ⟨45234179396057630451399965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30156119597371753634266643 45234179396057630451399965)
      ·
        refine ⟨16962817273521611419274987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45234179396057630451399965 16962817273521611419274987)
        ·
          refine ⟨25444225910282417128912481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16962817273521611419274987 25444225910282417128912481)
          ·
            refine ⟨19083169432711812846684361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25444225910282417128912481 19083169432711812846684361)
            ·
              refine ⟨14312377074533859635013271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19083169432711812846684361 14312377074533859635013271)
              ·
                refine ⟨21468565611800789452519907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14312377074533859635013271 21468565611800789452519907)
                ·
                  refine ⟨32202848417701184178779861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21468565611800789452519907 32202848417701184178779861)
                  ·
                    refine ⟨754754259789871504190153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32202848417701184178779861 754754259789871504190153)
                    ·
                      rfl

theorem cell23_4409636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_4409636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409636 prefixEnd_4409636 := by exact prefixLift 4409636
  have htrace : WordTrace (prefixWord ++ tailWord_4409636) baseStart_4409636 baseEnd_4409636 := by
    simpa [prefixWord, tailWord_4409636, baseEnd_4409636] using wordTrace_append hprefix tailTrace_4409636
  have hstable : (prefixWord ++ tailWord_4409636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409636).length < 2 ^ (prefixWord ++ tailWord_4409636).sum := by decide
  have hdescent : baseEnd_4409636 < baseStart_4409636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409656 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_4409656 : Nat := 118140960795 + 4409656 * 2 ^ 59
def prefixEnd_4409656 : Nat := 4983230072969 + 3 ^ 40 * 4409656 * 2
def baseEnd_4409656 : Nat := 2264273048982704434320367

theorem tailTrace_4409656 : CollatzResearch.WordTrace tailWord_4409656 prefixEnd_4409656 2264273048982704434320367 := by
  unfold tailWord_4409656
  simp only [CollatzResearch.WordTrace]
  refine ⟨80416683656288448065908411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107222244875051264087877881 80416683656288448065908411)
  ·
    refine ⟨120625025484432672098862617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80416683656288448065908411 120625025484432672098862617)
    ·
      refine ⟨90468769113324504074146963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120625025484432672098862617 90468769113324504074146963)
      ·
        refine ⟨135703153669986756111220445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90468769113324504074146963 135703153669986756111220445)
        ·
          refine ⟨50888682626245033541707667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135703153669986756111220445 50888682626245033541707667)
          ·
            refine ⟨76333023939367550312561501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50888682626245033541707667 76333023939367550312561501)
            ·
              refine ⟨28624883977262831367210563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76333023939367550312561501 28624883977262831367210563)
              ·
                refine ⟨42937325965894247050815845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28624883977262831367210563 42937325965894247050815845)
                ·
                  refine ⟨8050748618605171322027971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42937325965894247050815845 8050748618605171322027971)
                  ·
                    refine ⟨12076122927907756983041957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8050748618605171322027971 12076122927907756983041957)
                    ·
                      refine ⟨2264273048982704434320367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12076122927907756983041957 2264273048982704434320367)
                      ·
                        rfl

theorem cell23_4409656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_4409656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409656 prefixEnd_4409656 := by exact prefixLift 4409656
  have htrace : WordTrace (prefixWord ++ tailWord_4409656) baseStart_4409656 baseEnd_4409656 := by
    simpa [prefixWord, tailWord_4409656, baseEnd_4409656] using wordTrace_append hprefix tailTrace_4409656
  have hstable : (prefixWord ++ tailWord_4409656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409656).length < 2 ^ (prefixWord ++ tailWord_4409656).sum := by decide
  have hdescent : baseEnd_4409656 < baseStart_4409656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409668 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4409668 : Nat := 118140960795 + 4409668 * 2 ^ 59
def prefixEnd_4409668 : Nat := 4983230072969 + 3 ^ 40 * 4409668 * 2
def baseEnd_4409668 : Nat := 2264279210750558387370313

theorem tailTrace_4409668 : CollatzResearch.WordTrace tailWord_4409668 prefixEnd_4409668 2264279210750558387370313 := by
  unfold tailWord_4409668
  simp only [CollatzResearch.WordTrace]
  refine ⟨80416902494266711090626829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107222536659022281454169105 80416902494266711090626829)
  ·
    refine ⟨30156338435350016658985061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80416902494266711090626829 30156338435350016658985061)
    ·
      refine ⟨5654313456628128123559699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30156338435350016658985061 5654313456628128123559699)
      ·
        refine ⟨8481470184942192185339549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5654313456628128123559699 8481470184942192185339549)
        ·
          refine ⟨3180551319353322069502331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8481470184942192185339549 3180551319353322069502331)
          ·
            refine ⟨4770826979029983104253497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180551319353322069502331 4770826979029983104253497)
            ·
              refine ⟨3578120234272487328190123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4770826979029983104253497 3578120234272487328190123)
              ·
                refine ⟨5367180351408730992285185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3578120234272487328190123 5367180351408730992285185)
                ·
                  refine ⟨4025385263556548244213889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367180351408730992285185 4025385263556548244213889)
                  ·
                    refine ⟨3019038947667411183160417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025385263556548244213889 3019038947667411183160417)
                    ·
                      refine ⟨2264279210750558387370313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019038947667411183160417 2264279210750558387370313)
                      ·
                        rfl

theorem cell23_4409668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4409668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409668 prefixEnd_4409668 := by exact prefixLift 4409668
  have htrace : WordTrace (prefixWord ++ tailWord_4409668) baseStart_4409668 baseEnd_4409668 := by
    simpa [prefixWord, tailWord_4409668, baseEnd_4409668] using wordTrace_append hprefix tailTrace_4409668
  have hstable : (prefixWord ++ tailWord_4409668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409668).length < 2 ^ (prefixWord ++ tailWord_4409668).sum := by decide
  have hdescent : baseEnd_4409668 < baseStart_4409668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409679 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 10]
def baseStart_4409679 : Nat := 118140960795 + 4409679 * 2 ^ 59
def prefixEnd_4409679 : Nat := 4983230072969 + 3 ^ 40 * 4409679 * 2
def baseEnd_4409679 : Nat := 251587206559750871592529

theorem tailTrace_4409679 : CollatzResearch.WordTrace tailWord_4409679 prefixEnd_4409679 251587206559750871592529 := by
  unfold tailWord_4409679
  simp only [CollatzResearch.WordTrace]
  refine ⟨160834206191493571059904091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107222804127662380706602727 160834206191493571059904091)
  ·
    refine ⟨241251309287240356589856137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160834206191493571059904091 241251309287240356589856137)
    ·
      refine ⟨180938481965430267442392103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241251309287240356589856137 180938481965430267442392103)
      ·
        refine ⟨271407722948145401163588155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180938481965430267442392103 271407722948145401163588155)
        ·
          refine ⟨407111584422218101745382233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271407722948145401163588155 407111584422218101745382233)
          ·
            refine ⟨305333688316663576309036675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407111584422218101745382233 305333688316663576309036675)
            ·
              refine ⟨458000532474995364463555013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305333688316663576309036675 458000532474995364463555013)
              ·
                refine ⟨85875099839061630836916565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458000532474995364463555013 85875099839061630836916565)
                ·
                  refine ⟨251587206559750871592529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85875099839061630836916565 251587206559750871592529)
                  ·
                    rfl

theorem cell23_4409679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 10].length) (baseStart_4409679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409679 prefixEnd_4409679 := by exact prefixLift 4409679
  have htrace : WordTrace (prefixWord ++ tailWord_4409679) baseStart_4409679 baseEnd_4409679 := by
    simpa [prefixWord, tailWord_4409679, baseEnd_4409679] using wordTrace_append hprefix tailTrace_4409679
  have hstable : (prefixWord ++ tailWord_4409679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409679).length < 2 ^ (prefixWord ++ tailWord_4409679).sum := by decide
  have hdescent : baseEnd_4409679 < baseStart_4409679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409700 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_4409700 : Nat := 118140960795 + 4409700 * 2 ^ 59
def prefixEnd_4409700 : Nat := 4983230072969 + 3 ^ 40 * 4409700 * 2
def baseEnd_4409700 : Nat := 754765214043834087390055

theorem tailTrace_4409700 : CollatzResearch.WordTrace tailWord_4409700 prefixEnd_4409700 754765214043834087390055 := by
  unfold tailWord_4409700
  simp only [CollatzResearch.WordTrace]
  refine ⟨80417486062208745823209277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107223314749611661097612369 80417486062208745823209277)
  ·
    refine ⟨30156557273328279683703479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80417486062208745823209277 30156557273328279683703479)
    ·
      refine ⟨45234835909992419525555219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30156557273328279683703479 45234835909992419525555219)
      ·
        refine ⟨67852253864988629288332829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45234835909992419525555219 67852253864988629288332829)
        ·
          refine ⟨25444595199370735983124811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67852253864988629288332829 25444595199370735983124811)
          ·
            refine ⟨38166892799056103974687217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25444595199370735983124811 38166892799056103974687217)
            ·
              refine ⟨28625169599292077981015413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38166892799056103974687217 28625169599292077981015413)
              ·
                refine ⟨2683609649933632310720195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28625169599292077981015413 2683609649933632310720195)
                ·
                  refine ⟨4025414474900448466080293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683609649933632310720195 4025414474900448466080293)
                  ·
                    refine ⟨754765214043834087390055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025414474900448466080293 754765214043834087390055)
                    ·
                      rfl

theorem cell23_4409700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_4409700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409700 prefixEnd_4409700 := by exact prefixLift 4409700
  have htrace : WordTrace (prefixWord ++ tailWord_4409700) baseStart_4409700 baseEnd_4409700 := by
    simpa [prefixWord, tailWord_4409700, baseEnd_4409700] using wordTrace_append hprefix tailTrace_4409700
  have hstable : (prefixWord ++ tailWord_4409700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409700).length < 2 ^ (prefixWord ++ tailWord_4409700).sum := by decide
  have hdescent : baseEnd_4409700 < baseStart_4409700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409717 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4409717 : Nat := 118140960795 + 4409717 * 2 ^ 59
def prefixEnd_4409717 : Nat := 4983230072969 + 3 ^ 40 * 4409717 * 2
def baseEnd_4409717 : Nat := 754768123767542898552529

theorem tailTrace_4409717 : CollatzResearch.WordTrace tailWord_4409717 prefixEnd_4409717 754768123767542898552529 := by
  unfold tailWord_4409717
  simp only [CollatzResearch.WordTrace]
  refine ⟨160835592165355903549787405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107223728110237269033191603 160835592165355903549787405)
  ·
    refine ⟨60313347062008463831170277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160835592165355903549787405 60313347062008463831170277)
    ·
      refine ⟨11308752574126586968344427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60313347062008463831170277 11308752574126586968344427)
      ·
        refine ⟨16963128861189880452516641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308752574126586968344427 16963128861189880452516641)
        ·
          refine ⟨12722346645892410339387481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16963128861189880452516641 12722346645892410339387481)
          ·
            refine ⟨9541759984419307754540611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12722346645892410339387481 9541759984419307754540611)
            ·
              refine ⟨14312639976628961631810917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9541759984419307754540611 14312639976628961631810917)
              ·
                refine ⟨2683619995617930305964547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14312639976628961631810917 2683619995617930305964547)
                ·
                  refine ⟨4025429993426895458946821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683619995617930305964547 4025429993426895458946821)
                  ·
                    refine ⟨754768123767542898552529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025429993426895458946821 754768123767542898552529)
                    ·
                      rfl

theorem cell23_4409717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4409717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409717 prefixEnd_4409717 := by exact prefixLift 4409717
  have htrace : WordTrace (prefixWord ++ tailWord_4409717) baseStart_4409717 baseEnd_4409717 := by
    simpa [prefixWord, tailWord_4409717, baseEnd_4409717] using wordTrace_append hprefix tailTrace_4409717
  have hstable : (prefixWord ++ tailWord_4409717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409717).length < 2 ^ (prefixWord ++ tailWord_4409717).sum := by decide
  have hdescent : baseEnd_4409717 < baseStart_4409717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409733 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 1, 5, 2]
def baseStart_4409733 : Nat := 118140960795 + 4409733 * 2 ^ 59
def prefixEnd_4409733 : Nat := 4983230072969 + 3 ^ 40 * 4409733 * 2
def baseEnd_4409733 : Nat := 2264312586993100633057513

theorem tailTrace_4409733 : CollatzResearch.WordTrace tailWord_4409733 prefixEnd_4409733 2264312586993100633057513 := by
  unfold tailWord_4409733
  simp only [CollatzResearch.WordTrace]
  refine ⟨160836175733297938282369853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107224117155531958854913235 160836175733297938282369853)
  ·
    refine ⟨60313565899986726855888695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160836175733297938282369853 60313565899986726855888695)
    ·
      refine ⟨90470348849980090283833043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60313565899986726855888695 90470348849980090283833043)
      ·
        refine ⟨135705523274970135425749565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90470348849980090283833043 135705523274970135425749565)
        ·
          refine ⟨50889571228113800784656087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135705523274970135425749565 50889571228113800784656087)
          ·
            refine ⟨76334356842170701176984131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50889571228113800784656087 76334356842170701176984131)
            ·
              refine ⟨114501535263256051765476197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76334356842170701176984131 114501535263256051765476197)
              ·
                refine ⟨21469037861860509706026787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114501535263256051765476197 21469037861860509706026787)
                ·
                  refine ⟨32203556792790764559040181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21469037861860509706026787 32203556792790764559040181)
                  ·
                    refine ⟨3019083449324134177410017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32203556792790764559040181 3019083449324134177410017)
                    ·
                      refine ⟨2264312586993100633057513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019083449324134177410017 2264312586993100633057513)
                      ·
                        rfl

theorem cell23_4409733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_4409733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409733 prefixEnd_4409733 := by exact prefixLift 4409733
  have htrace : WordTrace (prefixWord ++ tailWord_4409733) baseStart_4409733 baseEnd_4409733 := by
    simpa [prefixWord, tailWord_4409733, baseEnd_4409733] using wordTrace_append hprefix tailTrace_4409733
  have hstable : (prefixWord ++ tailWord_4409733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409733).length < 2 ^ (prefixWord ++ tailWord_4409733).sum := by decide
  have hdescent : baseEnd_4409733 < baseStart_4409733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409736 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4409736 : Nat := 118140960795 + 4409736 * 2 ^ 59
def prefixEnd_4409736 : Nat := 4983230072969 + 3 ^ 40 * 4409736 * 2
def baseEnd_4409736 : Nat := 2264314127435064121319999

theorem tailTrace_4409736 : CollatzResearch.WordTrace tailWord_4409736 prefixEnd_4409736 2264314127435064121319999 := by
  unfold tailWord_4409736
  simp only [CollatzResearch.WordTrace]
  refine ⟨80418142576143534897364531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107224190101524713196486041 80418142576143534897364531)
  ·
    refine ⟨120627213864215302346046797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80418142576143534897364531 120627213864215302346046797)
    ·
      refine ⟨45235205199080738379767549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120627213864215302346046797 45235205199080738379767549)
      ·
        refine ⟨16963201949655276892412831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45235205199080738379767549 16963201949655276892412831)
        ·
          refine ⟨25444802924482915338619247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16963201949655276892412831 25444802924482915338619247)
          ·
            refine ⟨38167204386724373007928871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25444802924482915338619247 38167204386724373007928871)
            ·
              refine ⟨57250806580086559511893307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38167204386724373007928871 57250806580086559511893307)
              ·
                refine ⟨85876209870129839267839961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57250806580086559511893307 85876209870129839267839961)
                ·
                  refine ⟨64407157402597379450879971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85876209870129839267839961 64407157402597379450879971)
                  ·
                    refine ⟨96610736103896069176319957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64407157402597379450879971 96610736103896069176319957)
                    ·
                      refine ⟨2264314127435064121319999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96610736103896069176319957 2264314127435064121319999)
                      ·
                        rfl

theorem cell23_4409736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4409736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409736 prefixEnd_4409736 := by exact prefixLift 4409736
  have htrace : WordTrace (prefixWord ++ tailWord_4409736) baseStart_4409736 baseEnd_4409736 := by
    simpa [prefixWord, tailWord_4409736, baseEnd_4409736] using wordTrace_append hprefix tailTrace_4409736
  have hstable : (prefixWord ++ tailWord_4409736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409736).length < 2 ^ (prefixWord ++ tailWord_4409736).sum := by decide
  have hdescent : baseEnd_4409736 < baseStart_4409736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409740 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_4409740 : Nat := 118140960795 + 4409740 * 2 ^ 59
def prefixEnd_4409740 : Nat := 4983230072969 + 3 ^ 40 * 4409740 * 2
def baseEnd_4409740 : Nat := 2264316181357682105669981

theorem tailTrace_4409740 : CollatzResearch.WordTrace tailWord_4409740 prefixEnd_4409740 2264316181357682105669981 := by
  unfold tailWord_4409740
  simp only [CollatzResearch.WordTrace]
  refine ⟨80418215522136289238937337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107224287362848385651916449 80418215522136289238937337)
  ·
    refine ⟨60313661641602216929203003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80418215522136289238937337 60313661641602216929203003)
    ·
      refine ⟨90470492462403325393804505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60313661641602216929203003 90470492462403325393804505)
      ·
        refine ⟨67852869346802494045353379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90470492462403325393804505 67852869346802494045353379)
        ·
          refine ⟨101779304020203741068030069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67852869346802494045353379 101779304020203741068030069)
          ·
            refine ⟨9541809751894100725127819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101779304020203741068030069 9541809751894100725127819)
            ·
              refine ⟨14312714627841151087691729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9541809751894100725127819 14312714627841151087691729)
              ·
                refine ⟨10734535970880863315768797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14312714627841151087691729 10734535970880863315768797)
                ·
                  refine ⟨4025450989080323743413299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10734535970880863315768797 4025450989080323743413299)
                  ·
                    refine ⟨6038176483620485615119949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4025450989080323743413299 6038176483620485615119949)
                    ·
                      refine ⟨2264316181357682105669981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6038176483620485615119949 2264316181357682105669981)
                      ·
                        rfl

theorem cell23_4409740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_4409740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409740 prefixEnd_4409740 := by exact prefixLift 4409740
  have htrace : WordTrace (prefixWord ++ tailWord_4409740) baseStart_4409740 baseEnd_4409740 := by
    simpa [prefixWord, tailWord_4409740, baseEnd_4409740] using wordTrace_append hprefix tailTrace_4409740
  have hstable : (prefixWord ++ tailWord_4409740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409740).length < 2 ^ (prefixWord ++ tailWord_4409740).sum := by decide
  have hdescent : baseEnd_4409740 < baseStart_4409740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409760 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 1, 5]
def baseStart_4409760 : Nat := 118140960795 + 4409760 * 2 ^ 59
def prefixEnd_4409760 : Nat := 4983230072969 + 3 ^ 40 * 4409760 * 2
def baseEnd_4409760 : Nat := 754775483656924009139963

theorem tailTrace_4409760 : CollatzResearch.WordTrace tailWord_4409760 prefixEnd_4409760 754775483656924009139963 := by
  unfold tailWord_4409760
  simp only [CollatzResearch.WordTrace]
  refine ⟨80418580252100060946801367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107224773669466747929068489 80418580252100060946801367)
  ·
    refine ⟨120627870378150091420202051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80418580252100060946801367 120627870378150091420202051)
    ·
      refine ⟨180941805567225137130303077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120627870378150091420202051 180941805567225137130303077)
      ·
        refine ⟨33926588543854713211931827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180941805567225137130303077 33926588543854713211931827)
        ·
          refine ⟨50889882815782069817897741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33926588543854713211931827 50889882815782069817897741)
          ·
            refine ⟨19083706055918276181711653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50889882815782069817897741 19083706055918276181711653)
            ·
              refine ⟨3578194885484676784070935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19083706055918276181711653 3578194885484676784070935)
              ·
                refine ⟨5367292328227015176106403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3578194885484676784070935 5367292328227015176106403)
                ·
                  refine ⟨8050938492340522764159605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5367292328227015176106403 8050938492340522764159605)
                  ·
                    refine ⟨754775483656924009139963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8050938492340522764159605 754775483656924009139963)
                    ·
                      rfl

theorem cell23_4409760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 5].length) (baseStart_4409760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409760 prefixEnd_4409760 := by exact prefixLift 4409760
  have htrace : WordTrace (prefixWord ++ tailWord_4409760) baseStart_4409760 baseEnd_4409760 := by
    simpa [prefixWord, tailWord_4409760, baseEnd_4409760] using wordTrace_append hprefix tailTrace_4409760
  have hstable : (prefixWord ++ tailWord_4409760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409760).length < 2 ^ (prefixWord ++ tailWord_4409760).sum := by decide
  have hdescent : baseEnd_4409760 < baseStart_4409760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409783 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_4409783 : Nat := 118140960795 + 4409783 * 2 ^ 59
def prefixEnd_4409783 : Nat := 4983230072969 + 3 ^ 40 * 4409783 * 2
def baseEnd_4409783 : Nat := 2264338261025825437432283

theorem tailTrace_4409783 : CollatzResearch.WordTrace tailWord_4409783 prefixEnd_4409783 2264338261025825437432283 := by
  unfold tailWord_4409783
  simp only [CollatzResearch.WordTrace]
  refine ⟨160837999383116796821690003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107225332922077864547793335 160837999383116796821690003)
  ·
    refine ⟨241256999074675195232535005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160837999383116796821690003 241256999074675195232535005)
    ·
      refine ⟨90471374653003198212200627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241256999074675195232535005 90471374653003198212200627)
      ·
        refine ⟨135707061979504797318300941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90471374653003198212200627 135707061979504797318300941)
        ·
          refine ⟨50890148242314298994362853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135707061979504797318300941 50890148242314298994362853)
          ·
            refine ⟨9541902795433931061443035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50890148242314298994362853 9541902795433931061443035)
            ·
              refine ⟨14312854193150896592164553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9541902795433931061443035 14312854193150896592164553)
              ·
                refine ⟨10734640644863172444123415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14312854193150896592164553 10734640644863172444123415)
                ·
                  refine ⟨16101960967294758666185123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10734640644863172444123415 16101960967294758666185123)
                  ·
                    refine ⟨24152941450942137999277685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16101960967294758666185123 24152941450942137999277685)
                    ·
                      refine ⟨2264338261025825437432283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24152941450942137999277685 2264338261025825437432283)
                      ·
                        rfl

theorem cell23_4409783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_4409783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409783 prefixEnd_4409783 := by exact prefixLift 4409783
  have htrace : WordTrace (prefixWord ++ tailWord_4409783) baseStart_4409783 baseEnd_4409783 := by
    simpa [prefixWord, tailWord_4409783, baseEnd_4409783] using wordTrace_append hprefix tailTrace_4409783
  have hstable : (prefixWord ++ tailWord_4409783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409783).length < 2 ^ (prefixWord ++ tailWord_4409783).sum := by decide
  have hdescent : baseEnd_4409783 < baseStart_4409783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409790 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_4409790 : Nat := 118140960795 + 4409790 * 2 ^ 59
def prefixEnd_4409790 : Nat := 4983230072969 + 3 ^ 40 * 4409790 * 2
def baseEnd_4409790 : Nat := 754780618463468970014917

theorem tailTrace_4409790 : CollatzResearch.WordTrace tailWord_4409790 prefixEnd_4409790 754780618463468970014917 := by
  unfold tailWord_4409790
  simp only [CollatzResearch.WordTrace]
  refine ⟨20104781836761429627149353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107225503129394291344796549 20104781836761429627149353)
  ·
    refine ⟨15078586377571072220362015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20104781836761429627149353 15078586377571072220362015)
    ·
      refine ⟨22617879566356608330543023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15078586377571072220362015 22617879566356608330543023)
      ·
        refine ⟨33926819349534912495814535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22617879566356608330543023 33926819349534912495814535)
        ·
          refine ⟨50890229024302368743721803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33926819349534912495814535 50890229024302368743721803)
          ·
            refine ⟨76335343536453553115582705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50890229024302368743721803 76335343536453553115582705)
            ·
              refine ⟨57251507652340164836687029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76335343536453553115582705 57251507652340164836687029)
              ·
                refine ⟨5367328842406890453439409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57251507652340164836687029 5367328842406890453439409)
                ·
                  refine ⟨4025496631805167840079557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367328842406890453439409 4025496631805167840079557)
                  ·
                    refine ⟨754780618463468970014917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025496631805167840079557 754780618463468970014917)
                    ·
                      rfl

theorem cell23_4409790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_4409790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409790 prefixEnd_4409790 := by exact prefixLift 4409790
  have htrace : WordTrace (prefixWord ++ tailWord_4409790) baseStart_4409790 baseEnd_4409790 := by
    simpa [prefixWord, tailWord_4409790, baseEnd_4409790] using wordTrace_append hprefix tailTrace_4409790
  have hstable : (prefixWord ++ tailWord_4409790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409790).length < 2 ^ (prefixWord ++ tailWord_4409790).sum := by decide
  have hdescent : baseEnd_4409790 < baseStart_4409790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409800 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_4409800 : Nat := 118140960795 + 4409800 * 2 ^ 59
def prefixEnd_4409800 : Nat := 4983230072969 + 3 ^ 40 * 4409800 * 2
def baseEnd_4409800 : Nat := 2264346990196951870919705

theorem tailTrace_4409800 : CollatzResearch.WordTrace tailWord_4409800 prefixEnd_4409800 2264346990196951870919705 := by
  unfold tailWord_4409800
  simp only [CollatzResearch.WordTrace]
  refine ⟨80419309712027604362529427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107225746282703472483372569 80419309712027604362529427)
  ·
    refine ⟨120628964568041406543794141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80419309712027604362529427 120628964568041406543794141)
    ·
      refine ⟨45235861713015527453922803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120628964568041406543794141 45235861713015527453922803)
      ·
        refine ⟨67853792569523291180884205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45235861713015527453922803 67853792569523291180884205)
        ·
          refine ⟨25445172213571234192831577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67853792569523291180884205 25445172213571234192831577)
          ·
            refine ⟨19083879160178425644623683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25445172213571234192831577 19083879160178425644623683)
            ·
              refine ⟨28625818740267638466935525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19083879160178425644623683 28625818740267638466935525)
              ·
                refine ⟨5367341013800182212550411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28625818740267638466935525 5367341013800182212550411)
                ·
                  refine ⟨8051011520700273318825617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5367341013800182212550411 8051011520700273318825617)
                  ·
                    refine ⟨6038258640525204989119213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8051011520700273318825617 6038258640525204989119213)
                    ·
                      refine ⟨2264346990196951870919705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6038258640525204989119213 2264346990196951870919705)
                      ·
                        rfl

theorem cell23_4409800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_4409800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409800 prefixEnd_4409800 := by exact prefixLift 4409800
  have htrace : WordTrace (prefixWord ++ tailWord_4409800) baseStart_4409800 baseEnd_4409800 := by
    simpa [prefixWord, tailWord_4409800, baseEnd_4409800] using wordTrace_append hprefix tailTrace_4409800
  have hstable : (prefixWord ++ tailWord_4409800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409800).length < 2 ^ (prefixWord ++ tailWord_4409800).sum := by decide
  have hdescent : baseEnd_4409800 < baseStart_4409800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409816 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_4409816 : Nat := 118140960795 + 4409816 * 2 ^ 59
def prefixEnd_4409816 : Nat := 4983230072969 + 3 ^ 40 * 4409816 * 2
def baseEnd_4409816 : Nat := 754785068629141269439877

theorem tailTrace_4409816 : CollatzResearch.WordTrace tailWord_4409816 prefixEnd_4409816 754785068629141269439877 := by
  unfold tailWord_4409816
  simp only [CollatzResearch.WordTrace]
  refine ⟨80419601495998621728820651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107226135327998162305094201 80419601495998621728820651)
  ·
    refine ⟨120629402243997932593230977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80419601495998621728820651 120629402243997932593230977)
    ·
      refine ⟨90472051682998449444923233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120629402243997932593230977 90472051682998449444923233)
      ·
        refine ⟨67854038762248837083692425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90472051682998449444923233 67854038762248837083692425)
        ·
          refine ⟨50890529071686627812769319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67854038762248837083692425 50890529071686627812769319)
          ·
            refine ⟨76335793607529941719153979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50890529071686627812769319 76335793607529941719153979)
            ·
              refine ⟨114503690411294912578730969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76335793607529941719153979 114503690411294912578730969)
              ·
                refine ⟨85877767808471184434048227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114503690411294912578730969 85877767808471184434048227)
                ·
                  refine ⟨128816651712706776651072341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85877767808471184434048227 128816651712706776651072341)
                  ·
                    refine ⟨754785068629141269439877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128816651712706776651072341 754785068629141269439877)
                    ·
                      rfl

theorem cell23_4409816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_4409816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409816 prefixEnd_4409816 := by exact prefixLift 4409816
  have htrace : WordTrace (prefixWord ++ tailWord_4409816) baseStart_4409816 baseEnd_4409816 := by
    simpa [prefixWord, tailWord_4409816, baseEnd_4409816] using wordTrace_append hprefix tailTrace_4409816
  have hstable : (prefixWord ++ tailWord_4409816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409816).length < 2 ^ (prefixWord ++ tailWord_4409816).sum := by decide
  have hdescent : baseEnd_4409816 < baseStart_4409816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409831 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4409831 : Nat := 118140960795 + 4409831 * 2 ^ 59
def prefixEnd_4409831 : Nat := 4983230072969 + 3 ^ 40 * 4409831 * 2
def baseEnd_4409831 : Nat := 2264362908097241249632063

theorem tailTrace_4409831 : CollatzResearch.WordTrace tailWord_4409831 prefixEnd_4409831 2264362908097241249632063 := by
  unfold tailWord_4409831
  simp only [CollatzResearch.WordTrace]
  refine ⟨160839750086942901019437347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107226500057961934012958231 160839750086942901019437347)
  ·
    refine ⟨241259625130414351529156021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160839750086942901019437347 241259625130414351529156021)
    ·
      refine ⟨22618089855976345455858377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241259625130414351529156021 22618089855976345455858377)
      ·
        refine ⟨16963567391982259091893783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22618089855976345455858377 16963567391982259091893783)
        ·
          refine ⟨25445351087973388637840675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16963567391982259091893783 25445351087973388637840675)
          ·
            refine ⟨38168026631960082956761013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25445351087973388637840675 38168026631960082956761013)
            ·
              refine ⟨3578252496746257777196345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38168026631960082956761013 3578252496746257777196345)
              ·
                refine ⟨2683689372559693332897259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3578252496746257777196345 2683689372559693332897259)
                ·
                  refine ⟨4025534058839539999345889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683689372559693332897259 4025534058839539999345889)
                  ·
                    refine ⟨3019150544129654999509417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025534058839539999345889 3019150544129654999509417)
                    ·
                      refine ⟨2264362908097241249632063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019150544129654999509417 2264362908097241249632063)
                      ·
                        rfl

theorem cell23_4409831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4409831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409831 prefixEnd_4409831 := by exact prefixLift 4409831
  have htrace : WordTrace (prefixWord ++ tailWord_4409831) baseStart_4409831 baseEnd_4409831 := by
    simpa [prefixWord, tailWord_4409831, baseEnd_4409831] using wordTrace_append hprefix tailTrace_4409831
  have hstable : (prefixWord ++ tailWord_4409831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409831).length < 2 ^ (prefixWord ++ tailWord_4409831).sum := by decide
  have hdescent : baseEnd_4409831 < baseStart_4409831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409840 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 3, 3, 2]
def baseStart_4409840 : Nat := 118140960795 + 4409840 * 2 ^ 59
def prefixEnd_4409840 : Nat := 4983230072969 + 3 ^ 40 * 4409840 * 2
def baseEnd_4409840 : Nat := 2264367529423131714419521

theorem tailTrace_4409840 : CollatzResearch.WordTrace tailWord_4409840 prefixEnd_4409840 2264367529423131714419521 := by
  unfold tailWord_4409840
  simp only [CollatzResearch.WordTrace]
  refine ⟨80420039171955147778257487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107226718895940197037676649 80420039171955147778257487)
  ·
    refine ⟨120630058757932721667386231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80420039171955147778257487 120630058757932721667386231)
    ·
      refine ⟨180945088136899082501079347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120630058757932721667386231 180945088136899082501079347)
      ·
        refine ⟨271417632205348623751619021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180945088136899082501079347 271417632205348623751619021)
        ·
          refine ⟨101781612077005733906857133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271417632205348623751619021 101781612077005733906857133)
          ·
            refine ⟨38168104528877150215071425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101781612077005733906857133 38168104528877150215071425)
            ·
              refine ⟨28626078396657862661303569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38168104528877150215071425 28626078396657862661303569)
              ·
                refine ⟨21469558797493396995977677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28626078396657862661303569 21469558797493396995977677)
                ·
                  refine ⟨8051084549060023873491629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21469558797493396995977677 8051084549060023873491629)
                  ·
                    refine ⟨3019156705897508952559361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8051084549060023873491629 3019156705897508952559361)
                    ·
                      refine ⟨2264367529423131714419521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019156705897508952559361 2264367529423131714419521)
                      ·
                        rfl

theorem cell23_4409840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 3, 2].length) (baseStart_4409840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409840 prefixEnd_4409840 := by exact prefixLift 4409840
  have htrace : WordTrace (prefixWord ++ tailWord_4409840) baseStart_4409840 baseEnd_4409840 := by
    simpa [prefixWord, tailWord_4409840, baseEnd_4409840] using wordTrace_append hprefix tailTrace_4409840
  have hstable : (prefixWord ++ tailWord_4409840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409840).length < 2 ^ (prefixWord ++ tailWord_4409840).sum := by decide
  have hdescent : baseEnd_4409840 < baseStart_4409840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409856 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_4409856 : Nat := 118140960795 + 4409856 * 2 ^ 59
def prefixEnd_4409856 : Nat := 4983230072969 + 3 ^ 40 * 4409856 * 2
def baseEnd_4409856 : Nat := 2264375745113603651819447

theorem tailTrace_4409856 : CollatzResearch.WordTrace tailWord_4409856 prefixEnd_4409856 2264375745113603651819447 := by
  unfold tailWord_4409856
  simp only [CollatzResearch.WordTrace]
  refine ⟨80420330955926165144548711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107227107941234886859398281 80420330955926165144548711)
  ·
    refine ⟨120630496433889247716823067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80420330955926165144548711 120630496433889247716823067)
    ·
      refine ⟨180945744650833871575234601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120630496433889247716823067 180945744650833871575234601)
      ·
        refine ⟨135709308488125403681425951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180945744650833871575234601 135709308488125403681425951)
        ·
          refine ⟨203563962732188105522138927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135709308488125403681425951 203563962732188105522138927)
          ·
            refine ⟨305345944098282158283208391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203563962732188105522138927 305345944098282158283208391)
            ·
              refine ⟨458018916147423237424812587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305345944098282158283208391 458018916147423237424812587)
              ·
                refine ⟨687028374221134856137218881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458018916147423237424812587 687028374221134856137218881)
                ·
                  refine ⟨515271280665851142102914161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 687028374221134856137218881 515271280665851142102914161)
                  ·
                    refine ⟨386453460499388356577185621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 515271280665851142102914161 386453460499388356577185621)
                    ·
                      refine ⟨2264375745113603651819447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 386453460499388356577185621 2264375745113603651819447)
                      ·
                        rfl

theorem cell23_4409856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_4409856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409856 prefixEnd_4409856 := by exact prefixLift 4409856
  have htrace : WordTrace (prefixWord ++ tailWord_4409856) baseStart_4409856 baseEnd_4409856 := by
    simpa [prefixWord, tailWord_4409856, baseEnd_4409856] using wordTrace_append hprefix tailTrace_4409856
  have hstable : (prefixWord ++ tailWord_4409856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409856).length < 2 ^ (prefixWord ++ tailWord_4409856).sum := by decide
  have hdescent : baseEnd_4409856 < baseStart_4409856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409857 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_4409857 : Nat := 118140960795 + 4409857 * 2 ^ 59
def prefixEnd_4409857 : Nat := 4983230072969 + 3 ^ 40 * 4409857 * 2
def baseEnd_4409857 : Nat := 2264376258594258147906943

theorem tailTrace_4409857 : CollatzResearch.WordTrace tailWord_4409857 prefixEnd_4409857 2264376258594258147906943 := by
  unfold tailWord_4409857
  simp only [CollatzResearch.WordTrace]
  refine ⟨160840698384848707459883825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107227132256565804973255883 160840698384848707459883825)
  ·
    refine ⟨120630523788636530594912869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160840698384848707459883825 120630523788636530594912869)
    ·
      refine ⟨22618223210369349486546163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120630523788636530594912869 22618223210369349486546163)
      ·
        refine ⟨33927334815554024229819245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22618223210369349486546163 33927334815554024229819245)
        ·
          refine ⟨12722750555832759086182217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33927334815554024229819245 12722750555832759086182217)
          ·
            refine ⟨9542062916874569314636663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12722750555832759086182217 9542062916874569314636663)
            ·
              refine ⟨14313094375311853971954995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9542062916874569314636663 14313094375311853971954995)
              ·
                refine ⟨21469641562967780957932493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14313094375311853971954995 21469641562967780957932493)
                ·
                  refine ⟨8051115586112917859224685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21469641562967780957932493 8051115586112917859224685)
                  ·
                    refine ⟨3019168344792344197209257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8051115586112917859224685 3019168344792344197209257)
                    ·
                      refine ⟨2264376258594258147906943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019168344792344197209257 2264376258594258147906943)
                      ·
                        rfl

theorem cell23_4409857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_4409857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409857 prefixEnd_4409857 := by exact prefixLift 4409857
  have htrace : WordTrace (prefixWord ++ tailWord_4409857) baseStart_4409857 baseEnd_4409857 := by
    simpa [prefixWord, tailWord_4409857, baseEnd_4409857] using wordTrace_append hprefix tailTrace_4409857
  have hstable : (prefixWord ++ tailWord_4409857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409857).length < 2 ^ (prefixWord ++ tailWord_4409857).sum := by decide
  have hdescent : baseEnd_4409857 < baseStart_4409857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409910 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_4409910 : Nat := 118140960795 + 4409910 * 2 ^ 59
def prefixEnd_4409910 : Nat := 4983230072969 + 3 ^ 40 * 4409910 * 2
def baseEnd_4409910 : Nat := 251600385896549604504911

theorem tailTrace_4409910 : CollatzResearch.WordTrace tailWord_4409910 prefixEnd_4409910 251600385896549604504911 := by
  unfold tailWord_4409910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052664465853543594472699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107228420969104465007708789 10052664465853543594472699)
  ·
    refine ⟨15078996698780315391709049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10052664465853543594472699 15078996698780315391709049)
    ·
      refine ⟨11309247524085236543781787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15078996698780315391709049 11309247524085236543781787)
      ·
        refine ⟨16963871286127854815672681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11309247524085236543781787 16963871286127854815672681)
        ·
          refine ⟨12722903464595891111754511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16963871286127854815672681 12722903464595891111754511)
          ·
            refine ⟨19084355196893836667631767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12722903464595891111754511 19084355196893836667631767)
            ·
              refine ⟨28626532795340755001447651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19084355196893836667631767 28626532795340755001447651)
              ·
                refine ⟨42939799193011132502171477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28626532795340755001447651 42939799193011132502171477)
                ·
                  refine ⟨251600385896549604504911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42939799193011132502171477 251600385896549604504911)
                  ·
                    rfl

theorem cell23_4409910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_4409910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409910 prefixEnd_4409910 := by exact prefixLift 4409910
  have htrace : WordTrace (prefixWord ++ tailWord_4409910) baseStart_4409910 baseEnd_4409910 := by
    simpa [prefixWord, tailWord_4409910, baseEnd_4409910] using wordTrace_append hprefix tailTrace_4409910
  have hstable : (prefixWord ++ tailWord_4409910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409910).length < 2 ^ (prefixWord ++ tailWord_4409910).sum := by decide
  have hdescent : baseEnd_4409910 < baseStart_4409910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409927 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 5]
def baseStart_4409927 : Nat := 118140960795 + 4409927 * 2 ^ 59
def prefixEnd_4409927 : Nat := 4983230072969 + 3 ^ 40 * 4409927 * 2
def baseEnd_4409927 : Nat := 251601355804452541559069

theorem tailTrace_4409927 : CollatzResearch.WordTrace tailWord_4409927 prefixEnd_4409927 251601355804452541559069 := by
  unfold tailWord_4409927
  simp only [CollatzResearch.WordTrace]
  refine ⟨160843251494595109414932035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107228834329730072943288023 160843251494595109414932035)
  ·
    refine ⟨241264877241892664122398053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160843251494595109414932035 241264877241892664122398053)
    ·
      refine ⟨45237164482854874522949635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241264877241892664122398053 45237164482854874522949635)
      ·
        refine ⟨67855746724282311784424453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45237164482854874522949635 67855746724282311784424453)
        ·
          refine ⟨12722952510802933459579585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67855746724282311784424453 12722952510802933459579585)
          ·
            refine ⟨9542214383102200094684689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12722952510802933459579585 9542214383102200094684689)
            ·
              refine ⟨7156660787326650071013517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9542214383102200094684689 7156660787326650071013517)
              ·
                refine ⟨2683747795247493776630069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7156660787326650071013517 2683747795247493776630069)
                ·
                  refine ⟨251601355804452541559069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2683747795247493776630069 251601355804452541559069)
                  ·
                    rfl

theorem cell23_4409927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 5].length) (baseStart_4409927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409927 prefixEnd_4409927 := by exact prefixLift 4409927
  have htrace : WordTrace (prefixWord ++ tailWord_4409927) baseStart_4409927 baseEnd_4409927 := by
    simpa [prefixWord, tailWord_4409927, baseEnd_4409927] using wordTrace_append hprefix tailTrace_4409927
  have hstable : (prefixWord ++ tailWord_4409927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409927).length < 2 ^ (prefixWord ++ tailWord_4409927).sum := by decide
  have hdescent : baseEnd_4409927 < baseStart_4409927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409980 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_4409980 : Nat := 118140960795 + 4409980 * 2 ^ 59
def prefixEnd_4409980 : Nat := 4983230072969 + 3 ^ 40 * 4409980 * 2
def baseEnd_4409980 : Nat := 2264439416714761166668877

theorem tailTrace_4409980 : CollatzResearch.WordTrace tailWord_4409980 prefixEnd_4409980 2264439416714761166668877 := by
  unfold tailWord_4409980
  simp only [CollatzResearch.WordTrace]
  refine ⟨80422592281701549733305697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107230123042268732977740929 80422592281701549733305697)
  ·
    refine ⟨60316944211276162299979273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80422592281701549733305697 60316944211276162299979273)
    ·
      refine ⟨45237708158457121724984455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60316944211276162299979273 45237708158457121724984455)
      ·
        refine ⟨67856562237685682587476683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45237708158457121724984455 67856562237685682587476683)
        ·
          refine ⟨101784843356528523881215025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67856562237685682587476683 101784843356528523881215025)
          ·
            refine ⟨76338632517396392910911269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101784843356528523881215025 76338632517396392910911269)
            ·
              refine ⟨14313493597011823670795863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76338632517396392910911269 14313493597011823670795863)
              ·
                refine ⟨21470240395517735506193795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14313493597011823670795863 21470240395517735506193795)
                ·
                  refine ⟨32205360593276603259290693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21470240395517735506193795 32205360593276603259290693)
                  ·
                    refine ⟨6038505111239363111117005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32205360593276603259290693 6038505111239363111117005)
                    ·
                      refine ⟨2264439416714761166668877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6038505111239363111117005 2264439416714761166668877)
                      ·
                        rfl

theorem cell23_4409980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_4409980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4409980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4409980 prefixEnd_4409980 := by exact prefixLift 4409980
  have htrace : WordTrace (prefixWord ++ tailWord_4409980) baseStart_4409980 baseEnd_4409980 := by
    simpa [prefixWord, tailWord_4409980, baseEnd_4409980] using wordTrace_append hprefix tailTrace_4409980
  have hstable : (prefixWord ++ tailWord_4409980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409980).length < 2 ^ (prefixWord ++ tailWord_4409980).sum := by decide
  have hdescent : baseEnd_4409980 < baseStart_4409980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410004 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_4410004 : Nat := 118140960795 + 4410004 * 2 ^ 59
def prefixEnd_4410004 : Nat := 4983230072969 + 3 ^ 40 * 4410004 * 2
def baseEnd_4410004 : Nat := 754817246750156357589589

theorem tailTrace_4410004 : CollatzResearch.WordTrace tailWord_4410004 prefixEnd_4410004 754817246750156357589589 := by
  unfold tailWord_4410004
  simp only [CollatzResearch.WordTrace]
  refine ⟨80423029957658075782742533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107230706610210767710323377 80423029957658075782742533)
  ·
    refine ⟨15079318117060889209264225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80423029957658075782742533 15079318117060889209264225)
    ·
      refine ⟨11309488587795666906948169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15079318117060889209264225 11309488587795666906948169)
      ·
        refine ⟨8482116440846750180211127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11309488587795666906948169 8482116440846750180211127)
        ·
          refine ⟨12723174661270125270316691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8482116440846750180211127 12723174661270125270316691)
          ·
            refine ⟨19084761991905187905475037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12723174661270125270316691 19084761991905187905475037)
            ·
              refine ⟨7156785746964445464553139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19084761991905187905475037 7156785746964445464553139)
              ·
                refine ⟨10735178620446668196829709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7156785746964445464553139 10735178620446668196829709)
                ·
                  refine ⟨4025691982667500573811141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10735178620446668196829709 4025691982667500573811141)
                  ·
                    refine ⟨754817246750156357589589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025691982667500573811141 754817246750156357589589)
                    ·
                      rfl

theorem cell23_4410004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_4410004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410004 prefixEnd_4410004 := by exact prefixLift 4410004
  have htrace : WordTrace (prefixWord ++ tailWord_4410004) baseStart_4410004 baseEnd_4410004 := by
    simpa [prefixWord, tailWord_4410004, baseEnd_4410004] using wordTrace_append hprefix tailTrace_4410004
  have hstable : (prefixWord ++ tailWord_4410004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410004).length < 2 ^ (prefixWord ++ tailWord_4410004).sum := by decide
  have hdescent : baseEnd_4410004 < baseStart_4410004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410017 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 6]
def baseStart_4410017 : Nat := 118140960795 + 4410017 * 2 ^ 59
def prefixEnd_4410017 : Nat := 4983230072969 + 3 ^ 40 * 4410017 * 2
def baseEnd_4410017 : Nat := 251606490610997502434023

theorem tailTrace_4410017 : CollatzResearch.WordTrace tailWord_4410017 prefixEnd_4410017 251606490610997502434023 := by
  unfold tailWord_4410017
  simp only [CollatzResearch.WordTrace]
  refine ⟨160846534064269054785708305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107231022709512703190472203 160846534064269054785708305)
  ·
    refine ⟨120634900548201791089281229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160846534064269054785708305 120634900548201791089281229)
    ·
      refine ⟨45238087705575671658480461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120634900548201791089281229 45238087705575671658480461)
      ·
        refine ⟨16964282889590876871930173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45238087705575671658480461 16964282889590876871930173)
        ·
          refine ⟨6361606083596578826973815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16964282889590876871930173 6361606083596578826973815)
          ·
            refine ⟨9542409125394868240460723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6361606083596578826973815 9542409125394868240460723)
            ·
              refine ⟨14313613688092302360691085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9542409125394868240460723 14313613688092302360691085)
              ·
                refine ⟨5367605133034613385259157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14313613688092302360691085 5367605133034613385259157)
                ·
                  refine ⟨251606490610997502434023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5367605133034613385259157 251606490610997502434023)
                  ·
                    rfl

theorem cell23_4410017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 6].length) (baseStart_4410017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410017 prefixEnd_4410017 := by exact prefixLift 4410017
  have htrace : WordTrace (prefixWord ++ tailWord_4410017) baseStart_4410017 baseEnd_4410017 := by
    simpa [prefixWord, tailWord_4410017, baseEnd_4410017] using wordTrace_append hprefix tailTrace_4410017
  have hstable : (prefixWord ++ tailWord_4410017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410017).length < 2 ^ (prefixWord ++ tailWord_4410017).sum := by decide
  have hdescent : baseEnd_4410017 < baseStart_4410017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410084 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_4410084 : Nat := 118140960795 + 4410084 * 2 ^ 59
def prefixEnd_4410084 : Nat := 4983230072969 + 3 ^ 40 * 4410084 * 2
def baseEnd_4410084 : Nat := 2264492818702828759768399

theorem tailTrace_4410084 : CollatzResearch.WordTrace tailWord_4410084 prefixEnd_4410084 2264492818702828759768399 := by
  unfold tailWord_4410084
  simp only [CollatzResearch.WordTrace]
  refine ⟨80424488877513162614198653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107232651836684216818931537 80424488877513162614198653)
  ·
    refine ⟨30159183329067435980324495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80424488877513162614198653 30159183329067435980324495)
    ·
      refine ⟨45238774993601153970486743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30159183329067435980324495 45238774993601153970486743)
      ·
        refine ⟨67858162490401730955730115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45238774993601153970486743 67858162490401730955730115)
        ·
          refine ⟨101787243735602596433595173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67858162490401730955730115 101787243735602596433595173)
          ·
            refine ⟨19085108200425486831299095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101787243735602596433595173 19085108200425486831299095)
            ·
              refine ⟨28627662300638230246948643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19085108200425486831299095 28627662300638230246948643)
              ·
                refine ⟨42941493450957345370422965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28627662300638230246948643 42941493450957345370422965)
                ·
                  refine ⟨4025765011027251128477153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42941493450957345370422965 4025765011027251128477153)
                  ·
                    refine ⟨3019323758270438346357865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025765011027251128477153 3019323758270438346357865)
                    ·
                      refine ⟨2264492818702828759768399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019323758270438346357865 2264492818702828759768399)
                      ·
                        rfl

theorem cell23_4410084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_4410084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410084 prefixEnd_4410084 := by exact prefixLift 4410084
  have htrace : WordTrace (prefixWord ++ tailWord_4410084) baseStart_4410084 baseEnd_4410084 := by
    simpa [prefixWord, tailWord_4410084, baseEnd_4410084] using wordTrace_append hprefix tailTrace_4410084
  have hstable : (prefixWord ++ tailWord_4410084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410084).length < 2 ^ (prefixWord ++ tailWord_4410084).sum := by decide
  have hdescent : baseEnd_4410084 < baseStart_4410084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410088 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_4410088 : Nat := 118140960795 + 4410088 * 2 ^ 59
def prefixEnd_4410088 : Nat := 4983230072969 + 3 ^ 40 * 4410088 * 2
def baseEnd_4410088 : Nat := 2264494872625446744118381

theorem tailTrace_4410088 : CollatzResearch.WordTrace tailWord_4410088 prefixEnd_4410088 2264494872625446744118381 := by
  unfold tailWord_4410088
  simp only [CollatzResearch.WordTrace]
  refine ⟨80424561823505916955771459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107232749098007889274361945 80424561823505916955771459)
  ·
    refine ⟨120636842735258875433657189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80424561823505916955771459 120636842735258875433657189)
    ·
      refine ⟨22619408012861039143810723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120636842735258875433657189 22619408012861039143810723)
      ·
        refine ⟨33929112019291558715716085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22619408012861039143810723 33929112019291558715716085)
        ·
          refine ⟨3180854251808583629598383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33929112019291558715716085 3180854251808583629598383)
          ·
            refine ⟨4771281377712875444397575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180854251808583629598383 4771281377712875444397575)
            ·
              refine ⟨7156922066569313166596363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771281377712875444397575 7156922066569313166596363)
              ·
                refine ⟨10735383099853969749894545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7156922066569313166596363 10735383099853969749894545)
                ·
                  refine ⟨8051537324890477312420909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10735383099853969749894545 8051537324890477312420909)
                  ·
                    refine ⟨3019326496833928992157841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8051537324890477312420909 3019326496833928992157841)
                    ·
                      refine ⟨2264494872625446744118381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019326496833928992157841 2264494872625446744118381)
                      ·
                        rfl

theorem cell23_4410088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_4410088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410088 prefixEnd_4410088 := by exact prefixLift 4410088
  have htrace : WordTrace (prefixWord ++ tailWord_4410088) baseStart_4410088 baseEnd_4410088 := by
    simpa [prefixWord, tailWord_4410088, baseEnd_4410088] using wordTrace_append hprefix tailTrace_4410088
  have hstable : (prefixWord ++ tailWord_4410088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410088).length < 2 ^ (prefixWord ++ tailWord_4410088).sum := by decide
  have hdescent : baseEnd_4410088 < baseStart_4410088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410141 : List Nat := [1, 4, 2, 4, 1, 2, 2, 7]
def baseStart_4410141 : Nat := 118140960795 + 4410141 * 2 ^ 59
def prefixEnd_4410141 : Nat := 4983230072969 + 3 ^ 40 * 4410141 * 2
def baseEnd_4410141 : Nat := 83871188411116112472431

theorem tailTrace_4410141 : CollatzResearch.WordTrace tailWord_4410141 prefixEnd_4410141 83871188411116112472431 := by
  unfold tailWord_4410141
  simp only [CollatzResearch.WordTrace]
  refine ⟨160851056715819823963222277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107234037810546549308814851 160851056715819823963222277)
  ·
    refine ⟨30159573134216216993104177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160851056715819823963222277 30159573134216216993104177)
    ·
      refine ⟨22619679850662162744828133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30159573134216216993104177 22619679850662162744828133)
      ·
        refine ⟨4241189971999155514655275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22619679850662162744828133 4241189971999155514655275)
        ·
          refine ⟨6361784957998733271982913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241189971999155514655275 6361784957998733271982913)
          ·
            refine ⟨4771338718499049953987185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6361784957998733271982913 4771338718499049953987185)
            ·
              refine ⟨3578504038874287465490389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4771338718499049953987185 3578504038874287465490389)
              ·
                refine ⟨83871188411116112472431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3578504038874287465490389 83871188411116112472431)
                ·
                  rfl

theorem cell23_4410141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 7].length) (baseStart_4410141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410141 prefixEnd_4410141 := by exact prefixLift 4410141
  have htrace : WordTrace (prefixWord ++ tailWord_4410141) baseStart_4410141 baseEnd_4410141 := by
    simpa [prefixWord, tailWord_4410141, baseEnd_4410141] using wordTrace_append hprefix tailTrace_4410141
  have hstable : (prefixWord ++ tailWord_4410141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410141).length < 2 ^ (prefixWord ++ tailWord_4410141).sum := by decide
  have hdescent : baseEnd_4410141 < baseStart_4410141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410200 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_4410200 : Nat := 118140960795 + 4410200 * 2 ^ 59
def prefixEnd_4410200 : Nat := 4983230072969 + 3 ^ 40 * 4410200 * 2
def baseEnd_4410200 : Nat := 2264552382458750305917865

theorem tailTrace_4410200 : CollatzResearch.WordTrace tailWord_4410200 prefixEnd_4410200 2264552382458750305917865 := by
  unfold tailWord_4410200
  simp only [CollatzResearch.WordTrace]
  refine ⟨80426604311303038519810027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107235472415070718026413369 80426604311303038519810027)
  ·
    refine ⟨120639906466954557779715041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80426604311303038519810027 120639906466954557779715041)
    ·
      refine ⟨90479929850215918334786281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120639906466954557779715041 90479929850215918334786281)
      ·
        refine ⟨67859947387661938751089711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90479929850215918334786281 67859947387661938751089711)
        ·
          refine ⟨101789921081492908126634567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67859947387661938751089711 101789921081492908126634567)
          ·
            refine ⟨152684881622239362189951851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101789921081492908126634567 152684881622239362189951851)
            ·
              refine ⟨229027322433359043284927777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152684881622239362189951851 229027322433359043284927777)
              ·
                refine ⟨171770491825019282463695833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229027322433359043284927777 171770491825019282463695833)
                ·
                  refine ⟨128827868868764461847771875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171770491825019282463695833 128827868868764461847771875)
                  ·
                    refine ⟨193241803303146692771657813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128827868868764461847771875 193241803303146692771657813)
                    ·
                      refine ⟨2264552382458750305917865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 193241803303146692771657813 2264552382458750305917865)
                      ·
                        rfl

theorem cell23_4410200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_4410200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410200 prefixEnd_4410200 := by exact prefixLift 4410200
  have htrace : WordTrace (prefixWord ++ tailWord_4410200) baseStart_4410200 baseEnd_4410200 := by
    simpa [prefixWord, tailWord_4410200, baseEnd_4410200] using wordTrace_append hprefix tailTrace_4410200
  have hstable : (prefixWord ++ tailWord_4410200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410200).length < 2 ^ (prefixWord ++ tailWord_4410200).sum := by decide
  have hdescent : baseEnd_4410200 < baseStart_4410200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410227 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 2, 5]
def baseStart_4410227 : Nat := 118140960795 + 4410227 * 2 ^ 59
def prefixEnd_4410227 : Nat := 4983230072969 + 3 ^ 40 * 4410227 * 2
def baseEnd_4410227 : Nat := 754855415478807233426747

theorem tailTrace_4410227 : CollatzResearch.WordTrace tailWord_4410227 prefixEnd_4410227 754855415478807233426747 := by
  unfold tailWord_4410227
  simp only [CollatzResearch.WordTrace]
  refine ⟨160854193393508260650852935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107236128929005507100568623 160854193393508260650852935)
  ·
    refine ⟨241281290090262390976279403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160854193393508260650852935 241281290090262390976279403)
    ·
      refine ⟨361921935135393586464419105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241281290090262390976279403 361921935135393586464419105)
      ·
        refine ⟨271441451351545189848314329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361921935135393586464419105 271441451351545189848314329)
        ·
          refine ⟨203581088513658892386235747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271441451351545189848314329 203581088513658892386235747)
          ·
            refine ⟨305371632770488338579353621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203581088513658892386235747 305371632770488338579353621)
            ·
              refine ⟨14314295286116640870907201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 305371632770488338579353621 14314295286116640870907201)
              ·
                refine ⟨10735721464587480653180401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14314295286116640870907201 10735721464587480653180401)
                ·
                  refine ⟨8051791098440610489885301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10735721464587480653180401 8051791098440610489885301)
                  ·
                    refine ⟨754855415478807233426747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8051791098440610489885301 754855415478807233426747)
                    ·
                      rfl

theorem cell23_4410227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 5].length) (baseStart_4410227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410227 prefixEnd_4410227 := by exact prefixLift 4410227
  have htrace : WordTrace (prefixWord ++ tailWord_4410227) baseStart_4410227 baseEnd_4410227 := by
    simpa [prefixWord, tailWord_4410227, baseEnd_4410227] using wordTrace_append hprefix tailTrace_4410227
  have hstable : (prefixWord ++ tailWord_4410227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410227).length < 2 ^ (prefixWord ++ tailWord_4410227).sum := by decide
  have hdescent : baseEnd_4410227 < baseStart_4410227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410237 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_4410237 : Nat := 118140960795 + 4410237 * 2 ^ 59
def prefixEnd_4410237 : Nat := 4983230072969 + 3 ^ 40 * 4410237 * 2
def baseEnd_4410237 : Nat := 2264571381242966661155195

theorem tailTrace_4410237 : CollatzResearch.WordTrace tailWord_4410237 prefixEnd_4410237 2264571381242966661155195 := by
  unfold tailWord_4410237
  simp only [CollatzResearch.WordTrace]
  refine ⟨160854558123472032358716965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107236372082314688239144643 160854558123472032358716965)
  ·
    refine ⟨30160229648151006067259431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160854558123472032358716965 30160229648151006067259431)
    ·
      refine ⟨45240344472226509100889147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30160229648151006067259431 45240344472226509100889147)
      ·
        refine ⟨67860516708339763651333721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45240344472226509100889147 67860516708339763651333721)
        ·
          refine ⟨50895387531254822738500291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67860516708339763651333721 50895387531254822738500291)
          ·
            refine ⟨76343081296882234107750437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50895387531254822738500291 76343081296882234107750437)
            ·
              refine ⟨14314327743165418895203207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76343081296882234107750437 14314327743165418895203207)
              ·
                refine ⟨21471491614748128342804811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14314327743165418895203207 21471491614748128342804811)
                ·
                  refine ⟨32207237422122192514207217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21471491614748128342804811 32207237422122192514207217)
                  ·
                    refine ⟨24155428066591644385655413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32207237422122192514207217 24155428066591644385655413)
                    ·
                      refine ⟨2264571381242966661155195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24155428066591644385655413 2264571381242966661155195)
                      ·
                        rfl

theorem cell23_4410237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_4410237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410237 prefixEnd_4410237 := by exact prefixLift 4410237
  have htrace : WordTrace (prefixWord ++ tailWord_4410237) baseStart_4410237 baseEnd_4410237 := by
    simpa [prefixWord, tailWord_4410237, baseEnd_4410237] using wordTrace_append hprefix tailTrace_4410237
  have hstable : (prefixWord ++ tailWord_4410237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410237).length < 2 ^ (prefixWord ++ tailWord_4410237).sum := by decide
  have hdescent : baseEnd_4410237 < baseStart_4410237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410287 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 6]
def baseStart_4410287 : Nat := 118140960795 + 4410287 * 2 ^ 59
def prefixEnd_4410287 : Nat := 4983230072969 + 3 ^ 40 * 4410287 * 2
def baseEnd_4410287 : Nat := 251621895030632385058885

theorem tailTrace_4410287 : CollatzResearch.WordTrace tailWord_4410287 prefixEnd_4410287 251621895030632385058885 := by
  unfold tailWord_4410287
  simp only [CollatzResearch.WordTrace]
  refine ⟨160856381773290890898037115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107237587848860593932024743 160856381773290890898037115)
  ·
    refine ⟨241284572659936336347055673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160856381773290890898037115 241284572659936336347055673)
    ·
      refine ⟨180963429494952252260291755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241284572659936336347055673 180963429494952252260291755)
      ·
        refine ⟨271445144242428378390437633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180963429494952252260291755 271445144242428378390437633)
        ·
          refine ⟨203583858181821283792828225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271445144242428378390437633 203583858181821283792828225)
          ·
            refine ⟨152687893636365962844621169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203583858181821283792828225 152687893636365962844621169)
            ·
              refine ⟨114515920227274472133465877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152687893636365962844621169 114515920227274472133465877)
              ·
                refine ⟨5367933760653490881256213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114515920227274472133465877 5367933760653490881256213)
                ·
                  refine ⟨251621895030632385058885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5367933760653490881256213 251621895030632385058885)
                  ·
                    rfl

theorem cell23_4410287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 6].length) (baseStart_4410287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410287 prefixEnd_4410287 := by exact prefixLift 4410287
  have htrace : WordTrace (prefixWord ++ tailWord_4410287) baseStart_4410287 baseEnd_4410287 := by
    simpa [prefixWord, tailWord_4410287, baseEnd_4410287] using wordTrace_append hprefix tailTrace_4410287
  have hstable : (prefixWord ++ tailWord_4410287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410287).length < 2 ^ (prefixWord ++ tailWord_4410287).sum := by decide
  have hdescent : baseEnd_4410287 < baseStart_4410287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410325 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_4410325 : Nat := 118140960795 + 4410325 * 2 ^ 59
def prefixEnd_4410325 : Nat := 4983230072969 + 3 ^ 40 * 4410325 * 2
def baseEnd_4410325 : Nat := 754872189180187438951597

theorem tailTrace_4410325 : CollatzResearch.WordTrace tailWord_4410325 prefixEnd_4410325 754872189180187438951597 := by
  unfold tailWord_4410325
  simp only [CollatzResearch.WordTrace]
  refine ⟨160857767747153223387920429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107238511831435482258613619 160857767747153223387920429)
  ·
    refine ⟨60321662905182458770470161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160857767747153223387920429 60321662905182458770470161)
    ·
      refine ⟨45241247178886844077852621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60321662905182458770470161 45241247178886844077852621)
      ·
        refine ⟨16965467692082566529194733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45241247178886844077852621 16965467692082566529194733)
        ·
          refine ⟨6362050384530962448448025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16965467692082566529194733 6362050384530962448448025)
          ·
            refine ⟨4771537788398221836336019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6362050384530962448448025 4771537788398221836336019)
            ·
              refine ⟨7157306682597332754504029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771537788398221836336019 7157306682597332754504029)
              ·
                refine ⟨2683990005973999782939011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7157306682597332754504029 2683990005973999782939011)
                ·
                  refine ⟨4025985008960999674408517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683990005973999782939011 4025985008960999674408517)
                  ·
                    refine ⟨754872189180187438951597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025985008960999674408517 754872189180187438951597)
                    ·
                      rfl

theorem cell23_4410325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_4410325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410325 prefixEnd_4410325 := by exact prefixLift 4410325
  have htrace : WordTrace (prefixWord ++ tailWord_4410325) baseStart_4410325 baseEnd_4410325 := by
    simpa [prefixWord, tailWord_4410325, baseEnd_4410325] using wordTrace_append hprefix tailTrace_4410325
  have hstable : (prefixWord ++ tailWord_4410325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410325).length < 2 ^ (prefixWord ++ tailWord_4410325).sum := by decide
  have hdescent : baseEnd_4410325 < baseStart_4410325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410391 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4410391 : Nat := 118140960795 + 4410391 * 2 ^ 59
def prefixEnd_4410391 : Nat := 4983230072969 + 3 ^ 40 * 4410391 * 2
def baseEnd_4410391 : Nat := 2264650457263759058629487

theorem tailTrace_4410391 : CollatzResearch.WordTrace tailWord_4410391 prefixEnd_4410391 2264650457263759058629487 := by
  unfold tailWord_4410391
  simp only [CollatzResearch.WordTrace]
  refine ⟨160860174964914116659823027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107240116643276077773215351 160860174964914116659823027)
  ·
    refine ⟨241290262447371174989734541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160860174964914116659823027 241290262447371174989734541)
    ·
      refine ⟨90483848417764190621150453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241290262447371174989734541 90483848417764190621150453)
      ·
        refine ⟨8482860789165392870732855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90483848417764190621150453 8482860789165392870732855)
        ·
          refine ⟨12724291183748089306099283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8482860789165392870732855 12724291183748089306099283)
          ·
            refine ⟨19086436775622133959148925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12724291183748089306099283 19086436775622133959148925)
            ·
              refine ⟨7157413790858300234680847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19086436775622133959148925 7157413790858300234680847)
              ·
                refine ⟨10736120686287450352021271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7157413790858300234680847 10736120686287450352021271)
                ·
                  refine ⟨16104181029431175528031907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10736120686287450352021271 16104181029431175528031907)
                  ·
                    refine ⟨24156271544146763292047861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16104181029431175528031907 24156271544146763292047861)
                    ·
                      refine ⟨2264650457263759058629487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24156271544146763292047861 2264650457263759058629487)
                      ·
                        rfl

theorem cell23_4410391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4410391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410391 prefixEnd_4410391 := by exact prefixLift 4410391
  have htrace : WordTrace (prefixWord ++ tailWord_4410391) baseStart_4410391 baseEnd_4410391 := by
    simpa [prefixWord, tailWord_4410391, baseEnd_4410391] using wordTrace_append hprefix tailTrace_4410391
  have hstable : (prefixWord ++ tailWord_4410391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410391).length < 2 ^ (prefixWord ++ tailWord_4410391).sum := by decide
  have hdescent : baseEnd_4410391 < baseStart_4410391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410405 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 1, 2, 2]
def baseStart_4410405 : Nat := 118140960795 + 4410405 * 2 ^ 59
def prefixEnd_4410405 : Nat := 4983230072969 + 3 ^ 40 * 4410405 * 2
def baseEnd_4410405 : Nat := 2264657645992922003854423

theorem tailTrace_4410405 : CollatzResearch.WordTrace tailWord_4410405 prefixEnd_4410405 2264657645992922003854423 := by
  unfold tailWord_4410405
  simp only [CollatzResearch.WordTrace]
  refine ⟨160860685586863397050832669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107240457057908931367221779 160860685586863397050832669)
  ·
    refine ⟨60322757095073773894062251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160860685586863397050832669 60322757095073773894062251)
    ·
      refine ⟨90484135642610660841093377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60322757095073773894062251 90484135642610660841093377)
      ·
        refine ⟨67863101731957995630820033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90484135642610660841093377 67863101731957995630820033)
        ·
          refine ⟨50897326298968496723115025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67863101731957995630820033 50897326298968496723115025)
          ·
            refine ⟨38172994724226372542336269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50897326298968496723115025 38172994724226372542336269)
            ·
              refine ⟨14314873021584889703376101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38172994724226372542336269 14314873021584889703376101)
              ·
                refine ⟨2684038691547166819383019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14314873021584889703376101 2684038691547166819383019)
                ·
                  refine ⟨4026058037320750229074529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684038691547166819383019 4026058037320750229074529)
                  ·
                    refine ⟨3019543527990562671805897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4026058037320750229074529 3019543527990562671805897)
                    ·
                      refine ⟨2264657645992922003854423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019543527990562671805897 2264657645992922003854423)
                      ·
                        rfl

theorem cell23_4410405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_4410405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410405 prefixEnd_4410405 := by exact prefixLift 4410405
  have htrace : WordTrace (prefixWord ++ tailWord_4410405) baseStart_4410405 baseEnd_4410405 := by
    simpa [prefixWord, tailWord_4410405, baseEnd_4410405] using wordTrace_append hprefix tailTrace_4410405
  have hstable : (prefixWord ++ tailWord_4410405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410405).length < 2 ^ (prefixWord ++ tailWord_4410405).sum := by decide
  have hdescent : baseEnd_4410405 < baseStart_4410405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410421 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_4410421 : Nat := 118140960795 + 4410421 * 2 ^ 59
def prefixEnd_4410421 : Nat := 4983230072969 + 3 ^ 40 * 4410421 * 2
def baseEnd_4410421 : Nat := 2264665861683393941254349

theorem tailTrace_4410421 : CollatzResearch.WordTrace tailWord_4410421 prefixEnd_4410421 2264665861683393941254349 := by
  unfold tailWord_4410421
  simp only [CollatzResearch.WordTrace]
  refine ⟨160861269154805431783415117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107240846103203621188943411 160861269154805431783415117)
  ·
    refine ⟨60322975933052036918780669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160861269154805431783415117 60322975933052036918780669)
    ·
      refine ⟨22621115974894513844542751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60322975933052036918780669 22621115974894513844542751)
      ·
        refine ⟨33931673962341770766814127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22621115974894513844542751 33931673962341770766814127)
        ·
          refine ⟨50897510943512656150221191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33931673962341770766814127 50897510943512656150221191)
          ·
            refine ⟨76346266415268984225331787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50897510943512656150221191 76346266415268984225331787)
            ·
              refine ⟨114519399622903476337997681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76346266415268984225331787 114519399622903476337997681)
              ·
                refine ⟨85889549717177607253498261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114519399622903476337997681 85889549717177607253498261)
                ·
                  refine ⟨4026072642992700340007731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85889549717177607253498261 4026072642992700340007731)
                  ·
                    refine ⟨6039108964489050510011597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026072642992700340007731 6039108964489050510011597)
                    ·
                      refine ⟨2264665861683393941254349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039108964489050510011597 2264665861683393941254349)
                      ·
                        rfl

theorem cell23_4410421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_4410421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410421 prefixEnd_4410421 := by exact prefixLift 4410421
  have htrace : WordTrace (prefixWord ++ tailWord_4410421) baseStart_4410421 baseEnd_4410421 := by
    simpa [prefixWord, tailWord_4410421, baseEnd_4410421] using wordTrace_append hprefix tailTrace_4410421
  have hstable : (prefixWord ++ tailWord_4410421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410421).length < 2 ^ (prefixWord ++ tailWord_4410421).sum := by decide
  have hdescent : baseEnd_4410421 < baseStart_4410421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410427 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_4410427 : Nat := 118140960795 + 4410427 * 2 ^ 59
def prefixEnd_4410427 : Nat := 4983230072969 + 3 ^ 40 * 4410427 * 2
def baseEnd_4410427 : Nat := 2264668942567320917779321

theorem tailTrace_4410427 : CollatzResearch.WordTrace tailWord_4410427 prefixEnd_4410427 2264668942567320917779321 := by
  unfold tailWord_4410427
  simp only [CollatzResearch.WordTrace]
  refine ⟨160861487992783694808133535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107240991995189129872089023 160861487992783694808133535)
  ·
    refine ⟨241292231989175542212200303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160861487992783694808133535 241292231989175542212200303)
    ·
      refine ⟨361938347983763313318300455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241292231989175542212200303 361938347983763313318300455)
      ·
        refine ⟨542907521975644969977450683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361938347983763313318300455 542907521975644969977450683)
        ·
          refine ⟨814361282963467454966176025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542907521975644969977450683 814361282963467454966176025)
          ·
            refine ⟨610770962222600591224632019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814361282963467454966176025 610770962222600591224632019)
            ·
              refine ⟨916156443333900886836948029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610770962222600591224632019 916156443333900886836948029)
              ·
                refine ⟨343558666250212832563855511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 916156443333900886836948029 343558666250212832563855511)
                ·
                  refine ⟨515337999375319248845783267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343558666250212832563855511 515337999375319248845783267)
                  ·
                    refine ⟨773006999062978873268674901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 515337999375319248845783267 773006999062978873268674901)
                    ·
                      refine ⟨2264668942567320917779321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 773006999062978873268674901 2264668942567320917779321)
                      ·
                        rfl

theorem cell23_4410427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_4410427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410427 prefixEnd_4410427 := by exact prefixLift 4410427
  have htrace : WordTrace (prefixWord ++ tailWord_4410427) baseStart_4410427 baseEnd_4410427 := by
    simpa [prefixWord, tailWord_4410427, baseEnd_4410427] using wordTrace_append hprefix tailTrace_4410427
  have hstable : (prefixWord ++ tailWord_4410427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410427).length < 2 ^ (prefixWord ++ tailWord_4410427).sum := by decide
  have hdescent : baseEnd_4410427 < baseStart_4410427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410472 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4410472 : Nat := 118140960795 + 4410472 * 2 ^ 59
def prefixEnd_4410472 : Nat := 4983230072969 + 3 ^ 40 * 4410472 * 2
def baseEnd_4410472 : Nat := 2264692049196773241716615

theorem tailTrace_4410472 : CollatzResearch.WordTrace tailWord_4410472 prefixEnd_4410472 2264692049196773241716615 := by
  unfold tailWord_4410472
  simp only [CollatzResearch.WordTrace]
  refine ⟨80431564638810333746760835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107242086185080444995681113 80431564638810333746760835)
  ·
    refine ⟨120647346958215500620141253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80431564638810333746760835 120647346958215500620141253)
    ·
      refine ⟨22621377554665406366276485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120647346958215500620141253 22621377554665406366276485)
      ·
        refine ⟨4241508291499763693676841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22621377554665406366276485 4241508291499763693676841)
        ·
          refine ⟨3181131218624822770257631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4241508291499763693676841 3181131218624822770257631)
          ·
            refine ⟨4771696827937234155386447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181131218624822770257631 4771696827937234155386447)
            ·
              refine ⟨7157545241905851233079671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771696827937234155386447 7157545241905851233079671)
              ·
                refine ⟨10736317862858776849619507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7157545241905851233079671 10736317862858776849619507)
                ·
                  refine ⟨16104476794288165274429261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10736317862858776849619507 16104476794288165274429261)
                  ·
                    refine ⟨6039178797858061977910973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16104476794288165274429261 6039178797858061977910973)
                    ·
                      refine ⟨2264692049196773241716615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039178797858061977910973 2264692049196773241716615)
                      ·
                        rfl

theorem cell23_4410472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4410472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410472 prefixEnd_4410472 := by exact prefixLift 4410472
  have htrace : WordTrace (prefixWord ++ tailWord_4410472) baseStart_4410472 baseEnd_4410472 := by
    simpa [prefixWord, tailWord_4410472, baseEnd_4410472] using wordTrace_append hprefix tailTrace_4410472
  have hstable : (prefixWord ++ tailWord_4410472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410472).length < 2 ^ (prefixWord ++ tailWord_4410472).sum := by decide
  have hdescent : baseEnd_4410472 < baseStart_4410472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410571 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 3]
def baseStart_4410571 : Nat := 118140960795 + 4410571 * 2 ^ 59
def prefixEnd_4410571 : Nat := 4983230072969 + 3 ^ 40 * 4410571 * 2
def baseEnd_4410571 : Nat := 2264742883781568354378659

theorem tailTrace_4410571 : CollatzResearch.WordTrace tailWord_4410571 prefixEnd_4410571 2264742883781568354378659 := by
  unfold tailWord_4410571
  simp only [CollatzResearch.WordTrace]
  refine ⟨160866740104262007401375567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107244493402841338267583711 160866740104262007401375567)
  ·
    refine ⟨241300110156393011102063351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160866740104262007401375567 241300110156393011102063351)
    ·
      refine ⟨361950165234589516653095027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241300110156393011102063351 361950165234589516653095027)
      ·
        refine ⟨542925247851884274979642541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361950165234589516653095027 542925247851884274979642541)
        ·
          refine ⟨203596967944456603117365953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542925247851884274979642541 203596967944456603117365953)
          ·
            refine ⟨152697725958342452338024465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203596967944456603117365953 152697725958342452338024465)
            ·
              refine ⟨114523294468756839253518349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152697725958342452338024465 114523294468756839253518349)
              ·
                refine ⟨42946235425783814720069381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114523294468756839253518349 42946235425783814720069381)
                ·
                  refine ⟨8052419142334465260013009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42946235425783814720069381 8052419142334465260013009)
                  ·
                    refine ⟨6039314356750848945009757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8052419142334465260013009 6039314356750848945009757)
                    ·
                      refine ⟨2264742883781568354378659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039314356750848945009757 2264742883781568354378659)
                      ·
                        rfl

theorem cell23_4410571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 3].length) (baseStart_4410571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410571 prefixEnd_4410571 := by exact prefixLift 4410571
  have htrace : WordTrace (prefixWord ++ tailWord_4410571) baseStart_4410571 baseEnd_4410571 := by
    simpa [prefixWord, tailWord_4410571, baseEnd_4410571] using wordTrace_append hprefix tailTrace_4410571
  have hstable : (prefixWord ++ tailWord_4410571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410571).length < 2 ^ (prefixWord ++ tailWord_4410571).sum := by decide
  have hdescent : baseEnd_4410571 < baseStart_4410571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410578 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_4410578 : Nat := 118140960795 + 4410578 * 2 ^ 59
def prefixEnd_4410578 : Nat := 4983230072969 + 3 ^ 40 * 4410578 * 2
def baseEnd_4410578 : Nat := 754915492715383275663709

theorem tailTrace_4410578 : CollatzResearch.WordTrace tailWord_4410578 prefixEnd_4410578 754915492715383275663709 := by
  unfold tailWord_4410578
  simp only [CollatzResearch.WordTrace]
  refine ⟨40216748853809161899220097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107244663610157765064586925 40216748853809161899220097)
  ·
    refine ⟨30162561640356871424415073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40216748853809161899220097 30162561640356871424415073)
    ·
      refine ⟨22621921230267653568311305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30162561640356871424415073 22621921230267653568311305)
      ·
        refine ⟨16966440922700740176233479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22621921230267653568311305 16966440922700740176233479)
        ·
          refine ⟨25449661384051110264350219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16966440922700740176233479 25449661384051110264350219)
          ·
            refine ⟨38174492076076665396525329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25449661384051110264350219 38174492076076665396525329)
            ·
              refine ⟨28630869057057499047393997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38174492076076665396525329 28630869057057499047393997)
              ·
                refine ⟨10736575896396562142772749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28630869057057499047393997 10736575896396562142772749)
                ·
                  refine ⟨4026215961148710803539781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10736575896396562142772749 4026215961148710803539781)
                  ·
                    refine ⟨754915492715383275663709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4026215961148710803539781 754915492715383275663709)
                    ·
                      rfl

theorem cell23_4410578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_4410578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410578 prefixEnd_4410578 := by exact prefixLift 4410578
  have htrace : WordTrace (prefixWord ++ tailWord_4410578) baseStart_4410578 baseEnd_4410578 := by
    simpa [prefixWord, tailWord_4410578, baseEnd_4410578] using wordTrace_append hprefix tailTrace_4410578
  have hstable : (prefixWord ++ tailWord_4410578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410578).length < 2 ^ (prefixWord ++ tailWord_4410578).sum := by decide
  have hdescent : baseEnd_4410578 < baseStart_4410578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410591 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 6]
def baseStart_4410591 : Nat := 118140960795 + 4410591 * 2 ^ 59
def prefixEnd_4410591 : Nat := 4983230072969 + 3 ^ 40 * 4410591 * 2
def baseEnd_4410591 : Nat := 251639239266073141792063

theorem tailTrace_4410591 : CollatzResearch.WordTrace tailWord_4410591 prefixEnd_4410591 251639239266073141792063 := by
  unfold tailWord_4410591
  simp only [CollatzResearch.WordTrace]
  refine ⟨160867469564189550817103627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107244979709459700544735751 160867469564189550817103627)
  ·
    refine ⟨241301204346284326225655441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160867469564189550817103627 241301204346284326225655441)
    ·
      refine ⟨180975903259713244669241581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241301204346284326225655441 180975903259713244669241581)
      ·
        refine ⟨67865963722392466750965593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180975903259713244669241581 67865963722392466750965593)
        ·
          refine ⟨50899472791794350063224195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67865963722392466750965593 50899472791794350063224195)
          ·
            refine ⟨76349209187691525094836293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50899472791794350063224195 76349209187691525094836293)
            ·
              refine ⟨14315476722692160955281805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76349209187691525094836293 14315476722692160955281805)
              ·
                refine ⟨5368303771009560358230677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14315476722692160955281805 5368303771009560358230677)
                ·
                  refine ⟨251639239266073141792063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5368303771009560358230677 251639239266073141792063)
                  ·
                    rfl

theorem cell23_4410591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 6].length) (baseStart_4410591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410591 prefixEnd_4410591 := by exact prefixLift 4410591
  have htrace : WordTrace (prefixWord ++ tailWord_4410591) baseStart_4410591 baseEnd_4410591 := by
    simpa [prefixWord, tailWord_4410591, baseEnd_4410591] using wordTrace_append hprefix tailTrace_4410591
  have hstable : (prefixWord ++ tailWord_4410591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410591).length < 2 ^ (prefixWord ++ tailWord_4410591).sum := by decide
  have hdescent : baseEnd_4410591 < baseStart_4410591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410605 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4410605 : Nat := 118140960795 + 4410605 * 2 ^ 59
def prefixEnd_4410605 : Nat := 4983230072969 + 3 ^ 40 * 4410605 * 2
def baseEnd_4410605 : Nat := 2264760342123821221353503

theorem tailTrace_4410605 : CollatzResearch.WordTrace tailWord_4410605 prefixEnd_4410605 2264760342123821221353503 := by
  unfold tailWord_4410605
  simp only [CollatzResearch.WordTrace]
  refine ⟨160867980186138831208113269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107245320124092554138742179 160867980186138831208113269)
  ·
    refine ⟨15081373142450515425760619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160867980186138831208113269 15081373142450515425760619)
    ·
      refine ⟨22622059713675773138640929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15081373142450515425760619 22622059713675773138640929)
      ·
        refine ⟨16966544785256829853980697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22622059713675773138640929 16966544785256829853980697)
        ·
          refine ⟨12724908588942622390485523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16966544785256829853980697 12724908588942622390485523)
          ·
            refine ⟨19087362883413933585728285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12724908588942622390485523 19087362883413933585728285)
            ·
              refine ⟨7157761081280225094648107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19087362883413933585728285 7157761081280225094648107)
              ·
                refine ⟨10736641621920337641972161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7157761081280225094648107 10736641621920337641972161)
                ·
                  refine ⟨8052481216440253231479121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10736641621920337641972161 8052481216440253231479121)
                  ·
                    refine ⟨6039360912330189923609341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8052481216440253231479121 6039360912330189923609341)
                    ·
                      refine ⟨2264760342123821221353503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039360912330189923609341 2264760342123821221353503)
                      ·
                        rfl

theorem cell23_4410605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4410605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410605 prefixEnd_4410605 := by exact prefixLift 4410605
  have htrace : WordTrace (prefixWord ++ tailWord_4410605) baseStart_4410605 baseEnd_4410605 := by
    simpa [prefixWord, tailWord_4410605, baseEnd_4410605] using wordTrace_append hprefix tailTrace_4410605
  have hstable : (prefixWord ++ tailWord_4410605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410605).length < 2 ^ (prefixWord ++ tailWord_4410605).sum := by decide
  have hdescent : baseEnd_4410605 < baseStart_4410605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410618 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_4410618 : Nat := 118140960795 + 4410618 * 2 ^ 59
def prefixEnd_4410618 : Nat := 4983230072969 + 3 ^ 40 * 4410618 * 2
def baseEnd_4410618 : Nat := 2264767017372329670490943

theorem tailTrace_4410618 : CollatzResearch.WordTrace tailWord_4410618 prefixEnd_4410618 2264767017372329670490943 := by
  unfold tailWord_4410618
  simp only [CollatzResearch.WordTrace]
  refine ⟨40217113583772933607084127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107245636223394489618891005 40217113583772933607084127)
  ·
    refine ⟨60325670375659400410626191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40217113583772933607084127 60325670375659400410626191)
    ·
      refine ⟨90488505563489100615939287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60325670375659400410626191 90488505563489100615939287)
      ·
        refine ⟨135732758345233650923908931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90488505563489100615939287 135732758345233650923908931)
        ·
          refine ⟨203599137517850476385863397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135732758345233650923908931 203599137517850476385863397)
          ·
            refine ⟨38174838284596964322349387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203599137517850476385863397 38174838284596964322349387)
            ·
              refine ⟨57262257426895446483524081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38174838284596964322349387 57262257426895446483524081)
              ·
                refine ⟨42946693070171584862643061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57262257426895446483524081 42946693070171584862643061)
                ·
                  refine ⟨4026252475328586080872787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42946693070171584862643061 4026252475328586080872787)
                  ·
                    refine ⟨6039378712992879121309181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026252475328586080872787 6039378712992879121309181)
                    ·
                      refine ⟨2264767017372329670490943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039378712992879121309181 2264767017372329670490943)
                      ·
                        rfl

theorem cell23_4410618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_4410618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410618 prefixEnd_4410618 := by exact prefixLift 4410618
  have htrace : WordTrace (prefixWord ++ tailWord_4410618) baseStart_4410618 baseEnd_4410618 := by
    simpa [prefixWord, tailWord_4410618, baseEnd_4410618] using wordTrace_append hprefix tailTrace_4410618
  have hstable : (prefixWord ++ tailWord_4410618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410618).length < 2 ^ (prefixWord ++ tailWord_4410618).sum := by decide
  have hdescent : baseEnd_4410618 < baseStart_4410618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410635 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 3]
def baseStart_4410635 : Nat := 118140960795 + 4410635 * 2 ^ 59
def prefixEnd_4410635 : Nat := 4983230072969 + 3 ^ 40 * 4410635 * 2
def baseEnd_4410635 : Nat := 2264775746543456103978365

theorem tailTrace_4410635 : CollatzResearch.WordTrace tailWord_4410635 prefixEnd_4410635 2264775746543456103978365 := by
  unfold tailWord_4410635
  simp only [CollatzResearch.WordTrace]
  refine ⟨160869074376030146331705359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107246049584020097554470239 160869074376030146331705359)
  ·
    refine ⟨241303611564045219497558039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160869074376030146331705359 241303611564045219497558039)
    ·
      refine ⟨361955417346067829246337059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241303611564045219497558039 361955417346067829246337059)
      ·
        refine ⟨542933126019101743869505589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361955417346067829246337059 542933126019101743869505589)
        ·
          refine ⟨50899980564290788487766149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 542933126019101743869505589 50899980564290788487766149)
          ·
            refine ⟨9543746355804522841456153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50899980564290788487766149 9543746355804522841456153)
            ·
              refine ⟨7157809766853392131092115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9543746355804522841456153 7157809766853392131092115)
              ·
                refine ⟨10736714650280088196638173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7157809766853392131092115 10736714650280088196638173)
                ·
                  refine ⟨4026267993855033073739315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10736714650280088196638173 4026267993855033073739315)
                  ·
                    refine ⟨6039401990782549610608973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026267993855033073739315 6039401990782549610608973)
                    ·
                      refine ⟨2264775746543456103978365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039401990782549610608973 2264775746543456103978365)
                      ·
                        rfl

theorem cell23_4410635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 3].length) (baseStart_4410635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410635 prefixEnd_4410635 := by exact prefixLift 4410635
  have htrace : WordTrace (prefixWord ++ tailWord_4410635) baseStart_4410635 baseEnd_4410635 := by
    simpa [prefixWord, tailWord_4410635, baseEnd_4410635] using wordTrace_append hprefix tailTrace_4410635
  have hstable : (prefixWord ++ tailWord_4410635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410635).length < 2 ^ (prefixWord ++ tailWord_4410635).sum := by decide
  have hdescent : baseEnd_4410635 < baseStart_4410635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410655 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 1, 5]
def baseStart_4410655 : Nat := 118140960795 + 4410655 * 2 ^ 59
def prefixEnd_4410655 : Nat := 4983230072969 + 3 ^ 40 * 4410655 * 2
def baseEnd_4410655 : Nat := 754928672052182008576091

theorem tailTrace_4410655 : CollatzResearch.WordTrace tailWord_4410655 prefixEnd_4410655 754928672052182008576091 := by
  unfold tailWord_4410655
  simp only [CollatzResearch.WordTrace]
  refine ⟨160869803835957689747433419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107246535890638459831622279 160869803835957689747433419)
  ·
    refine ⟨241304705753936534621150129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160869803835957689747433419 241304705753936534621150129)
    ·
      refine ⟨180978529315452400965862597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241304705753936534621150129 180978529315452400965862597)
      ·
        refine ⟨33933474246647325181099237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180978529315452400965862597 33933474246647325181099237)
        ·
          refine ⟨6362526421246373471456107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33933474246647325181099237 6362526421246373471456107)
          ·
            refine ⟨9543789631869560207184161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6362526421246373471456107 9543789631869560207184161)
            ·
              refine ⟨7157842223902170155388121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9543789631869560207184161 7157842223902170155388121)
              ·
                refine ⟨5368381667926627616541091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7157842223902170155388121 5368381667926627616541091)
                ·
                  refine ⟨8052572501889941424811637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5368381667926627616541091 8052572501889941424811637)
                  ·
                    refine ⟨754928672052182008576091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8052572501889941424811637 754928672052182008576091)
                    ·
                      rfl

theorem cell23_4410655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_4410655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410655 prefixEnd_4410655 := by exact prefixLift 4410655
  have htrace : WordTrace (prefixWord ++ tailWord_4410655) baseStart_4410655 baseEnd_4410655 := by
    simpa [prefixWord, tailWord_4410655, baseEnd_4410655] using wordTrace_append hprefix tailTrace_4410655
  have hstable : (prefixWord ++ tailWord_4410655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410655).length < 2 ^ (prefixWord ++ tailWord_4410655).sum := by decide
  have hdescent : baseEnd_4410655 < baseStart_4410655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410671 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_4410671 : Nat := 118140960795 + 4410671 * 2 ^ 59
def prefixEnd_4410671 : Nat := 4983230072969 + 3 ^ 40 * 4410671 * 2
def baseEnd_4410671 : Nat := 2264794231847017963128199

theorem tailTrace_4410671 : CollatzResearch.WordTrace tailWord_4410671 prefixEnd_4410671 2264794231847017963128199 := by
  unfold tailWord_4410671
  simp only [CollatzResearch.WordTrace]
  refine ⟨160870387403899724480015867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107246924935933149653343911 160870387403899724480015867)
  ·
    refine ⟨241305581105849586720023801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160870387403899724480015867 241305581105849586720023801)
    ·
      refine ⟨180979185829387190040017851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241305581105849586720023801 180979185829387190040017851)
      ·
        refine ⟨271468778744080785060026777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180979185829387190040017851 271468778744080785060026777)
        ·
          refine ⟨203601584058060588795020083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271468778744080785060026777 203601584058060588795020083)
          ·
            refine ⟨305402376087090883192530125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203601584058060588795020083 305402376087090883192530125)
            ·
              refine ⟨114525891032659081197198797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305402376087090883192530125 114525891032659081197198797)
              ·
                refine ⟨42947209137247155448949549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114525891032659081197198797 42947209137247155448949549)
                ·
                  refine ⟨16105203426467683293356081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42947209137247155448949549 16105203426467683293356081)
                  ·
                    refine ⟨12078902569850762470017061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16105203426467683293356081 12078902569850762470017061)
                    ·
                      refine ⟨2264794231847017963128199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12078902569850762470017061 2264794231847017963128199)
                      ·
                        rfl

theorem cell23_4410671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_4410671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410671 prefixEnd_4410671 := by exact prefixLift 4410671
  have htrace : WordTrace (prefixWord ++ tailWord_4410671) baseStart_4410671 baseEnd_4410671 := by
    simpa [prefixWord, tailWord_4410671, baseEnd_4410671] using wordTrace_append hprefix tailTrace_4410671
  have hstable : (prefixWord ++ tailWord_4410671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410671).length < 2 ^ (prefixWord ++ tailWord_4410671).sum := by decide
  have hdescent : baseEnd_4410671 < baseStart_4410671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410721 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_4410721 : Nat := 118140960795 + 4410721 * 2 ^ 59
def prefixEnd_4410721 : Nat := 4983230072969 + 3 ^ 40 * 4410721 * 2
def baseEnd_4410721 : Nat := 2264819905879742767502969

theorem tailTrace_4410721 : CollatzResearch.WordTrace tailWord_4410721 prefixEnd_4410721 2264819905879742767502969 := by
  unfold tailWord_4410721
  simp only [CollatzResearch.WordTrace]
  refine ⟨160872211053718583019336017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107248140702479055346224011 160872211053718583019336017)
  ·
    refine ⟨120654158290288937264502013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160872211053718583019336017 120654158290288937264502013)
    ·
      refine ⟨45245309358858351474188255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120654158290288937264502013 45245309358858351474188255)
      ·
        refine ⟨67867964038287527211282383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45245309358858351474188255 67867964038287527211282383)
        ·
          refine ⟨101801946057431290816923575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67867964038287527211282383 101801946057431290816923575)
          ·
            refine ⟨152702919086146936225385363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101801946057431290816923575 152702919086146936225385363)
            ·
              refine ⟨229054378629220404338078045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152702919086146936225385363 229054378629220404338078045)
              ·
                refine ⟨85895391985957651626779267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229054378629220404338078045 85895391985957651626779267)
                ·
                  refine ⟨128843087978936477440168901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85895391985957651626779267 128843087978936477440168901)
                  ·
                    refine ⟨24158078996050589520031669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128843087978936477440168901 24158078996050589520031669)
                    ·
                      refine ⟨2264819905879742767502969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24158078996050589520031669 2264819905879742767502969)
                      ·
                        rfl

theorem cell23_4410721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_4410721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410721 prefixEnd_4410721 := by exact prefixLift 4410721
  have htrace : WordTrace (prefixWord ++ tailWord_4410721) baseStart_4410721 baseEnd_4410721 := by
    simpa [prefixWord, tailWord_4410721, baseEnd_4410721] using wordTrace_append hprefix tailTrace_4410721
  have hstable : (prefixWord ++ tailWord_4410721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410721).length < 2 ^ (prefixWord ++ tailWord_4410721).sum := by decide
  have hdescent : baseEnd_4410721 < baseStart_4410721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410731 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4]
def baseStart_4410731 : Nat := 118140960795 + 4410731 * 2 ^ 59
def prefixEnd_4410731 : Nat := 4983230072969 + 3 ^ 40 * 4410731 * 2
def baseEnd_4410731 : Nat := 2264825040686287728377923

theorem tailTrace_4410731 : CollatzResearch.WordTrace tailWord_4410731 prefixEnd_4410731 2264825040686287728377923 := by
  unfold tailWord_4410731
  simp only [CollatzResearch.WordTrace]
  refine ⟨160872575783682354727200047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107248383855788236484800031 160872575783682354727200047)
  ·
    refine ⟨241308863675523532090800071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160872575783682354727200047 241308863675523532090800071)
    ·
      refine ⟨361963295513285298136200107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241308863675523532090800071 361963295513285298136200107)
      ·
        refine ⟨542944943269927947204300161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361963295513285298136200107 542944943269927947204300161)
        ·
          refine ⟨407208707452445960403225121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542944943269927947204300161 407208707452445960403225121)
          ·
            refine ⟨305406530589334470302418841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407208707452445960403225121 305406530589334470302418841)
            ·
              refine ⟨229054897942000852726814131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305406530589334470302418841 229054897942000852726814131)
              ·
                refine ⟨343582346913001279090221197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229054897942000852726814131 343582346913001279090221197)
                ·
                  refine ⟨128843380092375479658832949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343582346913001279090221197 128843380092375479658832949)
                  ·
                    refine ⟨12079066883660201218015589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128843380092375479658832949 12079066883660201218015589)
                    ·
                      refine ⟨2264825040686287728377923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12079066883660201218015589 2264825040686287728377923)
                      ·
                        rfl

theorem cell23_4410731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_4410731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410731 prefixEnd_4410731 := by exact prefixLift 4410731
  have htrace : WordTrace (prefixWord ++ tailWord_4410731) baseStart_4410731 baseEnd_4410731 := by
    simpa [prefixWord, tailWord_4410731, baseEnd_4410731] using wordTrace_append hprefix tailTrace_4410731
  have hstable : (prefixWord ++ tailWord_4410731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410731).length < 2 ^ (prefixWord ++ tailWord_4410731).sum := by decide
  have hdescent : baseEnd_4410731 < baseStart_4410731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410778 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4410778 : Nat := 118140960795 + 4410778 * 2 ^ 59
def prefixEnd_4410778 : Nat := 4983230072969 + 3 ^ 40 * 4410778 * 2
def baseEnd_4410778 : Nat := 2264849174277049044490207

theorem tailTrace_4410778 : CollatzResearch.WordTrace tailWord_4410778 prefixEnd_4410778 2264849174277049044490207 := by
  unfold tailWord_4410778
  simp only [CollatzResearch.WordTrace]
  refine ⟨40218572503628020438540247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107249526676341387836107325 40218572503628020438540247)
  ·
    refine ⟨60327858755442030657810371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40218572503628020438540247 60327858755442030657810371)
    ·
      refine ⟨90491788133163045986715557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60327858755442030657810371 90491788133163045986715557)
      ·
        refine ⟨16967210274968071122509167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90491788133163045986715557 16967210274968071122509167)
        ·
          refine ⟨25450815412452106683763751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16967210274968071122509167 25450815412452106683763751)
          ·
            refine ⟨38176223118678160025645627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25450815412452106683763751 38176223118678160025645627)
            ·
              refine ⟨57264334678017240038468441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38176223118678160025645627 57264334678017240038468441)
              ·
                refine ⟨42948251008512930028851331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57264334678017240038468441 42948251008512930028851331)
                ·
                  refine ⟨64422376512769395043276997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42948251008512930028851331 64422376512769395043276997)
                  ·
                    refine ⟨12079195596144261570614437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64422376512769395043276997 12079195596144261570614437)
                    ·
                      refine ⟨2264849174277049044490207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12079195596144261570614437 2264849174277049044490207)
                      ·
                        rfl

theorem cell23_4410778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4410778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410778 prefixEnd_4410778 := by exact prefixLift 4410778
  have htrace : WordTrace (prefixWord ++ tailWord_4410778) baseStart_4410778 baseEnd_4410778 := by
    simpa [prefixWord, tailWord_4410778, baseEnd_4410778] using wordTrace_append hprefix tailTrace_4410778
  have hstable : (prefixWord ++ tailWord_4410778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410778).length < 2 ^ (prefixWord ++ tailWord_4410778).sum := by decide
  have hdescent : baseEnd_4410778 < baseStart_4410778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410786 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_4410786 : Nat := 118140960795 + 4410786 * 2 ^ 59
def prefixEnd_4410786 : Nat := 4983230072969 + 3 ^ 40 * 4410786 * 2
def baseEnd_4410786 : Nat := 2264853282122285013190171

theorem tailTrace_4410786 : CollatzResearch.WordTrace tailWord_4410786 prefixEnd_4410786 2264853282122285013190171 := by
  unfold tailWord_4410786
  simp only [CollatzResearch.WordTrace]
  refine ⟨40218645449620774780113053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107249721198988732746968141 40218645449620774780113053)
  ·
    refine ⟨15081992043607790542542395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40218645449620774780113053 15081992043607790542542395)
    ·
      refine ⟨22622988065411685813813593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15081992043607790542542395 22622988065411685813813593)
      ·
        refine ⟨16967241049058764360360195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22622988065411685813813593 16967241049058764360360195)
        ·
          refine ⟨25450861573588146540540293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16967241049058764360360195 25450861573588146540540293)
          ·
            refine ⟨4772036545047777476351305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25450861573588146540540293 4772036545047777476351305)
            ·
              refine ⟨3579027408785833107263479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4772036545047777476351305 3579027408785833107263479)
              ·
                refine ⟨5368541113178749660895219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3579027408785833107263479 5368541113178749660895219)
                ·
                  refine ⟨8052811669768124491342829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5368541113178749660895219 8052811669768124491342829)
                  ·
                    refine ⟨3019804376163046684253561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8052811669768124491342829 3019804376163046684253561)
                    ·
                      refine ⟨2264853282122285013190171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019804376163046684253561 2264853282122285013190171)
                      ·
                        rfl

theorem cell23_4410786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_4410786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410786 prefixEnd_4410786 := by exact prefixLift 4410786
  have htrace : WordTrace (prefixWord ++ tailWord_4410786) baseStart_4410786 baseEnd_4410786 := by
    simpa [prefixWord, tailWord_4410786, baseEnd_4410786] using wordTrace_append hprefix tailTrace_4410786
  have hstable : (prefixWord ++ tailWord_4410786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410786).length < 2 ^ (prefixWord ++ tailWord_4410786).sum := by decide
  have hdescent : baseEnd_4410786 < baseStart_4410786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410805 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 7]
def baseStart_4410805 : Nat := 118140960795 + 4410805 * 2 ^ 59
def prefixEnd_4410805 : Nat := 4983230072969 + 3 ^ 40 * 4410805 * 2
def baseEnd_4410805 : Nat := 251651448694968937650287

theorem tailTrace_4410805 : CollatzResearch.WordTrace tailWord_4410805 prefixEnd_4410805 251651448694968937650287 := by
  unfold tailWord_4410805
  simp only [CollatzResearch.WordTrace]
  refine ⟨160875274785414265365393869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107250183190276176910262579 160875274785414265365393869)
  ·
    refine ⟨60328228044530349512022701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160875274785414265365393869 60328228044530349512022701)
    ·
      refine ⟨22623085516698881067008513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60328228044530349512022701 22623085516698881067008513)
      ·
        refine ⟨16967314137524160800256385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22623085516698881067008513 16967314137524160800256385)
        ·
          refine ⟨12725485603143120600192289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16967314137524160800256385 12725485603143120600192289)
          ·
            refine ⟨9544114202357340450144217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12725485603143120600192289 9544114202357340450144217)
            ·
              refine ⟨7158085651768005337608163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9544114202357340450144217 7158085651768005337608163)
              ·
                refine ⟨10737128477652008006412245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7158085651768005337608163 10737128477652008006412245)
                ·
                  refine ⟨251651448694968937650287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10737128477652008006412245 251651448694968937650287)
                  ·
                    rfl

theorem cell23_4410805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_4410805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410805 prefixEnd_4410805 := by exact prefixLift 4410805
  have htrace : WordTrace (prefixWord ++ tailWord_4410805) baseStart_4410805 baseEnd_4410805 := by
    simpa [prefixWord, tailWord_4410805, baseEnd_4410805] using wordTrace_append hprefix tailTrace_4410805
  have hstable : (prefixWord ++ tailWord_4410805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410805).length < 2 ^ (prefixWord ++ tailWord_4410805).sum := by decide
  have hdescent : baseEnd_4410805 < baseStart_4410805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410855 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4410855 : Nat := 118140960795 + 4410855 * 2 ^ 59
def prefixEnd_4410855 : Nat := 4983230072969 + 3 ^ 40 * 4410855 * 2
def baseEnd_4410855 : Nat := 2264888712287445243227353

theorem tailTrace_4410855 : CollatzResearch.WordTrace tailWord_4410855 prefixEnd_4410855 2264888712287445243227353 := by
  unfold tailWord_4410855
  simp only [CollatzResearch.WordTrace]
  refine ⟨160877098435233123904714019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107251398956822082603142679 160877098435233123904714019)
  ·
    refine ⟨241315647652849685857071029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160877098435233123904714019 241315647652849685857071029)
    ·
      refine ⟨22623341967454658049100409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241315647652849685857071029 22623341967454658049100409)
      ·
        refine ⟨16967506475590993536825307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22623341967454658049100409 16967506475590993536825307)
        ·
          refine ⟨25451259713386490305237961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16967506475590993536825307 25451259713386490305237961)
          ·
            refine ⟨19088444785039867728928471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25451259713386490305237961 19088444785039867728928471)
            ·
              refine ⟨28632667177559801593392707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19088444785039867728928471 28632667177559801593392707)
              ·
                refine ⟨42949000766339702390089061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28632667177559801593392707 42949000766339702390089061)
                ·
                  refine ⟨8052937643688694198141699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42949000766339702390089061 8052937643688694198141699)
                  ·
                    refine ⟨12079406465533041297212549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8052937643688694198141699 12079406465533041297212549)
                    ·
                      refine ⟨2264888712287445243227353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12079406465533041297212549 2264888712287445243227353)
                      ·
                        rfl

theorem cell23_4410855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4410855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410855 prefixEnd_4410855 := by exact prefixLift 4410855
  have htrace : WordTrace (prefixWord ++ tailWord_4410855) baseStart_4410855 baseEnd_4410855 := by
    simpa [prefixWord, tailWord_4410855, baseEnd_4410855] using wordTrace_append hprefix tailTrace_4410855
  have hstable : (prefixWord ++ tailWord_4410855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410855).length < 2 ^ (prefixWord ++ tailWord_4410855).sum := by decide
  have hdescent : baseEnd_4410855 < baseStart_4410855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410912 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 6]
def baseStart_4410912 : Nat := 118140960795 + 4410912 * 2 ^ 59
def prefixEnd_4410912 : Nat := 4983230072969 + 3 ^ 40 * 4410912 * 2
def baseEnd_4410912 : Nat := 251657553409416835579399

theorem tailTrace_4410912 : CollatzResearch.WordTrace tailWord_4410912 prefixEnd_4410912 251657553409416835579399 := by
  unfold tailWord_4410912
  simp only [CollatzResearch.WordTrace]
  refine ⟨80439588698013311319769495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107252784930684415093025993 80439588698013311319769495)
  ·
    refine ⟨120659383047019966979654243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80439588698013311319769495 120659383047019966979654243)
    ·
      refine ⟨180989074570529950469481365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120659383047019966979654243 180989074570529950469481365)
      ·
        refine ⟨8483862870493591428256939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180989074570529950469481365 8483862870493591428256939)
        ·
          refine ⟨12725794305740387142385409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8483862870493591428256939 12725794305740387142385409)
          ·
            refine ⟨9544345729305290356789057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12725794305740387142385409 9544345729305290356789057)
            ·
              refine ⟨7158259296978967767591793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9544345729305290356789057 7158259296978967767591793)
              ·
                refine ⟨5368694472734225825693845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7158259296978967767591793 5368694472734225825693845)
                ·
                  refine ⟨251657553409416835579399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5368694472734225825693845 251657553409416835579399)
                  ·
                    rfl

theorem cell23_4410912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_4410912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410912 prefixEnd_4410912 := by exact prefixLift 4410912
  have htrace : WordTrace (prefixWord ++ tailWord_4410912) baseStart_4410912 baseEnd_4410912 := by
    simpa [prefixWord, tailWord_4410912, baseEnd_4410912] using wordTrace_append hprefix tailTrace_4410912
  have hstable : (prefixWord ++ tailWord_4410912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410912).length < 2 ^ (prefixWord ++ tailWord_4410912).sum := by decide
  have hdescent : baseEnd_4410912 < baseStart_4410912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410955 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 4, 4]
def baseStart_4410955 : Nat := 118140960795 + 4410955 * 2 ^ 59
def prefixEnd_4410955 : Nat := 4983230072969 + 3 ^ 40 * 4410955 * 2
def baseEnd_4410955 : Nat := 754980020117631617325631

theorem tailTrace_4410955 : CollatzResearch.WordTrace tailWord_4410955 prefixEnd_4410955 754980020117631617325631 := by
  unfold tailWord_4410955
  simp only [CollatzResearch.WordTrace]
  refine ⟨160880745734870840983354319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107253830489913893988902879 160880745734870840983354319)
  ·
    refine ⟨241321118602306261475031479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160880745734870840983354319 241321118602306261475031479)
    ·
      refine ⟨361981677903459392212547219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241321118602306261475031479 361981677903459392212547219)
      ·
        refine ⟨542972516855189088318820829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361981677903459392212547219 542972516855189088318820829)
        ·
          refine ⟨203614693820695908119557811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542972516855189088318820829 203614693820695908119557811)
          ·
            refine ⟨305422040731043862179336717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203614693820695908119557811 305422040731043862179336717)
            ·
              refine ⟨114533265274141448317251269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305422040731043862179336717 114533265274141448317251269)
              ·
                refine ⟨21474987238901521559484613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114533265274141448317251269 21474987238901521559484613)
                ·
                  refine ⟨4026560107294035292403365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21474987238901521559484613 4026560107294035292403365)
                  ·
                    refine ⟨754980020117631617325631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4026560107294035292403365 754980020117631617325631)
                    ·
                      rfl

theorem cell23_4410955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 4].length) (baseStart_4410955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410955 prefixEnd_4410955 := by exact prefixLift 4410955
  have htrace : WordTrace (prefixWord ++ tailWord_4410955) baseStart_4410955 baseEnd_4410955 := by
    simpa [prefixWord, tailWord_4410955, baseEnd_4410955] using wordTrace_append hprefix tailTrace_4410955
  have hstable : (prefixWord ++ tailWord_4410955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410955).length < 2 ^ (prefixWord ++ tailWord_4410955).sum := by decide
  have hdescent : baseEnd_4410955 < baseStart_4410955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410956 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 1, 1, 3]
def baseStart_4410956 : Nat := 118140960795 + 4410956 * 2 ^ 59
def prefixEnd_4410956 : Nat := 4983230072969 + 3 ^ 40 * 4410956 * 2
def baseEnd_4410956 : Nat := 2264940573833549348064389

theorem tailTrace_4410956 : CollatzResearch.WordTrace tailWord_4410956 prefixEnd_4410956 2264940573833549348064389 := by
  unfold tailWord_4410956
  simp only [CollatzResearch.WordTrace]
  refine ⟨80440391103933609077070361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107253854805244812102760481 80440391103933609077070361)
  ·
    refine ⟨60330293327950206807802771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80440391103933609077070361 60330293327950206807802771)
    ·
      refine ⟨90495439991925310211704157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60330293327950206807802771 90495439991925310211704157)
      ·
        refine ⟨33935789996971991329389059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90495439991925310211704157 33935789996971991329389059)
        ·
          refine ⟨50903684995457986994083589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33935789996971991329389059 50903684995457986994083589)
          ·
            refine ⟨9544440936648372561390673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50903684995457986994083589 9544440936648372561390673)
            ·
              refine ⟨7158330702486279421043005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9544440936648372561390673 7158330702486279421043005)
              ·
                refine ⟨2684374013432354782891127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7158330702486279421043005 2684374013432354782891127)
                ·
                  refine ⟨4026561020148532174336691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684374013432354782891127 4026561020148532174336691)
                  ·
                    refine ⟨6039841530222798261505037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026561020148532174336691 6039841530222798261505037)
                    ·
                      refine ⟨2264940573833549348064389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039841530222798261505037 2264940573833549348064389)
                      ·
                        rfl

theorem cell23_4410956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_4410956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410956 prefixEnd_4410956 := by exact prefixLift 4410956
  have htrace : WordTrace (prefixWord ++ tailWord_4410956) baseStart_4410956 baseEnd_4410956 := by
    simpa [prefixWord, tailWord_4410956, baseEnd_4410956] using wordTrace_append hprefix tailTrace_4410956
  have hstable : (prefixWord ++ tailWord_4410956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410956).length < 2 ^ (prefixWord ++ tailWord_4410956).sum := by decide
  have hdescent : baseEnd_4410956 < baseStart_4410956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410965 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4410965 : Nat := 118140960795 + 4410965 * 2 ^ 59
def prefixEnd_4410965 : Nat := 4983230072969 + 3 ^ 40 * 4410965 * 2
def baseEnd_4410965 : Nat := 2264945195159439812851847

theorem tailTrace_4410965 : CollatzResearch.WordTrace tailWord_4410965 prefixEnd_4410965 2264945195159439812851847 := by
  unfold tailWord_4410965
  simp only [CollatzResearch.WordTrace]
  refine ⟨160881110464834612691218349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107254073643223075127478899 160881110464834612691218349)
  ·
    refine ⟨60330416424312979759206881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160881110464834612691218349 60330416424312979759206881)
    ·
      refine ⟨45247812318234734819405161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60330416424312979759206881 45247812318234734819405161)
      ·
        refine ⟨33935859238676051114553871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45247812318234734819405161 33935859238676051114553871)
        ·
          refine ⟨50903788858014076671830807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33935859238676051114553871 50903788858014076671830807)
          ·
            refine ⟨76355683287021115007746211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50903788858014076671830807 76355683287021115007746211)
            ·
              refine ⟨114533524930531672511619317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76355683287021115007746211 114533524930531672511619317)
              ·
                refine ⟨10737517962237344297964311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114533524930531672511619317 10737517962237344297964311)
                ·
                  refine ⟨16106276943356016446946467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10737517962237344297964311 16106276943356016446946467)
                  ·
                    refine ⟨24159415415034024670419701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16106276943356016446946467 24159415415034024670419701)
                    ·
                      refine ⟨2264945195159439812851847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24159415415034024670419701 2264945195159439812851847)
                      ·
                        rfl

theorem cell23_4410965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4410965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410965 prefixEnd_4410965 := by exact prefixLift 4410965
  have htrace : WordTrace (prefixWord ++ tailWord_4410965) baseStart_4410965 baseEnd_4410965 := by
    simpa [prefixWord, tailWord_4410965, baseEnd_4410965] using wordTrace_append hprefix tailTrace_4410965
  have hstable : (prefixWord ++ tailWord_4410965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410965).length < 2 ^ (prefixWord ++ tailWord_4410965).sum := by decide
  have hdescent : baseEnd_4410965 < baseStart_4410965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410973 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4410973 : Nat := 118140960795 + 4410973 * 2 ^ 59
def prefixEnd_4410973 : Nat := 4983230072969 + 3 ^ 40 * 4410973 * 2
def baseEnd_4410973 : Nat := 2264949303004675781551811

theorem tailTrace_4410973 : CollatzResearch.WordTrace tailWord_4410973 prefixEnd_4410973 2264949303004675781551811 := by
  unfold tailWord_4410973
  simp only [CollatzResearch.WordTrace]
  refine ⟨160881402248805630057509573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107254268165870420038339715 160881402248805630057509573)
  ·
    refine ⟨30165262921651055635783045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160881402248805630057509573 30165262921651055635783045)
    ·
      refine ⟨5655986797809572931709321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30165262921651055635783045 5655986797809572931709321)
      ·
        refine ⟨4241990098357179698781991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5655986797809572931709321 4241990098357179698781991)
        ·
          refine ⟨6362985147535769548172987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241990098357179698781991 6362985147535769548172987)
          ·
            refine ⟨9544477721303654322259481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6362985147535769548172987 9544477721303654322259481)
            ·
              refine ⟨7158358290977740741694611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9544477721303654322259481 7158358290977740741694611)
              ·
                refine ⟨10737537436466611112541917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7158358290977740741694611 10737537436466611112541917)
                ·
                  refine ⟨4026576538674979167203219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10737537436466611112541917 4026576538674979167203219)
                  ·
                    refine ⟨6039864808012468750804829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026576538674979167203219 6039864808012468750804829)
                    ·
                      refine ⟨2264949303004675781551811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6039864808012468750804829 2264949303004675781551811)
                      ·
                        rfl

theorem cell23_4410973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4410973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410973 prefixEnd_4410973 := by exact prefixLift 4410973
  have htrace : WordTrace (prefixWord ++ tailWord_4410973) baseStart_4410973 baseEnd_4410973 := by
    simpa [prefixWord, tailWord_4410973, baseEnd_4410973] using wordTrace_append hprefix tailTrace_4410973
  have hstable : (prefixWord ++ tailWord_4410973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410973).length < 2 ^ (prefixWord ++ tailWord_4410973).sum := by decide
  have hdescent : baseEnd_4410973 < baseStart_4410973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410979 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 3, 2, 2]
def baseStart_4410979 : Nat := 118140960795 + 4410979 * 2 ^ 59
def prefixEnd_4410979 : Nat := 4983230072969 + 3 ^ 40 * 4410979 * 2
def baseEnd_4410979 : Nat := 2264952383888602758076783

theorem tailTrace_4410979 : CollatzResearch.WordTrace tailWord_4410979 prefixEnd_4410979 2264952383888602758076783 := by
  unfold tailWord_4410979
  simp only [CollatzResearch.WordTrace]
  refine ⟨160881621086783893082227991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107254414057855928721485327 160881621086783893082227991)
  ·
    refine ⟨241322431630175839623341987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160881621086783893082227991 241322431630175839623341987)
    ·
      refine ⟨361983647445263759435012981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241322431630175839623341987 361983647445263759435012981)
      ·
        refine ⟨33935966947993477447032467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 361983647445263759435012981 33935966947993477447032467)
        ·
          refine ⟨50903950421990216170548701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33935966947993477447032467 50903950421990216170548701)
          ·
            refine ⟨19088981408246331063955763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50903950421990216170548701 19088981408246331063955763)
            ·
              refine ⟨28633472112369496595933645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19088981408246331063955763 28633472112369496595933645)
              ·
                refine ⟨10737552042138561223475117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28633472112369496595933645 10737552042138561223475117)
                ·
                  refine ⟨4026582015801960458803169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10737552042138561223475117 4026582015801960458803169)
                  ·
                    refine ⟨3019936511851470344102377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4026582015801960458803169 3019936511851470344102377)
                    ·
                      refine ⟨2264952383888602758076783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019936511851470344102377 2264952383888602758076783)
                      ·
                        rfl

theorem cell23_4410979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_4410979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410979 prefixEnd_4410979 := by exact prefixLift 4410979
  have htrace : WordTrace (prefixWord ++ tailWord_4410979) baseStart_4410979 baseEnd_4410979 := by
    simpa [prefixWord, tailWord_4410979, baseEnd_4410979] using wordTrace_append hprefix tailTrace_4410979
  have hstable : (prefixWord ++ tailWord_4410979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410979).length < 2 ^ (prefixWord ++ tailWord_4410979).sum := by decide
  have hdescent : baseEnd_4410979 < baseStart_4410979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410989 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_4410989 : Nat := 118140960795 + 4410989 * 2 ^ 59
def prefixEnd_4410989 : Nat := 4983230072969 + 3 ^ 40 * 4410989 * 2
def baseEnd_4410989 : Nat := 754985839565049239650579

theorem tailTrace_4410989 : CollatzResearch.WordTrace tailWord_4410989 prefixEnd_4410989 754985839565049239650579 := by
  unfold tailWord_4410989
  simp only [CollatzResearch.WordTrace]
  refine ⟨160881985816747664790092021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107254657211165109860061347 160881985816747664790092021)
  ·
    refine ⟨15082686170320093574071127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160881985816747664790092021 15082686170320093574071127)
    ·
      refine ⟨22624029255480140361106691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15082686170320093574071127 22624029255480140361106691)
      ·
        refine ⟨33936043883220210541660037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22624029255480140361106691 33936043883220210541660037)
        ·
          refine ⟨6363008228103789476561257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33936043883220210541660037 6363008228103789476561257)
          ·
            refine ⟨4772256171077842107420943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6363008228103789476561257 4772256171077842107420943)
            ·
              refine ⟨7158384256616763161131415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4772256171077842107420943 7158384256616763161131415)
              ·
                refine ⟨10737576384925144741697123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7158384256616763161131415 10737576384925144741697123)
                ·
                  refine ⟨16106364577387717112545685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10737576384925144741697123 16106364577387717112545685)
                  ·
                    refine ⟨754985839565049239650579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16106364577387717112545685 754985839565049239650579)
                    ·
                      rfl

theorem cell23_4410989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_4410989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410989 prefixEnd_4410989 := by exact prefixLift 4410989
  have htrace : WordTrace (prefixWord ++ tailWord_4410989) baseStart_4410989 baseEnd_4410989 := by
    simpa [prefixWord, tailWord_4410989, baseEnd_4410989] using wordTrace_append hprefix tailTrace_4410989
  have hstable : (prefixWord ++ tailWord_4410989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410989).length < 2 ^ (prefixWord ++ tailWord_4410989).sum := by decide
  have hdescent : baseEnd_4410989 < baseStart_4410989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
