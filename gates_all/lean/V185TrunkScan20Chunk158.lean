import V185TrunkScan20Chunk157

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_961727 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 2]
def baseStart_961727 : Nat := 118140960795 + 961727 * 2 ^ 59
def prefixEnd_961727 : Nat := 4983230072969 + 3 ^ 40 * 961727 * 2
def baseEnd_961727 : Nat := 438958408361479086568537

theorem tailTrace_961727 : CollatzResearch.WordTrace tailWord_961727 prefixEnd_961727 438958408361479086568537 := by
  unfold tailWord_961727
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077065386834803740107435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23384710257889869160071623 35077065386834803740107435)
  ·
    refine ⟨52615598080252205610161153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35077065386834803740107435 52615598080252205610161153)
    ·
      refine ⟨39461698560189154207620865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52615598080252205610161153 39461698560189154207620865)
      ·
        refine ⟨29596273920141865655715649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39461698560189154207620865 29596273920141865655715649)
        ·
          refine ⟨22197205440106399241786737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29596273920141865655715649 22197205440106399241786737)
          ·
            refine ⟨16647904080079799431340053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22197205440106399241786737 16647904080079799431340053)
            ·
              refine ⟨780370503753740598344065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16647904080079799431340053 780370503753740598344065)
              ·
                refine ⟨585277877815305448758049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780370503753740598344065 585277877815305448758049)
                ·
                  refine ⟨438958408361479086568537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585277877815305448758049 438958408361479086568537)
                  ·
                    rfl

theorem cell20_961727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 2].length) (baseStart_961727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961727 prefixEnd_961727 := by exact prefixLift 961727
  have htrace : WordTrace (prefixWord ++ tailWord_961727) baseStart_961727 baseEnd_961727 := by
    simpa [prefixWord, tailWord_961727, baseEnd_961727] using wordTrace_append hprefix tailTrace_961727
  have hstable : (prefixWord ++ tailWord_961727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961727).length < 2 ^ (prefixWord ++ tailWord_961727).sum := by decide
  have hdescent : baseEnd_961727 < baseStart_961727 := by decide
  rcases family_descends (prefixWord ++ tailWord_961727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961730 : List Nat := [3, 5, 1, 1, 2, 2, 1, 5]
def baseStart_961730 : Nat := 118140960795 + 961730 * 2 ^ 59
def prefixEnd_961730 : Nat := 4983230072969 + 3 ^ 40 * 961730 * 2
def baseEnd_961730 : Nat := 146319925881074803156175

theorem tailTrace_961730 : CollatzResearch.WordTrace tailWord_961730 prefixEnd_961730 146319925881074803156175 := by
  unfold tailWord_961730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769293701455983813116661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23384783203882623501644429 8769293701455983813116661)
  ·
    refine ⟨822121284511498482479687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8769293701455983813116661 822121284511498482479687)
    ·
      refine ⟨1233181926767247723719531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822121284511498482479687 1233181926767247723719531)
      ·
        refine ⟨1849772890150871585579297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233181926767247723719531 1849772890150871585579297)
        ·
          refine ⟨1387329667613153689184473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849772890150871585579297 1387329667613153689184473)
          ·
            refine ⟨1040497250709865266888355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1387329667613153689184473 1040497250709865266888355)
            ·
              refine ⟨1560745876064797900332533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040497250709865266888355 1560745876064797900332533)
              ·
                refine ⟨146319925881074803156175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1560745876064797900332533 146319925881074803156175)
                ·
                  rfl

theorem cell20_961730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_961730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961730 prefixEnd_961730 := by exact prefixLift 961730
  have htrace : WordTrace (prefixWord ++ tailWord_961730) baseStart_961730 baseEnd_961730 := by
    simpa [prefixWord, tailWord_961730, baseEnd_961730] using wordTrace_append hprefix tailTrace_961730
  have hstable : (prefixWord ++ tailWord_961730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961730).length < 2 ^ (prefixWord ++ tailWord_961730).sum := by decide
  have hdescent : baseEnd_961730 < baseStart_961730 := by decide
  rcases family_descends (prefixWord ++ tailWord_961730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961745 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_961745 : Nat := 118140960795 + 961745 * 2 ^ 59
def prefixEnd_961745 : Nat := 4983230072969 + 3 ^ 40 * 961745 * 2
def baseEnd_961745 : Nat := 438966624051951023968463

theorem tailTrace_961745 : CollatzResearch.WordTrace tailWord_961745 prefixEnd_961745 438966624051951023968463 := by
  unfold tailWord_961745
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077721900769592814262689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23385147933846395209508459 35077721900769592814262689)
  ·
    refine ⟨26308291425577194610697017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35077721900769592814262689 26308291425577194610697017)
    ·
      refine ⟨19731218569182895958022763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26308291425577194610697017 19731218569182895958022763)
      ·
        refine ⟨29596827853774343937034145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19731218569182895958022763 29596827853774343937034145)
        ·
          refine ⟨22197620890330757952775609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29596827853774343937034145 22197620890330757952775609)
          ·
            refine ⟨16648215667748068464581707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22197620890330757952775609 16648215667748068464581707)
            ·
              refine ⟨24972323501622102696872561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16648215667748068464581707 24972323501622102696872561)
              ·
                refine ⟨18729242626216577022654421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24972323501622102696872561 18729242626216577022654421)
                ·
                  refine ⟨438966624051951023968463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18729242626216577022654421 438966624051951023968463)
                  ·
                    rfl

theorem cell20_961745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_961745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961745 prefixEnd_961745 := by exact prefixLift 961745
  have htrace : WordTrace (prefixWord ++ tailWord_961745) baseStart_961745 baseEnd_961745 := by
    simpa [prefixWord, tailWord_961745, baseEnd_961745] using wordTrace_append hprefix tailTrace_961745
  have hstable : (prefixWord ++ tailWord_961745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961745).length < 2 ^ (prefixWord ++ tailWord_961745).sum := by decide
  have hdescent : baseEnd_961745 < baseStart_961745 := by decide
  rcases family_descends (prefixWord ++ tailWord_961745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961779 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 3]
def baseStart_961779 : Nat := 118140960795 + 961779 * 2 ^ 59
def prefixEnd_961779 : Nat := 4983230072969 + 3 ^ 40 * 961779 * 2
def baseEnd_961779 : Nat := 438982142578398016834991

theorem tailTrace_961779 : CollatzResearch.WordTrace tailWord_961779 prefixEnd_961779 438982142578398016834991 := by
  unfold tailWord_961779
  simp only [CollatzResearch.WordTrace]
  refine ⟨35078961982646416621000391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23385974655097611080666927 35078961982646416621000391)
  ·
    refine ⟨52618442973969624931500587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35078961982646416621000391 52618442973969624931500587)
    ·
      refine ⟨78927664460954437397250881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52618442973969624931500587 78927664460954437397250881)
      ·
        refine ⟨59195748345715828047938161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78927664460954437397250881 59195748345715828047938161)
        ·
          refine ⟨44396811259286871035953621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59195748345715828047938161 44396811259286871035953621)
          ·
            refine ⟨1040550263889536039905163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44396811259286871035953621 1040550263889536039905163)
            ·
              refine ⟨1560825395834304059857745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040550263889536039905163 1560825395834304059857745)
              ·
                refine ⟨1170619046875728044893309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560825395834304059857745 1170619046875728044893309)
                ·
                  refine ⟨438982142578398016834991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170619046875728044893309 438982142578398016834991)
                  ·
                    rfl

theorem cell20_961779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_961779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961779 prefixEnd_961779 := by exact prefixLift 961779
  have htrace : WordTrace (prefixWord ++ tailWord_961779) baseStart_961779 baseEnd_961779 := by
    simpa [prefixWord, tailWord_961779, baseEnd_961779] using wordTrace_append hprefix tailTrace_961779
  have hstable : (prefixWord ++ tailWord_961779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961779).length < 2 ^ (prefixWord ++ tailWord_961779).sum := by decide
  have hdescent : baseEnd_961779 < baseStart_961779 := by decide
  rcases family_descends (prefixWord ++ tailWord_961779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961783 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_961783 : Nat := 118140960795 + 961783 * 2 ^ 59
def prefixEnd_961783 : Nat := 4983230072969 + 3 ^ 40 * 961783 * 2
def baseEnd_961783 : Nat := 438983968287391780701641

theorem tailTrace_961783 : CollatzResearch.WordTrace tailWord_961783 prefixEnd_961783 438983968287391780701641 := by
  unfold tailWord_961783
  simp only [CollatzResearch.WordTrace]
  refine ⟨35079107874631925304146003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23386071916421283536097335 35079107874631925304146003)
  ·
    refine ⟨52618661811947887956219005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35079107874631925304146003 52618661811947887956219005)
    ·
      refine ⟨19731998179480457983582127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52618661811947887956219005 19731998179480457983582127)
      ·
        refine ⟨29597997269220686975373191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19731998179480457983582127 29597997269220686975373191)
        ·
          refine ⟨44396995903831030463059787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29597997269220686975373191 44396995903831030463059787)
          ·
            refine ⟨66595493855746545694589681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44396995903831030463059787 66595493855746545694589681)
            ·
              refine ⟨49946620391809909270942261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66595493855746545694589681 49946620391809909270942261)
              ·
                refine ⟨4682495661732178994150837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49946620391809909270942261 4682495661732178994150837)
                ·
                  refine ⟨438983968287391780701641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4682495661732178994150837 438983968287391780701641)
                  ·
                    rfl

theorem cell20_961783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_961783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961783 prefixEnd_961783 := by exact prefixLift 961783
  have htrace : WordTrace (prefixWord ++ tailWord_961783) baseStart_961783 baseEnd_961783 := by
    simpa [prefixWord, tailWord_961783, baseEnd_961783] using wordTrace_append hprefix tailTrace_961783
  have hstable : (prefixWord ++ tailWord_961783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961783).length < 2 ^ (prefixWord ++ tailWord_961783).sum := by decide
  have hdescent : baseEnd_961783 < baseStart_961783 := by decide
  rcases family_descends (prefixWord ++ tailWord_961783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961786 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_961786 : Nat := 118140960795 + 961786 * 2 ^ 59
def prefixEnd_961786 : Nat := 4983230072969 + 3 ^ 40 * 961786 * 2
def baseEnd_961786 : Nat := 438985337569137103601629

theorem tailTrace_961786 : CollatzResearch.WordTrace tailWord_961786 prefixEnd_961786 438985337569137103601629 := by
  unfold tailWord_961786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769804323405264204126303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23386144862414037877670141 8769804323405264204126303)
  ·
    refine ⟨13154706485107896306189455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8769804323405264204126303 13154706485107896306189455)
    ·
      refine ⟨19732059727661844459284183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13154706485107896306189455 19732059727661844459284183)
      ·
        refine ⟨29598089591492766688926275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19732059727661844459284183 29598089591492766688926275)
        ·
          refine ⟨44397134387239150033389413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29598089591492766688926275 44397134387239150033389413)
          ·
            refine ⟨8324462697607340631260515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44397134387239150033389413 8324462697607340631260515)
            ·
              refine ⟨12486694046411010946890773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8324462697607340631260515 12486694046411010946890773)
              ·
                refine ⟨585313783425516138135505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12486694046411010946890773 585313783425516138135505)
                ·
                  refine ⟨438985337569137103601629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585313783425516138135505 438985337569137103601629)
                  ·
                    rfl

theorem cell20_961786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_961786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961786 prefixEnd_961786 := by exact prefixLift 961786
  have htrace : WordTrace (prefixWord ++ tailWord_961786) baseStart_961786 baseEnd_961786 := by
    simpa [prefixWord, tailWord_961786, baseEnd_961786] using wordTrace_append hprefix tailTrace_961786
  have hstable : (prefixWord ++ tailWord_961786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961786).length < 2 ^ (prefixWord ++ tailWord_961786).sum := by decide
  have hdescent : baseEnd_961786 < baseStart_961786 := by decide
  rcases family_descends (prefixWord ++ tailWord_961786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961796 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_961796 : Nat := 118140960795 + 961796 * 2 ^ 59
def prefixEnd_961796 : Nat := 4983230072969 + 3 ^ 40 * 961796 * 2
def baseEnd_961796 : Nat := 438989901841621513268255

theorem tailTrace_961796 : CollatzResearch.WordTrace tailWord_961796 prefixEnd_961796 438989901841621513268255 := by
  unfold tailWord_961796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17539791011792414262184621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23386388015723219016246161 17539791011792414262184621)
  ·
    refine ⟨6577421629422155348319233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17539791011792414262184621 6577421629422155348319233)
    ·
      refine ⟨4933066222066616511239425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6577421629422155348319233 4933066222066616511239425)
      ·
        refine ⟨3699799666549962383429569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4933066222066616511239425 3699799666549962383429569)
        ·
          refine ⟨2774849749912471787572177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3699799666549962383429569 2774849749912471787572177)
          ·
            refine ⟨2081137312434353840679133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774849749912471787572177 2081137312434353840679133)
            ·
              refine ⟨780426492162882690254675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081137312434353840679133 780426492162882690254675)
              ·
                refine ⟨1170639738244324035382013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780426492162882690254675 1170639738244324035382013)
                ·
                  refine ⟨438989901841621513268255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170639738244324035382013 438989901841621513268255)
                  ·
                    rfl

theorem cell20_961796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_961796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961796 prefixEnd_961796 := by exact prefixLift 961796
  have htrace : WordTrace (prefixWord ++ tailWord_961796) baseStart_961796 baseEnd_961796 := by
    simpa [prefixWord, tailWord_961796, baseEnd_961796] using wordTrace_append hprefix tailTrace_961796
  have hstable : (prefixWord ++ tailWord_961796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961796).length < 2 ^ (prefixWord ++ tailWord_961796).sum := by decide
  have hdescent : baseEnd_961796 < baseStart_961796 := by decide
  rcases family_descends (prefixWord ++ tailWord_961796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961837 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 2]
def baseStart_961837 : Nat := 118140960795 + 961837 * 2 ^ 59
def prefixEnd_961837 : Nat := 4983230072969 + 3 ^ 40 * 961837 * 2
def baseEnd_961837 : Nat := 439008615358807592901421

theorem tailTrace_961837 : CollatzResearch.WordTrace tailWord_961837 prefixEnd_961837 439008615358807592901421 := by
  unfold tailWord_961837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35081077416436292526611765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23387384944290861684407843 35081077416436292526611765)
  ·
    refine ⟨3288851007790902424369853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35081077416436292526611765 3288851007790902424369853)
    ·
      refine ⟨1233319127921588409138695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3288851007790902424369853 1233319127921588409138695)
      ·
        refine ⟨1849978691882382613708043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233319127921588409138695 1849978691882382613708043)
        ·
          refine ⟨2774968037823573920562065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849978691882382613708043 2774968037823573920562065)
          ·
            refine ⟨2081226028367680440421549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774968037823573920562065 2081226028367680440421549)
            ·
              refine ⟨780459760637880165158081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081226028367680440421549 780459760637880165158081)
              ·
                refine ⟨585344820478410123868561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780459760637880165158081 585344820478410123868561)
                ·
                  refine ⟨439008615358807592901421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585344820478410123868561 439008615358807592901421)
                  ·
                    rfl

theorem cell20_961837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_961837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961837 prefixEnd_961837 := by exact prefixLift 961837
  have htrace : WordTrace (prefixWord ++ tailWord_961837) baseStart_961837 baseEnd_961837 := by
    simpa [prefixWord, tailWord_961837, baseEnd_961837] using wordTrace_append hprefix tailTrace_961837
  have hstable : (prefixWord ++ tailWord_961837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961837).length < 2 ^ (prefixWord ++ tailWord_961837).sum := by decide
  have hdescent : baseEnd_961837 < baseStart_961837 := by decide
  rcases family_descends (prefixWord ++ tailWord_961837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961852 : List Nat := [2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_961852 : Nat := 118140960795 + 961852 * 2 ^ 59
def prefixEnd_961852 : Nat := 4983230072969 + 3 ^ 40 * 961852 * 2
def baseEnd_961852 : Nat := 146338487255844735800453

theorem tailTrace_961852 : CollatzResearch.WordTrace tailWord_961852 prefixEnd_961852 146338487255844735800453 := by
  unfold tailWord_961852
  simp only [CollatzResearch.WordTrace]
  refine ⟨17540812255690975044203905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23387749674254633392271873 17540812255690975044203905)
  ·
    refine ⟨13155609191768231283152929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17540812255690975044203905 13155609191768231283152929)
    ·
      refine ⟨9866706893826173462364697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13155609191768231283152929 9866706893826173462364697)
      ·
        refine ⟨7400030170369630096773523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9866706893826173462364697 7400030170369630096773523)
        ·
          refine ⟨11100045255554445145160285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400030170369630096773523 11100045255554445145160285)
          ·
            refine ⟨4162516970832916929435107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11100045255554445145160285 4162516970832916929435107)
            ·
              refine ⟨6243775456249375394152661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162516970832916929435107 6243775456249375394152661)
              ·
                refine ⟨146338487255844735800453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6243775456249375394152661 146338487255844735800453)
                ·
                  rfl

theorem cell20_961852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_961852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961852 prefixEnd_961852 := by exact prefixLift 961852
  have htrace : WordTrace (prefixWord ++ tailWord_961852) baseStart_961852 baseEnd_961852 := by
    simpa [prefixWord, tailWord_961852, baseEnd_961852] using wordTrace_append hprefix tailTrace_961852
  have hstable : (prefixWord ++ tailWord_961852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961852).length < 2 ^ (prefixWord ++ tailWord_961852).sum := by decide
  have hdescent : baseEnd_961852 < baseStart_961852 := by decide
  rcases family_descends (prefixWord ++ tailWord_961852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961855 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 3]
def baseStart_961855 : Nat := 118140960795 + 961855 * 2 ^ 59
def prefixEnd_961855 : Nat := 4983230072969 + 3 ^ 40 * 961855 * 2
def baseEnd_961855 : Nat := 439016831049279530301347

theorem tailTrace_961855 : CollatzResearch.WordTrace tailWord_961855 prefixEnd_961855 439016831049279530301347 := by
  unfold tailWord_961855
  simp only [CollatzResearch.WordTrace]
  refine ⟨35081733930371081600767019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23387822620247387733844679 35081733930371081600767019)
  ·
    refine ⟨52622600895556622401150529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35081733930371081600767019 52622600895556622401150529)
    ·
      refine ⟨39466950671667466800862897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52622600895556622401150529 39466950671667466800862897)
      ·
        refine ⟨29600213003750600100647173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39466950671667466800862897 29600213003750600100647173)
        ·
          refine ⟨5550039938203237518871345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29600213003750600100647173 5550039938203237518871345)
          ·
            refine ⟨4162529953652428139153509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5550039938203237518871345 4162529953652428139153509)
            ·
              refine ⟨780474366309830276091283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4162529953652428139153509 780474366309830276091283)
              ·
                refine ⟨1170711549464745414136925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780474366309830276091283 1170711549464745414136925)
                ·
                  refine ⟨439016831049279530301347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170711549464745414136925 439016831049279530301347)
                  ·
                    rfl

theorem cell20_961855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_961855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961855 prefixEnd_961855 := by exact prefixLift 961855
  have htrace : WordTrace (prefixWord ++ tailWord_961855) baseStart_961855 baseEnd_961855 := by
    simpa [prefixWord, tailWord_961855, baseEnd_961855] using wordTrace_append hprefix tailTrace_961855
  have hstable : (prefixWord ++ tailWord_961855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961855).length < 2 ^ (prefixWord ++ tailWord_961855).sum := by decide
  have hdescent : baseEnd_961855 < baseStart_961855 := by decide
  rcases family_descends (prefixWord ++ tailWord_961855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961886 : List Nat := [4, 4, 2, 10]
def baseStart_961886 : Nat := 118140960795 + 961886 * 2 ^ 59
def prefixEnd_961886 : Nat := 4983230072969 + 3 ^ 40 * 961886 * 2
def baseEnd_961886 : Nat := 1806711853061651029909

theorem tailTrace_961886 : CollatzResearch.WordTrace tailWord_961886 prefixEnd_961886 1806711853061651029909 := by
  unfold tailWord_961886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385358074157346736893189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23388576395505849263430341 4385358074157346736893189)
  ·
    refine ⟨822254638904502513167473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4385358074157346736893189 822254638904502513167473)
    ·
      refine ⟨616690979178376884875605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822254638904502513167473 616690979178376884875605)
      ·
        refine ⟨1806711853061651029909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 616690979178376884875605 1806711853061651029909)
        ·
          rfl

theorem cell20_961886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 10].length) (baseStart_961886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961886 prefixEnd_961886 := by exact prefixLift 961886
  have htrace : WordTrace (prefixWord ++ tailWord_961886) baseStart_961886 baseEnd_961886 := by
    simpa [prefixWord, tailWord_961886, baseEnd_961886] using wordTrace_append hprefix tailTrace_961886
  have hstable : (prefixWord ++ tailWord_961886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961886).length < 2 ^ (prefixWord ++ tailWord_961886).sum := by decide
  have hdescent : baseEnd_961886 < baseStart_961886 := by decide
  rcases family_descends (prefixWord ++ tailWord_961886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961934 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_961934 : Nat := 118140960795 + 961934 * 2 ^ 59
def prefixEnd_961934 : Nat := 4983230072969 + 3 ^ 40 * 961934 * 2
def baseEnd_961934 : Nat := 439052888801906366667691

theorem tailTrace_961934 : CollatzResearch.WordTrace tailWord_961934 prefixEnd_961934 439052888801906366667691 := by
  unfold tailWord_961934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385576912135609761611607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23389743531389918728595237 4385576912135609761611607)
  ·
    refine ⟨6578365368203414642417411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4385576912135609761611607 6578365368203414642417411)
    ·
      refine ⟨9867548052305121963626117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6578365368203414642417411 9867548052305121963626117)
      ·
        refine ⟨1850165259807210368179897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9867548052305121963626117 1850165259807210368179897)
        ·
          refine ⟨1387623944855407776134923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850165259807210368179897 1387623944855407776134923)
          ·
            refine ⟨2081435917283111664202385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387623944855407776134923 2081435917283111664202385)
            ·
              refine ⟨1561076937962333748151789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081435917283111664202385 1561076937962333748151789)
              ·
                refine ⟨585403851735875155556921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561076937962333748151789 585403851735875155556921)
                ·
                  refine ⟨439052888801906366667691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585403851735875155556921 439052888801906366667691)
                  ·
                    rfl

theorem cell20_961934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_961934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961934 prefixEnd_961934 := by exact prefixLift 961934
  have htrace : WordTrace (prefixWord ++ tailWord_961934) baseStart_961934 baseEnd_961934 := by
    simpa [prefixWord, tailWord_961934, baseEnd_961934] using wordTrace_append hprefix tailTrace_961934
  have hstable : (prefixWord ++ tailWord_961934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961934).length < 2 ^ (prefixWord ++ tailWord_961934).sum := by decide
  have hdescent : baseEnd_961934 < baseStart_961934 := by decide
  rcases family_descends (prefixWord ++ tailWord_961934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961969 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 3]
def baseStart_961969 : Nat := 118140960795 + 961969 * 2 ^ 59
def prefixEnd_961969 : Nat := 4983230072969 + 3 ^ 40 * 961969 * 2
def baseEnd_961969 : Nat := 439068863755601800500881

theorem tailTrace_961969 : CollatzResearch.WordTrace tailWord_961969 prefixEnd_961969 439068863755601800500881 := by
  unfold tailWord_961969
  simp only [CollatzResearch.WordTrace]
  refine ⟨35085891851958079070416961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23390594567972052713611307 35085891851958079070416961)
  ·
    refine ⟨26314418888968559302812721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35085891851958079070416961 26314418888968559302812721)
    ·
      refine ⟨19735814166726419477109541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26314418888968559302812721 19735814166726419477109541)
      ·
        refine ⟨3700465156261203651958039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19735814166726419477109541 3700465156261203651958039)
        ·
          refine ⟨5550697734391805477937059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700465156261203651958039 5550697734391805477937059)
          ·
            refine ⟨8326046601587708216905589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550697734391805477937059 8326046601587708216905589)
            ·
              refine ⟨780566868898847645334899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8326046601587708216905589 780566868898847645334899)
              ·
                refine ⟨1170850303348271468002349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780566868898847645334899 1170850303348271468002349)
                ·
                  refine ⟨439068863755601800500881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170850303348271468002349 439068863755601800500881)
                  ·
                    rfl

theorem cell20_961969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_961969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961969 prefixEnd_961969 := by exact prefixLift 961969
  have htrace : WordTrace (prefixWord ++ tailWord_961969) baseStart_961969 baseEnd_961969 := by
    simpa [prefixWord, tailWord_961969, baseEnd_961969] using wordTrace_append hprefix tailTrace_961969
  have hstable : (prefixWord ++ tailWord_961969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961969).length < 2 ^ (prefixWord ++ tailWord_961969).sum := by decide
  have hdescent : baseEnd_961969 < baseStart_961969 := by decide
  rcases family_descends (prefixWord ++ tailWord_961969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962021 : List Nat := [1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_962021 : Nat := 118140960795 + 962021 * 2 ^ 59
def prefixEnd_962021 : Nat := 4983230072969 + 3 ^ 40 * 962021 * 2
def baseEnd_962021 : Nat := 146364199324173576922445

theorem tailTrace_962021 : CollatzResearch.WordTrace tailWord_962021 prefixEnd_962021 146364199324173576922445 := by
  unfold tailWord_962021
  simp only [CollatzResearch.WordTrace]
  refine ⟨35087788447769691951309917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23391858965179794634206611 35087788447769691951309917)
  ·
    refine ⟨13157920667913634481741219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35087788447769691951309917 13157920667913634481741219)
    ·
      refine ⟨19736881001870451722611829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13157920667913634481741219 19736881001870451722611829)
      ·
        refine ⟨1850332593925354848994859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19736881001870451722611829 1850332593925354848994859)
        ·
          refine ⟨2775498890888032273492289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850332593925354848994859 2775498890888032273492289)
          ·
            refine ⟨2081624168166024205119217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775498890888032273492289 2081624168166024205119217)
            ·
              refine ⟨1561218126124518153839413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081624168166024205119217 1561218126124518153839413)
              ·
                refine ⟨146364199324173576922445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1561218126124518153839413 146364199324173576922445)
                ·
                  rfl

theorem cell20_962021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_962021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962021 prefixEnd_962021 := by exact prefixLift 962021
  have htrace : WordTrace (prefixWord ++ tailWord_962021) baseStart_962021 baseEnd_962021 := by
    simpa [prefixWord, tailWord_962021, baseEnd_962021] using wordTrace_append hprefix tailTrace_962021
  have hstable : (prefixWord ++ tailWord_962021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962021).length < 2 ^ (prefixWord ++ tailWord_962021).sum := by decide
  have hdescent : baseEnd_962021 < baseStart_962021 := by decide
  rcases family_descends (prefixWord ++ tailWord_962021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962061 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 2]
def baseStart_962061 : Nat := 118140960795 + 962061 * 2 ^ 59
def prefixEnd_962061 : Nat := 4983230072969 + 3 ^ 40 * 962061 * 2
def baseEnd_962061 : Nat := 439110855062458369433839

theorem tailTrace_962061 : CollatzResearch.WordTrace tailWord_962061 prefixEnd_962061 439110855062458369433839 := by
  unfold tailWord_962061
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089247367624778782766037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23392831578416519188510691 35089247367624778782766037)
  ·
    refine ⟨822404235178705752721079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35089247367624778782766037 822404235178705752721079)
    ·
      refine ⟨1233606352768058629081619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822404235178705752721079 1233606352768058629081619)
      ·
        refine ⟨1850409529152087943622429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233606352768058629081619 1850409529152087943622429)
        ·
          refine ⟨693903573432032978858411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1850409529152087943622429 693903573432032978858411)
          ·
            refine ⟨1040855360148049468287617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693903573432032978858411 1040855360148049468287617)
            ·
              refine ⟨780641520111037101215713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040855360148049468287617 780641520111037101215713)
              ·
                refine ⟨585481140083277825911785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780641520111037101215713 585481140083277825911785)
                ·
                  refine ⟨439110855062458369433839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585481140083277825911785 439110855062458369433839)
                  ·
                    rfl

theorem cell20_962061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_962061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962061 prefixEnd_962061 := by exact prefixLift 962061
  have htrace : WordTrace (prefixWord ++ tailWord_962061) baseStart_962061 baseEnd_962061 := by
    simpa [prefixWord, tailWord_962061, baseEnd_962061] using wordTrace_append hprefix tailTrace_962061
  have hstable : (prefixWord ++ tailWord_962061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962061).length < 2 ^ (prefixWord ++ tailWord_962061).sum := by decide
  have hdescent : baseEnd_962061 < baseStart_962061 := by decide
  rcases family_descends (prefixWord ++ tailWord_962061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962069 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 2]
def baseStart_962069 : Nat := 118140960795 + 962069 * 2 ^ 59
def prefixEnd_962069 : Nat := 4983230072969 + 3 ^ 40 * 962069 * 2
def baseEnd_962069 : Nat := 439114506480445897167139

theorem tailTrace_962069 : CollatzResearch.WordTrace tailWord_962069 prefixEnd_962069 439114506480445897167139 := by
  unfold tailWord_962069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089539151595796149057261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23393026101063864099371507 35089539151595796149057261)
  ·
    refine ⟨13158577181848423555896473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35089539151595796149057261 13158577181848423555896473)
    ·
      refine ⟨9868932886386317666922355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13158577181848423555896473 9868932886386317666922355)
      ·
        refine ⟨14803399329579476500383533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9868932886386317666922355 14803399329579476500383533)
        ·
          refine ⟨5551274748592303687643825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14803399329579476500383533 5551274748592303687643825)
          ·
            refine ⟨4163456061444227765732869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551274748592303687643825 4163456061444227765732869)
            ·
              refine ⟨780648011520792706074913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4163456061444227765732869 780648011520792706074913)
              ·
                refine ⟨585486008640594529556185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780648011520792706074913 585486008640594529556185)
                ·
                  refine ⟨439114506480445897167139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585486008640594529556185 439114506480445897167139)
                  ·
                    rfl

theorem cell20_962069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_962069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962069 prefixEnd_962069 := by exact prefixLift 962069
  have htrace : WordTrace (prefixWord ++ tailWord_962069) baseStart_962069 baseEnd_962069 := by
    simpa [prefixWord, tailWord_962069, baseEnd_962069] using wordTrace_append hprefix tailTrace_962069
  have hstable : (prefixWord ++ tailWord_962069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962069).length < 2 ^ (prefixWord ++ tailWord_962069).sum := by decide
  have hdescent : baseEnd_962069 < baseStart_962069 := by decide
  rcases family_descends (prefixWord ++ tailWord_962069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962134 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_962134 : Nat := 118140960795 + 962134 * 2 ^ 59
def prefixEnd_962134 : Nat := 4983230072969 + 3 ^ 40 * 962134 * 2
def baseEnd_962134 : Nat := 439144174251594560000207

theorem tailTrace_962134 : CollatzResearch.WordTrace tailWord_962134 prefixEnd_962134 439144174251594560000207 := by
  unfold tailWord_962134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193244368522519515635841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23394606597573541500115637 2193244368522519515635841)
  ·
    refine ⟨1644933276391889636726881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2193244368522519515635841 1644933276391889636726881)
    ·
      refine ⟨1233699957293917227545161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644933276391889636726881 1233699957293917227545161)
      ·
        refine ⟨925274967970437920658871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233699957293917227545161 925274967970437920658871)
        ·
          refine ⟨1387912451955656880988307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925274967970437920658871 1387912451955656880988307)
          ·
            refine ⟨2081868677933485321482461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387912451955656880988307 2081868677933485321482461)
            ·
              refine ⟨780700754225056995555923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081868677933485321482461 780700754225056995555923)
              ·
                refine ⟨1171051131337585493333885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780700754225056995555923 1171051131337585493333885)
                ·
                  refine ⟨439144174251594560000207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171051131337585493333885 439144174251594560000207)
                  ·
                    rfl

theorem cell20_962134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_962134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962134 prefixEnd_962134 := by exact prefixLift 962134
  have htrace : WordTrace (prefixWord ++ tailWord_962134) baseStart_962134 baseEnd_962134 := by
    simpa [prefixWord, tailWord_962134, baseEnd_962134] using wordTrace_append hprefix tailTrace_962134
  have hstable : (prefixWord ++ tailWord_962134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962134).length < 2 ^ (prefixWord ++ tailWord_962134).sum := by decide
  have hdescent : baseEnd_962134 < baseStart_962134 := by decide
  rcases family_descends (prefixWord ++ tailWord_962134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962149 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_962149 : Nat := 118140960795 + 962149 * 2 ^ 59
def prefixEnd_962149 : Nat := 4983230072969 + 3 ^ 40 * 962149 * 2
def baseEnd_962149 : Nat := 439151020660321174500145

theorem tailTrace_962149 : CollatzResearch.WordTrace tailWord_962149 prefixEnd_962149 439151020660321174500145 := by
  unfold tailWord_962149
  simp only [CollatzResearch.WordTrace]
  refine ⟨35092456991305969811969501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23394971327537313207979667 35092456991305969811969501)
  ·
    refine ⟨13159671371739738679488563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35092456991305969811969501 13159671371739738679488563)
    ·
      refine ⟨19739507057609608019232845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13159671371739738679488563 19739507057609608019232845)
      ·
        refine ⟨7402315146603603007212317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19739507057609608019232845 7402315146603603007212317)
        ·
          refine ⟨2775868179976351127704619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7402315146603603007212317 2775868179976351127704619)
          ·
            refine ⟨4163802269964526691556929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775868179976351127704619 4163802269964526691556929)
            ·
              refine ⟨3122851702473395018667697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163802269964526691556929 3122851702473395018667697)
              ·
                refine ⟨2342138776855046264000773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3122851702473395018667697 2342138776855046264000773)
                ·
                  refine ⟨439151020660321174500145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342138776855046264000773 439151020660321174500145)
                  ·
                    rfl

theorem cell20_962149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_962149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962149 prefixEnd_962149 := by exact prefixLift 962149
  have htrace : WordTrace (prefixWord ++ tailWord_962149) baseStart_962149 baseEnd_962149 := by
    simpa [prefixWord, tailWord_962149, baseEnd_962149] using wordTrace_append hprefix tailTrace_962149
  have hstable : (prefixWord ++ tailWord_962149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962149).length < 2 ^ (prefixWord ++ tailWord_962149).sum := by decide
  have hdescent : baseEnd_962149 < baseStart_962149 := by decide
  rcases family_descends (prefixWord ++ tailWord_962149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962152 : List Nat := [2, 1, 4, 3, 1, 3, 2, 4]
def baseStart_962152 : Nat := 118140960795 + 962152 * 2 ^ 59
def prefixEnd_962152 : Nat := 4983230072969 + 3 ^ 40 * 962152 * 2
def baseEnd_962152 : Nat := 146384129980688832466711

theorem tailTrace_962152 : CollatzResearch.WordTrace tailWord_962152 prefixEnd_962152 146384129980688832466711 := by
  unfold tailWord_962152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17546283205147550662164355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23395044273530067549552473 17546283205147550662164355)
  ·
    refine ⟨26319424807721325993246533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17546283205147550662164355 26319424807721325993246533)
    ·
      refine ⟨4934892151447748623733725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26319424807721325993246533 4934892151447748623733725)
      ·
        refine ⟨1850584556792905733900147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4934892151447748623733725 1850584556792905733900147)
        ·
          refine ⟨2775876835189358600850221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850584556792905733900147 2775876835189358600850221)
          ·
            refine ⟨1040953813196009475318833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2775876835189358600850221 1040953813196009475318833)
            ·
              refine ⟨780715359897007106489125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040953813196009475318833 780715359897007106489125)
              ·
                refine ⟨146384129980688832466711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780715359897007106489125 146384129980688832466711)
                ·
                  rfl

theorem cell20_962152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_962152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962152 prefixEnd_962152 := by exact prefixLift 962152
  have htrace : WordTrace (prefixWord ++ tailWord_962152) baseStart_962152 baseEnd_962152 := by
    simpa [prefixWord, tailWord_962152, baseEnd_962152] using wordTrace_append hprefix tailTrace_962152
  have hstable : (prefixWord ++ tailWord_962152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962152).length < 2 ^ (prefixWord ++ tailWord_962152).sum := by decide
  have hdescent : baseEnd_962152 < baseStart_962152 := by decide
  rcases family_descends (prefixWord ++ tailWord_962152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962183 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 2]
def baseStart_962183 : Nat := 118140960795 + 962183 * 2 ^ 59
def prefixEnd_962183 : Nat := 4983230072969 + 3 ^ 40 * 962183 * 2
def baseEnd_962183 : Nat := 439166539186768167366673

theorem tailTrace_962183 : CollatzResearch.WordTrace tailWord_962183 prefixEnd_962183 439166539186768167366673 := by
  unfold tailWord_962183
  simp only [CollatzResearch.WordTrace]
  refine ⟨35093697073182793618707203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23395798048788529079138135 35093697073182793618707203)
  ·
    refine ⟨52640545609774190428060805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35093697073182793618707203 52640545609774190428060805)
    ·
      refine ⟨9870102301832660705261401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52640545609774190428060805 9870102301832660705261401)
      ·
        refine ⟨7402576726374495528946051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9870102301832660705261401 7402576726374495528946051)
        ·
          refine ⟨11103865089561743293419077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402576726374495528946051 11103865089561743293419077)
          ·
            refine ⟨2081974704292826867516077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11103865089561743293419077 2081974704292826867516077)
            ·
              refine ⟨780740514109810075318529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081974704292826867516077 780740514109810075318529)
              ·
                refine ⟨585555385582357556488897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780740514109810075318529 585555385582357556488897)
                ·
                  refine ⟨439166539186768167366673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585555385582357556488897 439166539186768167366673)
                  ·
                    rfl

theorem cell20_962183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 2].length) (baseStart_962183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962183 prefixEnd_962183 := by exact prefixLift 962183
  have htrace : WordTrace (prefixWord ++ tailWord_962183) baseStart_962183 baseEnd_962183 := by
    simpa [prefixWord, tailWord_962183, baseEnd_962183] using wordTrace_append hprefix tailTrace_962183
  have hstable : (prefixWord ++ tailWord_962183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962183).length < 2 ^ (prefixWord ++ tailWord_962183).sum := by decide
  have hdescent : baseEnd_962183 < baseStart_962183 := by decide
  rcases family_descends (prefixWord ++ tailWord_962183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962238 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_962238 : Nat := 118140960795 + 962238 * 2 ^ 59
def prefixEnd_962238 : Nat := 4983230072969 + 3 ^ 40 * 962238 * 2
def baseEnd_962238 : Nat := 439191642685432420533115

theorem tailTrace_962238 : CollatzResearch.WordTrace tailWord_962238 prefixEnd_962238 439191642685432420533115 := by
  unfold tailWord_962238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386962885997942251494921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23397135391989025341306245 4386962885997942251494921)
  ·
    refine ⟨3290222164498456688621191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4386962885997942251494921 3290222164498456688621191)
    ·
      refine ⟨4935333246747685032931787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290222164498456688621191 4935333246747685032931787)
      ·
        refine ⟨7402999870121527549397681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935333246747685032931787 7402999870121527549397681)
        ·
          refine ⟨5552249902591145662048261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7402999870121527549397681 5552249902591145662048261)
          ·
            refine ⟨1041046856735839811634049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5552249902591145662048261 1041046856735839811634049)
            ·
              refine ⟨780785142551879858725537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041046856735839811634049 780785142551879858725537)
              ·
                refine ⟨585588856913909894044153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780785142551879858725537 585588856913909894044153)
                ·
                  refine ⟨439191642685432420533115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585588856913909894044153 439191642685432420533115)
                  ·
                    rfl

theorem cell20_962238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_962238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962238 prefixEnd_962238 := by exact prefixLift 962238
  have htrace : WordTrace (prefixWord ++ tailWord_962238) baseStart_962238 baseEnd_962238 := by
    simpa [prefixWord, tailWord_962238, baseEnd_962238] using wordTrace_append hprefix tailTrace_962238
  have hstable : (prefixWord ++ tailWord_962238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962238).length < 2 ^ (prefixWord ++ tailWord_962238).sum := by decide
  have hdescent : baseEnd_962238 < baseStart_962238 := by decide
  rcases family_descends (prefixWord ++ tailWord_962238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962277 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_962277 : Nat := 118140960795 + 962277 * 2 ^ 59
def prefixEnd_962277 : Nat := 4983230072969 + 3 ^ 40 * 962277 * 2
def baseEnd_962277 : Nat := 439209443348121618232955

theorem tailTrace_962277 : CollatzResearch.WordTrace tailWord_962277 prefixEnd_962277 439209443348121618232955 := by
  unfold tailWord_962277
  simp only [CollatzResearch.WordTrace]
  refine ⟨35097125534842247672629085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23398083689894831781752723 35097125534842247672629085)
  ·
    refine ⟨13161422075565842877235907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35097125534842247672629085 13161422075565842877235907)
    ·
      refine ⟨19742133113348764315853861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13161422075565842877235907 19742133113348764315853861)
      ·
        refine ⟨3701649958752893309222599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19742133113348764315853861 3701649958752893309222599)
        ·
          refine ⟨5552474938129339963833899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701649958752893309222599 5552474938129339963833899)
          ·
            refine ⟨8328712407194009945750849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552474938129339963833899 8328712407194009945750849)
            ·
              refine ⟨6246534305395507459313137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8328712407194009945750849 6246534305395507459313137)
              ·
                refine ⟨4684900729046630594484853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246534305395507459313137 4684900729046630594484853)
                ·
                  refine ⟨439209443348121618232955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4684900729046630594484853 439209443348121618232955)
                  ·
                    rfl

theorem cell20_962277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_962277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962277 prefixEnd_962277 := by exact prefixLift 962277
  have htrace : WordTrace (prefixWord ++ tailWord_962277) baseStart_962277 baseEnd_962277 := by
    simpa [prefixWord, tailWord_962277, baseEnd_962277] using wordTrace_append hprefix tailTrace_962277
  have hstable : (prefixWord ++ tailWord_962277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962277).length < 2 ^ (prefixWord ++ tailWord_962277).sum := by decide
  have hdescent : baseEnd_962277 < baseStart_962277 := by decide
  rcases family_descends (prefixWord ++ tailWord_962277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962280 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 2]
def baseStart_962280 : Nat := 118140960795 + 962280 * 2 ^ 59
def prefixEnd_962280 : Nat := 4983230072969 + 3 ^ 40 * 962280 * 2
def baseEnd_962280 : Nat := 439210812629866941132943

theorem tailTrace_962280 : CollatzResearch.WordTrace tailWord_962280 prefixEnd_962280 439210812629866941132943 := by
  unfold tailWord_962280
  simp only [CollatzResearch.WordTrace]
  refine ⟨17548617476915689592494147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23398156635887586123325529 17548617476915689592494147)
  ·
    refine ⟨26322926215373534388741221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17548617476915689592494147 26322926215373534388741221)
    ·
      refine ⟨4935548665382537697888979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26322926215373534388741221 4935548665382537697888979)
      ·
        refine ⟨7403322998073806546833469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935548665382537697888979 7403322998073806546833469)
        ·
          refine ⟨2776246124277677455062551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7403322998073806546833469 2776246124277677455062551)
          ·
            refine ⟨4164369186416516182593827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776246124277677455062551 4164369186416516182593827)
            ·
              refine ⟨6246553779624774273890741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164369186416516182593827 6246553779624774273890741)
              ·
                refine ⟨585614416839822588177257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6246553779624774273890741 585614416839822588177257)
                ·
                  refine ⟨439210812629866941132943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585614416839822588177257 439210812629866941132943)
                  ·
                    rfl

theorem cell20_962280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_962280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962280 prefixEnd_962280 := by exact prefixLift 962280
  have htrace : WordTrace (prefixWord ++ tailWord_962280) baseStart_962280 baseEnd_962280 := by
    simpa [prefixWord, tailWord_962280, baseEnd_962280] using wordTrace_append hprefix tailTrace_962280
  have hstable : (prefixWord ++ tailWord_962280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962280).length < 2 ^ (prefixWord ++ tailWord_962280).sum := by decide
  have hdescent : baseEnd_962280 < baseStart_962280 := by decide
  rcases family_descends (prefixWord ++ tailWord_962280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962294 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_962294 : Nat := 118140960795 + 962294 * 2 ^ 59
def prefixEnd_962294 : Nat := 4983230072969 + 3 ^ 40 * 962294 * 2
def baseEnd_962294 : Nat := 439217202611345114666219

theorem tailTrace_962294 : CollatzResearch.WordTrace tailWord_962294 prefixEnd_962294 439217202611345114666219 := by
  unfold tailWord_962294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193609098486291223499871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23398497050520439717331957 2193609098486291223499871)
  ·
    refine ⟨3290413647729436835249807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193609098486291223499871 3290413647729436835249807)
    ·
      refine ⟨4935620471594155252874711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290413647729436835249807 4935620471594155252874711)
      ·
        refine ⟨7403430707391232879312067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935620471594155252874711 7403430707391232879312067)
        ·
          refine ⟨11105146061086849318968101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403430707391232879312067 11105146061086849318968101)
          ·
            refine ⟨2082214886453784247306519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11105146061086849318968101 2082214886453784247306519)
            ·
              refine ⟨3123322329680676370959779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082214886453784247306519 3123322329680676370959779)
              ·
                refine ⟨4684983494521014556439669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123322329680676370959779 4684983494521014556439669)
                ·
                  refine ⟨439217202611345114666219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4684983494521014556439669 439217202611345114666219)
                  ·
                    rfl

theorem cell20_962294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_962294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962294 prefixEnd_962294 := by exact prefixLift 962294
  have htrace : WordTrace (prefixWord ++ tailWord_962294) baseStart_962294 baseEnd_962294 := by
    simpa [prefixWord, tailWord_962294, baseEnd_962294] using wordTrace_append hprefix tailTrace_962294
  have hstable : (prefixWord ++ tailWord_962294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962294).length < 2 ^ (prefixWord ++ tailWord_962294).sum := by decide
  have hdescent : baseEnd_962294 < baseStart_962294 := by decide
  rcases family_descends (prefixWord ++ tailWord_962294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962315 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_962315 : Nat := 118140960795 + 962315 * 2 ^ 59
def prefixEnd_962315 : Nat := 4983230072969 + 3 ^ 40 * 962315 * 2
def baseEnd_962315 : Nat := 439226787583562374966133

theorem tailTrace_962315 : CollatzResearch.WordTrace tailWord_962315 prefixEnd_962315 439226787583562374966133 := by
  unfold tailWord_962315
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098511508704580162512399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23399007672469720108341599 35098511508704580162512399)
  ·
    refine ⟨52647767263056870243768599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35098511508704580162512399 52647767263056870243768599)
    ·
      refine ⟨78971650894585305365652899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52647767263056870243768599 78971650894585305365652899)
      ·
        refine ⟨118457476341877958048479349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78971650894585305365652899 118457476341877958048479349)
        ·
          refine ⟨11105388407051058567044939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118457476341877958048479349 11105388407051058567044939)
          ·
            refine ⟨16658082610576587850567409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11105388407051058567044939 16658082610576587850567409)
            ·
              refine ⟨12493561957932440887925557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16658082610576587850567409 12493561957932440887925557)
              ·
                refine ⟨1171271433556166333243021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12493561957932440887925557 1171271433556166333243021)
                ·
                  refine ⟨439226787583562374966133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171271433556166333243021 439226787583562374966133)
                  ·
                    rfl

theorem cell20_962315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_962315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962315 prefixEnd_962315 := by exact prefixLift 962315
  have htrace : WordTrace (prefixWord ++ tailWord_962315) baseStart_962315 baseEnd_962315 := by
    simpa [prefixWord, tailWord_962315, baseEnd_962315] using wordTrace_append hprefix tailTrace_962315
  have hstable : (prefixWord ++ tailWord_962315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962315).length < 2 ^ (prefixWord ++ tailWord_962315).sum := by decide
  have hdescent : baseEnd_962315 < baseStart_962315 := by decide
  rcases family_descends (prefixWord ++ tailWord_962315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962317 : List Nat := [1, 7, 2, 1, 1, 2, 2, 4]
def baseStart_962317 : Nat := 118140960795 + 962317 * 2 ^ 59
def prefixEnd_962317 : Nat := 4983230072969 + 3 ^ 40 * 962317 * 2
def baseEnd_962317 : Nat := 146409233479353085633153

theorem tailTrace_962317 : CollatzResearch.WordTrace tailWord_962317 prefixEnd_962317 146409233479353085633153 := by
  unfold tailWord_962317
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098584454697334504085205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23399056303131556336056803 35098584454697334504085205)
  ·
    refine ⟨822623073156968777439497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35098584454697334504085205 822623073156968777439497)
    ·
      refine ⟨616967304867726583079623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822623073156968777439497 616967304867726583079623)
      ·
        refine ⟨925450957301589874619435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616967304867726583079623 925450957301589874619435)
        ·
          refine ⟨1388176435952384811929153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925450957301589874619435 1388176435952384811929153)
          ·
            refine ⟨1041132326964288608946865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388176435952384811929153 1041132326964288608946865)
            ·
              refine ⟨780849245223216456710149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041132326964288608946865 780849245223216456710149)
              ·
                refine ⟨146409233479353085633153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780849245223216456710149 146409233479353085633153)
                ·
                  rfl

theorem cell20_962317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].length) (baseStart_962317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962317 prefixEnd_962317 := by exact prefixLift 962317
  have htrace : WordTrace (prefixWord ++ tailWord_962317) baseStart_962317 baseEnd_962317 := by
    simpa [prefixWord, tailWord_962317, baseEnd_962317] using wordTrace_append hprefix tailTrace_962317
  have hstable : (prefixWord ++ tailWord_962317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962317).length < 2 ^ (prefixWord ++ tailWord_962317).sum := by decide
  have hdescent : baseEnd_962317 < baseStart_962317 := by decide
  rcases family_descends (prefixWord ++ tailWord_962317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962325 : List Nat := [1, 3, 2, 1, 2, 5, 2, 4]
def baseStart_962325 : Nat := 118140960795 + 962325 * 2 ^ 59
def prefixEnd_962325 : Nat := 4983230072969 + 3 ^ 40 * 962325 * 2
def baseEnd_962325 : Nat := 146410450618682261544253

theorem tailTrace_962325 : CollatzResearch.WordTrace tailWord_962325 prefixEnd_962325 146410450618682261544253 := by
  unfold tailWord_962325
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098876238668351870376429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23399250825778901246917619 35098876238668351870376429)
  ·
    refine ⟨13162078589500631951391161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35098876238668351870376429 13162078589500631951391161)
    ·
      refine ⟨9871558942125473963543371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13162078589500631951391161 9871558942125473963543371)
      ·
        refine ⟨14807338413188210945315057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871558942125473963543371 14807338413188210945315057)
        ·
          refine ⟨11105503809891158208986293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14807338413188210945315057 11105503809891158208986293)
          ·
            refine ⟨1041140982177296082092465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11105503809891158208986293 1041140982177296082092465)
            ·
              refine ⟨780855736632972061569349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041140982177296082092465 780855736632972061569349)
              ·
                refine ⟨146410450618682261544253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780855736632972061569349 146410450618682261544253)
                ·
                  rfl

theorem cell20_962325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_962325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962325 prefixEnd_962325 := by exact prefixLift 962325
  have htrace : WordTrace (prefixWord ++ tailWord_962325) baseStart_962325 baseEnd_962325 := by
    simpa [prefixWord, tailWord_962325, baseEnd_962325] using wordTrace_append hprefix tailTrace_962325
  have hstable : (prefixWord ++ tailWord_962325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962325).length < 2 ^ (prefixWord ++ tailWord_962325).sum := by decide
  have hdescent : baseEnd_962325 < baseStart_962325 := by decide
  rcases family_descends (prefixWord ++ tailWord_962325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962353 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_962353 : Nat := 118140960795 + 962353 * 2 ^ 59
def prefixEnd_962353 : Nat := 4983230072969 + 3 ^ 40 * 962353 * 2
def baseEnd_962353 : Nat := 439244131819003131699311

theorem tailTrace_962353 : CollatzResearch.WordTrace tailWord_962353 prefixEnd_962353 439244131819003131699311 := by
  unfold tailWord_962353
  simp only [CollatzResearch.WordTrace]
  refine ⟨35099897482566912652395713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23399931655044608434930475 35099897482566912652395713)
  ·
    refine ⟨26324923111925184489296785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35099897482566912652395713 26324923111925184489296785)
    ·
      refine ⟨19743692333943888366972589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26324923111925184489296785 19743692333943888366972589)
      ·
        refine ⟨7403884625228958137614721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19743692333943888366972589 7403884625228958137614721)
        ·
          refine ⟨5552913468921718603211041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7403884625228958137614721 5552913468921718603211041)
          ·
            refine ⟨4164685101691288952408281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5552913468921718603211041 4164685101691288952408281)
            ·
              refine ⟨3123513826268466714306211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164685101691288952408281 3123513826268466714306211)
              ·
                refine ⟨4685270739402700071459317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123513826268466714306211 4685270739402700071459317)
                ·
                  refine ⟨439244131819003131699311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4685270739402700071459317 439244131819003131699311)
                  ·
                    rfl

theorem cell20_962353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_962353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962353 prefixEnd_962353 := by exact prefixLift 962353
  have htrace : WordTrace (prefixWord ++ tailWord_962353) baseStart_962353 baseEnd_962353 := by
    simpa [prefixWord, tailWord_962353, baseEnd_962353] using wordTrace_append hprefix tailTrace_962353
  have hstable : (prefixWord ++ tailWord_962353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962353).length < 2 ^ (prefixWord ++ tailWord_962353).sum := by decide
  have hdescent : baseEnd_962353 < baseStart_962353 := by decide
  rcases family_descends (prefixWord ++ tailWord_962353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962356 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_962356 : Nat := 118140960795 + 962356 * 2 ^ 59
def prefixEnd_962356 : Nat := 4983230072969 + 3 ^ 40 * 962356 * 2
def baseEnd_962356 : Nat := 439245501100748454599299

theorem tailTrace_962356 : CollatzResearch.WordTrace tailWord_962356 prefixEnd_962356 439245501100748454599299 := by
  unfold tailWord_962356
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550003450778022082377461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23400004601037362776503281 17550003450778022082377461)
  ·
    refine ⟨1645312823510439570222887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17550003450778022082377461 1645312823510439570222887)
    ·
      refine ⟨2467969235265659355334331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645312823510439570222887 2467969235265659355334331)
      ·
        refine ⟨3701953852898489033001497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467969235265659355334331 3701953852898489033001497)
        ·
          refine ⟨2776465389673866774751123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701953852898489033001497 2776465389673866774751123)
          ·
            refine ⟨4164698084510800162126685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776465389673866774751123 4164698084510800162126685)
            ·
              refine ⟨1561761781691550060797507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4164698084510800162126685 1561761781691550060797507)
              ·
                refine ⟨2342642672537325091196261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561761781691550060797507 2342642672537325091196261)
                ·
                  refine ⟨439245501100748454599299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342642672537325091196261 439245501100748454599299)
                  ·
                    rfl

theorem cell20_962356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_962356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962356 prefixEnd_962356 := by exact prefixLift 962356
  have htrace : WordTrace (prefixWord ++ tailWord_962356) baseStart_962356 baseEnd_962356 := by
    simpa [prefixWord, tailWord_962356, baseEnd_962356] using wordTrace_append hprefix tailTrace_962356
  have hstable : (prefixWord ++ tailWord_962356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962356).length < 2 ^ (prefixWord ++ tailWord_962356).sum := by decide
  have hdescent : baseEnd_962356 < baseStart_962356 := by decide
  rcases family_descends (prefixWord ++ tailWord_962356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962366 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_962366 : Nat := 118140960795 + 962366 * 2 ^ 59
def prefixEnd_962366 : Nat := 4983230072969 + 3 ^ 40 * 962366 * 2
def baseEnd_962366 : Nat := 439250065373232864265925

theorem tailTrace_962366 : CollatzResearch.WordTrace tailWord_962366 prefixEnd_962366 439250065373232864265925 := by
  unfold tailWord_962366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4387546453939976984077369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23400247754346543915079301 4387546453939976984077369)
  ·
    refine ⟨3290659840454982738058027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4387546453939976984077369 3290659840454982738058027)
    ·
      refine ⟨4935989760682474107087041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290659840454982738058027 4935989760682474107087041)
      ·
        refine ⟨3701992320511855580315281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4935989760682474107087041 3701992320511855580315281)
        ·
          refine ⟨2776494240383891685236461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701992320511855580315281 2776494240383891685236461)
          ·
            refine ⟨1041185340143959381963673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2776494240383891685236461 1041185340143959381963673)
            ·
              refine ⟨780889005107969536472755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041185340143959381963673 780889005107969536472755)
              ·
                refine ⟨1171333507661954304709133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780889005107969536472755 1171333507661954304709133)
                ·
                  refine ⟨439250065373232864265925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171333507661954304709133 439250065373232864265925)
                  ·
                    rfl

theorem cell20_962366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_962366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962366 prefixEnd_962366 := by exact prefixLift 962366
  have htrace : WordTrace (prefixWord ++ tailWord_962366) baseStart_962366 baseEnd_962366 := by
    simpa [prefixWord, tailWord_962366, baseEnd_962366] using wordTrace_append hprefix tailTrace_962366
  have hstable : (prefixWord ++ tailWord_962366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962366).length < 2 ^ (prefixWord ++ tailWord_962366).sum := by decide
  have hdescent : baseEnd_962366 < baseStart_962366 := by decide
  rcases family_descends (prefixWord ++ tailWord_962366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962408 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_962408 : Nat := 118140960795 + 962408 * 2 ^ 59
def prefixEnd_962408 : Nat := 4983230072969 + 3 ^ 40 * 962408 * 2
def baseEnd_962408 : Nat := 439269235317667384865753

theorem tailTrace_962408 : CollatzResearch.WordTrace tailWord_962408 prefixEnd_962408 439269235317667384865753 := by
  unfold tailWord_962408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550951748683828522823939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23401268998245104697098585 17550951748683828522823939)
  ·
    refine ⟨26326427623025742784235909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17550951748683828522823939 26326427623025742784235909)
    ·
      refine ⟨4936205179317326772044233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26326427623025742784235909 4936205179317326772044233)
      ·
        refine ⟨3702153884487995079033175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4936205179317326772044233 3702153884487995079033175)
        ·
          refine ⟨5553230826731992618549763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702153884487995079033175 5553230826731992618549763)
          ·
            refine ⟨8329846240097988927824645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553230826731992618549763 8329846240097988927824645)
            ·
              refine ⟨1561846170018372923967121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8329846240097988927824645 1561846170018372923967121)
              ·
                refine ⟨1171384627513779692975341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561846170018372923967121 1171384627513779692975341)
                ·
                  refine ⟨439269235317667384865753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171384627513779692975341 439269235317667384865753)
                  ·
                    rfl

theorem cell20_962408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_962408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962408 prefixEnd_962408 := by exact prefixLift 962408
  have htrace : WordTrace (prefixWord ++ tailWord_962408) baseStart_962408 baseEnd_962408 := by
    simpa [prefixWord, tailWord_962408, baseEnd_962408] using wordTrace_append hprefix tailTrace_962408
  have hstable : (prefixWord ++ tailWord_962408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962408).length < 2 ^ (prefixWord ++ tailWord_962408).sum := by decide
  have hdescent : baseEnd_962408 < baseStart_962408 := by decide
  rcases family_descends (prefixWord ++ tailWord_962408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962436 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_962436 : Nat := 118140960795 + 962436 * 2 ^ 59
def prefixEnd_962436 : Nat := 4983230072969 + 3 ^ 40 * 962436 * 2
def baseEnd_962436 : Nat := 439282015280623731932305

theorem tailTrace_962436 : CollatzResearch.WordTrace tailWord_962436 prefixEnd_962436 439282015280623731932305 := by
  unfold tailWord_962436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17551462370633108913833581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23401949827510811885111441 17551462370633108913833581)
  ·
    refine ⟨6581798388987415842687593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17551462370633108913833581 6581798388987415842687593)
    ·
      refine ⟨4936348791740561882015695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6581798388987415842687593 4936348791740561882015695)
      ·
        refine ⟨7404523187610842823023543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4936348791740561882015695 7404523187610842823023543)
        ·
          refine ⟨11106784781416264234535315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404523187610842823023543 11106784781416264234535315)
          ·
            refine ⟨16660177172124396351802973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11106784781416264234535315 16660177172124396351802973)
            ·
              refine ⟨6247566439546648631926115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16660177172124396351802973 6247566439546648631926115)
              ·
                refine ⟨9371349659319972947889173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247566439546648631926115 9371349659319972947889173)
                ·
                  refine ⟨439282015280623731932305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9371349659319972947889173 439282015280623731932305)
                  ·
                    rfl

theorem cell20_962436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_962436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962436 prefixEnd_962436 := by exact prefixLift 962436
  have htrace : WordTrace (prefixWord ++ tailWord_962436) baseStart_962436 baseEnd_962436 := by
    simpa [prefixWord, tailWord_962436, baseEnd_962436] using wordTrace_append hprefix tailTrace_962436
  have hstable : (prefixWord ++ tailWord_962436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962436).length < 2 ^ (prefixWord ++ tailWord_962436).sum := by decide
  have hdescent : baseEnd_962436 < baseStart_962436 := by decide
  rcases family_descends (prefixWord ++ tailWord_962436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962439 : List Nat := [1, 1, 4, 2, 4, 1, 3, 4]
def baseStart_962439 : Nat := 118140960795 + 962439 * 2 ^ 59
def prefixEnd_962439 : Nat := 4983230072969 + 3 ^ 40 * 962439 * 2
def baseEnd_962439 : Nat := 146427794854123018277431

theorem tailTrace_962439 : CollatzResearch.WordTrace tailWord_962439 prefixEnd_962439 146427794854123018277431 := by
  unfold tailWord_962439
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103034160255349340026371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23402022773503566226684247 35103034160255349340026371)
  ·
    refine ⟨52654551240383024010039557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35103034160255349340026371 52654551240383024010039557)
    ·
      refine ⟨9872728357571817001882417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52654551240383024010039557 9872728357571817001882417)
      ·
        refine ⟨7404546268178862751411813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9872728357571817001882417 7404546268178862751411813)
        ·
          refine ⟨1388352425283536765889715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7404546268178862751411813 1388352425283536765889715)
          ·
            refine ⟨2082528637925305148834573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388352425283536765889715 2082528637925305148834573)
            ·
              refine ⟨780948239221989430812965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2082528637925305148834573 780948239221989430812965)
              ·
                refine ⟨146427794854123018277431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780948239221989430812965 146427794854123018277431)
                ·
                  rfl

theorem cell20_962439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_962439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962439 prefixEnd_962439 := by exact prefixLift 962439
  have htrace : WordTrace (prefixWord ++ tailWord_962439) baseStart_962439 baseEnd_962439 := by
    simpa [prefixWord, tailWord_962439, baseEnd_962439] using wordTrace_append hprefix tailTrace_962439
  have hstable : (prefixWord ++ tailWord_962439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962439).length < 2 ^ (prefixWord ++ tailWord_962439).sum := by decide
  have hdescent : baseEnd_962439 < baseStart_962439 := by decide
  rcases family_descends (prefixWord ++ tailWord_962439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962460 : List Nat := [2, 2, 3, 3, 1, 2, 7]
def baseStart_962460 : Nat := 118140960795 + 962460 * 2 ^ 59
def prefixEnd_962460 : Nat := 4983230072969 + 3 ^ 40 * 962460 * 2
def baseEnd_962460 : Nat := 48810329948287368348023

theorem tailTrace_962460 : CollatzResearch.WordTrace tailWord_962460 prefixEnd_962460 48810329948287368348023 := by
  unfold tailWord_962460
  simp only [CollatzResearch.WordTrace]
  refine ⟨17551900046589634963270417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23402533395452846617693889 17551900046589634963270417)
  ·
    refine ⟨13163925034942226222452813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17551900046589634963270417 13163925034942226222452813)
    ·
      refine ⟨4936471888103334833419805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13163925034942226222452813 4936471888103334833419805)
      ·
        refine ⟨1851176958038750562532427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4936471888103334833419805 1851176958038750562532427)
        ·
          refine ⟨2776765437058125843798641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851176958038750562532427 2776765437058125843798641)
          ·
            refine ⟨2082574077793594382848981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776765437058125843798641 2082574077793594382848981)
            ·
              refine ⟨48810329948287368348023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2082574077793594382848981 48810329948287368348023)
              ·
                rfl

theorem cell20_962460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_962460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962460 prefixEnd_962460 := by exact prefixLift 962460
  have htrace : WordTrace (prefixWord ++ tailWord_962460) baseStart_962460 baseEnd_962460 := by
    simpa [prefixWord, tailWord_962460, baseEnd_962460] using wordTrace_append hprefix tailTrace_962460
  have hstable : (prefixWord ++ tailWord_962460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962460).length < 2 ^ (prefixWord ++ tailWord_962460).sum := by decide
  have hdescent : baseEnd_962460 < baseStart_962460 := by decide
  rcases family_descends (prefixWord ++ tailWord_962460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962463 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 3]
def baseStart_962463 : Nat := 118140960795 + 962463 * 2 ^ 59
def prefixEnd_962463 : Nat := 4983230072969 + 3 ^ 40 * 962463 * 2
def baseEnd_962463 : Nat := 439294338816331638032195

theorem tailTrace_962463 : CollatzResearch.WordTrace tailWord_962463 prefixEnd_962463 439294338816331638032195 := by
  unfold tailWord_962463
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103909512168401438900043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23402606341445600959266695 35103909512168401438900043)
  ·
    refine ⟨52655864268252602158350065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35103909512168401438900043 52655864268252602158350065)
    ·
      refine ⟨39491898201189451618762549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52655864268252602158350065 39491898201189451618762549)
      ·
        refine ⟨3702365456361511089258989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39491898201189451618762549 3702365456361511089258989)
        ·
          refine ⟨1388387046135566658472121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3702365456361511089258989 1388387046135566658472121)
          ·
            refine ⟨1041290284601674993854091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388387046135566658472121 1041290284601674993854091)
            ·
              refine ⟨1561935426902512490781137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041290284601674993854091 1561935426902512490781137)
              ·
                refine ⟨1171451570176884368085853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561935426902512490781137 1171451570176884368085853)
                ·
                  refine ⟨439294338816331638032195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171451570176884368085853 439294338816331638032195)
                  ·
                    rfl

theorem cell20_962463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_962463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962463 prefixEnd_962463 := by exact prefixLift 962463
  have htrace : WordTrace (prefixWord ++ tailWord_962463) baseStart_962463 baseEnd_962463 := by
    simpa [prefixWord, tailWord_962463, baseEnd_962463] using wordTrace_append hprefix tailTrace_962463
  have hstable : (prefixWord ++ tailWord_962463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962463).length < 2 ^ (prefixWord ++ tailWord_962463).sum := by decide
  have hdescent : baseEnd_962463 < baseStart_962463 := by decide
  rcases family_descends (prefixWord ++ tailWord_962463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962508 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 2]
def baseStart_962508 : Nat := 118140960795 + 962508 * 2 ^ 59
def prefixEnd_962508 : Nat := 4983230072969 + 3 ^ 40 * 962508 * 2
def baseEnd_962508 : Nat := 439314878042511481532011

theorem tailTrace_962508 : CollatzResearch.WordTrace tailWord_962508 prefixEnd_962508 439314878042511481532011 := by
  unfold tailWord_962508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552775398502687062144089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23403700531336916082858785 17552775398502687062144089)
  ·
    refine ⟨13164581548877015296608067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17552775398502687062144089 13164581548877015296608067)
    ·
      refine ⟨19746872323315522944912101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13164581548877015296608067 19746872323315522944912101)
      ·
        refine ⟨3702538560621660552171019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19746872323315522944912101 3702538560621660552171019)
        ·
          refine ⟨5553807840932490828256529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702538560621660552171019 5553807840932490828256529)
          ·
            refine ⟨4165355880699368121192397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5553807840932490828256529 4165355880699368121192397)
            ·
              refine ⟨1562008455262263045447149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4165355880699368121192397 1562008455262263045447149)
              ·
                refine ⟨585753170723348642042681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562008455262263045447149 585753170723348642042681)
                ·
                  refine ⟨439314878042511481532011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585753170723348642042681 439314878042511481532011)
                  ·
                    rfl

theorem cell20_962508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_962508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962508 prefixEnd_962508 := by exact prefixLift 962508
  have htrace : WordTrace (prefixWord ++ tailWord_962508) baseStart_962508 baseEnd_962508 := by
    simpa [prefixWord, tailWord_962508, baseEnd_962508] using wordTrace_append hprefix tailTrace_962508
  have hstable : (prefixWord ++ tailWord_962508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962508).length < 2 ^ (prefixWord ++ tailWord_962508).sum := by decide
  have hdescent : baseEnd_962508 < baseStart_962508 := by decide
  rcases family_descends (prefixWord ++ tailWord_962508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962525 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 4]
def baseStart_962525 : Nat := 118140960795 + 962525 * 2 ^ 59
def prefixEnd_962525 : Nat := 4983230072969 + 3 ^ 40 * 962525 * 2
def baseEnd_962525 : Nat := 439322637305734977965275

theorem tailTrace_962525 : CollatzResearch.WordTrace tailWord_962525 prefixEnd_962525 439322637305734977965275 := by
  unfold tailWord_962525
  simp only [CollatzResearch.WordTrace]
  refine ⟨35106170837943786027657029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23404113891962524018438019 35106170837943786027657029)
  ·
    refine ⟨6582407032114459880185693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35106170837943786027657029 6582407032114459880185693)
    ·
      refine ⟨2468402637042922455069635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6582407032114459880185693 2468402637042922455069635)
      ·
        refine ⟨3702603955564383682604453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468402637042922455069635 3702603955564383682604453)
        ·
          refine ⟨694238241668321940488335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3702603955564383682604453 694238241668321940488335)
          ·
            refine ⟨1041357362502482910732503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694238241668321940488335 1041357362502482910732503)
            ·
              refine ⟨1562036043753724366098755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041357362502482910732503 1562036043753724366098755)
              ·
                refine ⟨2343054065630586549148133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562036043753724366098755 2343054065630586549148133)
                ·
                  refine ⟨439322637305734977965275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2343054065630586549148133 439322637305734977965275)
                  ·
                    rfl

theorem cell20_962525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_962525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962525 prefixEnd_962525 := by exact prefixLift 962525
  have htrace : WordTrace (prefixWord ++ tailWord_962525) baseStart_962525 baseEnd_962525 := by
    simpa [prefixWord, tailWord_962525, baseEnd_962525] using wordTrace_append hprefix tailTrace_962525
  have hstable : (prefixWord ++ tailWord_962525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962525).length < 2 ^ (prefixWord ++ tailWord_962525).sum := by decide
  have hdescent : baseEnd_962525 < baseStart_962525 := by decide
  rcases family_descends (prefixWord ++ tailWord_962525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962529 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 2]
def baseStart_962529 : Nat := 118140960795 + 962529 * 2 ^ 59
def prefixEnd_962529 : Nat := 4983230072969 + 3 ^ 40 * 962529 * 2
def baseEnd_962529 : Nat := 439324463014728741831925

theorem tailTrace_962529 : CollatzResearch.WordTrace tailWord_962529 prefixEnd_962529 439324463014728741831925 := by
  unfold tailWord_962529
  simp only [CollatzResearch.WordTrace]
  refine ⟨35106316729929294710802641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23404211153286196473868427 35106316729929294710802641)
  ·
    refine ⟨26329737547446971033101981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35106316729929294710802641 26329737547446971033101981)
    ·
      refine ⟨9873651580292614137413243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26329737547446971033101981 9873651580292614137413243)
      ·
        refine ⟨14810477370438921206119865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9873651580292614137413243 14810477370438921206119865)
        ·
          refine ⟨11107858027829190904589899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14810477370438921206119865 11107858027829190904589899)
          ·
            refine ⟨16661787041743786356884849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11107858027829190904589899 16661787041743786356884849)
            ·
              refine ⟨12496340281307839767663637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16661787041743786356884849 12496340281307839767663637)
              ·
                refine ⟨585765950686304989109233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12496340281307839767663637 585765950686304989109233)
                ·
                  refine ⟨439324463014728741831925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585765950686304989109233 439324463014728741831925)
                  ·
                    rfl

theorem cell20_962529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_962529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962529 prefixEnd_962529 := by exact prefixLift 962529
  have htrace : WordTrace (prefixWord ++ tailWord_962529) baseStart_962529 baseEnd_962529 := by
    simpa [prefixWord, tailWord_962529, baseEnd_962529] using wordTrace_append hprefix tailTrace_962529
  have hstable : (prefixWord ++ tailWord_962529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962529).length < 2 ^ (prefixWord ++ tailWord_962529).sum := by decide
  have hdescent : baseEnd_962529 < baseStart_962529 := by decide
  rcases family_descends (prefixWord ++ tailWord_962529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962543 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_962543 : Nat := 118140960795 + 962543 * 2 ^ 59
def prefixEnd_962543 : Nat := 4983230072969 + 3 ^ 40 * 962543 * 2
def baseEnd_962543 : Nat := 439330852996206915365201

theorem tailTrace_962543 : CollatzResearch.WordTrace tailWord_962543 prefixEnd_962543 439330852996206915365201 := by
  unfold tailWord_962543
  simp only [CollatzResearch.WordTrace]
  refine ⟨35106827351878575101812283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23404551567919050067874855 35106827351878575101812283)
  ·
    refine ⟨52660241027817862652718425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35106827351878575101812283 52660241027817862652718425)
    ·
      refine ⟨39495180770863396989538819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52660241027817862652718425 39495180770863396989538819)
      ·
        refine ⟨59242771156295095484308229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39495180770863396989538819 59242771156295095484308229)
        ·
          refine ⟨11108019591805330403307793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59242771156295095484308229 11108019591805330403307793)
          ·
            refine ⟨8331014693853997802480845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11108019591805330403307793 8331014693853997802480845)
            ·
              refine ⟨3124130510195249175930317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8331014693853997802480845 3124130510195249175930317)
              ·
                refine ⟨1171548941323218440973869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124130510195249175930317 1171548941323218440973869)
                ·
                  refine ⟨439330852996206915365201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171548941323218440973869 439330852996206915365201)
                  ·
                    rfl

theorem cell20_962543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_962543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962543 prefixEnd_962543 := by exact prefixLift 962543
  have htrace : WordTrace (prefixWord ++ tailWord_962543) baseStart_962543 baseEnd_962543 := by
    simpa [prefixWord, tailWord_962543, baseEnd_962543] using wordTrace_append hprefix tailTrace_962543
  have hstable : (prefixWord ++ tailWord_962543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962543).length < 2 ^ (prefixWord ++ tailWord_962543).sum := by decide
  have hdescent : baseEnd_962543 < baseStart_962543 := by decide
  rcases family_descends (prefixWord ++ tailWord_962543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962557 : List Nat := [1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_962557 : Nat := 118140960795 + 962557 * 2 ^ 59
def prefixEnd_962557 : Nat := 4983230072969 + 3 ^ 40 * 962557 * 2
def baseEnd_962557 : Nat := 146445747659228362966159

theorem tailTrace_962557 : CollatzResearch.WordTrace tailWord_962557 prefixEnd_962557 146445747659228362966159 := by
  unfold tailWord_962557
  simp only [CollatzResearch.WordTrace]
  refine ⟨35107337973827855492821925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23404891982551903661881283 35107337973827855492821925)
  ·
    refine ⟨6582625870092722904904111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35107337973827855492821925 6582625870092722904904111)
    ·
      refine ⟨9873938805139084357356167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6582625870092722904904111 9873938805139084357356167)
      ·
        refine ⟨14810908207708626536034251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9873938805139084357356167 14810908207708626536034251)
        ·
          refine ⟨22216362311562939804051377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14810908207708626536034251 22216362311562939804051377)
          ·
            refine ⟨16662271733672204853038533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22216362311562939804051377 16662271733672204853038533)
            ·
              refine ⟨3124175950063538409944725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16662271733672204853038533 3124175950063538409944725)
              ·
                refine ⟨146445747659228362966159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3124175950063538409944725 146445747659228362966159)
                ·
                  rfl

theorem cell20_962557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_962557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962557 prefixEnd_962557 := by exact prefixLift 962557
  have htrace : WordTrace (prefixWord ++ tailWord_962557) baseStart_962557 baseEnd_962557 := by
    simpa [prefixWord, tailWord_962557, baseEnd_962557] using wordTrace_append hprefix tailTrace_962557
  have hstable : (prefixWord ++ tailWord_962557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962557).length < 2 ^ (prefixWord ++ tailWord_962557).sum := by decide
  have hdescent : baseEnd_962557 < baseStart_962557 := by decide
  rcases family_descends (prefixWord ++ tailWord_962557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962573 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 3]
def baseStart_962573 : Nat := 118140960795 + 962573 * 2 ^ 59
def prefixEnd_962573 : Nat := 4983230072969 + 3 ^ 40 * 962573 * 2
def baseEnd_962573 : Nat := 439344545813660144365079

theorem tailTrace_962573 : CollatzResearch.WordTrace tailWord_962573 prefixEnd_962573 439344545813660144365079 := by
  unfold tailWord_962573
  simp only [CollatzResearch.WordTrace]
  refine ⟨35107921541769890225404373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23405281027846593483602915 35107921541769890225404373)
  ·
    refine ⟨822841911135231802157915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35107921541769890225404373 822841911135231802157915)
    ·
      refine ⟨1234262866702847703236873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822841911135231802157915 1234262866702847703236873)
      ·
        refine ⟨925697150027135777427655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1234262866702847703236873 925697150027135777427655)
        ·
          refine ⟨1388545725040703666141483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925697150027135777427655 1388545725040703666141483)
          ·
            refine ⟨2082818587561055499212225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388545725040703666141483 2082818587561055499212225)
            ·
              refine ⟨1562113940670791624409169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082818587561055499212225 1562113940670791624409169)
              ·
                refine ⟨1171585455503093718306877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562113940670791624409169 1171585455503093718306877)
                ·
                  refine ⟨439344545813660144365079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171585455503093718306877 439344545813660144365079)
                  ·
                    rfl

theorem cell20_962573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_962573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962573 prefixEnd_962573 := by exact prefixLift 962573
  have htrace : WordTrace (prefixWord ++ tailWord_962573) baseStart_962573 baseEnd_962573 := by
    simpa [prefixWord, tailWord_962573, baseEnd_962573] using wordTrace_append hprefix tailTrace_962573
  have hstable : (prefixWord ++ tailWord_962573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962573).length < 2 ^ (prefixWord ++ tailWord_962573).sum := by decide
  have hdescent : baseEnd_962573 < baseStart_962573 := by decide
  rcases family_descends (prefixWord ++ tailWord_962573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962580 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 2]
def baseStart_962580 : Nat := 118140960795 + 962580 * 2 ^ 59
def prefixEnd_962580 : Nat := 4983230072969 + 3 ^ 40 * 962580 * 2
def baseEnd_962580 : Nat := 439347740804399231131717

theorem tailTrace_962580 : CollatzResearch.WordTrace tailWord_962580 prefixEnd_962580 439347740804399231131717 := by
  unfold tailWord_962580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554088426372265210454597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23405451235163020280606129 17554088426372265210454597)
  ·
    refine ⟨3291391579944799726960237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17554088426372265210454597 3291391579944799726960237)
    ·
      refine ⟨1234271842479299897610089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3291391579944799726960237 1234271842479299897610089)
      ·
        refine ⟨925703881859474923207567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1234271842479299897610089 925703881859474923207567)
        ·
          refine ⟨1388555822789212384811351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925703881859474923207567 1388555822789212384811351)
          ·
            refine ⟨2082833734183818577217027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388555822789212384811351 2082833734183818577217027)
            ·
              refine ⟨3124250601275727865825541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082833734183818577217027 3124250601275727865825541)
              ·
                refine ⟨585796987739198974842289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3124250601275727865825541 585796987739198974842289)
                ·
                  refine ⟨439347740804399231131717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585796987739198974842289 439347740804399231131717)
                  ·
                    rfl

theorem cell20_962580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_962580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962580 prefixEnd_962580 := by exact prefixLift 962580
  have htrace : WordTrace (prefixWord ++ tailWord_962580) baseStart_962580 baseEnd_962580 := by
    simpa [prefixWord, tailWord_962580, baseEnd_962580] using wordTrace_append hprefix tailTrace_962580
  have hstable : (prefixWord ++ tailWord_962580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962580).length < 2 ^ (prefixWord ++ tailWord_962580).sum := by decide
  have hdescent : baseEnd_962580 < baseStart_962580 := by decide
  rcases family_descends (prefixWord ++ tailWord_962580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962671 : List Nat := [1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_962671 : Nat := 118140960795 + 962671 * 2 ^ 59
def prefixEnd_962671 : Nat := 4983230072969 + 3 ^ 40 * 962671 * 2
def baseEnd_962671 : Nat := 146463091894669119699337

theorem tailTrace_962671 : CollatzResearch.WordTrace tailWord_962671 prefixEnd_962671 146463091894669119699337 := by
  unfold tailWord_962671
  simp only [CollatzResearch.WordTrace]
  refine ⟨35111495895414852962471867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23407663930276568641647911 35111495895414852962471867)
  ·
    refine ⟨52667243843122279443707801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35111495895414852962471867 52667243843122279443707801)
    ·
      refine ⟨39500432882341709582780851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52667243843122279443707801 39500432882341709582780851)
      ·
        refine ⟨59250649323512564374171277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39500432882341709582780851 59250649323512564374171277)
        ·
          refine ⟨22218993496317211640314229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59250649323512564374171277 22218993496317211640314229)
          ·
            refine ⟨2083030640279738591279459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22218993496317211640314229 2083030640279738591279459)
            ·
              refine ⟨3124545960419607886919189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083030640279738591279459 3124545960419607886919189)
              ·
                refine ⟨146463091894669119699337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3124545960419607886919189 146463091894669119699337)
                ·
                  rfl

theorem cell20_962671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_962671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962671 prefixEnd_962671 := by exact prefixLift 962671
  have htrace : WordTrace (prefixWord ++ tailWord_962671) baseStart_962671 baseEnd_962671 := by
    simpa [prefixWord, tailWord_962671, baseEnd_962671] using wordTrace_append hprefix tailTrace_962671
  have hstable : (prefixWord ++ tailWord_962671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962671).length < 2 ^ (prefixWord ++ tailWord_962671).sum := by decide
  have hdescent : baseEnd_962671 < baseStart_962671 := by decide
  rcases family_descends (prefixWord ++ tailWord_962671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962709 : List Nat := [1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_962709 : Nat := 118140960795 + 962709 * 2 ^ 59
def prefixEnd_962709 : Nat := 4983230072969 + 3 ^ 40 * 962709 * 2
def baseEnd_962709 : Nat := 146468873306482705277063

theorem tailTrace_962709 : CollatzResearch.WordTrace tailWord_962709 prefixEnd_962709 146468873306482705277063 := by
  unfold tailWord_962709
  simp only [CollatzResearch.WordTrace]
  refine ⟨35112881869277185452355181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23408587912851456968236787 35112881869277185452355181)
  ·
    refine ⟨13167330700978944544633193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35112881869277185452355181 13167330700978944544633193)
    ·
      refine ⟨9875498025734208408474895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13167330700978944544633193 9875498025734208408474895)
      ·
        refine ⟨14813247038601312612712343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9875498025734208408474895 14813247038601312612712343)
        ·
          refine ⟨22219870557901968919068515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813247038601312612712343 22219870557901968919068515)
          ·
            refine ⟨33329805836852953378602773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22219870557901968919068515 33329805836852953378602773)
            ·
              refine ⟨1562334648602482189622005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33329805836852953378602773 1562334648602482189622005)
              ·
                refine ⟨146468873306482705277063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1562334648602482189622005 146468873306482705277063)
                ·
                  rfl

theorem cell20_962709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_962709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962709 prefixEnd_962709 := by exact prefixLift 962709
  have htrace : WordTrace (prefixWord ++ tailWord_962709) baseStart_962709 baseEnd_962709 := by
    simpa [prefixWord, tailWord_962709, baseEnd_962709] using wordTrace_append hprefix tailTrace_962709
  have hstable : (prefixWord ++ tailWord_962709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962709).length < 2 ^ (prefixWord ++ tailWord_962709).sum := by decide
  have hdescent : baseEnd_962709 < baseStart_962709 := by decide
  rcases family_descends (prefixWord ++ tailWord_962709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962712 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_962712 : Nat := 118140960795 + 962712 * 2 ^ 59
def prefixEnd_962712 : Nat := 4983230072969 + 3 ^ 40 * 962712 * 2
def baseEnd_962712 : Nat := 439407989201193438731177

theorem tailTrace_962712 : CollatzResearch.WordTrace tailWord_962712 prefixEnd_962712 439407989201193438731177 := by
  unfold tailWord_962712
  simp only [CollatzResearch.WordTrace]
  refine ⟨17556495644133158482357195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23408660858844211309809593 17556495644133158482357195)
  ·
    refine ⟨26334743466199737723535793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17556495644133158482357195 26334743466199737723535793)
    ·
      refine ⟨19751057599649803292651845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26334743466199737723535793 19751057599649803292651845)
      ·
        refine ⟨3703323299934338117372221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19751057599649803292651845 3703323299934338117372221)
        ·
          refine ⟨1388746237475376794014583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3703323299934338117372221 1388746237475376794014583)
          ·
            refine ⟨2083119356213065191021875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388746237475376794014583 2083119356213065191021875)
            ·
              refine ⟨3124679034319597786532813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083119356213065191021875 3124679034319597786532813)
              ·
                refine ⟨1171754637869849169949805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124679034319597786532813 1171754637869849169949805)
                ·
                  refine ⟨439407989201193438731177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171754637869849169949805 439407989201193438731177)
                  ·
                    rfl

theorem cell20_962712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_962712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962712 prefixEnd_962712 := by exact prefixLift 962712
  have htrace : WordTrace (prefixWord ++ tailWord_962712) baseStart_962712 baseEnd_962712 := by
    simpa [prefixWord, tailWord_962712, baseEnd_962712] using wordTrace_append hprefix tailTrace_962712
  have hstable : (prefixWord ++ tailWord_962712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962712).length < 2 ^ (prefixWord ++ tailWord_962712).sum := by decide
  have hdescent : baseEnd_962712 < baseStart_962712 := by decide
  rcases family_descends (prefixWord ++ tailWord_962712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962753 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 2]
def baseStart_962753 : Nat := 118140960795 + 962753 * 2 ^ 59
def prefixEnd_962753 : Nat := 4983230072969 + 3 ^ 40 * 962753 * 2
def baseEnd_962753 : Nat := 439426702718379518364343

theorem tailTrace_962753 : CollatzResearch.WordTrace tailWord_962753 prefixEnd_962753 439426702718379518364343 := by
  unfold tailWord_962753
  simp only [CollatzResearch.WordTrace]
  refine ⟨35114486681117780966956913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23409657787411853977971275 35114486681117780966956913)
  ·
    refine ⟨26335865010838335725217685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35114486681117780966956913 26335865010838335725217685)
    ·
      refine ⟨1234493672383046987119579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26335865010838335725217685 1234493672383046987119579)
      ·
        refine ⟨1851740508574570480679369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234493672383046987119579 1851740508574570480679369)
        ·
          refine ⟨1388805381430927860509527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851740508574570480679369 1388805381430927860509527)
          ·
            refine ⟨2083208072146391790764291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388805381430927860509527 2083208072146391790764291)
            ·
              refine ⟨3124812108219587686146437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083208072146391790764291 3124812108219587686146437)
              ·
                refine ⟨585902270291172691152457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3124812108219587686146437 585902270291172691152457)
                ·
                  refine ⟨439426702718379518364343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585902270291172691152457 439426702718379518364343)
                  ·
                    rfl

theorem cell20_962753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_962753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962753 prefixEnd_962753 := by exact prefixLift 962753
  have htrace : WordTrace (prefixWord ++ tailWord_962753) baseStart_962753 baseEnd_962753 := by
    simpa [prefixWord, tailWord_962753, baseEnd_962753] using wordTrace_append hprefix tailTrace_962753
  have hstable : (prefixWord ++ tailWord_962753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962753).length < 2 ^ (prefixWord ++ tailWord_962753).sum := by decide
  have hdescent : baseEnd_962753 < baseStart_962753 := by decide
  rcases family_descends (prefixWord ++ tailWord_962753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962774 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_962774 : Nat := 118140960795 + 962774 * 2 ^ 59
def prefixEnd_962774 : Nat := 4983230072969 + 3 ^ 40 * 962774 * 2
def baseEnd_962774 : Nat := 439436287690596778664257

theorem tailTrace_962774 : CollatzResearch.WordTrace tailWord_962774 prefixEnd_962774 439436287690596778664257 := by
  unfold tailWord_962774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194703288377606347091961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23410168409361134368980917 2194703288377606347091961)
  ·
    refine ⟨1646027466283204760318971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2194703288377606347091961 1646027466283204760318971)
    ·
      refine ⟨2469041199424807140478457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646027466283204760318971 2469041199424807140478457)
      ·
        refine ⟨1851780899568605355358843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469041199424807140478457 1851780899568605355358843)
        ·
          refine ⟨2777671349352908033038265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851780899568605355358843 2777671349352908033038265)
          ·
            refine ⟨2083253512014681024778699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777671349352908033038265 2083253512014681024778699)
            ·
              refine ⟨3124880268022021537168049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083253512014681024778699 3124880268022021537168049)
              ·
                refine ⟨2343660201016516152876037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124880268022021537168049 2343660201016516152876037)
                ·
                  refine ⟨439436287690596778664257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2343660201016516152876037 439436287690596778664257)
                  ·
                    rfl

theorem cell20_962774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_962774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962774 prefixEnd_962774 := by exact prefixLift 962774
  have htrace : WordTrace (prefixWord ++ tailWord_962774) baseStart_962774 baseEnd_962774 := by
    simpa [prefixWord, tailWord_962774, baseEnd_962774] using wordTrace_append hprefix tailTrace_962774
  have hstable : (prefixWord ++ tailWord_962774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962774).length < 2 ^ (prefixWord ++ tailWord_962774).sum := by decide
  have hdescent : baseEnd_962774 < baseStart_962774 := by decide
  rcases family_descends (prefixWord ++ tailWord_962774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962781 : List Nat := [1, 4, 3, 2, 1, 2, 3, 4]
def baseStart_962781 : Nat := 118140960795 + 962781 * 2 ^ 59
def prefixEnd_962781 : Nat := 4983230072969 + 3 ^ 40 * 962781 * 2
def baseEnd_962781 : Nat := 146479827560445288476965

theorem tailTrace_962781 : CollatzResearch.WordTrace tailWord_962781 prefixEnd_962781 146479827560445288476965 := by
  unfold tailWord_962781
  simp only [CollatzResearch.WordTrace]
  refine ⟨35115507925016341748976197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23410338616677561165984131 35115507925016341748976197)
  ·
    refine ⟨6584157735940564077933037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35115507925016341748976197 6584157735940564077933037)
    ·
      refine ⟨2469059150977711529224889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6584157735940564077933037 2469059150977711529224889)
      ·
        refine ⟨1851794363233283646918667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469059150977711529224889 1851794363233283646918667)
        ·
          refine ⟨2777691544849925470378001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851794363233283646918667 2777691544849925470378001)
          ·
            refine ⟨2083268658637444102783501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777691544849925470378001 2083268658637444102783501)
            ·
              refine ⟨781225746989041538543813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2083268658637444102783501 781225746989041538543813)
              ·
                refine ⟨146479827560445288476965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781225746989041538543813 146479827560445288476965)
                ·
                  rfl

theorem cell20_962781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_962781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962781 prefixEnd_962781 := by exact prefixLift 962781
  have htrace : WordTrace (prefixWord ++ tailWord_962781) baseStart_962781 baseEnd_962781 := by
    simpa [prefixWord, tailWord_962781, baseEnd_962781] using wordTrace_append hprefix tailTrace_962781
  have hstable : (prefixWord ++ tailWord_962781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962781).length < 2 ^ (prefixWord ++ tailWord_962781).sum := by decide
  have hdescent : baseEnd_962781 < baseStart_962781 := by decide
  rcases family_descends (prefixWord ++ tailWord_962781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962795 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 2]
def baseStart_962795 : Nat := 118140960795 + 962795 * 2 ^ 59
def prefixEnd_962795 : Nat := 4983230072969 + 3 ^ 40 * 962795 * 2
def baseEnd_962795 : Nat := 439445872662814038964171

theorem tailTrace_962795 : CollatzResearch.WordTrace tailWord_962795 prefixEnd_962795 439445872662814038964171 := by
  unfold tailWord_962795
  simp only [CollatzResearch.WordTrace]
  refine ⟨35116018546965622139985839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23410679031310414759990559 35116018546965622139985839)
  ·
    refine ⟨52674027820448433209978759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35116018546965622139985839 52674027820448433209978759)
    ·
      refine ⟨79011041730672649814968139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52674027820448433209978759 79011041730672649814968139)
      ·
        refine ⟨118516562596008974722452209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79011041730672649814968139 118516562596008974722452209)
        ·
          refine ⟨88887421947006731041839157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118516562596008974722452209 88887421947006731041839157)
          ·
            refine ⟨8333195807531881035172421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88887421947006731041839157 8333195807531881035172421)
            ·
              refine ⟨1562474213912227694094829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8333195807531881035172421 1562474213912227694094829)
              ·
                refine ⟨585927830217085385285561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562474213912227694094829 585927830217085385285561)
                ·
                  refine ⟨439445872662814038964171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585927830217085385285561 439445872662814038964171)
                  ·
                    rfl

theorem cell20_962795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 2].length) (baseStart_962795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962795 prefixEnd_962795 := by exact prefixLift 962795
  have htrace : WordTrace (prefixWord ++ tailWord_962795) baseStart_962795 baseEnd_962795 := by
    simpa [prefixWord, tailWord_962795, baseEnd_962795] using wordTrace_append hprefix tailTrace_962795
  have hstable : (prefixWord ++ tailWord_962795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962795).length < 2 ^ (prefixWord ++ tailWord_962795).sum := by decide
  have hdescent : baseEnd_962795 < baseStart_962795 := by decide
  rcases family_descends (prefixWord ++ tailWord_962795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962846 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_962846 : Nat := 118140960795 + 962846 * 2 ^ 59
def prefixEnd_962846 : Nat := 4983230072969 + 3 ^ 40 * 962846 * 2
def baseEnd_962846 : Nat := 439469150452484528263963

theorem tailTrace_962846 : CollatzResearch.WordTrace tailWord_962846 prefixEnd_962846 439469150452484528263963 := by
  unfold tailWord_962846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389734833722607231261549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23411919113187238566728261 4389734833722607231261549)
  ·
    refine ⟨1646150562645977711723081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4389734833722607231261549 1646150562645977711723081)
    ·
      refine ⟨1234612921984483283792311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1646150562645977711723081 1234612921984483283792311)
      ·
        refine ⟨1851919382976724925688467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234612921984483283792311 1851919382976724925688467)
        ·
          refine ⟨2777879074465087388532701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851919382976724925688467 2777879074465087388532701)
          ·
            refine ⟨1041704652924407770699763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2777879074465087388532701 1041704652924407770699763)
            ·
              refine ⟨1562556979386611656049645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041704652924407770699763 1562556979386611656049645)
              ·
                refine ⟨585958867269979371018617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562556979386611656049645 585958867269979371018617)
                ·
                  refine ⟨439469150452484528263963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585958867269979371018617 439469150452484528263963)
                  ·
                    rfl

theorem cell20_962846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_962846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962846 prefixEnd_962846 := by exact prefixLift 962846
  have htrace : WordTrace (prefixWord ++ tailWord_962846) baseStart_962846 baseEnd_962846 := by
    simpa [prefixWord, tailWord_962846, baseEnd_962846] using wordTrace_append hprefix tailTrace_962846
  have hstable : (prefixWord ++ tailWord_962846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962846).length < 2 ^ (prefixWord ++ tailWord_962846).sum := by decide
  have hdescent : baseEnd_962846 < baseStart_962846 := by decide
  rcases family_descends (prefixWord ++ tailWord_962846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962850 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_962850 : Nat := 118140960795 + 962850 * 2 ^ 59
def prefixEnd_962850 : Nat := 4983230072969 + 3 ^ 40 * 962850 * 2
def baseEnd_962850 : Nat := 439470976161478292130613

theorem tailTrace_962850 : CollatzResearch.WordTrace tailWord_962850 prefixEnd_962850 439470976161478292130613 := by
  unfold tailWord_962850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8779506140441591633309501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23412016374510911022158669 8779506140441591633309501)
  ·
    refine ⟨3292314802665596862491063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8779506140441591633309501 3292314802665596862491063)
    ·
      refine ⟨4938472203998395293736595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292314802665596862491063 4938472203998395293736595)
      ·
        refine ⟨7407708305997592940604893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938472203998395293736595 7407708305997592940604893)
        ·
          refine ⟨2777890614749097352726835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7407708305997592940604893 2777890614749097352726835)
          ·
            refine ⟨4166835922123646029090253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777890614749097352726835 4166835922123646029090253)
            ·
              refine ⟨1562563470796367260908845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4166835922123646029090253 1562563470796367260908845)
              ·
                refine ⟨585961301548637722840817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562563470796367260908845 585961301548637722840817)
                ·
                  refine ⟨439470976161478292130613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585961301548637722840817 439470976161478292130613)
                  ·
                    rfl

theorem cell20_962850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_962850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962850 prefixEnd_962850 := by exact prefixLift 962850
  have htrace : WordTrace (prefixWord ++ tailWord_962850) baseStart_962850 baseEnd_962850 := by
    simpa [prefixWord, tailWord_962850, baseEnd_962850] using wordTrace_append hprefix tailTrace_962850
  have hstable : (prefixWord ++ tailWord_962850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962850).length < 2 ^ (prefixWord ++ tailWord_962850).sum := by decide
  have hdescent : baseEnd_962850 < baseStart_962850 := by decide
  rcases family_descends (prefixWord ++ tailWord_962850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962878 : List Nat := [4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_962878 : Nat := 118140960795 + 962878 * 2 ^ 59
def prefixEnd_962878 : Nat := 4983230072969 + 3 ^ 40 * 962878 * 2
def baseEnd_962878 : Nat := 146494585374811546399055

theorem tailTrace_962878 : CollatzResearch.WordTrace tailWord_962878 prefixEnd_962878 146494585374811546399055 := by
  unfold tailWord_962878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389880725708115914407161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23412697203776618210171525 4389880725708115914407161)
  ·
    refine ⟨3292410544281086935805371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4389880725708115914407161 3292410544281086935805371)
    ·
      refine ⟨4938615816421630403708057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292410544281086935805371 4938615816421630403708057)
      ·
        refine ⟨3703961862316222802781043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4938615816421630403708057 3703961862316222802781043)
        ·
          refine ⟨5555942793474334204171565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703961862316222802781043 5555942793474334204171565)
          ·
            refine ⟨2083478547552875326564337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5555942793474334204171565 2083478547552875326564337)
            ·
              refine ⟨1562608910664656494923253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083478547552875326564337 1562608910664656494923253)
              ·
                refine ⟨146494585374811546399055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1562608910664656494923253 146494585374811546399055)
                ·
                  rfl

theorem cell20_962878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_962878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_962878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_962878 prefixEnd_962878 := by exact prefixLift 962878
  have htrace : WordTrace (prefixWord ++ tailWord_962878) baseStart_962878 baseEnd_962878 := by
    simpa [prefixWord, tailWord_962878, baseEnd_962878] using wordTrace_append hprefix tailTrace_962878
  have hstable : (prefixWord ++ tailWord_962878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962878).length < 2 ^ (prefixWord ++ tailWord_962878).sum := by decide
  have hdescent : baseEnd_962878 < baseStart_962878 := by decide
  rcases family_descends (prefixWord ++ tailWord_962878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963006 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_963006 : Nat := 118140960795 + 963006 * 2 ^ 59
def prefixEnd_963006 : Nat := 4983230072969 + 3 ^ 40 * 963006 * 2
def baseEnd_963006 : Nat := 439542178812235082929975

theorem tailTrace_963006 : CollatzResearch.WordTrace tailWord_963006 prefixEnd_963006 439542178812235082929975 := by
  unfold tailWord_963006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390464293650150646989609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23415809566134136783944581 4390464293650150646989609)
  ·
    refine ⟨3292848220237612985242207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4390464293650150646989609 3292848220237612985242207)
    ·
      refine ⟨4939272330356419477863311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292848220237612985242207 4939272330356419477863311)
      ·
        refine ⟨7408908495534629216794967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939272330356419477863311 7408908495534629216794967)
        ·
          refine ⟨11113362743301943825192451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408908495534629216794967 11113362743301943825192451)
          ·
            refine ⟨16670044114952915737788677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113362743301943825192451 16670044114952915737788677)
            ·
              refine ⟨3125633271553671700835377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16670044114952915737788677 3125633271553671700835377)
              ·
                refine ⟨2344224953665253775626533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125633271553671700835377 2344224953665253775626533)
                ·
                  refine ⟨439542178812235082929975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344224953665253775626533 439542178812235082929975)
                  ·
                    rfl

theorem cell20_963006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_963006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963006 prefixEnd_963006 := by exact prefixLift 963006
  have htrace : WordTrace (prefixWord ++ tailWord_963006) baseStart_963006 baseEnd_963006 := by
    simpa [prefixWord, tailWord_963006, baseEnd_963006] using wordTrace_append hprefix tailTrace_963006
  have hstable : (prefixWord ++ tailWord_963006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963006).length < 2 ^ (prefixWord ++ tailWord_963006).sum := by decide
  have hdescent : baseEnd_963006 < baseStart_963006 := by decide
  rcases family_descends (prefixWord ++ tailWord_963006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963037 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_963037 : Nat := 118140960795 + 963037 * 2 ^ 59
def prefixEnd_963037 : Nat := 4983230072969 + 3 ^ 40 * 963037 * 2
def baseEnd_963037 : Nat := 439556328056936752896515

theorem tailTrace_963037 : CollatzResearch.WordTrace tailWord_963037 prefixEnd_963037 439556328056936752896515 := by
  unfold tailWord_963037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124845012088897470295365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23416563341392598313530243 35124845012088897470295365)
  ·
    refine ⟨6585908439766668275680381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35124845012088897470295365 6585908439766668275680381)
    ·
      refine ⟨2469715664912500603380143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6585908439766668275680381 2469715664912500603380143)
      ·
        refine ⟨3704573497368750905070215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469715664912500603380143 3704573497368750905070215)
        ·
          refine ⟨5556860246053126357605323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704573497368750905070215 5556860246053126357605323)
          ·
            refine ⟨8335290369079689536407985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556860246053126357605323 8335290369079689536407985)
            ·
              refine ⟨6251467776809767152305989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335290369079689536407985 6251467776809767152305989)
              ·
                refine ⟨1172150208151831341057373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6251467776809767152305989 1172150208151831341057373)
                ·
                  refine ⟨439556328056936752896515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172150208151831341057373 439556328056936752896515)
                  ·
                    rfl

theorem cell20_963037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_963037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963037 prefixEnd_963037 := by exact prefixLift 963037
  have htrace : WordTrace (prefixWord ++ tailWord_963037) baseStart_963037 baseEnd_963037 := by
    simpa [prefixWord, tailWord_963037, baseEnd_963037] using wordTrace_append hprefix tailTrace_963037
  have hstable : (prefixWord ++ tailWord_963037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963037).length < 2 ^ (prefixWord ++ tailWord_963037).sum := by decide
  have hdescent : baseEnd_963037 < baseStart_963037 := by decide
  rcases family_descends (prefixWord ++ tailWord_963037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963054 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_963054 : Nat := 118140960795 + 963054 * 2 ^ 59
def prefixEnd_963054 : Nat := 4983230072969 + 3 ^ 40 * 963054 * 2
def baseEnd_963054 : Nat := 439564087320160249329779

theorem tailTrace_963054 : CollatzResearch.WordTrace tailWord_963054 prefixEnd_963054 439564087320160249329779 := by
  unfold tailWord_963054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390683131628413671708027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23416976702018206249109477 4390683131628413671708027)
  ·
    refine ⟨6586024697442620507562041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4390683131628413671708027 6586024697442620507562041)
    ·
      refine ⟨4939518523081965380671531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6586024697442620507562041 4939518523081965380671531)
      ·
        refine ⟨7409277784622948071007297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939518523081965380671531 7409277784622948071007297)
        ·
          refine ⟨5556958338467211053255473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409277784622948071007297 5556958338467211053255473)
          ·
            refine ⟨4167718753850408289941605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5556958338467211053255473 4167718753850408289941605)
            ·
              refine ⟨781447266346951554364051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4167718753850408289941605 781447266346951554364051)
              ·
                refine ⟨1172170899520427331546077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781447266346951554364051 1172170899520427331546077)
                ·
                  refine ⟨439564087320160249329779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172170899520427331546077 439564087320160249329779)
                  ·
                    rfl

theorem cell20_963054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_963054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963054 prefixEnd_963054 := by exact prefixLift 963054
  have htrace : WordTrace (prefixWord ++ tailWord_963054) baseStart_963054 baseEnd_963054 := by
    simpa [prefixWord, tailWord_963054, baseEnd_963054] using wordTrace_append hprefix tailTrace_963054
  have hstable : (prefixWord ++ tailWord_963054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963054).length < 2 ^ (prefixWord ++ tailWord_963054).sum := by decide
  have hdescent : baseEnd_963054 < baseStart_963054 := by decide
  rcases family_descends (prefixWord ++ tailWord_963054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963065 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_963065 : Nat := 118140960795 + 963065 * 2 ^ 59
def prefixEnd_963065 : Nat := 4983230072969 + 3 ^ 40 * 963065 * 2
def baseEnd_963065 : Nat := 439569108019893099963067

theorem tailTrace_963065 : CollatzResearch.WordTrace tailWord_963065 prefixEnd_963065 439569108019893099963067 := by
  unfold tailWord_963065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35125866255987458252314649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23417244170658305501543099 35125866255987458252314649)
  ·
    refine ⟨26344399691990593689235987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35125866255987458252314649 26344399691990593689235987)
    ·
      refine ⟨39516599537985890533853981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26344399691990593689235987 39516599537985890533853981)
      ·
        refine ⟨14818724826744708950195243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39516599537985890533853981 14818724826744708950195243)
        ·
          refine ⟨22228087240117063425292865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14818724826744708950195243 22228087240117063425292865)
          ·
            refine ⟨16671065430087797568969649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22228087240117063425292865 16671065430087797568969649)
            ·
              refine ⟨12503299072565848176727237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16671065430087797568969649 12503299072565848176727237)
              ·
                refine ⟨2344368576106096533136357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12503299072565848176727237 2344368576106096533136357)
                ·
                  refine ⟨439569108019893099963067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344368576106096533136357 439569108019893099963067)
                  ·
                    rfl

theorem cell20_963065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_963065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963065 prefixEnd_963065 := by exact prefixLift 963065
  have htrace : WordTrace (prefixWord ++ tailWord_963065) baseStart_963065 baseEnd_963065 := by
    simpa [prefixWord, tailWord_963065, baseEnd_963065] using wordTrace_append hprefix tailTrace_963065
  have hstable : (prefixWord ++ tailWord_963065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963065).length < 2 ^ (prefixWord ++ tailWord_963065).sum := by decide
  have hdescent : baseEnd_963065 < baseStart_963065 := by decide
  rcases family_descends (prefixWord ++ tailWord_963065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963092 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_963092 : Nat := 118140960795 + 963092 * 2 ^ 59
def prefixEnd_963092 : Nat := 4983230072969 + 3 ^ 40 * 963092 * 2
def baseEnd_963092 : Nat := 439581431555601006062957

theorem tailTrace_963092 : CollatzResearch.WordTrace tailWord_963092 prefixEnd_963092 439581431555601006062957 := by
  unfold tailWord_963092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563425513444820931773765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23417900684593094575698353 17563425513444820931773765)
  ·
    refine ⟨3293142283770903924707581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17563425513444820931773765 3293142283770903924707581)
    ·
      refine ⟨1234928356414088971765343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3293142283770903924707581 1234928356414088971765343)
      ·
        refine ⟨1852392534621133457648015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234928356414088971765343 1852392534621133457648015)
        ·
          refine ⟨2778588801931700186472023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852392534621133457648015 2778588801931700186472023)
          ·
            refine ⟨4167883202897550279708035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778588801931700186472023 4167883202897550279708035)
            ·
              refine ⟨6251824804346325419562053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167883202897550279708035 6251824804346325419562053)
              ·
                refine ⟨1172217150814936016167885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6251824804346325419562053 1172217150814936016167885)
                ·
                  refine ⟨439581431555601006062957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172217150814936016167885 439581431555601006062957)
                  ·
                    rfl

theorem cell20_963092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_963092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963092 prefixEnd_963092 := by exact prefixLift 963092
  have htrace : WordTrace (prefixWord ++ tailWord_963092) baseStart_963092 baseEnd_963092 := by
    simpa [prefixWord, tailWord_963092, baseEnd_963092] using wordTrace_append hprefix tailTrace_963092
  have hstable : (prefixWord ++ tailWord_963092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963092).length < 2 ^ (prefixWord ++ tailWord_963092).sum := by decide
  have hdescent : baseEnd_963092 < baseStart_963092 := by decide
  rcases family_descends (prefixWord ++ tailWord_963092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963103 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_963103 : Nat := 118140960795 + 963103 * 2 ^ 59
def prefixEnd_963103 : Nat := 4983230072969 + 3 ^ 40 * 963103 * 2
def baseEnd_963103 : Nat := 439586452255333856696245

theorem tailTrace_963103 : CollatzResearch.WordTrace tailWord_963103 prefixEnd_963103 439586452255333856696245 := by
  unfold tailWord_963103
  simp only [CollatzResearch.WordTrace]
  refine ⟨35127252229849790742197963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23418168153233193828131975 35127252229849790742197963)
  ·
    refine ⟨52690878344774686113296945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35127252229849790742197963 52690878344774686113296945)
    ·
      refine ⟨39518158758581014584972709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52690878344774686113296945 39518158758581014584972709)
      ·
        refine ⟨7409654767233940234682383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39518158758581014584972709 7409654767233940234682383)
        ·
          refine ⟨11114482150850910352023575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409654767233940234682383 11114482150850910352023575)
          ·
            refine ⟨16671723226276365528035363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11114482150850910352023575 16671723226276365528035363)
            ·
              refine ⟨25007584839414548292053045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16671723226276365528035363 25007584839414548292053045)
              ·
                refine ⟨2344461078695113902379973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25007584839414548292053045 2344461078695113902379973)
                ·
                  refine ⟨439586452255333856696245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344461078695113902379973 439586452255333856696245)
                  ·
                    rfl

theorem cell20_963103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_963103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963103 prefixEnd_963103 := by exact prefixLift 963103
  have htrace : WordTrace (prefixWord ++ tailWord_963103) baseStart_963103 baseEnd_963103 := by
    simpa [prefixWord, tailWord_963103, baseEnd_963103] using wordTrace_append hprefix tailTrace_963103
  have hstable : (prefixWord ++ tailWord_963103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963103).length < 2 ^ (prefixWord ++ tailWord_963103).sum := by decide
  have hdescent : baseEnd_963103 < baseStart_963103 := by decide
  rcases family_descends (prefixWord ++ tailWord_963103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963127 : List Nat := [1, 1, 3, 1, 2, 3, 5, 4]
def baseStart_963127 : Nat := 118140960795 + 963127 * 2 ^ 59
def prefixEnd_963127 : Nat := 4983230072969 + 3 ^ 40 * 963127 * 2
def baseEnd_963127 : Nat := 146532468836432146632049

theorem tailTrace_963127 : CollatzResearch.WordTrace tailWord_963127 prefixEnd_963127 146532468836432146632049 := by
  unfold tailWord_963127
  simp only [CollatzResearch.WordTrace]
  refine ⟨35128127581762842841071635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23418751721175228560714423 35128127581762842841071635)
  ·
    refine ⟨52692191372644264261607453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35128127581762842841071635 52692191372644264261607453)
    ·
      refine ⟨19759571764741599098102795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52692191372644264261607453 19759571764741599098102795)
      ·
        refine ⟨29639357647112398647154193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19759571764741599098102795 29639357647112398647154193)
        ·
          refine ⟨22229518235334298985365645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29639357647112398647154193 22229518235334298985365645)
          ·
            refine ⟨8336069338250362119512117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22229518235334298985365645 8336069338250362119512117)
            ·
              refine ⟨781506500460971448704261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8336069338250362119512117 781506500460971448704261)
              ·
                refine ⟨146532468836432146632049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781506500460971448704261 146532468836432146632049)
                ·
                  rfl

theorem cell20_963127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_963127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963127 prefixEnd_963127 := by exact prefixLift 963127
  have htrace : WordTrace (prefixWord ++ tailWord_963127) baseStart_963127 baseEnd_963127 := by
    simpa [prefixWord, tailWord_963127, baseEnd_963127] using wordTrace_append hprefix tailTrace_963127
  have hstable : (prefixWord ++ tailWord_963127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963127).length < 2 ^ (prefixWord ++ tailWord_963127).sum := by decide
  have hdescent : baseEnd_963127 < baseStart_963127 := by decide
  rcases family_descends (prefixWord ++ tailWord_963127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963137 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 2]
def baseStart_963137 : Nat := 118140960795 + 963137 * 2 ^ 59
def prefixEnd_963137 : Nat := 4983230072969 + 3 ^ 40 * 963137 * 2
def baseEnd_963137 : Nat := 439601970781780849562773

theorem tailTrace_963137 : CollatzResearch.WordTrace tailWord_963137 prefixEnd_963137 439601970781780849562773 := by
  unfold tailWord_963137
  simp only [CollatzResearch.WordTrace]
  refine ⟨35128492311726614548935665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23418994874484409699290443 35128492311726614548935665)
  ·
    refine ⟨26346369233794960911701749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35128492311726614548935665 26346369233794960911701749)
    ·
      refine ⟨2469972115668277585472039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26346369233794960911701749 2469972115668277585472039)
      ·
        refine ⟨3704958173502416378208059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469972115668277585472039 3704958173502416378208059)
        ·
          refine ⟨5557437260253624567312089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704958173502416378208059 5557437260253624567312089)
          ·
            refine ⟨4168077945190218425484067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557437260253624567312089 4168077945190218425484067)
            ·
              refine ⟨6252116917785327638226101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168077945190218425484067 6252116917785327638226101)
              ·
                refine ⟨586135961042374466083697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6252116917785327638226101 586135961042374466083697)
                ·
                  refine ⟨439601970781780849562773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586135961042374466083697 439601970781780849562773)
                  ·
                    rfl

theorem cell20_963137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_963137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963137 prefixEnd_963137 := by exact prefixLift 963137
  have htrace : WordTrace (prefixWord ++ tailWord_963137) baseStart_963137 baseEnd_963137 := by
    simpa [prefixWord, tailWord_963137, baseEnd_963137] using wordTrace_append hprefix tailTrace_963137
  have hstable : (prefixWord ++ tailWord_963137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963137).length < 2 ^ (prefixWord ++ tailWord_963137).sum := by decide
  have hdescent : baseEnd_963137 < baseStart_963137 := by decide
  rcases family_descends (prefixWord ++ tailWord_963137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963148 : List Nat := [2, 2, 1, 3, 1, 2, 9]
def baseStart_963148 : Nat := 118140960795 + 963148 * 2 ^ 59
def prefixEnd_963148 : Nat := 4983230072969 + 3 ^ 40 * 963148 * 2
def baseEnd_963148 : Nat := 48845221275723744466229

theorem tailTrace_963148 : CollatzResearch.WordTrace tailWord_963148 prefixEnd_963148 48845221275723744466229 := by
  unfold tailWord_963148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564446757343381713793049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23419262343124508951724065 17564446757343381713793049)
  ·
    refine ⟨13173335068007536285344787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17564446757343381713793049 13173335068007536285344787)
    ·
      refine ⟨19760002602011304428017181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13173335068007536285344787 19760002602011304428017181)
      ·
        refine ⟨7410000975754239160506443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19760002602011304428017181 7410000975754239160506443)
        ·
          refine ⟨11115001463631358740759665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410000975754239160506443 11115001463631358740759665)
          ·
            refine ⟨8336251097723519055569749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115001463631358740759665 8336251097723519055569749)
            ·
              refine ⟨48845221275723744466229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8336251097723519055569749 48845221275723744466229)
              ·
                rfl

theorem cell20_963148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_963148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963148 prefixEnd_963148 := by exact prefixLift 963148
  have htrace : WordTrace (prefixWord ++ tailWord_963148) baseStart_963148 baseEnd_963148 := by
    simpa [prefixWord, tailWord_963148, baseEnd_963148] using wordTrace_append hprefix tailTrace_963148
  have hstable : (prefixWord ++ tailWord_963148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963148).length < 2 ^ (prefixWord ++ tailWord_963148).sum := by decide
  have hdescent : baseEnd_963148 < baseStart_963148 := by decide
  rcases family_descends (prefixWord ++ tailWord_963148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963182 : List Nat := [4, 1, 2, 2, 2, 1, 4, 4]
def baseStart_963182 : Nat := 118140960795 + 963182 * 2 ^ 59
def prefixEnd_963182 : Nat := 4983230072969 + 3 ^ 40 * 963182 * 2
def baseEnd_963182 : Nat := 146540836669320231020863

theorem tailTrace_963182 : CollatzResearch.WordTrace tailWord_963182 prefixEnd_963182 146540836669320231020863 := by
  unfold tailWord_963182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391266699570448404290475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23420089064375724822882533 4391266699570448404290475)
  ·
    refine ⟨6586900049355672606435713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4391266699570448404290475 6586900049355672606435713)
    ·
      refine ⟨4940175037016754454826785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6586900049355672606435713 4940175037016754454826785)
      ·
        refine ⟨3705131277762565841120089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4940175037016754454826785 3705131277762565841120089)
        ·
          refine ⟨2778848458321924380840067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3705131277762565841120089 2778848458321924380840067)
          ·
            refine ⟨4168272687482886571260101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778848458321924380840067 4168272687482886571260101)
            ·
              refine ⟨781551128903041232111269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4168272687482886571260101 781551128903041232111269)
              ·
                refine ⟨146540836669320231020863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781551128903041232111269 146540836669320231020863)
                ·
                  rfl

theorem cell20_963182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_963182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963182 prefixEnd_963182 := by exact prefixLift 963182
  have htrace : WordTrace (prefixWord ++ tailWord_963182) baseStart_963182 baseEnd_963182 := by
    simpa [prefixWord, tailWord_963182, baseEnd_963182] using wordTrace_append hprefix tailTrace_963182
  have hstable : (prefixWord ++ tailWord_963182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963182).length < 2 ^ (prefixWord ++ tailWord_963182).sum := by decide
  have hdescent : baseEnd_963182 < baseStart_963182 := by decide
  rcases family_descends (prefixWord ++ tailWord_963182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963220 : List Nat := [2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_963220 : Nat := 118140960795 + 963220 * 2 ^ 59
def prefixEnd_963220 : Nat := 4983230072969 + 3 ^ 40 * 963220 * 2
def baseEnd_963220 : Nat := 146546618081133816598589

theorem tailTrace_963220 : CollatzResearch.WordTrace tailWord_963220 prefixEnd_963220 146546618081133816598589 := by
  unfold tailWord_963220
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565759785212959862103557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23421013046950613149471409 17565759785212959862103557)
  ·
    refine ⟨3293579959727429974144417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17565759785212959862103557 3293579959727429974144417)
    ·
      refine ⟨2470184969795572480608313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3293579959727429974144417 2470184969795572480608313)
      ·
        refine ⟨1852638727346679360456235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2470184969795572480608313 1852638727346679360456235)
        ·
          refine ⟨2778958091020019040684353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852638727346679360456235 2778958091020019040684353)
          ·
            refine ⟨2084218568265014280513265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778958091020019040684353 2084218568265014280513265)
            ·
              refine ⟨1563163926198760710384949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2084218568265014280513265 1563163926198760710384949)
              ·
                refine ⟨146546618081133816598589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1563163926198760710384949 146546618081133816598589)
                ·
                  rfl

theorem cell20_963220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_963220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963220 prefixEnd_963220 := by exact prefixLift 963220
  have htrace : WordTrace (prefixWord ++ tailWord_963220) baseStart_963220 baseEnd_963220 := by
    simpa [prefixWord, tailWord_963220, baseEnd_963220] using wordTrace_append hprefix tailTrace_963220
  have hstable : (prefixWord ++ tailWord_963220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963220).length < 2 ^ (prefixWord ++ tailWord_963220).sum := by decide
  have hdescent : baseEnd_963220 < baseStart_963220 := by decide
  rcases family_descends (prefixWord ++ tailWord_963220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963268 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 2]
def baseStart_963268 : Nat := 118140960795 + 963268 * 2 ^ 59
def prefixEnd_963268 : Nat := 4983230072969 + 3 ^ 40 * 963268 * 2
def baseEnd_963268 : Nat := 439661762751326616195571

theorem tailTrace_963268 : CollatzResearch.WordTrace tailWord_963268 prefixEnd_963268 439661762751326616195571 := by
  unfold tailWord_963268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17566635137126011960977229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23422180182834682614636305 17566635137126011960977229)
  ·
    refine ⟨6587488176422254485366461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17566635137126011960977229 6587488176422254485366461)
    ·
      refine ⟨2470308066158345432012423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6587488176422254485366461 2470308066158345432012423)
      ·
        refine ⟨3705462099237518148018635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470308066158345432012423 3705462099237518148018635)
        ·
          refine ⟨5558193148856277222027953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705462099237518148018635 5558193148856277222027953)
          ·
            refine ⟨4168644861642207916520965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558193148856277222027953 4168644861642207916520965)
            ·
              refine ⟨781620911557913984347681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4168644861642207916520965 781620911557913984347681)
              ·
                refine ⟨586215683668435488260761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781620911557913984347681 586215683668435488260761)
                ·
                  refine ⟨439661762751326616195571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586215683668435488260761 439661762751326616195571)
                  ·
                    rfl

theorem cell20_963268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_963268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963268 prefixEnd_963268 := by exact prefixLift 963268
  have htrace : WordTrace (prefixWord ++ tailWord_963268) baseStart_963268 baseEnd_963268 := by
    simpa [prefixWord, tailWord_963268, baseEnd_963268] using wordTrace_append hprefix tailTrace_963268
  have hstable : (prefixWord ++ tailWord_963268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963268).length < 2 ^ (prefixWord ++ tailWord_963268).sum := by decide
  have hdescent : baseEnd_963268 < baseStart_963268 := by decide
  rcases family_descends (prefixWord ++ tailWord_963268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963307 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_963307 : Nat := 118140960795 + 963307 * 2 ^ 59
def prefixEnd_963307 : Nat := 4983230072969 + 3 ^ 40 * 963307 * 2
def baseEnd_963307 : Nat := 439679563414015813895411

theorem tailTrace_963307 : CollatzResearch.WordTrace tailWord_963307 prefixEnd_963307 439679563414015813895411 := by
  unfold tailWord_963307
  simp only [CollatzResearch.WordTrace]
  refine ⟨35134692721110733582624175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23423128480740489055082783 35134692721110733582624175)
  ·
    refine ⟨52702039081666100373936263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35134692721110733582624175 52702039081666100373936263)
    ·
      refine ⟨79053058622499150560904395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52702039081666100373936263 79053058622499150560904395)
      ·
        refine ⟨118579587933748725841356593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79053058622499150560904395 118579587933748725841356593)
        ·
          refine ⟨88934690950311544381017445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118579587933748725841356593 88934690950311544381017445)
          ·
            refine ⟨16675254553183414571440771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88934690950311544381017445 16675254553183414571440771)
            ·
              refine ⟨25012881829775121857161157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16675254553183414571440771 25012881829775121857161157)
              ·
                refine ⟨4689915343082835348217717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25012881829775121857161157 4689915343082835348217717)
                ·
                  refine ⟨439679563414015813895411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689915343082835348217717 439679563414015813895411)
                  ·
                    rfl

theorem cell20_963307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_963307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963307 prefixEnd_963307 := by exact prefixLift 963307
  have htrace : WordTrace (prefixWord ++ tailWord_963307) baseStart_963307 baseEnd_963307 := by
    simpa [prefixWord, tailWord_963307, baseEnd_963307] using wordTrace_append hprefix tailTrace_963307
  have hstable : (prefixWord ++ tailWord_963307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963307).length < 2 ^ (prefixWord ++ tailWord_963307).sum := by decide
  have hdescent : baseEnd_963307 < baseStart_963307 := by decide
  rcases family_descends (prefixWord ++ tailWord_963307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963316 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_963316 : Nat := 118140960795 + 963316 * 2 ^ 59
def prefixEnd_963316 : Nat := 4983230072969 + 3 ^ 40 * 963316 * 2
def baseEnd_963316 : Nat := 439683671259251782595375

theorem tailTrace_963316 : CollatzResearch.WordTrace tailWord_963316 prefixEnd_963316 439683671259251782595375 := by
  unfold tailWord_963316
  simp only [CollatzResearch.WordTrace]
  refine ⟨17567510489039064059850901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23423347318718752079801201 17567510489039064059850901)
  ·
    refine ⟨823477054173706127805511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17567510489039064059850901 823477054173706127805511)
    ·
      refine ⟨1235215581260559191708267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823477054173706127805511 1235215581260559191708267)
      ·
        refine ⟨1852823371890838787562401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235215581260559191708267 1852823371890838787562401)
        ·
          refine ⟨1389617528918129090671801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852823371890838787562401 1389617528918129090671801)
          ·
            refine ⟨1042213146688596818003851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389617528918129090671801 1042213146688596818003851)
            ·
              refine ⟨1563319720032895227005777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042213146688596818003851 1563319720032895227005777)
              ·
                refine ⟨1172489790024671420254333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563319720032895227005777 1172489790024671420254333)
                ·
                  refine ⟨439683671259251782595375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172489790024671420254333 439683671259251782595375)
                  ·
                    rfl

theorem cell20_963316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_963316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963316 prefixEnd_963316 := by exact prefixLift 963316
  have htrace : WordTrace (prefixWord ++ tailWord_963316) baseStart_963316 baseEnd_963316 := by
    simpa [prefixWord, tailWord_963316, baseEnd_963316] using wordTrace_append hprefix tailTrace_963316
  have hstable : (prefixWord ++ tailWord_963316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963316).length < 2 ^ (prefixWord ++ tailWord_963316).sum := by decide
  have hdescent : baseEnd_963316 < baseStart_963316 := by decide
  rcases family_descends (prefixWord ++ tailWord_963316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963324 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_963324 : Nat := 118140960795 + 963324 * 2 ^ 59
def prefixEnd_963324 : Nat := 4983230072969 + 3 ^ 40 * 963324 * 2
def baseEnd_963324 : Nat := 439687322677239310328675

theorem tailTrace_963324 : CollatzResearch.WordTrace tailWord_963324 prefixEnd_963324 439687322677239310328675 := by
  unfold tailWord_963324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17567656381024572742996513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23423541841366096990662017 17567656381024572742996513)
  ·
    refine ⟨13175742285768429557247385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17567656381024572742996513 13175742285768429557247385)
    ·
      refine ⟨9881806714326322167935539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13175742285768429557247385 9881806714326322167935539)
      ·
        refine ⟨14822710071489483251903309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9881806714326322167935539 14822710071489483251903309)
        ·
          refine ⟨5558516276808556219463741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14822710071489483251903309 5558516276808556219463741)
          ·
            refine ⟨2084443603803208582298903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5558516276808556219463741 2084443603803208582298903)
            ·
              refine ⟨3126665405704812873448355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084443603803208582298903 3126665405704812873448355)
              ·
                refine ⟨4689998108557219310172533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126665405704812873448355 4689998108557219310172533)
                ·
                  refine ⟨439687322677239310328675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689998108557219310172533 439687322677239310328675)
                  ·
                    rfl

theorem cell20_963324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_963324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963324 prefixEnd_963324 := by exact prefixLift 963324
  have htrace : WordTrace (prefixWord ++ tailWord_963324) baseStart_963324 baseEnd_963324 := by
    simpa [prefixWord, tailWord_963324, baseEnd_963324] using wordTrace_append hprefix tailTrace_963324
  have hstable : (prefixWord ++ tailWord_963324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963324).length < 2 ^ (prefixWord ++ tailWord_963324).sum := by decide
  have hdescent : baseEnd_963324 < baseStart_963324 := by decide
  rcases family_descends (prefixWord ++ tailWord_963324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963338 : List Nat := [3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_963338 : Nat := 118140960795 + 963338 * 2 ^ 59
def prefixEnd_963338 : Nat := 4983230072969 + 3 ^ 40 * 963338 * 2
def baseEnd_963338 : Nat := 146564570886239161287317

theorem tailTrace_963338 : CollatzResearch.WordTrace tailWord_963338 prefixEnd_963338 146564570886239161287317 := by
  unfold tailWord_963338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783955845999606469250667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23423882255998950584668445 8783955845999606469250667)
  ·
    refine ⟨13175933768999409703876001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783955845999606469250667 13175933768999409703876001)
    ·
      refine ⟨9881950326749557277907001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13175933768999409703876001 9881950326749557277907001)
      ·
        refine ⟨7411462745062167958430251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9881950326749557277907001 7411462745062167958430251)
        ·
          refine ⟨11117194117593251937645377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411462745062167958430251 11117194117593251937645377)
          ·
            refine ⟨8337895588194938953234033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117194117593251937645377 8337895588194938953234033)
            ·
              refine ⟨6253421691146204214925525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337895588194938953234033 6253421691146204214925525)
              ·
                refine ⟨146564570886239161287317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6253421691146204214925525 146564570886239161287317)
                ·
                  rfl

theorem cell20_963338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_963338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963338 prefixEnd_963338 := by exact prefixLift 963338
  have htrace : WordTrace (prefixWord ++ tailWord_963338) baseStart_963338 baseEnd_963338 := by
    simpa [prefixWord, tailWord_963338, baseEnd_963338] using wordTrace_append hprefix tailTrace_963338
  have hstable : (prefixWord ++ tailWord_963338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963338).length < 2 ^ (prefixWord ++ tailWord_963338).sum := by decide
  have hdescent : baseEnd_963338 < baseStart_963338 := by decide
  rcases family_descends (prefixWord ++ tailWord_963338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963351 : List Nat := [1, 1, 3, 4, 4, 1, 2, 4]
def baseStart_963351 : Nat := 118140960795 + 963351 * 2 ^ 59
def prefixEnd_963351 : Nat := 4983230072969 + 3 ^ 40 * 963351 * 2
def baseEnd_963351 : Nat := 146566548737649072142855

theorem tailTrace_963351 : CollatzResearch.WordTrace tailWord_963351 prefixEnd_963351 146566548737649072142855 := by
  unfold tailWord_963351
  simp only [CollatzResearch.WordTrace]
  refine ⟨35136297532951329097225907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23424198355300886064817271 35136297532951329097225907)
  ·
    refine ⟨52704446299426993645838861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35136297532951329097225907 52704446299426993645838861)
    ·
      refine ⟨19764167362285122617189573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52704446299426993645838861 19764167362285122617189573)
      ·
        refine ⟨3705781380428460490723045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19764167362285122617189573 3705781380428460490723045)
        ·
          refine ⟨694834008830336342010571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3705781380428460490723045 694834008830336342010571)
          ·
            refine ⟨1042251013245504513015857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694834008830336342010571 1042251013245504513015857)
            ·
              refine ⟨781688259934128384761893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042251013245504513015857 781688259934128384761893)
              ·
                refine ⟨146566548737649072142855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781688259934128384761893 146566548737649072142855)
                ·
                  rfl

theorem cell20_963351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].length) (baseStart_963351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963351 prefixEnd_963351 := by exact prefixLift 963351
  have htrace : WordTrace (prefixWord ++ tailWord_963351) baseStart_963351 baseEnd_963351 := by
    simpa [prefixWord, tailWord_963351, baseEnd_963351] using wordTrace_append hprefix tailTrace_963351
  have hstable : (prefixWord ++ tailWord_963351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963351).length < 2 ^ (prefixWord ++ tailWord_963351).sum := by decide
  have hdescent : baseEnd_963351 < baseStart_963351 := by decide
  rcases family_descends (prefixWord ++ tailWord_963351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963362 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_963362 : Nat := 118140960795 + 963362 * 2 ^ 59
def prefixEnd_963362 : Nat := 4983230072969 + 3 ^ 40 * 963362 * 2
def baseEnd_963362 : Nat := 439704666912680067061853

theorem tailTrace_963362 : CollatzResearch.WordTrace tailWord_963362 prefixEnd_963362 439704666912680067061853 := by
  unfold tailWord_963362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784174683977869493969085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23424465823940985317250893 8784174683977869493969085)
  ·
    refine ⟨3294065506491701060238407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8784174683977869493969085 3294065506491701060238407)
    ·
      refine ⟨4941098259737551590357611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294065506491701060238407 4941098259737551590357611)
      ·
        refine ⟨7411647389606327385536417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941098259737551590357611 7411647389606327385536417)
        ·
          refine ⟨5558735542204745539152313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7411647389606327385536417 5558735542204745539152313)
          ·
            refine ⟨4169051656653559154364235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558735542204745539152313 4169051656653559154364235)
            ·
              refine ⟨6253577484980338731546353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169051656653559154364235 6253577484980338731546353)
              ·
                refine ⟨4690183113735254048659765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253577484980338731546353 4690183113735254048659765)
                ·
                  refine ⟨439704666912680067061853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690183113735254048659765 439704666912680067061853)
                  ·
                    rfl

theorem cell20_963362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_963362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963362 prefixEnd_963362 := by exact prefixLift 963362
  have htrace : WordTrace (prefixWord ++ tailWord_963362) baseStart_963362 baseEnd_963362 := by
    simpa [prefixWord, tailWord_963362, baseEnd_963362] using wordTrace_append hprefix tailTrace_963362
  have hstable : (prefixWord ++ tailWord_963362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963362).length < 2 ^ (prefixWord ++ tailWord_963362).sum := by decide
  have hdescent : baseEnd_963362 < baseStart_963362 := by decide
  rcases family_descends (prefixWord ++ tailWord_963362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963382 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_963382 : Nat := 118140960795 + 963382 * 2 ^ 59
def prefixEnd_963382 : Nat := 4983230072969 + 3 ^ 40 * 963382 * 2
def baseEnd_963382 : Nat := 439713795457648886395105

theorem tailTrace_963382 : CollatzResearch.WordTrace tailWord_963382 prefixEnd_963382 439713795457648886395105 := by
  unfold tailWord_963382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196089262239938836975275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23424952130559347594402933 2196089262239938836975275)
  ·
    refine ⟨3294133893359908255462913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196089262239938836975275 3294133893359908255462913)
    ·
      refine ⟨2470600420019931191597185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3294133893359908255462913 2470600420019931191597185)
      ·
        refine ⟨1852950315014948393697889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2470600420019931191597185 1852950315014948393697889)
        ·
          refine ⟨1389712736261211295273417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852950315014948393697889 1389712736261211295273417)
          ·
            refine ⟨1042284552195908471455063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389712736261211295273417 1042284552195908471455063)
            ·
              refine ⟨1563426828293862707182595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042284552195908471455063 1563426828293862707182595)
              ·
                refine ⟨2345140242440794060773893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563426828293862707182595 2345140242440794060773893)
                ·
                  refine ⟨439713795457648886395105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345140242440794060773893 439713795457648886395105)
                  ·
                    rfl

theorem cell20_963382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_963382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963382 prefixEnd_963382 := by exact prefixLift 963382
  have htrace : WordTrace (prefixWord ++ tailWord_963382) baseStart_963382 baseEnd_963382 := by
    simpa [prefixWord, tailWord_963382, baseEnd_963382] using wordTrace_append hprefix tailTrace_963382
  have hstable : (prefixWord ++ tailWord_963382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963382).length < 2 ^ (prefixWord ++ tailWord_963382).sum := by decide
  have hdescent : baseEnd_963382 < baseStart_963382 := by decide
  rcases family_descends (prefixWord ++ tailWord_963382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963383 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_963383 : Nat := 118140960795 + 963383 * 2 ^ 59
def prefixEnd_963383 : Nat := 4983230072969 + 3 ^ 40 * 963383 * 2
def baseEnd_963383 : Nat := 439714251884897327361767

theorem tailTrace_963383 : CollatzResearch.WordTrace tailWord_963383 prefixEnd_963383 439714251884897327361767 := by
  unfold tailWord_963383
  simp only [CollatzResearch.WordTrace]
  refine ⟨35137464668835398562390803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23424976445890265708260535 35137464668835398562390803)
  ·
    refine ⟨52706197003253097843586205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35137464668835398562390803 52706197003253097843586205)
    ·
      refine ⟨19764823876219911691344827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52706197003253097843586205 19764823876219911691344827)
      ·
        refine ⟨29647235814329867537017241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19764823876219911691344827 29647235814329867537017241)
        ·
          refine ⟨22235426860747400652762931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29647235814329867537017241 22235426860747400652762931)
          ·
            refine ⟨33353140291121100979144397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22235426860747400652762931 33353140291121100979144397)
            ·
              refine ⟨12507427609170412867179149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33353140291121100979144397 12507427609170412867179149)
              ·
                refine ⟨4690285353438904825192181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12507427609170412867179149 4690285353438904825192181)
                ·
                  refine ⟨439714251884897327361767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690285353438904825192181 439714251884897327361767)
                  ·
                    rfl

theorem cell20_963383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_963383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963383 prefixEnd_963383 := by exact prefixLift 963383
  have htrace : WordTrace (prefixWord ++ tailWord_963383) baseStart_963383 baseEnd_963383 := by
    simpa [prefixWord, tailWord_963383, baseEnd_963383] using wordTrace_append hprefix tailTrace_963383
  have hstable : (prefixWord ++ tailWord_963383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963383).length < 2 ^ (prefixWord ++ tailWord_963383).sum := by decide
  have hdescent : baseEnd_963383 < baseStart_963383 := by decide
  rcases family_descends (prefixWord ++ tailWord_963383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963400 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_963400 : Nat := 118140960795 + 963400 * 2 ^ 59
def prefixEnd_963400 : Nat := 4983230072969 + 3 ^ 40 * 963400 * 2
def baseEnd_963400 : Nat := 439722011148120823795031

theorem tailTrace_963400 : CollatzResearch.WordTrace tailWord_963400 prefixEnd_963400 439722011148120823795031 := by
  unfold tailWord_963400
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569042354886905232879827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23425389806515873643839769 17569042354886905232879827)
  ·
    refine ⟨26353563532330357849319741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17569042354886905232879827 26353563532330357849319741)
    ·
      refine ⟨9882586324623884193494903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26353563532330357849319741 9882586324623884193494903)
      ·
        refine ⟨14823879486935826290242355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9882586324623884193494903 14823879486935826290242355)
        ·
          refine ⟨22235819230403739435363533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823879486935826290242355 22235819230403739435363533)
          ·
            refine ⟨8338432211401402288261325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22235819230403739435363533 8338432211401402288261325)
            ·
              refine ⟨3126912079275525858097997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8338432211401402288261325 3126912079275525858097997)
              ·
                refine ⟨1172592029728322196786749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126912079275525858097997 1172592029728322196786749)
                ·
                  refine ⟨439722011148120823795031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172592029728322196786749 439722011148120823795031)
                  ·
                    rfl

theorem cell20_963400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_963400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963400 prefixEnd_963400 := by exact prefixLift 963400
  have htrace : WordTrace (prefixWord ++ tailWord_963400) baseStart_963400 baseEnd_963400 := by
    simpa [prefixWord, tailWord_963400, baseEnd_963400] using wordTrace_append hprefix tailTrace_963400
  have hstable : (prefixWord ++ tailWord_963400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963400).length < 2 ^ (prefixWord ++ tailWord_963400).sum := by decide
  have hdescent : baseEnd_963400 < baseStart_963400 := by decide
  rcases family_descends (prefixWord ++ tailWord_963400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963424 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 2]
def baseStart_963424 : Nat := 118140960795 + 963424 * 2 ^ 59
def prefixEnd_963424 : Nat := 4983230072969 + 3 ^ 40 * 963424 * 2
def baseEnd_963424 : Nat := 439732965402083406994933

theorem tailTrace_963424 : CollatzResearch.WordTrace tailWord_963424 prefixEnd_963424 439732965402083406994933 := by
  unfold tailWord_963424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569480030843431282316663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23425973374457908376422217 17569480030843431282316663)
  ·
    refine ⟨26354220046265146923474995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17569480030843431282316663 26354220046265146923474995)
    ·
      refine ⟨39531330069397720385212493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26354220046265146923474995 39531330069397720385212493)
      ·
        refine ⟨14824248776024145144454685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39531330069397720385212493 14824248776024145144454685)
        ·
          refine ⟨5559093291009054429170507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14824248776024145144454685 5559093291009054429170507)
          ·
            refine ⟨8338639936513581643755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559093291009054429170507 8338639936513581643755761)
            ·
              refine ⟨6253979952385186232816821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8338639936513581643755761 6253979952385186232816821)
              ·
                refine ⟨586310620536111209326577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6253979952385186232816821 586310620536111209326577)
                ·
                  refine ⟨439732965402083406994933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586310620536111209326577 439732965402083406994933)
                  ·
                    rfl

theorem cell20_963424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_963424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963424 prefixEnd_963424 := by exact prefixLift 963424
  have htrace : WordTrace (prefixWord ++ tailWord_963424) baseStart_963424 baseEnd_963424 := by
    simpa [prefixWord, tailWord_963424, baseEnd_963424] using wordTrace_append hprefix tailTrace_963424
  have hstable : (prefixWord ++ tailWord_963424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963424).length < 2 ^ (prefixWord ++ tailWord_963424).sum := by decide
  have hdescent : baseEnd_963424 < baseStart_963424 := by decide
  rcases family_descends (prefixWord ++ tailWord_963424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963441 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 2]
def baseStart_963441 : Nat := 118140960795 + 963441 * 2 ^ 59
def prefixEnd_963441 : Nat := 4983230072969 + 3 ^ 40 * 963441 * 2
def baseEnd_963441 : Nat := 439740724665306903428197

theorem tailTrace_963441 : CollatzResearch.WordTrace tailWord_963441 prefixEnd_963441 439740724665306903428197 := by
  unfold tailWord_963441
  simp only [CollatzResearch.WordTrace]
  refine ⟨35139580102625274468002177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23426386735083516312001451 35139580102625274468002177)
  ·
    refine ⟨26354685076968955851001633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35139580102625274468002177 26354685076968955851001633)
    ·
      refine ⟨19766013807726716888251225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26354685076968955851001633 19766013807726716888251225)
      ·
        refine ⟨14824510355795037666188419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19766013807726716888251225 14824510355795037666188419)
        ·
          refine ⟨22236765533692556499282629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14824510355795037666188419 22236765533692556499282629)
          ·
            refine ⟨4169393537567354343615493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22236765533692556499282629 4169393537567354343615493)
            ·
              refine ⟨781761288293878939427905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4169393537567354343615493 781761288293878939427905)
              ·
                refine ⟨586320966220409204570929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781761288293878939427905 586320966220409204570929)
                ·
                  refine ⟨439740724665306903428197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586320966220409204570929 439740724665306903428197)
                  ·
                    rfl

theorem cell20_963441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_963441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963441 prefixEnd_963441 := by exact prefixLift 963441
  have htrace : WordTrace (prefixWord ++ tailWord_963441) baseStart_963441 baseEnd_963441 := by
    simpa [prefixWord, tailWord_963441, baseEnd_963441] using wordTrace_append hprefix tailTrace_963441
  have hstable : (prefixWord ++ tailWord_963441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963441).length < 2 ^ (prefixWord ++ tailWord_963441).sum := by decide
  have hdescent : baseEnd_963441 < baseStart_963441 := by decide
  rcases family_descends (prefixWord ++ tailWord_963441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963458 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_963458 : Nat := 118140960795 + 963458 * 2 ^ 59
def prefixEnd_963458 : Nat := 4983230072969 + 3 ^ 40 * 963458 * 2
def baseEnd_963458 : Nat := 439748483928530399861461

theorem tailTrace_963458 : CollatzResearch.WordTrace tailWord_963458 prefixEnd_963458 439748483928530399861461 := by
  unfold tailWord_963458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785050035890921592842757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23426800095709124247580685 8785050035890921592842757)
  ·
    refine ⟨1647196881729547798658017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8785050035890921592842757 1647196881729547798658017)
    ·
      refine ⟨1235397661297160848993513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1647196881729547798658017 1235397661297160848993513)
      ·
        refine ⟨926548245972870636745135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1235397661297160848993513 926548245972870636745135)
        ·
          refine ⟨1389822368959305955117703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926548245972870636745135 1389822368959305955117703)
          ·
            refine ⟨2084733553438958932676555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389822368959305955117703 2084733553438958932676555)
            ·
              refine ⟨3127100330158438399014833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084733553438958932676555 3127100330158438399014833)
              ·
                refine ⟨2345325247618828799261125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127100330158438399014833 2345325247618828799261125)
                ·
                  refine ⟨439748483928530399861461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345325247618828799261125 439748483928530399861461)
                  ·
                    rfl

theorem cell20_963458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_963458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963458 prefixEnd_963458 := by exact prefixLift 963458
  have htrace : WordTrace (prefixWord ++ tailWord_963458) baseStart_963458 baseEnd_963458 := by
    simpa [prefixWord, tailWord_963458, baseEnd_963458] using wordTrace_append hprefix tailTrace_963458
  have hstable : (prefixWord ++ tailWord_963458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963458).length < 2 ^ (prefixWord ++ tailWord_963458).sum := by decide
  have hdescent : baseEnd_963458 < baseStart_963458 := by decide
  rcases family_descends (prefixWord ++ tailWord_963458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963476 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_963476 : Nat := 118140960795 + 963476 * 2 ^ 59
def prefixEnd_963476 : Nat := 4983230072969 + 3 ^ 40 * 963476 * 2
def baseEnd_963476 : Nat := 439756699619002337261387

theorem tailTrace_963476 : CollatzResearch.WordTrace tailWord_963476 prefixEnd_963476 439756699619002337261387 := by
  unfold tailWord_963476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17570428328749237722763141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23427237771665650297017521 17570428328749237722763141)
  ·
    refine ⟨3294455311640482073018089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17570428328749237722763141 3294455311640482073018089)
    ·
      refine ⟨2470841483730361554763567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3294455311640482073018089 2470841483730361554763567)
      ·
        refine ⟨3706262225595542332145351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470841483730361554763567 3706262225595542332145351)
        ·
          refine ⟨5559393338393313498218027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706262225595542332145351 5559393338393313498218027)
          ·
            refine ⟨8339090007589970247327041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559393338393313498218027 8339090007589970247327041)
            ·
              refine ⟨6254317505692477685495281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339090007589970247327041 6254317505692477685495281)
              ·
                refine ⟨4690738129269358264121461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6254317505692477685495281 4690738129269358264121461)
                ·
                  refine ⟨439756699619002337261387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690738129269358264121461 439756699619002337261387)
                  ·
                    rfl

theorem cell20_963476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_963476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963476 prefixEnd_963476 := by exact prefixLift 963476
  have htrace : WordTrace (prefixWord ++ tailWord_963476) baseStart_963476 baseEnd_963476 := by
    simpa [prefixWord, tailWord_963476, baseEnd_963476] using wordTrace_append hprefix tailTrace_963476
  have hstable : (prefixWord ++ tailWord_963476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963476).length < 2 ^ (prefixWord ++ tailWord_963476).sum := by decide
  have hdescent : baseEnd_963476 < baseStart_963476 := by decide
  rcases family_descends (prefixWord ++ tailWord_963476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963497 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_963497 : Nat := 118140960795 + 963497 * 2 ^ 59
def prefixEnd_963497 : Nat := 4983230072969 + 3 ^ 40 * 963497 * 2
def baseEnd_963497 : Nat := 439766284591219597561301

theorem tailTrace_963497 : CollatzResearch.WordTrace tailWord_963497 prefixEnd_963497 439766284591219597561301 := by
  unfold tailWord_963497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35141622590422396032040745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23427748393614930688027163 35141622590422396032040745)
  ·
    refine ⟨26356216942816797024030559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35141622590422396032040745 26356216942816797024030559)
    ·
      refine ⟨39534325414225195536045839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26356216942816797024030559 39534325414225195536045839)
      ·
        refine ⟨59301488121337793304068759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39534325414225195536045839 59301488121337793304068759)
        ·
          refine ⟨88952232182006689956103139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59301488121337793304068759 88952232182006689956103139)
          ·
            refine ⟨133428348273010034934154709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88952232182006689956103139 133428348273010034934154709)
            ·
              refine ⟨3127226912648672693769251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133428348273010034934154709 3127226912648672693769251)
              ·
                refine ⟨4690840368973009040653877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127226912648672693769251 4690840368973009040653877)
                ·
                  refine ⟨439766284591219597561301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690840368973009040653877 439766284591219597561301)
                  ·
                    rfl

theorem cell20_963497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_963497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963497 prefixEnd_963497 := by exact prefixLift 963497
  have htrace : WordTrace (prefixWord ++ tailWord_963497) baseStart_963497 baseEnd_963497 := by
    simpa [prefixWord, tailWord_963497, baseEnd_963497] using wordTrace_append hprefix tailTrace_963497
  have hstable : (prefixWord ++ tailWord_963497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963497).length < 2 ^ (prefixWord ++ tailWord_963497).sum := by decide
  have hdescent : baseEnd_963497 < baseStart_963497 := by decide
  rcases family_descends (prefixWord ++ tailWord_963497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963524 : List Nat := [2, 3, 3, 3, 1, 1, 1, 6]
def baseStart_963524 : Nat := 118140960795 + 963524 * 2 ^ 59
def prefixEnd_963524 : Nat := 4983230072969 + 3 ^ 40 * 963524 * 2
def baseEnd_963524 : Nat := 146592869375642501220397

theorem tailTrace_963524 : CollatzResearch.WordTrace tailWord_963524 prefixEnd_963524 146592869375642501220397 := by
  unfold tailWord_963524
  simp only [CollatzResearch.WordTrace]
  refine ⟨17571303680662289821636813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23428404907549719762182417 17571303680662289821636813)
  ·
    refine ⟨6589238880248358683113805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17571303680662289821636813 6589238880248358683113805)
    ·
      refine ⟨2470964580093134506167677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6589238880248358683113805 2470964580093134506167677)
      ·
        refine ⟨926611717534925439812879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2470964580093134506167677 926611717534925439812879)
        ·
          refine ⟨1389917576302388159719319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926611717534925439812879 1389917576302388159719319)
          ·
            refine ⟨2084876364453582239578979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389917576302388159719319 2084876364453582239578979)
            ·
              refine ⟨3127314546680373359368469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084876364453582239578979 3127314546680373359368469)
              ·
                refine ⟨146592869375642501220397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3127314546680373359368469 146592869375642501220397)
                ·
                  rfl

theorem cell20_963524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_963524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963524 prefixEnd_963524 := by exact prefixLift 963524
  have htrace : WordTrace (prefixWord ++ tailWord_963524) baseStart_963524 baseEnd_963524 := by
    simpa [prefixWord, tailWord_963524, baseEnd_963524] using wordTrace_append hprefix tailTrace_963524
  have hstable : (prefixWord ++ tailWord_963524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963524).length < 2 ^ (prefixWord ++ tailWord_963524).sum := by decide
  have hdescent : baseEnd_963524 < baseStart_963524 := by decide
  rcases family_descends (prefixWord ++ tailWord_963524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963526 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_963526 : Nat := 118140960795 + 963526 * 2 ^ 59
def prefixEnd_963526 : Nat := 4983230072969 + 3 ^ 40 * 963526 * 2
def baseEnd_963526 : Nat := 439779520981424385594517

theorem tailTrace_963526 : CollatzResearch.WordTrace tailWord_963526 prefixEnd_963526 439779520981424385594517 := by
  unfold tailWord_963526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098208759603666687026451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23428453538211555989897621 1098208759603666687026451)
  ·
    refine ⟨1647313139405500030539677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098208759603666687026451 1647313139405500030539677)
    ·
      refine ⟨617742427277062511452379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1647313139405500030539677 617742427277062511452379)
      ·
        refine ⟨926613640915593767178569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617742427277062511452379 926613640915593767178569)
        ·
          refine ⟨694960230686695325383927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926613640915593767178569 694960230686695325383927)
          ·
            refine ⟨1042440346030042988075891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694960230686695325383927 1042440346030042988075891)
            ·
              refine ⟨1563660519045064482113837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042440346030042988075891 1563660519045064482113837)
              ·
                refine ⟨586372694641899180792689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1563660519045064482113837 586372694641899180792689)
                ·
                  refine ⟨439779520981424385594517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586372694641899180792689 439779520981424385594517)
                  ·
                    rfl

theorem cell20_963526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_963526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963526 prefixEnd_963526 := by exact prefixLift 963526
  have htrace : WordTrace (prefixWord ++ tailWord_963526) baseStart_963526 baseEnd_963526 := by
    simpa [prefixWord, tailWord_963526, baseEnd_963526] using wordTrace_append hprefix tailTrace_963526
  have hstable : (prefixWord ++ tailWord_963526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963526).length < 2 ^ (prefixWord ++ tailWord_963526).sum := by decide
  have hdescent : baseEnd_963526 < baseStart_963526 := by decide
  rcases family_descends (prefixWord ++ tailWord_963526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963535 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_963535 : Nat := 118140960795 + 963535 * 2 ^ 59
def prefixEnd_963535 : Nat := 4983230072969 + 3 ^ 40 * 963535 * 2
def baseEnd_963535 : Nat := 439783628826660354294479

theorem tailTrace_963535 : CollatzResearch.WordTrace tailWord_963535 prefixEnd_963535 439783628826660354294479 := by
  unfold tailWord_963535
  simp only [CollatzResearch.WordTrace]
  refine ⟨35143008564284728521924059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23428672376189819014616039 35143008564284728521924059)
  ·
    refine ⟨52714512846427092782886089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35143008564284728521924059 52714512846427092782886089)
    ·
      refine ⟨39535884634820319587164567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52714512846427092782886089 39535884634820319587164567)
      ·
        refine ⟨59303826952230479380746851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39535884634820319587164567 59303826952230479380746851)
        ·
          refine ⟨88955740428345719071120277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59303826952230479380746851 88955740428345719071120277)
          ·
            refine ⟨4169800332578705581458763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88955740428345719071120277 4169800332578705581458763)
            ·
              refine ⟨6254700498868058372188145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169800332578705581458763 6254700498868058372188145)
              ·
                refine ⟨4691025374151043779141109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6254700498868058372188145 4691025374151043779141109)
                ·
                  refine ⟨439783628826660354294479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4691025374151043779141109 439783628826660354294479)
                  ·
                    rfl

theorem cell20_963535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_963535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963535 prefixEnd_963535 := by exact prefixLift 963535
  have htrace : WordTrace (prefixWord ++ tailWord_963535) baseStart_963535 baseEnd_963535 := by
    simpa [prefixWord, tailWord_963535, baseEnd_963535] using wordTrace_append hprefix tailTrace_963535
  have hstable : (prefixWord ++ tailWord_963535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963535).length < 2 ^ (prefixWord ++ tailWord_963535).sum := by decide
  have hdescent : baseEnd_963535 < baseStart_963535 := by decide
  rcases family_descends (prefixWord ++ tailWord_963535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963555 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 2]
def baseStart_963555 : Nat := 118140960795 + 963555 * 2 ^ 59
def prefixEnd_963555 : Nat := 4983230072969 + 3 ^ 40 * 963555 * 2
def baseEnd_963555 : Nat := 439792757371629173627731

theorem tailTrace_963555 : CollatzResearch.WordTrace tailWord_963555 prefixEnd_963555 439792757371629173627731 := by
  unfold tailWord_963555
  simp only [CollatzResearch.WordTrace]
  refine ⟨35143738024212271937652119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23429158682808181291768079 35143738024212271937652119)
  ·
    refine ⟨52715607036318407906478179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35143738024212271937652119 52715607036318407906478179)
    ·
      refine ⟨79073410554477611859717269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52715607036318407906478179 79073410554477611859717269)
      ·
        refine ⟨3706566119741138055924247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79073410554477611859717269 3706566119741138055924247)
        ·
          refine ⟨5559849179611707083886371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706566119741138055924247 5559849179611707083886371)
          ·
            refine ⟨8339773769417560625829557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559849179611707083886371 8339773769417560625829557)
            ·
              refine ⟨781853790882896308671521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8339773769417560625829557 781853790882896308671521)
              ·
                refine ⟨586390343162172231503641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781853790882896308671521 586390343162172231503641)
                ·
                  refine ⟨439792757371629173627731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586390343162172231503641 439792757371629173627731)
                  ·
                    rfl

theorem cell20_963555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 2].length) (baseStart_963555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963555 prefixEnd_963555 := by exact prefixLift 963555
  have htrace : WordTrace (prefixWord ++ tailWord_963555) baseStart_963555 baseEnd_963555 := by
    simpa [prefixWord, tailWord_963555, baseEnd_963555] using wordTrace_append hprefix tailTrace_963555
  have hstable : (prefixWord ++ tailWord_963555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963555).length < 2 ^ (prefixWord ++ tailWord_963555).sum := by decide
  have hdescent : baseEnd_963555 < baseStart_963555 := by decide
  rcases family_descends (prefixWord ++ tailWord_963555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963569 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 3]
def baseStart_963569 : Nat := 118140960795 + 963569 * 2 ^ 59
def prefixEnd_963569 : Nat := 4983230072969 + 3 ^ 40 * 963569 * 2
def baseEnd_963569 : Nat := 439799147353107347161007

theorem tailTrace_963569 : CollatzResearch.WordTrace tailWord_963569 prefixEnd_963569 439799147353107347161007 := by
  unfold tailWord_963569
  simp only [CollatzResearch.WordTrace]
  refine ⟨35144248646161552328661761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23429499097441034885774507 35144248646161552328661761)
  ·
    refine ⟨26358186484621164246496321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35144248646161552328661761 26358186484621164246496321)
    ·
      refine ⟨19768639863465873184872241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26358186484621164246496321 19768639863465873184872241)
      ·
        refine ⟨14826479897599404888654181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19768639863465873184872241 14826479897599404888654181)
        ·
          refine ⟨2779964980799888416622659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14826479897599404888654181 2779964980799888416622659)
          ·
            refine ⟨4169947471199832624933989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779964980799888416622659 4169947471199832624933989)
            ·
              refine ⟨781865150849968617175123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4169947471199832624933989 781865150849968617175123)
              ·
                refine ⟨1172797726274952925762685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781865150849968617175123 1172797726274952925762685)
                ·
                  refine ⟨439799147353107347161007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172797726274952925762685 439799147353107347161007)
                  ·
                    rfl

theorem cell20_963569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_963569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963569 prefixEnd_963569 := by exact prefixLift 963569
  have htrace : WordTrace (prefixWord ++ tailWord_963569) baseStart_963569 baseEnd_963569 := by
    simpa [prefixWord, tailWord_963569, baseEnd_963569] using wordTrace_append hprefix tailTrace_963569
  have hstable : (prefixWord ++ tailWord_963569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963569).length < 2 ^ (prefixWord ++ tailWord_963569).sum := by decide
  have hdescent : baseEnd_963569 < baseStart_963569 := by decide
  rcases family_descends (prefixWord ++ tailWord_963569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963604 : List Nat := [2, 4, 3, 11]
def baseStart_963604 : Nat := 118140960795 + 963604 * 2 ^ 59
def prefixEnd_963604 : Nat := 4983230072969 + 3 ^ 40 * 963604 * 2
def baseEnd_963604 : Nat := 1809938774925114325079

theorem tailTrace_963604 : CollatzResearch.WordTrace tailWord_963604 prefixEnd_963604 1809938774925114325079 := by
  unfold tailWord_963604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17572762600517376653092933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23430350134023168870790577 17572762600517376653092933)
  ·
    refine ⟨3294892987597008122454925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17572762600517376653092933 3294892987597008122454925)
    ·
      refine ⟨1235584870348878045920597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3294892987597008122454925 1235584870348878045920597)
      ·
        refine ⟨1809938774925114325079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1235584870348878045920597 1809938774925114325079)
        ·
          rfl

theorem cell20_963604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 11].length) (baseStart_963604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963604 prefixEnd_963604 := by exact prefixLift 963604
  have htrace : WordTrace (prefixWord ++ tailWord_963604) baseStart_963604 baseEnd_963604 := by
    simpa [prefixWord, tailWord_963604, baseEnd_963604] using wordTrace_append hprefix tailTrace_963604
  have hstable : (prefixWord ++ tailWord_963604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963604).length < 2 ^ (prefixWord ++ tailWord_963604).sum := by decide
  have hdescent : baseEnd_963604 < baseStart_963604 := by decide
  rcases family_descends (prefixWord ++ tailWord_963604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963607 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_963607 : Nat := 118140960795 + 963607 * 2 ^ 59
def prefixEnd_963607 : Nat := 4983230072969 + 3 ^ 40 * 963607 * 2
def baseEnd_963607 : Nat := 439816491588548103894185

theorem tailTrace_963607 : CollatzResearch.WordTrace tailWord_963607 prefixEnd_963607 439816491588548103894185 := by
  unfold tailWord_963607
  simp only [CollatzResearch.WordTrace]
  refine ⟨35145634620023884818545075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23430423080015923212363383 35145634620023884818545075)
  ·
    refine ⟨52718451930035827227817613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35145634620023884818545075 52718451930035827227817613)
    ·
      refine ⟨19769419473763435210431605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52718451930035827227817613 19769419473763435210431605)
      ·
        refine ⟨1853383075665322050977963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19769419473763435210431605 1853383075665322050977963)
        ·
          refine ⟨2780074613497983076466945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853383075665322050977963 2780074613497983076466945)
          ·
            refine ⟨2085055960123487307350209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780074613497983076466945 2085055960123487307350209)
            ·
              refine ⟨1563791970092615480512657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085055960123487307350209 1563791970092615480512657)
              ·
                refine ⟨1172843977569461610384493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563791970092615480512657 1172843977569461610384493)
                ·
                  refine ⟨439816491588548103894185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172843977569461610384493 439816491588548103894185)
                  ·
                    rfl

theorem cell20_963607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_963607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963607 prefixEnd_963607 := by exact prefixLift 963607
  have htrace : WordTrace (prefixWord ++ tailWord_963607) baseStart_963607 baseEnd_963607 := by
    simpa [prefixWord, tailWord_963607, baseEnd_963607] using wordTrace_append hprefix tailTrace_963607
  have hstable : (prefixWord ++ tailWord_963607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963607).length < 2 ^ (prefixWord ++ tailWord_963607).sum := by decide
  have hdescent : baseEnd_963607 < baseStart_963607 := by decide
  rcases family_descends (prefixWord ++ tailWord_963607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963638 : List Nat := [5, 1, 2, 1, 1, 3, 3, 4]
def baseStart_963638 : Nat := 118140960795 + 963638 * 2 ^ 59
def prefixEnd_963638 : Nat := 4983230072969 + 3 ^ 40 * 963638 * 2
def baseEnd_963638 : Nat := 146610213611083257953575

theorem tailTrace_963638 : CollatzResearch.WordTrace tailWord_963638 prefixEnd_963638 146610213611083257953575 := by
  unfold tailWord_963638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196672830181973569557723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23431176855274384741949045 2196672830181973569557723)
  ·
    refine ⟨3295009245272960354336585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196672830181973569557723 3295009245272960354336585)
    ·
      refine ⟨2471256933954720265752439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3295009245272960354336585 2471256933954720265752439)
      ·
        refine ⟨3706885400932080398628659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471256933954720265752439 3706885400932080398628659)
        ·
          refine ⟨5560328101398120597942989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706885400932080398628659 5560328101398120597942989)
          ·
            refine ⟨2085123038024295224228621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5560328101398120597942989 2085123038024295224228621)
            ·
              refine ⟨781921139259110709085733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2085123038024295224228621 781921139259110709085733)
              ·
                refine ⟨146610213611083257953575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781921139259110709085733 146610213611083257953575)
                ·
                  rfl

theorem cell20_963638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_963638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963638 prefixEnd_963638 := by exact prefixLift 963638
  have htrace : WordTrace (prefixWord ++ tailWord_963638) baseStart_963638 baseEnd_963638 := by
    simpa [prefixWord, tailWord_963638, baseEnd_963638] using wordTrace_append hprefix tailTrace_963638
  have hstable : (prefixWord ++ tailWord_963638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963638).length < 2 ^ (prefixWord ++ tailWord_963638).sum := by decide
  have hdescent : baseEnd_963638 < baseStart_963638 := by decide
  rcases family_descends (prefixWord ++ tailWord_963638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963656 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_963656 : Nat := 118140960795 + 963656 * 2 ^ 59
def prefixEnd_963656 : Nat := 4983230072969 + 3 ^ 40 * 963656 * 2
def baseEnd_963656 : Nat := 439838856523721711260651

theorem tailTrace_963656 : CollatzResearch.WordTrace tailWord_963656 prefixEnd_963656 439838856523721711260651 := by
  unfold tailWord_963656
  simp only [CollatzResearch.WordTrace]
  refine ⟨17573710898423183093539411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23431614531230910791385881 17573710898423183093539411)
  ·
    refine ⟨26360566347634774640309117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17573710898423183093539411 26360566347634774640309117)
    ·
      refine ⟨9885212380363040490115919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26360566347634774640309117 9885212380363040490115919)
      ·
        refine ⟨14827818570544560735173879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885212380363040490115919 14827818570544560735173879)
        ·
          refine ⟨22241727855816841102760819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14827818570544560735173879 22241727855816841102760819)
          ·
            refine ⟨33362591783725261654141229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22241727855816841102760819 33362591783725261654141229)
            ·
              refine ⟨12510971918896973120302961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33362591783725261654141229 12510971918896973120302961)
              ·
                refine ⟨9383228939172729840227221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12510971918896973120302961 9383228939172729840227221)
                ·
                  refine ⟨439838856523721711260651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9383228939172729840227221 439838856523721711260651)
                  ·
                    rfl

theorem cell20_963656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_963656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963656 prefixEnd_963656 := by exact prefixLift 963656
  have htrace : WordTrace (prefixWord ++ tailWord_963656) baseStart_963656 baseEnd_963656 := by
    simpa [prefixWord, tailWord_963656, baseEnd_963656] using wordTrace_append hprefix tailTrace_963656
  have hstable : (prefixWord ++ tailWord_963656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963656).length < 2 ^ (prefixWord ++ tailWord_963656).sum := by decide
  have hdescent : baseEnd_963656 < baseStart_963656 := by decide
  rcases family_descends (prefixWord ++ tailWord_963656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963666 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_963666 : Nat := 118140960795 + 963666 * 2 ^ 59
def prefixEnd_963666 : Nat := 4983230072969 + 3 ^ 40 * 963666 * 2
def baseEnd_963666 : Nat := 439843420796206120927277

theorem tailTrace_963666 : CollatzResearch.WordTrace tailWord_963666 prefixEnd_963666 439843420796206120927277 := by
  unfold tailWord_963666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786946631702534473735713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23431857684540091929961901 8786946631702534473735713)
  ·
    refine ⟨6590209973776900855301785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8786946631702534473735713 6590209973776900855301785)
    ·
      refine ⟨4942657480332675641476339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6590209973776900855301785 4942657480332675641476339)
      ·
        refine ⟨7413986220499013462214509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942657480332675641476339 7413986220499013462214509)
        ·
          refine ⟨2780244832687130048330441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7413986220499013462214509 2780244832687130048330441)
          ·
            refine ⟨2085183624515347536247831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780244832687130048330441 2085183624515347536247831)
            ·
              refine ⟨3127775436773021304371747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085183624515347536247831 3127775436773021304371747)
              ·
                refine ⟨4691663155159531956557621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127775436773021304371747 4691663155159531956557621)
                ·
                  refine ⟨439843420796206120927277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4691663155159531956557621 439843420796206120927277)
                  ·
                    rfl

theorem cell20_963666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_963666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963666 prefixEnd_963666 := by exact prefixLift 963666
  have htrace : WordTrace (prefixWord ++ tailWord_963666) baseStart_963666 baseEnd_963666 := by
    simpa [prefixWord, tailWord_963666, baseEnd_963666] using wordTrace_append hprefix tailTrace_963666
  have hstable : (prefixWord ++ tailWord_963666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963666).length < 2 ^ (prefixWord ++ tailWord_963666).sum := by decide
  have hdescent : baseEnd_963666 < baseStart_963666 := by decide
  rcases family_descends (prefixWord ++ tailWord_963666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963710 : List Nat := [4, 2, 4, 1, 2, 1, 6]
def baseStart_963710 : Nat := 118140960795 + 963710 * 2 ^ 59
def prefixEnd_963710 : Nat := 4983230072969 + 3 ^ 40 * 963710 * 2
def baseEnd_963710 : Nat := 48873722621681947051159

theorem tailTrace_963710 : CollatzResearch.WordTrace tailWord_963710 prefixEnd_963710 48873722621681947051159 := by
  unfold tailWord_963710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393673917331341676193073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23432927559100488939696389 4393673917331341676193073)
  ·
    refine ⟨3295255437998506257144805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4393673917331341676193073 3295255437998506257144805)
    ·
      refine ⟨617860394624719923214651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3295255437998506257144805 617860394624719923214651)
      ·
        refine ⟨926790591937079884821977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617860394624719923214651 926790591937079884821977)
        ·
          refine ⟨695092943952809913616483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926790591937079884821977 695092943952809913616483)
          ·
            refine ⟨1042639415929214870424725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695092943952809913616483 1042639415929214870424725)
            ·
              refine ⟨48873722621681947051159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1042639415929214870424725 48873722621681947051159)
              ·
                rfl

theorem cell20_963710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 6].length) (baseStart_963710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963710 prefixEnd_963710 := by exact prefixLift 963710
  have htrace : WordTrace (prefixWord ++ tailWord_963710) baseStart_963710 baseEnd_963710 := by
    simpa [prefixWord, tailWord_963710, baseEnd_963710] using wordTrace_append hprefix tailTrace_963710
  have hstable : (prefixWord ++ tailWord_963710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963710).length < 2 ^ (prefixWord ++ tailWord_963710).sum := by decide
  have hdescent : baseEnd_963710 < baseStart_963710 := by decide
  rcases family_descends (prefixWord ++ tailWord_963710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963738 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_963738 : Nat := 118140960795 + 963738 * 2 ^ 59
def prefixEnd_963738 : Nat := 4983230072969 + 3 ^ 40 * 963738 * 2
def baseEnd_963738 : Nat := 439876283558093870526983

theorem tailTrace_963738 : CollatzResearch.WordTrace tailWord_963738 prefixEnd_963738 439876283558093870526983 := by
  unfold tailWord_963738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787603145637323547890967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23433608388366196127709245 8787603145637323547890967)
  ·
    refine ⟨13181404718455985321836451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8787603145637323547890967 13181404718455985321836451)
    ·
      refine ⟨19772107077683977982754677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13181404718455985321836451 19772107077683977982754677)
      ·
        refine ⟨1853635038532872935883251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19772107077683977982754677 1853635038532872935883251)
        ·
          refine ⟨2780452557799309403824877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853635038532872935883251 2780452557799309403824877)
          ·
            refine ⟨1042669709174741026434329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2780452557799309403824877 1042669709174741026434329)
            ·
              refine ⟨782002281881055769825747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042669709174741026434329 782002281881055769825747)
              ·
                refine ⟨1173003422821583654738621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782002281881055769825747 1173003422821583654738621)
                ·
                  refine ⟨439876283558093870526983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173003422821583654738621 439876283558093870526983)
                  ·
                    rfl

theorem cell20_963738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_963738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963738 prefixEnd_963738 := by exact prefixLift 963738
  have htrace : WordTrace (prefixWord ++ tailWord_963738) baseStart_963738 baseEnd_963738 := by
    simpa [prefixWord, tailWord_963738, baseEnd_963738] using wordTrace_append hprefix tailTrace_963738
  have hstable : (prefixWord ++ tailWord_963738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963738).length < 2 ^ (prefixWord ++ tailWord_963738).sum := by decide
  have hdescent : baseEnd_963738 < baseStart_963738 := by decide
  rcases family_descends (prefixWord ++ tailWord_963738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963790 : List Nat := [4, 1, 1, 1, 6, 1, 1, 5]
def baseStart_963790 : Nat := 118140960795 + 963790 * 2 ^ 59
def prefixEnd_963790 : Nat := 4983230072969 + 3 ^ 40 * 963790 * 2
def baseEnd_963790 : Nat := 146633339258337600264479

theorem tailTrace_963790 : CollatzResearch.WordTrace tailWord_963790 prefixEnd_963790 146633339258337600264479 := by
  unfold tailWord_963790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394038647295113384057103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23434872785573938048304549 4394038647295113384057103)
  ·
    refine ⟨6591057970942670076085655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394038647295113384057103 6591057970942670076085655)
    ·
      refine ⟨9886586956414005114128483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591057970942670076085655 9886586956414005114128483)
      ·
        refine ⟨14829880434621007671192725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9886586956414005114128483 14829880434621007671192725)
        ·
          refine ⟨695150645372859734587159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14829880434621007671192725 695150645372859734587159)
          ·
            refine ⟨1042725968059289601880739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695150645372859734587159 1042725968059289601880739)
            ·
              refine ⟨1564088952088934402821109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042725968059289601880739 1564088952088934402821109)
              ·
                refine ⟨146633339258337600264479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1564088952088934402821109 146633339258337600264479)
                ·
                  rfl

theorem cell20_963790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_963790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963790 prefixEnd_963790 := by exact prefixLift 963790
  have htrace : WordTrace (prefixWord ++ tailWord_963790) baseStart_963790 baseEnd_963790 := by
    simpa [prefixWord, tailWord_963790, baseEnd_963790] using wordTrace_append hprefix tailTrace_963790
  have hstable : (prefixWord ++ tailWord_963790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963790).length < 2 ^ (prefixWord ++ tailWord_963790).sum := by decide
  have hdescent : baseEnd_963790 < baseStart_963790 := by decide
  rcases family_descends (prefixWord ++ tailWord_963790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963808 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_963808 : Nat := 118140960795 + 963808 * 2 ^ 59
def prefixEnd_963808 : Nat := 4983230072969 + 3 ^ 40 * 963808 * 2
def baseEnd_963808 : Nat := 439908233465484738193363

theorem tailTrace_963808 : CollatzResearch.WordTrace tailWord_963808 prefixEnd_963808 439908233465484738193363 := by
  unfold tailWord_963808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576482846147848073306039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23435310461530464097741385 17576482846147848073306039)
  ·
    refine ⟨26364724269221772109959059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17576482846147848073306039 26364724269221772109959059)
    ·
      refine ⟨39547086403832658164938589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26364724269221772109959059 39547086403832658164938589)
      ·
        refine ⟨14830157401437246811851971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39547086403832658164938589 14830157401437246811851971)
        ·
          refine ⟨22245236102155870217777957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14830157401437246811851971 22245236102155870217777957)
          ·
            refine ⟨4170981769154225665833367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22245236102155870217777957 4170981769154225665833367)
            ·
              refine ⟨6256472653731338498750051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170981769154225665833367 6256472653731338498750051)
              ·
                refine ⟨9384708980597007748125077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256472653731338498750051 9384708980597007748125077)
                ·
                  refine ⟨439908233465484738193363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9384708980597007748125077 439908233465484738193363)
                  ·
                    rfl

theorem cell20_963808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_963808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963808 prefixEnd_963808 := by exact prefixLift 963808
  have htrace : WordTrace (prefixWord ++ tailWord_963808) baseStart_963808 baseEnd_963808 := by
    simpa [prefixWord, tailWord_963808, baseEnd_963808] using wordTrace_append hprefix tailTrace_963808
  have hstable : (prefixWord ++ tailWord_963808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963808).length < 2 ^ (prefixWord ++ tailWord_963808).sum := by decide
  have hdescent : baseEnd_963808 < baseStart_963808 := by decide
  rcases family_descends (prefixWord ++ tailWord_963808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963821 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 2]
def baseStart_963821 : Nat := 118140960795 + 963821 * 2 ^ 59
def prefixEnd_963821 : Nat := 4983230072969 + 3 ^ 40 * 963821 * 2
def baseEnd_963821 : Nat := 439914167019714470759977

theorem tailTrace_963821 : CollatzResearch.WordTrace tailWord_963821 prefixEnd_963821 439914167019714470759977 := by
  unfold tailWord_963821
  simp only [CollatzResearch.WordTrace]
  refine ⟨35153439841248599366835317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23435626560832399577890211 35153439841248599366835317)
  ·
    refine ⟨3295634985117056190640811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35153439841248599366835317 3295634985117056190640811)
    ·
      refine ⟨4943452477675584285961217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3295634985117056190640811 4943452477675584285961217)
      ·
        refine ⟨3707589358256688214470913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4943452477675584285961217 3707589358256688214470913)
        ·
          refine ⟨2780692018692516160853185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3707589358256688214470913 2780692018692516160853185)
          ·
            refine ⟨2085519014019387120639889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780692018692516160853185 2085519014019387120639889)
            ·
              refine ⟨1564139260514540340479917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085519014019387120639889 1564139260514540340479917)
              ·
                refine ⟨586552222692952627679969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1564139260514540340479917 586552222692952627679969)
                ·
                  refine ⟨439914167019714470759977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586552222692952627679969 439914167019714470759977)
                  ·
                    rfl

theorem cell20_963821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_963821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963821 prefixEnd_963821 := by exact prefixLift 963821
  have htrace : WordTrace (prefixWord ++ tailWord_963821) baseStart_963821 baseEnd_963821 := by
    simpa [prefixWord, tailWord_963821, baseEnd_963821] using wordTrace_append hprefix tailTrace_963821
  have hstable : (prefixWord ++ tailWord_963821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963821).length < 2 ^ (prefixWord ++ tailWord_963821).sum := by decide
  have hdescent : baseEnd_963821 < baseStart_963821 := by decide
  rcases family_descends (prefixWord ++ tailWord_963821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963839 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_963839 : Nat := 118140960795 + 963839 * 2 ^ 59
def prefixEnd_963839 : Nat := 4983230072969 + 3 ^ 40 * 963839 * 2
def baseEnd_963839 : Nat := 439922382710186408159903

theorem tailTrace_963839 : CollatzResearch.WordTrace tailWord_963839 prefixEnd_963839 439922382710186408159903 := by
  unfold tailWord_963839
  simp only [CollatzResearch.WordTrace]
  refine ⟨35154096355183388440990571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23436064236788925627327047 35154096355183388440990571)
  ·
    refine ⟨52731144532775082661485857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35154096355183388440990571 52731144532775082661485857)
    ·
      refine ⟨39548358399581311996114393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52731144532775082661485857 39548358399581311996114393)
      ·
        refine ⟨29661268799685983997085795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39548358399581311996114393 29661268799685983997085795)
        ·
          refine ⟨44491903199528975995628693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29661268799685983997085795 44491903199528975995628693)
          ·
            refine ⟨2085557962477920749795095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44491903199528975995628693 2085557962477920749795095)
            ·
              refine ⟨3128336943716881124692643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085557962477920749795095 3128336943716881124692643)
              ·
                refine ⟨4692505415575321687038965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128336943716881124692643 4692505415575321687038965)
                ·
                  refine ⟨439922382710186408159903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4692505415575321687038965 439922382710186408159903)
                  ·
                    rfl

theorem cell20_963839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_963839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963839 prefixEnd_963839 := by exact prefixLift 963839
  have htrace : WordTrace (prefixWord ++ tailWord_963839) baseStart_963839 baseEnd_963839 := by
    simpa [prefixWord, tailWord_963839, baseEnd_963839] using wordTrace_append hprefix tailTrace_963839
  have hstable : (prefixWord ++ tailWord_963839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963839).length < 2 ^ (prefixWord ++ tailWord_963839).sum := by decide
  have hdescent : baseEnd_963839 < baseStart_963839 := by decide
  rcases family_descends (prefixWord ++ tailWord_963839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963877 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_963877 : Nat := 118140960795 + 963877 * 2 ^ 59
def prefixEnd_963877 : Nat := 4983230072969 + 3 ^ 40 * 963877 * 2
def baseEnd_963877 : Nat := 439939726945627164893081

theorem tailTrace_963877 : CollatzResearch.WordTrace tailWord_963877 prefixEnd_963877 439939726945627164893081 := by
  unfold tailWord_963877
  simp only [CollatzResearch.WordTrace]
  refine ⟨35155482329045720930873885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23436988219363813953915923 35155482329045720930873885)
  ·
    refine ⟨13183305873392145349077707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35155482329045720930873885 13183305873392145349077707)
    ·
      refine ⟨19774958810088218023616561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13183305873392145349077707 19774958810088218023616561)
      ·
        refine ⟨14831219107566163517712421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19774958810088218023616561 14831219107566163517712421)
        ·
          refine ⟨2780853582668655659571079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14831219107566163517712421 2780853582668655659571079)
          ·
            refine ⟨4171280374002983489356619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780853582668655659571079 4171280374002983489356619)
            ·
              refine ⟨6256920561004475234034929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171280374002983489356619 6256920561004475234034929)
              ·
                refine ⟨4692690420753356425526197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6256920561004475234034929 4692690420753356425526197)
                ·
                  refine ⟨439939726945627164893081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4692690420753356425526197 439939726945627164893081)
                  ·
                    rfl

theorem cell20_963877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_963877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963877 prefixEnd_963877 := by exact prefixLift 963877
  have htrace : WordTrace (prefixWord ++ tailWord_963877) baseStart_963877 baseEnd_963877 := by
    simpa [prefixWord, tailWord_963877, baseEnd_963877] using wordTrace_append hprefix tailTrace_963877
  have hstable : (prefixWord ++ tailWord_963877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963877).length < 2 ^ (prefixWord ++ tailWord_963877).sum := by decide
  have hdescent : baseEnd_963877 < baseStart_963877 := by decide
  rcases family_descends (prefixWord ++ tailWord_963877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963891 : List Nat := [1, 1, 1, 2, 5, 2, 8]
def baseStart_963891 : Nat := 118140960795 + 963891 * 2 ^ 59
def prefixEnd_963891 : Nat := 4983230072969 + 3 ^ 40 * 963891 * 2
def baseEnd_963891 : Nat := 48882901880789482047373

theorem tailTrace_963891 : CollatzResearch.WordTrace tailWord_963891 prefixEnd_963891 48882901880789482047373 := by
  unfold tailWord_963891
  simp only [CollatzResearch.WordTrace]
  refine ⟨35155992950995001321883527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23437328633996667547922351 35155992950995001321883527)
  ·
    refine ⟨52733989426492501982825291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35155992950995001321883527 52733989426492501982825291)
    ·
      refine ⟨79100984139738752974237937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52733989426492501982825291 79100984139738752974237937)
      ·
        refine ⟨59325738104804064730678453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79100984139738752974237937 59325738104804064730678453)
        ·
          refine ⟨5561787947325381068501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59325738104804064730678453 5561787947325381068501105)
          ·
            refine ⟨4171340960494035801375829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5561787947325381068501105 4171340960494035801375829)
            ·
              refine ⟨48882901880789482047373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4171340960494035801375829 48882901880789482047373)
              ·
                rfl

theorem cell20_963891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_963891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963891 prefixEnd_963891 := by exact prefixLift 963891
  have htrace : WordTrace (prefixWord ++ tailWord_963891) baseStart_963891 baseEnd_963891 := by
    simpa [prefixWord, tailWord_963891, baseEnd_963891] using wordTrace_append hprefix tailTrace_963891
  have hstable : (prefixWord ++ tailWord_963891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963891).length < 2 ^ (prefixWord ++ tailWord_963891).sum := by decide
  have hdescent : baseEnd_963891 < baseStart_963891 := by decide
  rcases family_descends (prefixWord ++ tailWord_963891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963897 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 4]
def baseStart_963897 : Nat := 118140960795 + 963897 * 2 ^ 59
def prefixEnd_963897 : Nat := 4983230072969 + 3 ^ 40 * 963897 * 2
def baseEnd_963897 : Nat := 439948855490595984226333

theorem tailTrace_963897 : CollatzResearch.WordTrace tailWord_963897 prefixEnd_963897 439948855490595984226333 := by
  unfold tailWord_963897
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156211788973264346601945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23437474525982176231067963 35156211788973264346601945)
  ·
    refine ⟨26367158841729948259951459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35156211788973264346601945 26367158841729948259951459)
    ·
      refine ⟨39550738262594922389927189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26367158841729948259951459 39550738262594922389927189)
      ·
        refine ⟨1853940856059136987027837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39550738262594922389927189 1853940856059136987027837)
        ·
          refine ⟨695227821022176370135439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1853940856059136987027837 695227821022176370135439)
          ·
            refine ⟨1042841731533264555203159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695227821022176370135439 1042841731533264555203159)
            ·
              refine ⟨1564262597299896832804739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042841731533264555203159 1564262597299896832804739)
              ·
                refine ⟨2346393895949845249207109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564262597299896832804739 2346393895949845249207109)
                ·
                  refine ⟨439948855490595984226333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2346393895949845249207109 439948855490595984226333)
                  ·
                    rfl

theorem cell20_963897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_963897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963897 prefixEnd_963897 := by exact prefixLift 963897
  have htrace : WordTrace (prefixWord ++ tailWord_963897) baseStart_963897 baseEnd_963897 := by
    simpa [prefixWord, tailWord_963897, baseEnd_963897] using wordTrace_append hprefix tailTrace_963897
  have hstable : (prefixWord ++ tailWord_963897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963897).length < 2 ^ (prefixWord ++ tailWord_963897).sum := by decide
  have hdescent : baseEnd_963897 < baseStart_963897 := by decide
  rcases family_descends (prefixWord ++ tailWord_963897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963911 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 3]
def baseStart_963911 : Nat := 118140960795 + 963911 * 2 ^ 59
def prefixEnd_963911 : Nat := 4983230072969 + 3 ^ 40 * 963911 * 2
def baseEnd_963911 : Nat := 439955245472074157759609

theorem tailTrace_963911 : CollatzResearch.WordTrace tailWord_963911 prefixEnd_963911 439955245472074157759609 := by
  unfold tailWord_963911
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156722410922544737611587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23437814940615029825074391 35156722410922544737611587)
  ·
    refine ⟨52735083616383817106417381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35156722410922544737611587 52735083616383817106417381)
    ·
      refine ⟨9887828178071965707453259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52735083616383817106417381 9887828178071965707453259)
      ·
        refine ⟨14831742267107948561179889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887828178071965707453259 14831742267107948561179889)
        ·
          refine ⟨11123806700330961420884917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14831742267107948561179889 11123806700330961420884917)
          ·
            refine ⟨1042856878156027633207961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11123806700330961420884917 1042856878156027633207961)
            ·
              refine ⟨782142658617020724905971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042856878156027633207961 782142658617020724905971)
              ·
                refine ⟨1173213987925531087358957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782142658617020724905971 1173213987925531087358957)
                ·
                  refine ⟨439955245472074157759609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173213987925531087358957 439955245472074157759609)
                  ·
                    rfl

theorem cell20_963911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_963911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963911 prefixEnd_963911 := by exact prefixLift 963911
  have htrace : WordTrace (prefixWord ++ tailWord_963911) baseStart_963911 baseEnd_963911 := by
    simpa [prefixWord, tailWord_963911, baseEnd_963911] using wordTrace_append hprefix tailTrace_963911
  have hstable : (prefixWord ++ tailWord_963911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963911).length < 2 ^ (prefixWord ++ tailWord_963911).sum := by decide
  have hdescent : baseEnd_963911 < baseStart_963911 := by decide
  rcases family_descends (prefixWord ++ tailWord_963911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963922 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_963922 : Nat := 118140960795 + 963922 * 2 ^ 59
def prefixEnd_963922 : Nat := 4983230072969 + 3 ^ 40 * 963922 * 2
def baseEnd_963922 : Nat := 439960266171807008392897

theorem tailTrace_963922 : CollatzResearch.WordTrace tailWord_963922 prefixEnd_963922 439960266171807008392897 := by
  unfold tailWord_963922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789280903470673404065505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23438082409255129077508013 8789280903470673404065505)
  ·
    refine ⟨6591960677603005053049129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8789280903470673404065505 6591960677603005053049129)
    ·
      refine ⟨4943970508202253789786847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6591960677603005053049129 4943970508202253789786847)
      ·
        refine ⟨7415955762303380684680271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4943970508202253789786847 7415955762303380684680271)
        ·
          refine ⟨11123933643455071027020407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415955762303380684680271 11123933643455071027020407)
          ·
            refine ⟨16685900465182606540530611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123933643455071027020407 16685900465182606540530611)
            ·
              refine ⟨25028850697773909810795917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16685900465182606540530611 25028850697773909810795917)
              ·
                refine ⟨9385819011665216179048469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25028850697773909810795917 9385819011665216179048469)
                ·
                  refine ⟨439960266171807008392897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9385819011665216179048469 439960266171807008392897)
                  ·
                    rfl

theorem cell20_963922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_963922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963922 prefixEnd_963922 := by exact prefixLift 963922
  have htrace : WordTrace (prefixWord ++ tailWord_963922) baseStart_963922 baseEnd_963922 := by
    simpa [prefixWord, tailWord_963922, baseEnd_963922] using wordTrace_append hprefix tailTrace_963922
  have hstable : (prefixWord ++ tailWord_963922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963922).length < 2 ^ (prefixWord ++ tailWord_963922).sum := by decide
  have hdescent : baseEnd_963922 < baseStart_963922 := by decide
  rcases family_descends (prefixWord ++ tailWord_963922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963929 : List Nat := [1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_963929 : Nat := 118140960795 + 963929 * 2 ^ 59
def prefixEnd_963929 : Nat := 4983230072969 + 3 ^ 40 * 963929 * 2
def baseEnd_963929 : Nat := 146654487054182031719845

theorem tailTrace_963929 : CollatzResearch.WordTrace tailWord_963929 prefixEnd_963929 146654487054182031719845 := by
  unfold tailWord_963929
  simp only [CollatzResearch.WordTrace]
  refine ⟨35157378924857333811766841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23438252616571555874511227 35157378924857333811766841)
  ·
    refine ⟨26368034193643000358825131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35157378924857333811766841 26368034193643000358825131)
    ·
      refine ⟨39552051290464500538237697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26368034193643000358825131 39552051290464500538237697)
      ·
        refine ⟨29664038467848375403678273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39552051290464500538237697 29664038467848375403678273)
        ·
          refine ⟨22248028850886281552758705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29664038467848375403678273 22248028850886281552758705)
          ·
            refine ⟨16686021638164711164569029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22248028850886281552758705 16686021638164711164569029)
            ·
              refine ⟨3128629057155883343356693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16686021638164711164569029 3128629057155883343356693)
              ·
                refine ⟨146654487054182031719845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3128629057155883343356693 146654487054182031719845)
                ·
                  rfl

theorem cell20_963929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_963929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963929 prefixEnd_963929 := by exact prefixLift 963929
  have htrace : WordTrace (prefixWord ++ tailWord_963929) baseStart_963929 baseEnd_963929 := by
    simpa [prefixWord, tailWord_963929, baseEnd_963929] using wordTrace_append hprefix tailTrace_963929
  have hstable : (prefixWord ++ tailWord_963929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963929).length < 2 ^ (prefixWord ++ tailWord_963929).sum := by decide
  have hdescent : baseEnd_963929 < baseStart_963929 := by decide
  rcases family_descends (prefixWord ++ tailWord_963929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963946 : List Nat := [3, 1, 3, 3, 2, 8]
def baseStart_963946 : Nat := 118140960795 + 963946 * 2 ^ 59
def prefixEnd_963946 : Nat := 4983230072969 + 3 ^ 40 * 963946 * 2
def baseEnd_963946 : Nat := 16295230386139614503437

theorem tailTrace_963946 : CollatzResearch.WordTrace tailWord_963946 prefixEnd_963946 16295230386139614503437 := by
  unfold tailWord_963946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789499741448936428783923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23438665977197163810090461 8789499741448936428783923)
  ·
    refine ⟨13184249612173404643175885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8789499741448936428783923 13184249612173404643175885)
    ·
      refine ⟨4944093604565026741190957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13184249612173404643175885 4944093604565026741190957)
      ·
        refine ⟨1854035101711885027946609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4944093604565026741190957 1854035101711885027946609)
        ·
          refine ⟨1390526326283913770959957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1854035101711885027946609 1390526326283913770959957)
          ·
            refine ⟨16295230386139614503437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1390526326283913770959957 16295230386139614503437)
            ·
              rfl

theorem cell20_963946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 8].length) (baseStart_963946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963946 prefixEnd_963946 := by exact prefixLift 963946
  have htrace : WordTrace (prefixWord ++ tailWord_963946) baseStart_963946 baseEnd_963946 := by
    simpa [prefixWord, tailWord_963946, baseEnd_963946] using wordTrace_append hprefix tailTrace_963946
  have hstable : (prefixWord ++ tailWord_963946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963946).length < 2 ^ (prefixWord ++ tailWord_963946).sum := by decide
  have hdescent : baseEnd_963946 < baseStart_963946 := by decide
  rcases family_descends (prefixWord ++ tailWord_963946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963953 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_963953 : Nat := 118140960795 + 963953 * 2 ^ 59
def prefixEnd_963953 : Nat := 4983230072969 + 3 ^ 40 * 963953 * 2
def baseEnd_963953 : Nat := 439974415416508678359437

theorem tailTrace_963953 : CollatzResearch.WordTrace tailWord_963953 prefixEnd_963953 439974415416508678359437 := by
  unfold tailWord_963953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35158254276770385910640513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23438836184513590607093675 35158254276770385910640513)
  ·
    refine ⟨26368690707577789432980385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35158254276770385910640513 26368690707577789432980385)
    ·
      refine ⟨19776518030683342074735289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26368690707577789432980385 19776518030683342074735289)
      ·
        refine ⟨14832388523012506556051467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19776518030683342074735289 14832388523012506556051467)
        ·
          refine ⟨22248582784518759834077201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832388523012506556051467 22248582784518759834077201)
          ·
            refine ⟨16686437088389069875557901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22248582784518759834077201 16686437088389069875557901)
            ·
              refine ⟨6257413908145901203334213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16686437088389069875557901 6257413908145901203334213)
              ·
                refine ⟨1173265107777356475625165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6257413908145901203334213 1173265107777356475625165)
                ·
                  refine ⟨439974415416508678359437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173265107777356475625165 439974415416508678359437)
                  ·
                    rfl

theorem cell20_963953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_963953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963953 prefixEnd_963953 := by exact prefixLift 963953
  have htrace : WordTrace (prefixWord ++ tailWord_963953) baseStart_963953 baseEnd_963953 := by
    simpa [prefixWord, tailWord_963953, baseEnd_963953] using wordTrace_append hprefix tailTrace_963953
  have hstable : (prefixWord ++ tailWord_963953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963953).length < 2 ^ (prefixWord ++ tailWord_963953).sum := by decide
  have hdescent : baseEnd_963953 < baseStart_963953 := by decide
  rcases family_descends (prefixWord ++ tailWord_963953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963977 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_963977 : Nat := 118140960795 + 963977 * 2 ^ 59
def prefixEnd_963977 : Nat := 4983230072969 + 3 ^ 40 * 963977 * 2
def baseEnd_963977 : Nat := 439985369670471261559339

theorem tailTrace_963977 : CollatzResearch.WordTrace tailWord_963977 prefixEnd_963977 439985369670471261559339 := by
  unfold tailWord_963977
  simp only [CollatzResearch.WordTrace]
  refine ⟨35159129628683438009514185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23439419752455625339676123 35159129628683438009514185)
  ·
    refine ⟨26369347221512578507135639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35159129628683438009514185 26369347221512578507135639)
    ·
      refine ⟨39554020832268867760703459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26369347221512578507135639 39554020832268867760703459)
      ·
        refine ⟨59331031248403301641055189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39554020832268867760703459 59331031248403301641055189)
        ·
          refine ⟨1390571044884452382212231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59331031248403301641055189 1390571044884452382212231)
          ·
            refine ⟨2085856567326678573318347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390571044884452382212231 2085856567326678573318347)
            ·
              refine ⟨3128784850990017859977521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085856567326678573318347 3128784850990017859977521)
              ·
                refine ⟨2346588638242513394983141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128784850990017859977521 2346588638242513394983141)
                ·
                  refine ⟨439985369670471261559339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2346588638242513394983141 439985369670471261559339)
                  ·
                    rfl

theorem cell20_963977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_963977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963977 prefixEnd_963977 := by exact prefixLift 963977
  have htrace : WordTrace (prefixWord ++ tailWord_963977) baseStart_963977 baseEnd_963977 := by
    simpa [prefixWord, tailWord_963977, baseEnd_963977] using wordTrace_append hprefix tailTrace_963977
  have hstable : (prefixWord ++ tailWord_963977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963977).length < 2 ^ (prefixWord ++ tailWord_963977).sum := by decide
  have hdescent : baseEnd_963977 < baseStart_963977 := by decide
  rcases family_descends (prefixWord ++ tailWord_963977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963994 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_963994 : Nat := 118140960795 + 963994 * 2 ^ 59
def prefixEnd_963994 : Nat := 4983230072969 + 3 ^ 40 * 963994 * 2
def baseEnd_963994 : Nat := 439993128933694757992603

theorem tailTrace_963994 : CollatzResearch.WordTrace tailWord_963994 prefixEnd_963994 439993128933694757992603 := by
  unfold tailWord_963994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789937417405462478220759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23439833113081233275255357 8789937417405462478220759)
  ·
    refine ⟨13184906126108193717331139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8789937417405462478220759 13184906126108193717331139)
    ·
      refine ⟨19777359189162290575996709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13184906126108193717331139 19777359189162290575996709)
      ·
        refine ⟨3708254847967929482999383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19777359189162290575996709 3708254847967929482999383)
        ·
          refine ⟨5562382271951894224499075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708254847967929482999383 5562382271951894224499075)
          ·
            refine ⟨8343573407927841336748613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562382271951894224499075 8343573407927841336748613)
            ·
              refine ⟨1564420013986470250640365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8343573407927841336748613 1564420013986470250640365)
              ·
                refine ⟨586657505244926343990137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1564420013986470250640365 586657505244926343990137)
                ·
                  refine ⟨439993128933694757992603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586657505244926343990137 439993128933694757992603)
                  ·
                    rfl

theorem cell20_963994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_963994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_963994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_963994 prefixEnd_963994 := by exact prefixLift 963994
  have htrace : WordTrace (prefixWord ++ tailWord_963994) baseStart_963994 baseEnd_963994 := by
    simpa [prefixWord, tailWord_963994, baseEnd_963994] using wordTrace_append hprefix tailTrace_963994
  have hstable : (prefixWord ++ tailWord_963994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963994).length < 2 ^ (prefixWord ++ tailWord_963994).sum := by decide
  have hdescent : baseEnd_963994 < baseStart_963994 := by decide
  rcases family_descends (prefixWord ++ tailWord_963994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964025 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 3]
def baseStart_964025 : Nat := 118140960795 + 964025 * 2 ^ 59
def prefixEnd_964025 : Nat := 4983230072969 + 3 ^ 40 * 964025 * 2
def baseEnd_964025 : Nat := 440007278178396427959143

theorem tailTrace_964025 : CollatzResearch.WordTrace tailWord_964025 prefixEnd_964025 440007278178396427959143 := by
  unfold tailWord_964025
  simp only [CollatzResearch.WordTrace]
  refine ⟨35160880332509542207261529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23440586888339694804841019 35160880332509542207261529)
  ·
    refine ⟨26370660249382156655446147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35160880332509542207261529 26370660249382156655446147)
    ·
      refine ⟨39555990374073234983169221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26370660249382156655446147 39555990374073234983169221)
      ·
        refine ⟨7416748195138731559344229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39555990374073234983169221 7416748195138731559344229)
        ·
          refine ⟨1390640286588512167377043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7416748195138731559344229 1390640286588512167377043)
          ·
            refine ⟨2085960429882768251065565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390640286588512167377043 2085960429882768251065565)
            ·
              refine ⟨782235161206038094149587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2085960429882768251065565 782235161206038094149587)
              ·
                refine ⟨1173352741809057141224381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782235161206038094149587 1173352741809057141224381)
                ·
                  refine ⟨440007278178396427959143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173352741809057141224381 440007278178396427959143)
                  ·
                    rfl

theorem cell20_964025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_964025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964025 prefixEnd_964025 := by exact prefixLift 964025
  have htrace : WordTrace (prefixWord ++ tailWord_964025) baseStart_964025 baseEnd_964025 := by
    simpa [prefixWord, tailWord_964025, baseEnd_964025] using wordTrace_append hprefix tailTrace_964025
  have hstable : (prefixWord ++ tailWord_964025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964025).length < 2 ^ (prefixWord ++ tailWord_964025).sum := by decide
  have hdescent : baseEnd_964025 < baseStart_964025 := by decide
  rcases family_descends (prefixWord ++ tailWord_964025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964067 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_964067 : Nat := 118140960795 + 964067 * 2 ^ 59
def prefixEnd_964067 : Nat := 4983230072969 + 3 ^ 40 * 964067 * 2
def baseEnd_964067 : Nat := 440026448122830948558971

theorem tailTrace_964067 : CollatzResearch.WordTrace tailWord_964067 prefixEnd_964067 440026448122830948558971 := by
  unfold tailWord_964067
  simp only [CollatzResearch.WordTrace]
  refine ⟨35162412198357383380290455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23441608132238255586860303 35162412198357383380290455)
  ·
    refine ⟨52743618297536075070435683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35162412198357383380290455 52743618297536075070435683)
    ·
      refine ⟨79115427446304112605653525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52743618297536075070435683 79115427446304112605653525)
      ·
        refine ⟨3708535661545505278390009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79115427446304112605653525 3708535661545505278390009)
        ·
          refine ⟨2781401746159128958792507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3708535661545505278390009 2781401746159128958792507)
          ·
            refine ⟨4172102619238693438188761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781401746159128958792507 4172102619238693438188761)
            ·
              refine ⟨3129076964429020078641571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172102619238693438188761 3129076964429020078641571)
              ·
                refine ⟨4693615446643530117962357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129076964429020078641571 4693615446643530117962357)
                ·
                  refine ⟨440026448122830948558971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4693615446643530117962357 440026448122830948558971)
                  ·
                    rfl

theorem cell20_964067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_964067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964067 prefixEnd_964067 := by exact prefixLift 964067
  have htrace : WordTrace (prefixWord ++ tailWord_964067) baseStart_964067 baseEnd_964067 := by
    simpa [prefixWord, tailWord_964067, baseEnd_964067] using wordTrace_append hprefix tailTrace_964067
  have hstable : (prefixWord ++ tailWord_964067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964067).length < 2 ^ (prefixWord ++ tailWord_964067).sum := by decide
  have hdescent : baseEnd_964067 < baseStart_964067 := by decide
  rcases family_descends (prefixWord ++ tailWord_964067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964077 : List Nat := [1, 5, 1, 3, 2, 1, 2, 5]
def baseStart_964077 : Nat := 118140960795 + 964077 * 2 ^ 59
def prefixEnd_964077 : Nat := 4983230072969 + 3 ^ 40 * 964077 * 2
def baseEnd_964077 : Nat := 146677004131771786075199

theorem tailTrace_964077 : CollatzResearch.WordTrace tailWord_964077 prefixEnd_964077 146677004131771786075199 := by
  unfold tailWord_964077
  simp only [CollatzResearch.WordTrace]
  refine ⟨35162776928321155088154485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23441851285547436725436323 35162776928321155088154485)
  ·
    refine ⟨3296510337030108289514483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35162776928321155088154485 3296510337030108289514483)
    ·
      refine ⟨4944765505545162434271725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3296510337030108289514483 4944765505545162434271725)
      ·
        refine ⟨1854287064579435912851897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4944765505545162434271725 1854287064579435912851897)
        ·
          refine ⟨1390715298434576934638923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1854287064579435912851897 1390715298434576934638923)
          ·
            refine ⟨2086072947651865401958385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390715298434576934638923 2086072947651865401958385)
            ·
              refine ⟨1564554710738899051468789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086072947651865401958385 1564554710738899051468789)
              ·
                refine ⟨146677004131771786075199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1564554710738899051468789 146677004131771786075199)
                ·
                  rfl

theorem cell20_964077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_964077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964077 prefixEnd_964077 := by exact prefixLift 964077
  have htrace : WordTrace (prefixWord ++ tailWord_964077) baseStart_964077 baseEnd_964077 := by
    simpa [prefixWord, tailWord_964077, baseEnd_964077] using wordTrace_append hprefix tailTrace_964077
  have hstable : (prefixWord ++ tailWord_964077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964077).length < 2 ^ (prefixWord ++ tailWord_964077).sum := by decide
  have hdescent : baseEnd_964077 < baseStart_964077 := by decide
  rcases family_descends (prefixWord ++ tailWord_964077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964081 : List Nat := [1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_964081 : Nat := 118140960795 + 964081 * 2 ^ 59
def prefixEnd_964081 : Nat := 4983230072969 + 3 ^ 40 * 964081 * 2
def baseEnd_964081 : Nat := 146677612701436374030749

theorem tailTrace_964081 : CollatzResearch.WordTrace tailWord_964081 prefixEnd_964081 146677612701436374030749 := by
  unfold tailWord_964081
  simp only [CollatzResearch.WordTrace]
  refine ⟨35162922820306663771300097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23441948546871109180866731 35162922820306663771300097)
  ·
    refine ⟨26372192115229997828475073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35162922820306663771300097 26372192115229997828475073)
    ·
      refine ⟨19779144086422498371356305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26372192115229997828475073 19779144086422498371356305)
      ·
        refine ⟨14834358064816873778517229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19779144086422498371356305 14834358064816873778517229)
        ·
          refine ⟨5562884274306327666943961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14834358064816873778517229 5562884274306327666943961)
          ·
            refine ⟨4172163205729745750207971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5562884274306327666943961 4172163205729745750207971)
            ·
              refine ⟨6258244808594618625311957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172163205729745750207971 6258244808594618625311957)
              ·
                refine ⟨146677612701436374030749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6258244808594618625311957 146677612701436374030749)
                ·
                  rfl

theorem cell20_964081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_964081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964081 prefixEnd_964081 := by exact prefixLift 964081
  have htrace : WordTrace (prefixWord ++ tailWord_964081) baseStart_964081 baseEnd_964081 := by
    simpa [prefixWord, tailWord_964081, baseEnd_964081] using wordTrace_append hprefix tailTrace_964081
  have hstable : (prefixWord ++ tailWord_964081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964081).length < 2 ^ (prefixWord ++ tailWord_964081).sum := by decide
  have hdescent : baseEnd_964081 < baseStart_964081 := by decide
  rcases family_descends (prefixWord ++ tailWord_964081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964171 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_964171 : Nat := 118140960795 + 964171 * 2 ^ 59
def prefixEnd_964171 : Nat := 4983230072969 + 3 ^ 40 * 964171 * 2
def baseEnd_964171 : Nat := 440073916556668809091879

theorem tailTrace_964171 : CollatzResearch.WordTrace tailWord_964171 prefixEnd_964171 440073916556668809091879 := by
  unfold tailWord_964171
  simp only [CollatzResearch.WordTrace]
  refine ⟨35166205389980609142076367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23444136926653739428050911 35166205389980609142076367)
  ·
    refine ⟨52749308084970913713114551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35166205389980609142076367 52749308084970913713114551)
    ·
      refine ⟨79123962127456370569671827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52749308084970913713114551 79123962127456370569671827)
      ·
        refine ⟨118685943191184555854507741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79123962127456370569671827 118685943191184555854507741)
        ·
          refine ⟨44507228696694208445440403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118685943191184555854507741 44507228696694208445440403)
          ·
            refine ⟨66760843045041312668160605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44507228696694208445440403 66760843045041312668160605)
            ·
              refine ⟨25035316141890492250560227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66760843045041312668160605 25035316141890492250560227)
              ·
                refine ⟨37552974212835738375840341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25035316141890492250560227 37552974212835738375840341)
                ·
                  refine ⟨440073916556668809091879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37552974212835738375840341 440073916556668809091879)
                  ·
                    rfl

theorem cell20_964171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_964171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964171 prefixEnd_964171 := by exact prefixLift 964171
  have htrace : WordTrace (prefixWord ++ tailWord_964171) baseStart_964171 baseEnd_964171 := by
    simpa [prefixWord, tailWord_964171, baseEnd_964171] using wordTrace_append hprefix tailTrace_964171
  have hstable : (prefixWord ++ tailWord_964171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964171).length < 2 ^ (prefixWord ++ tailWord_964171).sum := by decide
  have hdescent : baseEnd_964171 < baseStart_964171 := by decide
  rcases family_descends (prefixWord ++ tailWord_964171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964290 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_964290 : Nat := 118140960795 + 964290 * 2 ^ 59
def prefixEnd_964290 : Nat := 4983230072969 + 3 ^ 40 * 964290 * 2
def baseEnd_964290 : Nat := 440128231399233284124727

theorem tailTrace_964290 : CollatzResearch.WordTrace tailWord_964290 prefixEnd_964290 440128231399233284124727 := by
  unfold tailWord_964290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792636419137373116414581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23447030451032994977105549 8792636419137373116414581)
  ·
    refine ⟨824309664294128729663867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8792636419137373116414581 824309664294128729663867)
    ·
      refine ⟨1236464496441193094495801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824309664294128729663867 1236464496441193094495801)
      ·
        refine ⟨927348372330894820871851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1236464496441193094495801 927348372330894820871851)
        ·
          refine ⟨1391022558496342231307777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927348372330894820871851 1391022558496342231307777)
          ·
            refine ⟨1043266918872256673480833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391022558496342231307777 1043266918872256673480833)
            ·
              refine ⟨782450189154192505110625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043266918872256673480833 782450189154192505110625)
              ·
                refine ⟨586837641865644378832969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782450189154192505110625 586837641865644378832969)
                ·
                  refine ⟨440128231399233284124727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586837641865644378832969 440128231399233284124727)
                  ·
                    rfl

theorem cell20_964290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_964290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964290 prefixEnd_964290 := by exact prefixLift 964290
  have htrace : WordTrace (prefixWord ++ tailWord_964290) baseStart_964290 baseEnd_964290 := by
    simpa [prefixWord, tailWord_964290, baseEnd_964290] using wordTrace_append hprefix tailTrace_964290
  have hstable : (prefixWord ++ tailWord_964290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964290).length < 2 ^ (prefixWord ++ tailWord_964290).sum := by decide
  have hdescent : baseEnd_964290 < baseStart_964290 := by decide
  rcases family_descends (prefixWord ++ tailWord_964290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964294 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_964294 : Nat := 118140960795 + 964294 * 2 ^ 59
def prefixEnd_964294 : Nat := 4983230072969 + 3 ^ 40 * 964294 * 2
def baseEnd_964294 : Nat := 440130057108227047991377

theorem tailTrace_964294 : CollatzResearch.WordTrace tailWord_964294 prefixEnd_964294 440130057108227047991377 := by
  unfold tailWord_964294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099084111516718785900123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23447127712356667432535957 1099084111516718785900123)
  ·
    refine ⟨1648626167275078178850185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099084111516718785900123 1648626167275078178850185)
    ·
      refine ⟨1236469625456308634137639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1648626167275078178850185 1236469625456308634137639)
      ·
        refine ⟨1854704438184462951206459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236469625456308634137639 1854704438184462951206459)
        ·
          refine ⟨2782056657276694426809689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854704438184462951206459 2782056657276694426809689)
          ·
            refine ⟨2086542492957520820107267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2782056657276694426809689 2086542492957520820107267)
            ·
              refine ⟨3129813739436281230160901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086542492957520820107267 3129813739436281230160901)
              ·
                refine ⟨586840076144302730655169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3129813739436281230160901 586840076144302730655169)
                ·
                  refine ⟨440130057108227047991377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586840076144302730655169 440130057108227047991377)
                  ·
                    rfl

theorem cell20_964294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_964294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964294 prefixEnd_964294 := by exact prefixLift 964294
  have htrace : WordTrace (prefixWord ++ tailWord_964294) baseStart_964294 baseEnd_964294 := by
    simpa [prefixWord, tailWord_964294, baseEnd_964294] using wordTrace_append hprefix tailTrace_964294
  have hstable : (prefixWord ++ tailWord_964294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964294).length < 2 ^ (prefixWord ++ tailWord_964294).sum := by decide
  have hdescent : baseEnd_964294 < baseStart_964294 := by decide
  rcases family_descends (prefixWord ++ tailWord_964294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964295 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_964295 : Nat := 118140960795 + 964295 * 2 ^ 59
def prefixEnd_964295 : Nat := 4983230072969 + 3 ^ 40 * 964295 * 2
def baseEnd_964295 : Nat := 440130513535475488958039

theorem tailTrace_964295 : CollatzResearch.WordTrace tailWord_964295 prefixEnd_964295 440130513535475488958039 := by
  unfold tailWord_964295
  simp only [CollatzResearch.WordTrace]
  refine ⟨35170728041531378319590339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23447152027687585546393559 35170728041531378319590339)
  ·
    refine ⟨52756092062297067479385509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35170728041531378319590339 52756092062297067479385509)
    ·
      refine ⟨9891767261680700152384783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52756092062297067479385509 9891767261680700152384783)
      ·
        refine ⟨14837650892521050228577175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891767261680700152384783 14837650892521050228577175)
        ·
          refine ⟨22256476338781575342865763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14837650892521050228577175 22256476338781575342865763)
          ·
            refine ⟨33384714508172363014298645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22256476338781575342865763 33384714508172363014298645)
            ·
              refine ⟨1564908492570579516295249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33384714508172363014298645 1564908492570579516295249)
              ·
                refine ⟨1173681369427934637221437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564908492570579516295249 1173681369427934637221437)
                ·
                  refine ⟨440130513535475488958039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173681369427934637221437 440130513535475488958039)
                  ·
                    rfl

theorem cell20_964295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_964295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964295 prefixEnd_964295 := by exact prefixLift 964295
  have htrace : WordTrace (prefixWord ++ tailWord_964295) baseStart_964295 baseEnd_964295 := by
    simpa [prefixWord, tailWord_964295, baseEnd_964295] using wordTrace_append hprefix tailTrace_964295
  have hstable : (prefixWord ++ tailWord_964295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964295).length < 2 ^ (prefixWord ++ tailWord_964295).sum := by decide
  have hdescent : baseEnd_964295 < baseStart_964295 := by decide
  rcases family_descends (prefixWord ++ tailWord_964295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964298 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_964298 : Nat := 118140960795 + 964298 * 2 ^ 59
def prefixEnd_964298 : Nat := 4983230072969 + 3 ^ 40 * 964298 * 2
def baseEnd_964298 : Nat := 440131882817220811858027

theorem tailTrace_964298 : CollatzResearch.WordTrace tailWord_964298 prefixEnd_964298 440131882817220811858027 := by
  unfold tailWord_964298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792709365130127457987387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23447224973680339887966365 8792709365130127457987387)
  ·
    refine ⟨13189064047695191186981081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8792709365130127457987387 13189064047695191186981081)
    ·
      refine ⟨9891798035771393390235811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13189064047695191186981081 9891798035771393390235811)
      ·
        refine ⟨14837697053657090085353717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891798035771393390235811 14837697053657090085353717)
        ·
          refine ⟨1391034098780352195501911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14837697053657090085353717 1391034098780352195501911)
          ·
            refine ⟨2086551148170528293252867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391034098780352195501911 2086551148170528293252867)
            ·
              refine ⟨3129826722255792439879301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086551148170528293252867 3129826722255792439879301)
              ·
                refine ⟨586842510422961082477369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3129826722255792439879301 586842510422961082477369)
                ·
                  refine ⟨440131882817220811858027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586842510422961082477369 440131882817220811858027)
                  ·
                    rfl

theorem cell20_964298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_964298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964298 prefixEnd_964298 := by exact prefixLift 964298
  have htrace : WordTrace (prefixWord ++ tailWord_964298) baseStart_964298 baseEnd_964298 := by
    simpa [prefixWord, tailWord_964298, baseEnd_964298] using wordTrace_append hprefix tailTrace_964298
  have hstable : (prefixWord ++ tailWord_964298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964298).length < 2 ^ (prefixWord ++ tailWord_964298).sum := by decide
  have hdescent : baseEnd_964298 < baseStart_964298 := by decide
  rcases family_descends (prefixWord ++ tailWord_964298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964302 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_964302 : Nat := 118140960795 + 964302 * 2 ^ 59
def prefixEnd_964302 : Nat := 4983230072969 + 3 ^ 40 * 964302 * 2
def baseEnd_964302 : Nat := 440133708526214575724677

theorem tailTrace_964302 : CollatzResearch.WordTrace tailWord_964302 prefixEnd_964302 440133708526214575724677 := by
  unfold tailWord_964302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396372919063252314386895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23447322235004012343396773 4396372919063252314386895)
  ·
    refine ⟨6594559378594878471580343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4396372919063252314386895 6594559378594878471580343)
    ·
      refine ⟨9891839067892317707370515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6594559378594878471580343 9891839067892317707370515)
      ·
        refine ⟨14837758601838476561055773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891839067892317707370515 14837758601838476561055773)
        ·
          refine ⟨5564159475689428710395915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14837758601838476561055773 5564159475689428710395915)
          ·
            refine ⟨8346239213534143065593873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564159475689428710395915 8346239213534143065593873)
            ·
              refine ⟨6259679410150607299195405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346239213534143065593873 6259679410150607299195405)
              ·
                refine ⟨2347379778806477737198277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6259679410150607299195405 2347379778806477737198277)
                ·
                  refine ⟨440133708526214575724677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347379778806477737198277 440133708526214575724677)
                  ·
                    rfl

theorem cell20_964302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_964302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964302 prefixEnd_964302 := by exact prefixLift 964302
  have htrace : WordTrace (prefixWord ++ tailWord_964302) baseStart_964302 baseEnd_964302 := by
    simpa [prefixWord, tailWord_964302, baseEnd_964302] using wordTrace_append hprefix tailTrace_964302
  have hstable : (prefixWord ++ tailWord_964302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964302).length < 2 ^ (prefixWord ++ tailWord_964302).sum := by decide
  have hdescent : baseEnd_964302 < baseStart_964302 := by decide
  rcases family_descends (prefixWord ++ tailWord_964302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964350 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_964350 : Nat := 118140960795 + 964350 * 2 ^ 59
def prefixEnd_964350 : Nat := 4983230072969 + 3 ^ 40 * 964350 * 2
def baseEnd_964350 : Nat := 440155617034139742124481

theorem tailTrace_964350 : CollatzResearch.WordTrace tailWord_964350 prefixEnd_964350 440155617034139742124481 := by
  unfold tailWord_964350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396591757041515339105313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23448489370888081808561669 4396591757041515339105313)
  ·
    refine ⟨3297443817781136504328985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4396591757041515339105313 3297443817781136504328985)
    ·
      refine ⟨2473082863335852378246739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3297443817781136504328985 2473082863335852378246739)
      ·
        refine ⟨3709624295003778567370109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473082863335852378246739 3709624295003778567370109)
        ·
          refine ⟨1391109110626416962763791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3709624295003778567370109 1391109110626416962763791)
          ·
            refine ⟨2086663665939625444145687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391109110626416962763791 2086663665939625444145687)
            ·
              refine ⟨3129995498909438166218531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086663665939625444145687 3129995498909438166218531)
              ·
                refine ⟨4694993248364157249327797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129995498909438166218531 4694993248364157249327797)
                ·
                  refine ⟨440155617034139742124481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4694993248364157249327797 440155617034139742124481)
                  ·
                    rfl

theorem cell20_964350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_964350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964350 prefixEnd_964350 := by exact prefixLift 964350
  have htrace : WordTrace (prefixWord ++ tailWord_964350) baseStart_964350 baseEnd_964350 := by
    simpa [prefixWord, tailWord_964350, baseEnd_964350] using wordTrace_append hprefix tailTrace_964350
  have hstable : (prefixWord ++ tailWord_964350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964350).length < 2 ^ (prefixWord ++ tailWord_964350).sum := by decide
  have hdescent : baseEnd_964350 < baseStart_964350 := by decide
  rcases family_descends (prefixWord ++ tailWord_964350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964378 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_964378 : Nat := 118140960795 + 964378 * 2 ^ 59
def prefixEnd_964378 : Nat := 4983230072969 + 3 ^ 40 * 964378 * 2
def baseEnd_964378 : Nat := 440168396997096089191033

theorem tailTrace_964378 : CollatzResearch.WordTrace tailWord_964378 prefixEnd_964378 440168396997096089191033 := by
  unfold tailWord_964378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8793438825057670873715447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23449170200153788996574525 8793438825057670873715447)
  ·
    refine ⟨13190158237586506310573171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8793438825057670873715447 13190158237586506310573171)
    ·
      refine ⟨19785237356379759465859757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13190158237586506310573171 19785237356379759465859757)
      ·
        refine ⟨7419464008642409799697409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19785237356379759465859757 7419464008642409799697409)
        ·
          refine ⟨5564598006481807349773057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7419464008642409799697409 5564598006481807349773057)
          ·
            refine ⟨4173448504861355512329793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5564598006481807349773057 4173448504861355512329793)
            ·
              refine ⟨3130086378646016634247345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173448504861355512329793 3130086378646016634247345)
              ·
                refine ⟨2347564783984512475685509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130086378646016634247345 2347564783984512475685509)
                ·
                  refine ⟨440168396997096089191033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347564783984512475685509 440168396997096089191033)
                  ·
                    rfl

theorem cell20_964378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_964378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964378 prefixEnd_964378 := by exact prefixLift 964378
  have htrace : WordTrace (prefixWord ++ tailWord_964378) baseStart_964378 baseEnd_964378 := by
    simpa [prefixWord, tailWord_964378, baseEnd_964378] using wordTrace_append hprefix tailTrace_964378
  have hstable : (prefixWord ++ tailWord_964378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964378).length < 2 ^ (prefixWord ++ tailWord_964378).sum := by decide
  have hdescent : baseEnd_964378 < baseStart_964378 := by decide
  rcases family_descends (prefixWord ++ tailWord_964378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964385 : List Nat := [1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_964385 : Nat := 118140960795 + 964385 * 2 ^ 59
def prefixEnd_964385 : Nat := 4983230072969 + 3 ^ 40 * 964385 * 2
def baseEnd_964385 : Nat := 146723863995945058652557

theorem tailTrace_964385 : CollatzResearch.WordTrace tailWord_964385 prefixEnd_964385 146723863995945058652557 := by
  unfold tailWord_964385
  simp only [CollatzResearch.WordTrace]
  refine ⟨35174010611205323690366609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23449340407470215793577739 35174010611205323690366609)
  ·
    refine ⟨26380507958403992767774957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35174010611205323690366609 26380507958403992767774957)
    ·
      refine ⟨9892690484401497287915609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26380507958403992767774957 9892690484401497287915609)
      ·
        refine ⟨7419517863301122965936707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9892690484401497287915609 7419517863301122965936707)
        ·
          refine ⟨11129276794951684448905061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419517863301122965936707 11129276794951684448905061)
          ·
            refine ⟨2086739399053440834169699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11129276794951684448905061 2086739399053440834169699)
            ·
              refine ⟨3130109098580161251254549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086739399053440834169699 3130109098580161251254549)
              ·
                refine ⟨146723863995945058652557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3130109098580161251254549 146723863995945058652557)
                ·
                  rfl

theorem cell20_964385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_964385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964385 prefixEnd_964385 := by exact prefixLift 964385
  have htrace : WordTrace (prefixWord ++ tailWord_964385) baseStart_964385 baseEnd_964385 := by
    simpa [prefixWord, tailWord_964385, baseEnd_964385] using wordTrace_append hprefix tailTrace_964385
  have hstable : (prefixWord ++ tailWord_964385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964385).length < 2 ^ (prefixWord ++ tailWord_964385).sum := by decide
  have hdescent : baseEnd_964385 < baseStart_964385 := by decide
  rcases family_descends (prefixWord ++ tailWord_964385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964422 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_964422 : Nat := 118140960795 + 964422 * 2 ^ 59
def prefixEnd_964422 : Nat := 4983230072969 + 3 ^ 40 * 964422 * 2
def baseEnd_964422 : Nat := 440188479796027491724187

theorem tailTrace_964422 : CollatzResearch.WordTrace tailWord_964422 prefixEnd_964422 440188479796027491724187 := by
  unfold tailWord_964422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099230003502227469045735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23450240074714186006309013 1099230003502227469045735)
  ·
    refine ⟨1648845005253341203568603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099230003502227469045735 1648845005253341203568603)
    ·
      refine ⟨2473267507880011805352905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648845005253341203568603 2473267507880011805352905)
      ·
        refine ⟨1854950630910008854014679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2473267507880011805352905 1854950630910008854014679)
        ·
          refine ⟨2782425946365013281022019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854950630910008854014679 2782425946365013281022019)
          ·
            refine ⟨4173638919547519921533029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782425946365013281022019 4173638919547519921533029)
            ·
              refine ⟨782557297415159985287443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4173638919547519921533029 782557297415159985287443)
              ·
                refine ⟨1173835946122739977931165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782557297415159985287443 1173835946122739977931165)
                ·
                  refine ⟨440188479796027491724187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173835946122739977931165 440188479796027491724187)
                  ·
                    rfl

theorem cell20_964422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_964422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964422 prefixEnd_964422 := by exact prefixLift 964422
  have htrace : WordTrace (prefixWord ++ tailWord_964422) baseStart_964422 baseEnd_964422 := by
    simpa [prefixWord, tailWord_964422, baseEnd_964422] using wordTrace_append hprefix tailTrace_964422
  have hstable : (prefixWord ++ tailWord_964422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964422).length < 2 ^ (prefixWord ++ tailWord_964422).sum := by decide
  have hdescent : baseEnd_964422 < baseStart_964422 := by decide
  rcases family_descends (prefixWord ++ tailWord_964422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964475 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_964475 : Nat := 118140960795 + 964475 * 2 ^ 59
def prefixEnd_964475 : Nat := 4983230072969 + 3 ^ 40 * 964475 * 2
def baseEnd_964475 : Nat := 440212670440194862957303

theorem tailTrace_964475 : CollatzResearch.WordTrace tailWord_964475 prefixEnd_964475 440212670440194862957303 := by
  unfold tailWord_964475
  simp only [CollatzResearch.WordTrace]
  refine ⟨35177293180879269061142879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23451528787252846040761919 35177293180879269061142879)
  ·
    refine ⟨52765939771318903591714319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35177293180879269061142879 52765939771318903591714319)
    ·
      refine ⟨79148909656978355387571479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52765939771318903591714319 79148909656978355387571479)
      ·
        refine ⟨118723364485467533081357219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79148909656978355387571479 118723364485467533081357219)
        ·
          refine ⟨178085046728201299622035829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118723364485467533081357219 178085046728201299622035829)
          ·
            refine ⟨16695473130768871839565859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178085046728201299622035829 16695473130768871839565859)
            ·
              refine ⟨25043209696153307759348789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695473130768871839565859 25043209696153307759348789)
              ·
                refine ⟨2347800909014372602438949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25043209696153307759348789 2347800909014372602438949)
                ·
                  refine ⟨440212670440194862957303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347800909014372602438949 440212670440194862957303)
                  ·
                    rfl

theorem cell20_964475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_964475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964475 prefixEnd_964475 := by exact prefixLift 964475
  have htrace : WordTrace (prefixWord ++ tailWord_964475) baseStart_964475 baseEnd_964475 := by
    simpa [prefixWord, tailWord_964475, baseEnd_964475] using wordTrace_append hprefix tailTrace_964475
  have hstable : (prefixWord ++ tailWord_964475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964475).length < 2 ^ (prefixWord ++ tailWord_964475).sum := by decide
  have hdescent : baseEnd_964475 < baseStart_964475 := by decide
  rcases family_descends (prefixWord ++ tailWord_964475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964509 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 2]
def baseStart_964509 : Nat := 118140960795 + 964509 * 2 ^ 59
def prefixEnd_964509 : Nat := 4983230072969 + 3 ^ 40 * 964509 * 2
def baseEnd_964509 : Nat := 440228188966641855823831

theorem tailTrace_964509 : CollatzResearch.WordTrace tailWord_964509 prefixEnd_964509 440228188966641855823831 := by
  unfold tailWord_964509
  simp only [CollatzResearch.WordTrace]
  refine ⟨35178533262756092867880581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23452355508504061911920387 35178533262756092867880581)
  ·
    refine ⟨6595974986766767412727609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35178533262756092867880581 6595974986766767412727609)
    ·
      refine ⟨4946981240075075559545707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6595974986766767412727609 4946981240075075559545707)
      ·
        refine ⟨7420471860112613339318561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946981240075075559545707 7420471860112613339318561)
        ·
          refine ⟨5565353895084460004488921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7420471860112613339318561 5565353895084460004488921)
          ·
            refine ⟨4174015421313345003366691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5565353895084460004488921 4174015421313345003366691)
            ·
              refine ⟨6261023131970017505050037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174015421313345003366691 6261023131970017505050037)
              ·
                refine ⟨586970918622189141098441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6261023131970017505050037 586970918622189141098441)
                ·
                  refine ⟨440228188966641855823831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586970918622189141098441 440228188966641855823831)
                  ·
                    rfl

theorem cell20_964509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_964509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964509 prefixEnd_964509 := by exact prefixLift 964509
  have htrace : WordTrace (prefixWord ++ tailWord_964509) baseStart_964509 baseEnd_964509 := by
    simpa [prefixWord, tailWord_964509, baseEnd_964509] using wordTrace_append hprefix tailTrace_964509
  have hstable : (prefixWord ++ tailWord_964509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964509).length < 2 ^ (prefixWord ++ tailWord_964509).sum := by decide
  have hdescent : baseEnd_964509 < baseStart_964509 := by decide
  rcases family_descends (prefixWord ++ tailWord_964509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964575 : List Nat := [1, 1, 2, 3, 4, 3, 6]
def baseStart_964575 : Nat := 118140960795 + 964575 * 2 ^ 59
def prefixEnd_964575 : Nat := 4983230072969 + 3 ^ 40 * 964575 * 2
def baseEnd_964575 : Nat := 48917590351670995513729

theorem tailTrace_964575 : CollatzResearch.WordTrace tailWord_964575 prefixEnd_964575 48917590351670995513729 := by
  unfold tailWord_964575
  simp only [CollatzResearch.WordTrace]
  refine ⟨35180940480516986139783179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23453960320344657426522119 35180940480516986139783179)
  ·
    refine ⟨52771410720775479209674769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35180940480516986139783179 52771410720775479209674769)
    ·
      refine ⟨39578558040581609407256077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52771410720775479209674769 39578558040581609407256077)
      ·
        refine ⟨14841959265218103527721029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39578558040581609407256077 14841959265218103527721029)
        ·
          refine ⟨2782867362228394411447693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14841959265218103527721029 2782867362228394411447693)
          ·
            refine ⟨1043575260835647904292885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2782867362228394411447693 1043575260835647904292885)
            ·
              refine ⟨48917590351670995513729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1043575260835647904292885 48917590351670995513729)
              ·
                rfl

theorem cell20_964575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_964575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964575 prefixEnd_964575 := by exact prefixLift 964575
  have htrace : WordTrace (prefixWord ++ tailWord_964575) baseStart_964575 baseEnd_964575 := by
    simpa [prefixWord, tailWord_964575, baseEnd_964575] using wordTrace_append hprefix tailTrace_964575
  have hstable : (prefixWord ++ tailWord_964575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964575).length < 2 ^ (prefixWord ++ tailWord_964575).sum := by decide
  have hdescent : baseEnd_964575 < baseStart_964575 := by decide
  rcases family_descends (prefixWord ++ tailWord_964575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964634 : List Nat := [3, 1, 1, 3, 1, 11]
def baseStart_964634 : Nat := 118140960795 + 964634 * 2 ^ 59
def prefixEnd_964634 : Nat := 4983230072969 + 3 ^ 40 * 964634 * 2
def baseEnd_964634 : Nat := 16306860828618406542839

theorem tailTrace_964634 : CollatzResearch.WordTrace tailWord_964634 prefixEnd_964634 16306860828618406542839 := by
  unfold tailWord_964634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795773096825809804045239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23455394924868826144120637 8795773096825809804045239)
  ·
    refine ⟨13193659645238714706067859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8795773096825809804045239 13193659645238714706067859)
    ·
      refine ⟨19790489467858072059101789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13193659645238714706067859 19790489467858072059101789)
      ·
        refine ⟨7421433550446777022163171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19790489467858072059101789 7421433550446777022163171)
        ·
          refine ⟨11132150325670165533244757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421433550446777022163171 11132150325670165533244757)
          ·
            refine ⟨16306860828618406542839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11132150325670165533244757 16306860828618406542839)
            ·
              rfl

theorem cell20_964634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 11].length) (baseStart_964634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964634 prefixEnd_964634 := by exact prefixLift 964634
  have htrace : WordTrace (prefixWord ++ tailWord_964634) baseStart_964634 baseEnd_964634 := by
    simpa [prefixWord, tailWord_964634, baseEnd_964634] using wordTrace_append hprefix tailTrace_964634
  have hstable : (prefixWord ++ tailWord_964634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964634).length < 2 ^ (prefixWord ++ tailWord_964634).sum := by decide
  have hdescent : baseEnd_964634 < baseStart_964634 := by decide
  rcases family_descends (prefixWord ++ tailWord_964634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964637 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_964637 : Nat := 118140960795 + 964637 * 2 ^ 59
def prefixEnd_964637 : Nat := 4983230072969 + 3 ^ 40 * 964637 * 2
def baseEnd_964637 : Nat := 440286611654442299556641

theorem tailTrace_964637 : CollatzResearch.WordTrace tailWord_964637 prefixEnd_964637 440286611654442299556641 := by
  unfold tailWord_964637
  simp only [CollatzResearch.WordTrace]
  refine ⟨35183201806292370728540165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23455467870861580485693443 35183201806292370728540165)
  ·
    refine ⟨6596850338679819511601281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35183201806292370728540165 6596850338679819511601281)
    ·
      refine ⟨4947637754009864633700961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6596850338679819511601281 4947637754009864633700961)
      ·
        refine ⟨3710728315507398475275721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4947637754009864633700961 3710728315507398475275721)
        ·
          refine ⟨2783046236630548856456791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3710728315507398475275721 2783046236630548856456791)
          ·
            refine ⟨4174569354945823284685187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783046236630548856456791 4174569354945823284685187)
            ·
              refine ⟨6261854032418734927027781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174569354945823284685187 6261854032418734927027781)
              ·
                refine ⟨1174097631078512798817709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6261854032418734927027781 1174097631078512798817709)
                ·
                  refine ⟨440286611654442299556641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174097631078512798817709 440286611654442299556641)
                  ·
                    rfl

theorem cell20_964637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_964637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964637 prefixEnd_964637 := by exact prefixLift 964637
  have htrace : WordTrace (prefixWord ++ tailWord_964637) baseStart_964637 baseEnd_964637 := by
    simpa [prefixWord, tailWord_964637, baseEnd_964637] using wordTrace_append hprefix tailTrace_964637
  have hstable : (prefixWord ++ tailWord_964637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964637).length < 2 ^ (prefixWord ++ tailWord_964637).sum := by decide
  have hdescent : baseEnd_964637 < baseStart_964637 := by decide
  rcases family_descends (prefixWord ++ tailWord_964637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964647 : List Nat := [1, 1, 7, 1, 2, 2, 1, 5]
def baseStart_964647 : Nat := 118140960795 + 964647 * 2 ^ 59
def prefixEnd_964647 : Nat := 4983230072969 + 3 ^ 40 * 964647 * 2
def baseEnd_964647 : Nat := 146763725308975569741089

theorem tailTrace_964647 : CollatzResearch.WordTrace tailWord_964647 prefixEnd_964647 146763725308975569741089 := by
  unfold tailWord_964647
  simp only [CollatzResearch.WordTrace]
  refine ⟨35183566536256142436404195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23455711024170761624269463 35183566536256142436404195)
  ·
    refine ⟨52775349804384213654606293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35183566536256142436404195 52775349804384213654606293)
    ·
      refine ⟨1236922261040255007529835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 52775349804384213654606293 1236922261040255007529835)
      ·
        refine ⟨1855383391560382511294753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236922261040255007529835 1855383391560382511294753)
        ·
          refine ⟨1391537543670286883471065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855383391560382511294753 1391537543670286883471065)
          ·
            refine ⟨1043653157752715162603299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391537543670286883471065 1043653157752715162603299)
            ·
              refine ⟨1565479736629072743904949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043653157752715162603299 1565479736629072743904949)
              ·
                refine ⟨146763725308975569741089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1565479736629072743904949 146763725308975569741089)
                ·
                  rfl

theorem cell20_964647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_964647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964647 prefixEnd_964647 := by exact prefixLift 964647
  have htrace : WordTrace (prefixWord ++ tailWord_964647) baseStart_964647 baseEnd_964647 := by
    simpa [prefixWord, tailWord_964647, baseEnd_964647] using wordTrace_append hprefix tailTrace_964647
  have hstable : (prefixWord ++ tailWord_964647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964647).length < 2 ^ (prefixWord ++ tailWord_964647).sum := by decide
  have hdescent : baseEnd_964647 < baseStart_964647 := by decide
  rcases family_descends (prefixWord ++ tailWord_964647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964696 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_964696 : Nat := 118140960795 + 964696 * 2 ^ 59
def prefixEnd_964696 : Nat := 4983230072969 + 3 ^ 40 * 964696 * 2
def baseEnd_964696 : Nat := 440313540862100316589733

theorem tailTrace_964696 : CollatzResearch.WordTrace tailWord_964696 prefixEnd_964696 440313540862100316589733 := by
  unfold tailWord_964696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17592676856539311902468971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23456902475385749203291961 17592676856539311902468971)
  ·
    refine ⟨26389015284808967853703457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17592676856539311902468971 26389015284808967853703457)
    ·
      refine ⟨19791761463606725890277593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26389015284808967853703457 19791761463606725890277593)
      ·
        refine ⟨14843821097705044417708195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19791761463606725890277593 14843821097705044417708195)
        ·
          refine ⟨22265731646557566626562293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14843821097705044417708195 22265731646557566626562293)
          ·
            refine ⟨2087412341864771871240215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22265731646557566626562293 2087412341864771871240215)
            ·
              refine ⟨3131118512797157806860323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087412341864771871240215 3131118512797157806860323)
              ·
                refine ⟨4696677769195736710290485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131118512797157806860323 4696677769195736710290485)
                ·
                  refine ⟨440313540862100316589733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696677769195736710290485 440313540862100316589733)
                  ·
                    rfl

theorem cell20_964696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_964696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964696 prefixEnd_964696 := by exact prefixLift 964696
  have htrace : WordTrace (prefixWord ++ tailWord_964696) baseStart_964696 baseEnd_964696 := by
    simpa [prefixWord, tailWord_964696, baseEnd_964696] using wordTrace_append hprefix tailTrace_964696
  have hstable : (prefixWord ++ tailWord_964696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964696).length < 2 ^ (prefixWord ++ tailWord_964696).sum := by decide
  have hdescent : baseEnd_964696 < baseStart_964696 := by decide
  rcases family_descends (prefixWord ++ tailWord_964696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964713 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 3]
def baseStart_964713 : Nat := 118140960795 + 964713 * 2 ^ 59
def prefixEnd_964713 : Nat := 4983230072969 + 3 ^ 40 * 964713 * 2
def baseEnd_964713 : Nat := 440321300125323813022997

theorem tailTrace_964713 : CollatzResearch.WordTrace tailWord_964713 prefixEnd_964713 440321300125323813022997 := by
  unfold tailWord_964713
  simp only [CollatzResearch.WordTrace]
  refine ⟨35185973754017035708306793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23457315836011357138871195 35185973754017035708306793)
  ·
    refine ⟨26389480315512776781230095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35185973754017035708306793 26389480315512776781230095)
    ·
      refine ⟨39584220473269165171845143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26389480315512776781230095 39584220473269165171845143)
      ·
        refine ⟨59376330709903747757767715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39584220473269165171845143 59376330709903747757767715)
        ·
          refine ⟨89064496064855621636651573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59376330709903747757767715 89064496064855621636651573)
          ·
            refine ⟨8349796506080214528436085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89064496064855621636651573 8349796506080214528436085)
            ·
              refine ⟨782793422445020112040883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8349796506080214528436085 782793422445020112040883)
              ·
                refine ⟨1174190133667530168061325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782793422445020112040883 1174190133667530168061325)
                ·
                  refine ⟨440321300125323813022997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174190133667530168061325 440321300125323813022997)
                  ·
                    rfl

theorem cell20_964713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_964713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964713 prefixEnd_964713 := by exact prefixLift 964713
  have htrace : WordTrace (prefixWord ++ tailWord_964713) baseStart_964713 baseEnd_964713 := by
    simpa [prefixWord, tailWord_964713, baseEnd_964713] using wordTrace_append hprefix tailTrace_964713
  have hstable : (prefixWord ++ tailWord_964713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964713).length < 2 ^ (prefixWord ++ tailWord_964713).sum := by decide
  have hdescent : baseEnd_964713 < baseStart_964713 := by decide
  rcases family_descends (prefixWord ++ tailWord_964713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964727 : List Nat := [1, 1, 3, 1, 1, 5, 4, 4]
def baseStart_964727 : Nat := 118140960795 + 964727 * 2 ^ 59
def prefixEnd_964727 : Nat := 4983230072969 + 3 ^ 40 * 964727 * 2
def baseEnd_964727 : Nat := 146775896702267328852091

theorem tailTrace_964727 : CollatzResearch.WordTrace tailWord_964727 prefixEnd_964727 146775896702267328852091 := by
  unfold tailWord_964727
  simp only [CollatzResearch.WordTrace]
  refine ⟨35186484375966316099316435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23457656250644210732877623 35186484375966316099316435)
  ·
    refine ⟨52779726563949474148974653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35186484375966316099316435 52779726563949474148974653)
    ·
      refine ⟨19792397461481052805865495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52779726563949474148974653 19792397461481052805865495)
      ·
        refine ⟨29688596192221579208798243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19792397461481052805865495 29688596192221579208798243)
        ·
          refine ⟨44532894288332368813197365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29688596192221579208798243 44532894288332368813197365)
          ·
            refine ⟨4174958839531159576237253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44532894288332368813197365 4174958839531159576237253)
            ·
              refine ⟨782804782412092420544485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4174958839531159576237253 782804782412092420544485)
              ·
                refine ⟨146775896702267328852091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782804782412092420544485 146775896702267328852091)
                ·
                  rfl

theorem cell20_964727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_964727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964727 prefixEnd_964727 := by exact prefixLift 964727
  have htrace : WordTrace (prefixWord ++ tailWord_964727) baseStart_964727 baseEnd_964727 := by
    simpa [prefixWord, tailWord_964727, baseEnd_964727] using wordTrace_append hprefix tailTrace_964727
  have hstable : (prefixWord ++ tailWord_964727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964727).length < 2 ^ (prefixWord ++ tailWord_964727).sum := by decide
  have hdescent : baseEnd_964727 < baseStart_964727 := by decide
  rcases family_descends (prefixWord ++ tailWord_964727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964754 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_964754 : Nat := 118140960795 + 964754 * 2 ^ 59
def prefixEnd_964754 : Nat := 4983230072969 + 3 ^ 40 * 964754 * 2
def baseEnd_964754 : Nat := 440340013642509892656163

theorem tailTrace_964754 : CollatzResearch.WordTrace tailWord_964754 prefixEnd_964754 440340013642509892656163 := by
  unfold tailWord_964754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796867286717124927637329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23458312764578999807032877 8796867286717124927637329)
  ·
    refine ⟨6597650465037843695727997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8796867286717124927637329 6597650465037843695727997)
    ·
      refine ⟨2474118924389191385897999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6597650465037843695727997 2474118924389191385897999)
      ·
        refine ⟨3711178386583787078846999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474118924389191385897999 3711178386583787078846999)
        ·
          refine ⟨5566767579875680618270499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711178386583787078846999 5566767579875680618270499)
          ·
            refine ⟨8350151369813520927405749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566767579875680618270499 8350151369813520927405749)
            ·
              refine ⟨782826690920017586944289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8350151369813520927405749 782826690920017586944289)
              ·
                refine ⟨587120018190013190208217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782826690920017586944289 587120018190013190208217)
                ·
                  refine ⟨440340013642509892656163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587120018190013190208217 440340013642509892656163)
                  ·
                    rfl

theorem cell20_964754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_964754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964754 prefixEnd_964754 := by exact prefixLift 964754
  have htrace : WordTrace (prefixWord ++ tailWord_964754) baseStart_964754 baseEnd_964754 := by
    simpa [prefixWord, tailWord_964754, baseEnd_964754] using wordTrace_append hprefix tailTrace_964754
  have hstable : (prefixWord ++ tailWord_964754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964754).length < 2 ^ (prefixWord ++ tailWord_964754).sum := by decide
  have hdescent : baseEnd_964754 < baseStart_964754 := by decide
  rcases family_descends (prefixWord ++ tailWord_964754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964765 : List Nat := [1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_964765 : Nat := 118140960795 + 964765 * 2 ^ 59
def prefixEnd_964765 : Nat := 4983230072969 + 3 ^ 40 * 964765 * 2
def baseEnd_964765 : Nat := 146781678114080914429817

theorem tailTrace_964765 : CollatzResearch.WordTrace tailWord_964765 prefixEnd_964765 146781678114080914429817 := by
  unfold tailWord_964765
  simp only [CollatzResearch.WordTrace]
  refine ⟨35187870349828648589199749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23458580233219099059466499 35187870349828648589199749)
  ·
    refine ⟨6597725690592871610474953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35187870349828648589199749 6597725690592871610474953)
    ·
      refine ⟨4948294267944653707856215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6597725690592871610474953 4948294267944653707856215)
      ·
        refine ⟨7422441401916980561784323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948294267944653707856215 7422441401916980561784323)
        ·
          refine ⟨11133662102875470842676485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7422441401916980561784323 11133662102875470842676485)
          ·
            refine ⟨2087561644289150783001841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11133662102875470842676485 2087561644289150783001841)
            ·
              refine ⟨1565671233216863087251381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087561644289150783001841 1565671233216863087251381)
              ·
                refine ⟨146781678114080914429817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1565671233216863087251381 146781678114080914429817)
                ·
                  rfl

theorem cell20_964765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_964765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964765 prefixEnd_964765 := by exact prefixLift 964765
  have htrace : WordTrace (prefixWord ++ tailWord_964765) baseStart_964765 baseEnd_964765 := by
    simpa [prefixWord, tailWord_964765, baseEnd_964765] using wordTrace_append hprefix tailTrace_964765
  have hstable : (prefixWord ++ tailWord_964765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964765).length < 2 ^ (prefixWord ++ tailWord_964765).sum := by decide
  have hdescent : baseEnd_964765 < baseStart_964765 := by decide
  rcases family_descends (prefixWord ++ tailWord_964765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964768 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_964768 : Nat := 118140960795 + 964768 * 2 ^ 59
def prefixEnd_964768 : Nat := 4983230072969 + 3 ^ 40 * 964768 * 2
def baseEnd_964768 : Nat := 440346403623988066189439

theorem tailTrace_964768 : CollatzResearch.WordTrace tailWord_964768 prefixEnd_964768 440346403623988066189439 := by
  unfold tailWord_964768
  simp only [CollatzResearch.WordTrace]
  refine ⟨17593989884408890050779479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23458653179211853401039305 17593989884408890050779479)
  ·
    refine ⟨26390984826613335076169219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17593989884408890050779479 26390984826613335076169219)
    ·
      refine ⟨39586477239920002614253829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26390984826613335076169219 39586477239920002614253829)
      ·
        refine ⟨7422464482485000490172593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39586477239920002614253829 7422464482485000490172593)
        ·
          refine ⟨5566848361863750367629445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7422464482485000490172593 5566848361863750367629445)
          ·
            refine ⟨1043784067849453193930521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5566848361863750367629445 1043784067849453193930521)
            ·
              refine ⟨782838050887089895447891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043784067849453193930521 782838050887089895447891)
              ·
                refine ⟨1174257076330634843171837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782838050887089895447891 1174257076330634843171837)
                ·
                  refine ⟨440346403623988066189439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174257076330634843171837 440346403623988066189439)
                  ·
                    rfl

theorem cell20_964768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_964768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964768 prefixEnd_964768 := by exact prefixLift 964768
  have htrace : WordTrace (prefixWord ++ tailWord_964768) baseStart_964768 baseEnd_964768 := by
    simpa [prefixWord, tailWord_964768, baseEnd_964768] using wordTrace_append hprefix tailTrace_964768
  have hstable : (prefixWord ++ tailWord_964768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964768).length < 2 ^ (prefixWord ++ tailWord_964768).sum := by decide
  have hdescent : baseEnd_964768 < baseStart_964768 := by decide
  rcases family_descends (prefixWord ++ tailWord_964768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964786 : List Nat := [3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_964786 : Nat := 118140960795 + 964786 * 2 ^ 59
def prefixEnd_964786 : Nat := 4983230072969 + 3 ^ 40 * 964786 * 2
def baseEnd_964786 : Nat := 146784873104820001196455

theorem tailTrace_964786 : CollatzResearch.WordTrace tailWord_964786 prefixEnd_964786 146784873104820001196455 := by
  unfold tailWord_964786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797159070688142293928553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23459090855168379450476141 8797159070688142293928553)
  ·
    refine ⟨6597869303016106720446415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8797159070688142293928553 6597869303016106720446415)
    ·
      refine ⟨9896803954524160080669623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597869303016106720446415 9896803954524160080669623)
      ·
        refine ⟨14845205931786240121004435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896803954524160080669623 14845205931786240121004435)
        ·
          refine ⟨22267808897679360181506653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14845205931786240121004435 22267808897679360181506653)
          ·
            refine ⟨8350428336629760068064995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22267808897679360181506653 8350428336629760068064995)
            ·
              refine ⟨12525642504944640102097493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350428336629760068064995 12525642504944640102097493)
              ·
                refine ⟨146784873104820001196455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12525642504944640102097493 146784873104820001196455)
                ·
                  rfl

theorem cell20_964786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_964786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964786 prefixEnd_964786 := by exact prefixLift 964786
  have htrace : WordTrace (prefixWord ++ tailWord_964786) baseStart_964786 baseEnd_964786 := by
    simpa [prefixWord, tailWord_964786, baseEnd_964786] using wordTrace_append hprefix tailTrace_964786
  have hstable : (prefixWord ++ tailWord_964786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964786).length < 2 ^ (prefixWord ++ tailWord_964786).sum := by decide
  have hdescent : baseEnd_964786 < baseStart_964786 := by decide
  rcases family_descends (prefixWord ++ tailWord_964786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964831 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_964831 : Nat := 118140960795 + 964831 * 2 ^ 59
def prefixEnd_964831 : Nat := 4983230072969 + 3 ^ 40 * 964831 * 2
def baseEnd_964831 : Nat := 440375158540639847089181

theorem tailTrace_964831 : CollatzResearch.WordTrace tailWord_964831 prefixEnd_964831 440375158540639847089181 := by
  unfold tailWord_964831
  simp only [CollatzResearch.WordTrace]
  refine ⟨35190277567589541861102347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23460185045059694574068231 35190277567589541861102347)
  ·
    refine ⟨52785416351384312791653521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35190277567589541861102347 52785416351384312791653521)
    ·
      refine ⟨39589062263538234593740141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52785416351384312791653521 39589062263538234593740141)
      ·
        refine ⟨14845898348826837972652553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39589062263538234593740141 14845898348826837972652553)
        ·
          refine ⟨11134423761620128479489415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14845898348826837972652553 11134423761620128479489415)
          ·
            refine ⟨16701635642430192719234123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134423761620128479489415 16701635642430192719234123)
            ·
              refine ⟨25052453463645289078851185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16701635642430192719234123 25052453463645289078851185)
              ·
                refine ⟨18789340097733966809138389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25052453463645289078851185 18789340097733966809138389)
                ·
                  refine ⟨440375158540639847089181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18789340097733966809138389 440375158540639847089181)
                  ·
                    rfl

theorem cell20_964831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_964831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964831 prefixEnd_964831 := by exact prefixLift 964831
  have htrace : WordTrace (prefixWord ++ tailWord_964831) baseStart_964831 baseEnd_964831 := by
    simpa [prefixWord, tailWord_964831, baseEnd_964831] using wordTrace_append hprefix tailTrace_964831
  have hstable : (prefixWord ++ tailWord_964831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964831).length < 2 ^ (prefixWord ++ tailWord_964831).sum := by decide
  have hdescent : baseEnd_964831 < baseStart_964831 := by decide
  rcases family_descends (prefixWord ++ tailWord_964831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964872 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_964872 : Nat := 118140960795 + 964872 * 2 ^ 59
def prefixEnd_964872 : Nat := 4983230072969 + 3 ^ 40 * 964872 * 2
def baseEnd_964872 : Nat := 440393872057825926722347

theorem tailTrace_964872 : CollatzResearch.WordTrace tailWord_964872 prefixEnd_964872 440393872057825926722347 := by
  unfold tailWord_964872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17595886480220502931672435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23461181973627337242229913 17595886480220502931672435)
  ·
    refine ⟨26393829720330754397508653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17595886480220502931672435 26393829720330754397508653)
    ·
      refine ⟨9897686145124032899065745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26393829720330754397508653 9897686145124032899065745)
      ·
        refine ⟨7423264608843024674299309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9897686145124032899065745 7423264608843024674299309)
        ·
          refine ⟨2783724228316134252862241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7423264608843024674299309 2783724228316134252862241)
          ·
            refine ⟨2087793171237100689646681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783724228316134252862241 2087793171237100689646681)
            ·
              refine ⟨1565844878427825517235011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087793171237100689646681 1565844878427825517235011)
              ·
                refine ⟨2348767317641738275852517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565844878427825517235011 2348767317641738275852517)
                ·
                  refine ⟨440393872057825926722347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348767317641738275852517 440393872057825926722347)
                  ·
                    rfl

theorem cell20_964872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_964872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964872 prefixEnd_964872 := by exact prefixLift 964872
  have htrace : WordTrace (prefixWord ++ tailWord_964872) baseStart_964872 baseEnd_964872 := by
    simpa [prefixWord, tailWord_964872, baseEnd_964872] using wordTrace_append hprefix tailTrace_964872
  have hstable : (prefixWord ++ tailWord_964872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964872).length < 2 ^ (prefixWord ++ tailWord_964872).sum := by decide
  have hdescent : baseEnd_964872 < baseStart_964872 := by decide
  rcases family_descends (prefixWord ++ tailWord_964872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964896 : List Nat := [2, 1, 1, 5, 2, 3, 2, 4]
def baseStart_964896 : Nat := 118140960795 + 964896 * 2 ^ 59
def prefixEnd_964896 : Nat := 4983230072969 + 3 ^ 40 * 964896 * 2
def baseEnd_964896 : Nat := 146801608770596169974083

theorem tailTrace_964896 : CollatzResearch.WordTrace tailWord_964896 prefixEnd_964896 146801608770596169974083 := by
  unfold tailWord_964896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17596324156177028981109271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23461765541569371974812361 17596324156177028981109271)
  ·
    refine ⟨26394486234265543471663907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17596324156177028981109271 26394486234265543471663907)
    ·
      refine ⟨39591729351398315207495861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26394486234265543471663907 39591729351398315207495861)
      ·
        refine ⟨3711724626693592050702737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39591729351398315207495861 3711724626693592050702737)
        ·
          refine ⟨2783793470020194038027053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3711724626693592050702737 2783793470020194038027053)
          ·
            refine ⟨1043922551257572764260145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2783793470020194038027053 1043922551257572764260145)
            ·
              refine ⟨782941913443179573195109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043922551257572764260145 782941913443179573195109)
              ·
                refine ⟨146801608770596169974083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782941913443179573195109 146801608770596169974083)
                ·
                  rfl

theorem cell20_964896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_964896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964896 prefixEnd_964896 := by exact prefixLift 964896
  have htrace : WordTrace (prefixWord ++ tailWord_964896) baseStart_964896 baseEnd_964896 := by
    simpa [prefixWord, tailWord_964896, baseEnd_964896] using wordTrace_append hprefix tailTrace_964896
  have hstable : (prefixWord ++ tailWord_964896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964896).length < 2 ^ (prefixWord ++ tailWord_964896).sum := by decide
  have hdescent : baseEnd_964896 < baseStart_964896 := by decide
  rcases family_descends (prefixWord ++ tailWord_964896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964924 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_964924 : Nat := 118140960795 + 964924 * 2 ^ 59
def prefixEnd_964924 : Nat := 4983230072969 + 3 ^ 40 * 964924 * 2
def baseEnd_964924 : Nat := 440417606274744856988801

theorem tailTrace_964924 : CollatzResearch.WordTrace tailWord_964924 prefixEnd_964924 440417606274744856988801 := by
  unfold tailWord_964924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17596834778126309372118913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23462446370835079162825217 17596834778126309372118913)
  ·
    refine ⟨13197626083594732029089185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17596834778126309372118913 13197626083594732029089185)
    ·
      refine ⟨9898219562696049021816889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13197626083594732029089185 9898219562696049021816889)
      ·
        refine ⟨7423664672022036766362667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9898219562696049021816889 7423664672022036766362667)
        ·
          refine ⟨11135497008033055149544001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423664672022036766362667 11135497008033055149544001)
          ·
            refine ⟨8351622756024791362158001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11135497008033055149544001 8351622756024791362158001)
            ·
              refine ⟨6263717067018593521618501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8351622756024791362158001 6263717067018593521618501)
              ·
                refine ⟨1174446950065986285303469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6263717067018593521618501 1174446950065986285303469)
                ·
                  refine ⟨440417606274744856988801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174446950065986285303469 440417606274744856988801)
                  ·
                    rfl

theorem cell20_964924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_964924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964924 prefixEnd_964924 := by exact prefixLift 964924
  have htrace : WordTrace (prefixWord ++ tailWord_964924) baseStart_964924 baseEnd_964924 := by
    simpa [prefixWord, tailWord_964924, baseEnd_964924] using wordTrace_append hprefix tailTrace_964924
  have hstable : (prefixWord ++ tailWord_964924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964924).length < 2 ^ (prefixWord ++ tailWord_964924).sum := by decide
  have hdescent : baseEnd_964924 < baseStart_964924 := by decide
  rcases family_descends (prefixWord ++ tailWord_964924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964927 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 2]
def baseStart_964927 : Nat := 118140960795 + 964927 * 2 ^ 59
def prefixEnd_964927 : Nat := 4983230072969 + 3 ^ 40 * 964927 * 2
def baseEnd_964927 : Nat := 440418975556490179888789

theorem tailTrace_964927 : CollatzResearch.WordTrace tailWord_964927 prefixEnd_964927 440418975556490179888789 := by
  unfold tailWord_964927
  simp only [CollatzResearch.WordTrace]
  refine ⟨35193778975241750256597035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23462519316827833504398023 35193778975241750256597035)
  ·
    refine ⟨52790668462862625384895553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35193778975241750256597035 52790668462862625384895553)
    ·
      refine ⟨39593001347146969038671665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52790668462862625384895553 39593001347146969038671665)
      ·
        refine ⟨29694751010360226779003749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39593001347146969038671665 29694751010360226779003749)
        ·
          refine ⟨5567765814442542521063203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29694751010360226779003749 5567765814442542521063203)
          ·
            refine ⟨8351648721663813781594805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567765814442542521063203 8351648721663813781594805)
            ·
              refine ⟨782967067655982542024513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8351648721663813781594805 782967067655982542024513)
              ·
                refine ⟨587225300741986906518385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782967067655982542024513 587225300741986906518385)
                ·
                  refine ⟨440418975556490179888789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587225300741986906518385 440418975556490179888789)
                  ·
                    rfl

theorem cell20_964927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 2].length) (baseStart_964927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964927 prefixEnd_964927 := by exact prefixLift 964927
  have htrace : WordTrace (prefixWord ++ tailWord_964927) baseStart_964927 baseEnd_964927 := by
    simpa [prefixWord, tailWord_964927, baseEnd_964927] using wordTrace_append hprefix tailTrace_964927
  have hstable : (prefixWord ++ tailWord_964927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964927).length < 2 ^ (prefixWord ++ tailWord_964927).sum := by decide
  have hdescent : baseEnd_964927 < baseStart_964927 := by decide
  rcases family_descends (prefixWord ++ tailWord_964927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964931 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_964931 : Nat := 118140960795 + 964931 * 2 ^ 59
def prefixEnd_964931 : Nat := 4983230072969 + 3 ^ 40 * 964931 * 2
def baseEnd_964931 : Nat := 440420801265483943755439

theorem tailTrace_964931 : CollatzResearch.WordTrace tailWord_964931 prefixEnd_964931 440420801265483943755439 := by
  unfold tailWord_964931
  simp only [CollatzResearch.WordTrace]
  refine ⟨35193924867227258939742647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23462616578151505959828431 35193924867227258939742647)
  ·
    refine ⟨52790887300840888409613971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35193924867227258939742647 52790887300840888409613971)
    ·
      refine ⟨79186330951261332614420957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52790887300840888409613971 79186330951261332614420957)
      ·
        refine ⟨29694874106722999730407859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79186330951261332614420957 29694874106722999730407859)
        ·
          refine ⟨44542311160084499595611789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29694874106722999730407859 44542311160084499595611789)
          ·
            refine ⟨16703366685031687348354421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44542311160084499595611789 16703366685031687348354421)
            ·
              refine ⟨1565940626721720688908227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16703366685031687348354421 1565940626721720688908227)
              ·
                refine ⟨2348910940082581033362341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565940626721720688908227 2348910940082581033362341)
                ·
                  refine ⟨440420801265483943755439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348910940082581033362341 440420801265483943755439)
                  ·
                    rfl

theorem cell20_964931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_964931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964931 prefixEnd_964931 := by exact prefixLift 964931
  have htrace : WordTrace (prefixWord ++ tailWord_964931) baseStart_964931 baseEnd_964931 := by
    simpa [prefixWord, tailWord_964931, baseEnd_964931] using wordTrace_append hprefix tailTrace_964931
  have hstable : (prefixWord ++ tailWord_964931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964931).length < 2 ^ (prefixWord ++ tailWord_964931).sum := by decide
  have hdescent : baseEnd_964931 < baseStart_964931 := by decide
  rcases family_descends (prefixWord ++ tailWord_964931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964993 : List Nat := [1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_964993 : Nat := 118140960795 + 964993 * 2 ^ 59
def prefixEnd_964993 : Nat := 4983230072969 + 3 ^ 40 * 964993 * 2
def baseEnd_964993 : Nat := 146816366584962427896173

theorem tailTrace_964993 : CollatzResearch.WordTrace tailWord_964993 prefixEnd_964993 146816366584962427896173 := by
  unfold tailWord_964993
  simp only [CollatzResearch.WordTrace]
  refine ⟨35196186193002643528499633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23464124128668429018999755 35196186193002643528499633)
  ·
    refine ⟨26397139644751982646374725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35196186193002643528499633 26397139644751982646374725)
    ·
      refine ⟨4949463683390996746195261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26397139644751982646374725 4949463683390996746195261)
      ·
        refine ⟨1856048881271623779823223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4949463683390996746195261 1856048881271623779823223)
        ·
          refine ⟨2784073321907435669734835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856048881271623779823223 2784073321907435669734835)
          ·
            refine ⟨4176109982861153504602253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784073321907435669734835 4176109982861153504602253)
            ·
              refine ⟨1566041243572932564225845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4176109982861153504602253 1566041243572932564225845)
              ·
                refine ⟨146816366584962427896173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1566041243572932564225845 146816366584962427896173)
                ·
                  rfl

theorem cell20_964993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_964993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_964993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_964993 prefixEnd_964993 := by exact prefixLift 964993
  have htrace : WordTrace (prefixWord ++ tailWord_964993) baseStart_964993 baseEnd_964993 := by
    simpa [prefixWord, tailWord_964993, baseEnd_964993] using wordTrace_append hprefix tailTrace_964993
  have hstable : (prefixWord ++ tailWord_964993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964993).length < 2 ^ (prefixWord ++ tailWord_964993).sum := by decide
  have hdescent : baseEnd_964993 < baseStart_964993 := by decide
  rcases family_descends (prefixWord ++ tailWord_964993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965000 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_965000 : Nat := 118140960795 + 965000 * 2 ^ 59
def prefixEnd_965000 : Nat := 4983230072969 + 3 ^ 40 * 965000 * 2
def baseEnd_965000 : Nat := 440452294745626370455157

theorem tailTrace_965000 : CollatzResearch.WordTrace tailWord_965000 prefixEnd_965000 440452294745626370455157 := by
  unfold tailWord_965000
  simp only [CollatzResearch.WordTrace]
  refine ⟨17598220751988641862002227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23464294335984855816002969 17598220751988641862002227)
  ·
    refine ⟨26397331127982962793003341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17598220751988641862002227 26397331127982962793003341)
    ·
      refine ⟨9898999172993611047376253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26397331127982962793003341 9898999172993611047376253)
      ·
        refine ⟨3712124689872604142766095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9898999172993611047376253 3712124689872604142766095)
        ·
          refine ⟨5568187034808906214149143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712124689872604142766095 5568187034808906214149143)
          ·
            refine ⟨8352280552213359321223715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568187034808906214149143 8352280552213359321223715)
            ·
              refine ⟨12528420828320038981835573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352280552213359321223715 12528420828320038981835573)
              ·
                refine ⟨1174539452655003654547085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12528420828320038981835573 1174539452655003654547085)
                ·
                  refine ⟨440452294745626370455157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174539452655003654547085 440452294745626370455157)
                  ·
                    rfl

theorem cell20_965000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_965000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965000 prefixEnd_965000 := by exact prefixLift 965000
  have htrace : WordTrace (prefixWord ++ tailWord_965000) baseStart_965000 baseEnd_965000 := by
    simpa [prefixWord, tailWord_965000, baseEnd_965000] using wordTrace_append hprefix tailTrace_965000
  have hstable : (prefixWord ++ tailWord_965000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965000).length < 2 ^ (prefixWord ++ tailWord_965000).sum := by decide
  have hdescent : baseEnd_965000 < baseStart_965000 := by decide
  rcases family_descends (prefixWord ++ tailWord_965000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965024 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 2]
def baseStart_965024 : Nat := 118140960795 + 965024 * 2 ^ 59
def prefixEnd_965024 : Nat := 4983230072969 + 3 ^ 40 * 965024 * 2
def baseEnd_965024 : Nat := 440463248999588953655059

theorem tailTrace_965024 : CollatzResearch.WordTrace tailWord_965024 prefixEnd_965024 440463248999588953655059 := by
  unfold tailWord_965024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17598658427945167911439063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23464877903926890548585417 17598658427945167911439063)
  ·
    refine ⟨26397987641917751867158595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17598658427945167911439063 26397987641917751867158595)
    ·
      refine ⟨39596981462876627800737893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26397987641917751867158595 39596981462876627800737893)
      ·
        refine ⟨7424434024289367712638355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39596981462876627800737893 7424434024289367712638355)
        ·
          refine ⟨11136651036434051568957533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424434024289367712638355 11136651036434051568957533)
          ·
            refine ⟨4176244138662769338359075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11136651036434051568957533 4176244138662769338359075)
            ·
              refine ⟨6264366207994154007538613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176244138662769338359075 6264366207994154007538613)
              ·
                refine ⟨587284331999451938206745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6264366207994154007538613 587284331999451938206745)
                ·
                  refine ⟨440463248999588953655059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587284331999451938206745 440463248999588953655059)
                  ·
                    rfl

theorem cell20_965024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_965024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965024 prefixEnd_965024 := by exact prefixLift 965024
  have htrace : WordTrace (prefixWord ++ tailWord_965024) baseStart_965024 baseEnd_965024 := by
    simpa [prefixWord, tailWord_965024, baseEnd_965024] using wordTrace_append hprefix tailTrace_965024
  have hstable : (prefixWord ++ tailWord_965024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965024).length < 2 ^ (prefixWord ++ tailWord_965024).sum := by decide
  have hdescent : baseEnd_965024 < baseStart_965024 := by decide
  rcases family_descends (prefixWord ++ tailWord_965024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965076 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_965076 : Nat := 118140960795 + 965076 * 2 ^ 59
def prefixEnd_965076 : Nat := 4983230072969 + 3 ^ 40 * 965076 * 2
def baseEnd_965076 : Nat := 440486983216507883921513

theorem tailTrace_965076 : CollatzResearch.WordTrace tailWord_965076 prefixEnd_965076 440486983216507883921513 := by
  unfold tailWord_965076
  simp only [CollatzResearch.WordTrace]
  refine ⟨17599606725850974351885541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23466142301134632469180721 17599606725850974351885541)
  ·
    refine ⟨3299926261097057690978539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17599606725850974351885541 3299926261097057690978539)
    ·
      refine ⟨4949889391645586536467809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299926261097057690978539 4949889391645586536467809)
      ·
        refine ⟨3712417043734189902350857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4949889391645586536467809 3712417043734189902350857)
        ·
          refine ⟨2784312782800642426763143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3712417043734189902350857 2784312782800642426763143)
          ·
            refine ⟨4176469174200963640144715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784312782800642426763143 4176469174200963640144715)
            ·
              refine ⟨6264703761301445460217073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176469174200963640144715 6264703761301445460217073)
              ·
                refine ⟨4698527820976084095162805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6264703761301445460217073 4698527820976084095162805)
                ·
                  refine ⟨440486983216507883921513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4698527820976084095162805 440486983216507883921513)
                  ·
                    rfl

theorem cell20_965076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_965076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965076 prefixEnd_965076 := by exact prefixLift 965076
  have htrace : WordTrace (prefixWord ++ tailWord_965076) baseStart_965076 baseEnd_965076 := by
    simpa [prefixWord, tailWord_965076, baseEnd_965076] using wordTrace_append hprefix tailTrace_965076
  have hstable : (prefixWord ++ tailWord_965076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965076).length < 2 ^ (prefixWord ++ tailWord_965076).sum := by decide
  have hdescent : baseEnd_965076 < baseStart_965076 := by decide
  rcases family_descends (prefixWord ++ tailWord_965076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965155 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 2]
def baseStart_965155 : Nat := 118140960795 + 965155 * 2 ^ 59
def prefixEnd_965155 : Nat := 4983230072969 + 3 ^ 40 * 965155 * 2
def baseEnd_965155 : Nat := 440523040969134720287857

theorem tailTrace_965155 : CollatzResearch.WordTrace tailWord_965155 prefixEnd_965155 440523040969134720287857 := by
  unfold tailWord_965155
  simp only [CollatzResearch.WordTrace]
  refine ⟨35202094818415745195896919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23468063212277163463931279 35202094818415745195896919)
  ·
    refine ⟨52803142227623617793845379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35202094818415745195896919 52803142227623617793845379)
    ·
      refine ⟨79204713341435426690768069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52803142227623617793845379 79204713341435426690768069)
      ·
        refine ⟨14850883751519142504519013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79204713341435426690768069 14850883751519142504519013)
        ·
          refine ⟨2784540703409839219597315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14850883751519142504519013 2784540703409839219597315)
          ·
            refine ⟨4176811055114758829395973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784540703409839219597315 4176811055114758829395973)
            ·
              refine ⟨783152072834017280511745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4176811055114758829395973 783152072834017280511745)
              ·
                refine ⟨587364054625512960383809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783152072834017280511745 587364054625512960383809)
                ·
                  refine ⟨440523040969134720287857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587364054625512960383809 440523040969134720287857)
                  ·
                    rfl

theorem cell20_965155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 2].length) (baseStart_965155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965155 prefixEnd_965155 := by exact prefixLift 965155
  have htrace : WordTrace (prefixWord ++ tailWord_965155) baseStart_965155 baseEnd_965155 := by
    simpa [prefixWord, tailWord_965155, baseEnd_965155] using wordTrace_append hprefix tailTrace_965155
  have hstable : (prefixWord ++ tailWord_965155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965155).length < 2 ^ (prefixWord ++ tailWord_965155).sum := by decide
  have hdescent : baseEnd_965155 < baseStart_965155 := by decide
  rcases family_descends (prefixWord ++ tailWord_965155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965187 : List Nat := [1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_965187 : Nat := 118140960795 + 965187 * 2 ^ 59
def prefixEnd_965187 : Nat := 4983230072969 + 3 ^ 40 * 965187 * 2
def baseEnd_965187 : Nat := 146845882213694943740353

theorem tailTrace_965187 : CollatzResearch.WordTrace tailWord_965187 prefixEnd_965187 146845882213694943740353 := by
  unfold tailWord_965187
  simp only [CollatzResearch.WordTrace]
  refine ⟨35203261954299814661061815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23468841302866543107374543 35203261954299814661061815)
  ·
    refine ⟨52804892931449721991592723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35203261954299814661061815 52804892931449721991592723)
    ·
      refine ⟨79207339397174582987389085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52804892931449721991592723 79207339397174582987389085)
      ·
        refine ⟨29702752273940468620270907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79207339397174582987389085 29702752273940468620270907)
        ·
          refine ⟨44554128410910702930406361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29702752273940468620270907 44554128410910702930406361)
          ·
            refine ⟨33415596308183027197804771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44554128410910702930406361 33415596308183027197804771)
            ·
              refine ⟨50123394462274540796707157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33415596308183027197804771 50123394462274540796707157)
              ·
                refine ⟨146845882213694943740353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50123394462274540796707157 146845882213694943740353)
                ·
                  rfl

theorem cell20_965187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_965187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965187 prefixEnd_965187 := by exact prefixLift 965187
  have htrace : WordTrace (prefixWord ++ tailWord_965187) baseStart_965187 baseEnd_965187 := by
    simpa [prefixWord, tailWord_965187, baseEnd_965187] using wordTrace_append hprefix tailTrace_965187
  have hstable : (prefixWord ++ tailWord_965187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965187).length < 2 ^ (prefixWord ++ tailWord_965187).sum := by decide
  have hdescent : baseEnd_965187 < baseStart_965187 := by decide
  rcases family_descends (prefixWord ++ tailWord_965187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965204 : List Nat := [2, 4, 1, 1, 1, 4, 7]
def baseStart_965204 : Nat := 118140960795 + 965204 * 2 ^ 59
def prefixEnd_965204 : Nat := 4983230072969 + 3 ^ 40 * 965204 * 2
def baseEnd_965204 : Nat := 48949489544923147517147

theorem tailTrace_965204 : CollatzResearch.WordTrace tailWord_965204 prefixEnd_965204 48949489544923147517147 := by
  unfold tailWord_965204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17601940997619113282215333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23469254663492151042953777 17601940997619113282215333)
  ·
    refine ⟨3300363937053583740415375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17601940997619113282215333 3300363937053583740415375)
    ·
      refine ⟨4950545905580375610623063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3300363937053583740415375 4950545905580375610623063)
      ·
        refine ⟨7425818858370563415934595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4950545905580375610623063 7425818858370563415934595)
        ·
          refine ⟨11138728287555845123901893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425818858370563415934595 11138728287555845123901893)
          ·
            refine ⟨2088511553916720960731605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11138728287555845123901893 2088511553916720960731605)
            ·
              refine ⟨48949489544923147517147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2088511553916720960731605 48949489544923147517147)
              ·
                rfl

theorem cell20_965204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_965204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965204 prefixEnd_965204 := by exact prefixLift 965204
  have htrace : WordTrace (prefixWord ++ tailWord_965204) baseStart_965204 baseEnd_965204 := by
    simpa [prefixWord, tailWord_965204, baseEnd_965204] using wordTrace_append hprefix tailTrace_965204
  have hstable : (prefixWord ++ tailWord_965204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965204).length < 2 ^ (prefixWord ++ tailWord_965204).sum := by decide
  have hdescent : baseEnd_965204 < baseStart_965204 := by decide
  rcases family_descends (prefixWord ++ tailWord_965204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965224 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_965224 : Nat := 118140960795 + 965224 * 2 ^ 59
def prefixEnd_965224 : Nat := 4983230072969 + 3 ^ 40 * 965224 * 2
def baseEnd_965224 : Nat := 440554534449277146987575

theorem tailTrace_965224 : CollatzResearch.WordTrace tailWord_965224 prefixEnd_965224 440554534449277146987575 := by
  unfold tailWord_965224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17602305727582884990079363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23469740970110513320105817 17602305727582884990079363)
  ·
    refine ⟨26403458591374327485119045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17602305727582884990079363 26403458591374327485119045)
    ·
      refine ⟨4950648485882686403459821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26403458591374327485119045 4950648485882686403459821)
      ·
        refine ⟨1856493182206007401297433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4950648485882686403459821 1856493182206007401297433)
        ·
          refine ⟨1392369886654505550973075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856493182206007401297433 1392369886654505550973075)
          ·
            refine ⟨2088554829981758326459613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392369886654505550973075 2088554829981758326459613)
            ·
              refine ⟨783208061243159372422355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2088554829981758326459613 783208061243159372422355)
              ·
                refine ⟨1174812091864739058633533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783208061243159372422355 1174812091864739058633533)
                ·
                  refine ⟨440554534449277146987575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174812091864739058633533 440554534449277146987575)
                  ·
                    rfl

theorem cell20_965224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_965224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965224 prefixEnd_965224 := by exact prefixLift 965224
  have htrace : WordTrace (prefixWord ++ tailWord_965224) baseStart_965224 baseEnd_965224 := by
    simpa [prefixWord, tailWord_965224, baseEnd_965224] using wordTrace_append hprefix tailTrace_965224
  have hstable : (prefixWord ++ tailWord_965224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965224).length < 2 ^ (prefixWord ++ tailWord_965224).sum := by decide
  have hdescent : baseEnd_965224 < baseStart_965224 := by decide
  rcases family_descends (prefixWord ++ tailWord_965224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965225 : List Nat := [1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_965225 : Nat := 118140960795 + 965225 * 2 ^ 59
def prefixEnd_965225 : Nat := 4983230072969 + 3 ^ 40 * 965225 * 2
def baseEnd_965225 : Nat := 146851663625508529318079

theorem tailTrace_965225 : CollatzResearch.WordTrace tailWord_965225 prefixEnd_965225 146851663625508529318079 := by
  unfold tailWord_965225
  simp only [CollatzResearch.WordTrace]
  refine ⟨35204647928162147150945129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23469765285441431433963419 35204647928162147150945129)
  ·
    refine ⟨26403485946121610363208847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35204647928162147150945129 26403485946121610363208847)
    ·
      refine ⟨39605228919182415544813271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26403485946121610363208847 39605228919182415544813271)
      ·
        refine ⟨59407843378773623317219907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39605228919182415544813271 59407843378773623317219907)
        ·
          refine ⟨89111765068160434975829861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59407843378773623317219907 89111765068160434975829861)
          ·
            refine ⟨16708455950280081557968099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89111765068160434975829861 16708455950280081557968099)
            ·
              refine ⟨25062683925420122336952149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16708455950280081557968099 25062683925420122336952149)
              ·
                refine ⟨146851663625508529318079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25062683925420122336952149 146851663625508529318079)
                ·
                  rfl

theorem cell20_965225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_965225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965225 prefixEnd_965225 := by exact prefixLift 965225
  have htrace : WordTrace (prefixWord ++ tailWord_965225) baseStart_965225 baseEnd_965225 := by
    simpa [prefixWord, tailWord_965225, baseEnd_965225] using wordTrace_append hprefix tailTrace_965225
  have hstable : (prefixWord ++ tailWord_965225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965225).length < 2 ^ (prefixWord ++ tailWord_965225).sum := by decide
  have hdescent : baseEnd_965225 < baseStart_965225 := by decide
  rcases family_descends (prefixWord ++ tailWord_965225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965249 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_965249 : Nat := 118140960795 + 965249 * 2 ^ 59
def prefixEnd_965249 : Nat := 4983230072969 + 3 ^ 40 * 965249 * 2
def baseEnd_965249 : Nat := 440565945130488171154139

theorem tailTrace_965249 : CollatzResearch.WordTrace tailWord_965249 prefixEnd_965249 440565945130488171154139 := by
  unfold tailWord_965249
  simp only [CollatzResearch.WordTrace]
  refine ⟨35205523280075199249818801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23470348853383466166545867 35205523280075199249818801)
  ·
    refine ⟨26404142460056399437364101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35205523280075199249818801 26404142460056399437364101)
    ·
      refine ⟨4950776711260574894505769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26404142460056399437364101 4950776711260574894505769)
      ·
        refine ⟨3713082533445431170879327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4950776711260574894505769 3713082533445431170879327)
        ·
          refine ⟨5569623800168146756318991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713082533445431170879327 5569623800168146756318991)
          ·
            refine ⟨8354435700252220134478487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569623800168146756318991 8354435700252220134478487)
            ·
              refine ⟨12531653550378330201717731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354435700252220134478487 12531653550378330201717731)
              ·
                refine ⟨18797480325567495302576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531653550378330201717731 18797480325567495302576597)
                ·
                  refine ⟨440565945130488171154139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18797480325567495302576597 440565945130488171154139)
                  ·
                    rfl

theorem cell20_965249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_965249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965249 prefixEnd_965249 := by exact prefixLift 965249
  have htrace : WordTrace (prefixWord ++ tailWord_965249) baseStart_965249 baseEnd_965249 := by
    simpa [prefixWord, tailWord_965249, baseEnd_965249] using wordTrace_append hprefix tailTrace_965249
  have hstable : (prefixWord ++ tailWord_965249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965249).length < 2 ^ (prefixWord ++ tailWord_965249).sum := by decide
  have hdescent : baseEnd_965249 < baseStart_965249 := by decide
  rcases family_descends (prefixWord ++ tailWord_965249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965266 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_965266 : Nat := 118140960795 + 965266 * 2 ^ 59
def prefixEnd_965266 : Nat := 4983230072969 + 3 ^ 40 * 965266 * 2
def baseEnd_965266 : Nat := 440573704393711667587403

theorem tailTrace_965266 : CollatzResearch.WordTrace tailWord_965266 prefixEnd_965266 440573704393711667587403 := by
  unfold tailWord_965266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801535830253402788296913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23470762214009074102125101 8801535830253402788296913)
  ·
    refine ⟨6601151872690052091222685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8801535830253402788296913 6601151872690052091222685)
    ·
      refine ⟨2475431952258769534208507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6601151872690052091222685 2475431952258769534208507)
      ·
        refine ⟨3713147928388154301312761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475431952258769534208507 3713147928388154301312761)
        ·
          refine ⟨2784860946291115725984571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3713147928388154301312761 2784860946291115725984571)
          ·
            refine ⟨4177291419436673588976857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784860946291115725984571 4177291419436673588976857)
            ·
              refine ⟨3132968564577505191732643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4177291419436673588976857 3132968564577505191732643)
              ·
                refine ⟨4699452846866257787598965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132968564577505191732643 4699452846866257787598965)
                ·
                  refine ⟨440573704393711667587403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4699452846866257787598965 440573704393711667587403)
                  ·
                    rfl

theorem cell20_965266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_965266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965266 prefixEnd_965266 := by exact prefixLift 965266
  have htrace : WordTrace (prefixWord ++ tailWord_965266) baseStart_965266 baseEnd_965266 := by
    simpa [prefixWord, tailWord_965266, baseEnd_965266] using wordTrace_append hprefix tailTrace_965266
  have hstable : (prefixWord ++ tailWord_965266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965266).length < 2 ^ (prefixWord ++ tailWord_965266).sum := by decide
  have hdescent : baseEnd_965266 < baseStart_965266 := by decide
  rcases family_descends (prefixWord ++ tailWord_965266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965324 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 2]
def baseStart_965324 : Nat := 118140960795 + 965324 * 2 ^ 59
def prefixEnd_965324 : Nat := 4983230072969 + 3 ^ 40 * 965324 * 2
def baseEnd_965324 : Nat := 440600177174121243653833

theorem tailTrace_965324 : CollatzResearch.WordTrace tailWord_965324 prefixEnd_965324 440600177174121243653833 := by
  unfold tailWord_965324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17604129377401743529399513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23472172503202324705866017 17604129377401743529399513)
  ·
    refine ⟨13203097033051307647049635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17604129377401743529399513 13203097033051307647049635)
    ·
      refine ⟨19804645549576961470574453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203097033051307647049635 19804645549576961470574453)
      ·
        refine ⟨1856685520272840137866355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19804645549576961470574453 1856685520272840137866355)
        ·
          refine ⟨2785028280409260206799533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856685520272840137866355 2785028280409260206799533)
          ·
            refine ⟨1044385605153472577549825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2785028280409260206799533 1044385605153472577549825)
            ·
              refine ⟨783289203865104433162369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044385605153472577549825 783289203865104433162369)
              ·
                refine ⟨587466902898828324871777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783289203865104433162369 587466902898828324871777)
                ·
                  refine ⟨440600177174121243653833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587466902898828324871777 440600177174121243653833)
                  ·
                    rfl

theorem cell20_965324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_965324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965324 prefixEnd_965324 := by exact prefixLift 965324
  have htrace : WordTrace (prefixWord ++ tailWord_965324) baseStart_965324 baseEnd_965324 := by
    simpa [prefixWord, tailWord_965324, baseEnd_965324] using wordTrace_append hprefix tailTrace_965324
  have hstable : (prefixWord ++ tailWord_965324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965324).length < 2 ^ (prefixWord ++ tailWord_965324).sum := by decide
  have hdescent : baseEnd_965324 < baseStart_965324 := by decide
  rcases family_descends (prefixWord ++ tailWord_965324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965349 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_965349 : Nat := 118140960795 + 965349 * 2 ^ 59
def prefixEnd_965349 : Nat := 4983230072969 + 3 ^ 40 * 965349 * 2
def baseEnd_965349 : Nat := 440611587855332267820397

theorem tailTrace_965349 : CollatzResearch.WordTrace tailWord_965349 prefixEnd_965349 440611587855332267820397 := by
  unfold tailWord_965349
  simp only [CollatzResearch.WordTrace]
  refine ⟨35209170579712916328459101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23472780386475277552306067 35209170579712916328459101)
  ·
    refine ⟨13203438967392343623172163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35209170579712916328459101 13203438967392343623172163)
    ·
      refine ⟨19805158451088515434758245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203438967392343623172163 19805158451088515434758245)
      ·
        refine ⟨3713467209579096644017171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19805158451088515434758245 3713467209579096644017171)
        ·
          refine ⟨5570200814368644966025757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713467209579096644017171 5570200814368644966025757)
          ·
            refine ⟨2088825305388241862259659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5570200814368644966025757 2088825305388241862259659)
            ·
              refine ⟨3133237958082362793389489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088825305388241862259659 3133237958082362793389489)
              ·
                refine ⟨2349928468561772095042117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133237958082362793389489 2349928468561772095042117)
                ·
                  refine ⟨440611587855332267820397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2349928468561772095042117 440611587855332267820397)
                  ·
                    rfl

theorem cell20_965349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_965349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965349 prefixEnd_965349 := by exact prefixLift 965349
  have htrace : WordTrace (prefixWord ++ tailWord_965349) baseStart_965349 baseEnd_965349 := by
    simpa [prefixWord, tailWord_965349, baseEnd_965349] using wordTrace_append hprefix tailTrace_965349
  have hstable : (prefixWord ++ tailWord_965349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965349).length < 2 ^ (prefixWord ++ tailWord_965349).sum := by decide
  have hdescent : baseEnd_965349 < baseStart_965349 := by decide
  rcases family_descends (prefixWord ++ tailWord_965349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965428 : List Nat := [2, 5, 1, 1, 4, 1, 6]
def baseStart_965428 : Nat := 118140960795 + 965428 * 2 ^ 59
def prefixEnd_965428 : Nat := 4983230072969 + 3 ^ 40 * 965428 * 2
def baseEnd_965428 : Nat := 48960849511995456020749

theorem tailTrace_965428 : CollatzResearch.WordTrace tailWord_965428 prefixEnd_965428 48960849511995456020749 := by
  unfold tailWord_965428
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606025973213356410292469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23474701297617808547056625 17606025973213356410292469)
  ·
    refine ⟨1650564934988752163464919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17606025973213356410292469 1650564934988752163464919)
    ·
      refine ⟨2475847402483128245197379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650564934988752163464919 2475847402483128245197379)
      ·
        refine ⟨3713771103724692367796069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475847402483128245197379 3713771103724692367796069)
        ·
          refine ⟨696332081948379818961763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3713771103724692367796069 696332081948379818961763)
          ·
            refine ⟨1044498122922569728442645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696332081948379818961763 1044498122922569728442645)
            ·
              refine ⟨48960849511995456020749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1044498122922569728442645 48960849511995456020749)
              ·
                rfl

theorem cell20_965428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 6].length) (baseStart_965428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965428 prefixEnd_965428 := by exact prefixLift 965428
  have htrace : WordTrace (prefixWord ++ tailWord_965428) baseStart_965428 baseEnd_965428 := by
    simpa [prefixWord, tailWord_965428, baseEnd_965428] using wordTrace_append hprefix tailTrace_965428
  have hstable : (prefixWord ++ tailWord_965428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965428).length < 2 ^ (prefixWord ++ tailWord_965428).sum := by decide
  have hdescent : baseEnd_965428 < baseStart_965428 := by decide
  rcases family_descends (prefixWord ++ tailWord_965428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965438 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_965438 : Nat := 118140960795 + 965438 * 2 ^ 59
def prefixEnd_965438 : Nat := 4983230072969 + 3 ^ 40 * 965438 * 2
def baseEnd_965438 : Nat := 440652209880443513853367

theorem tailTrace_965438 : CollatzResearch.WordTrace tailWord_965438 prefixEnd_965438 440652209880443513853367 := by
  unfold tailWord_965438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401552084548810566056121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23474944450926989685632645 4401552084548810566056121)
  ·
    refine ⟨3301164063411607924542091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4401552084548810566056121 3301164063411607924542091)
    ·
      refine ⟨4951746095117411886813137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301164063411607924542091 4951746095117411886813137)
      ·
        refine ⟨3713809571338058915109853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4951746095117411886813137 3713809571338058915109853)
        ·
          refine ⟨1392678589251772093166195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3713809571338058915109853 1392678589251772093166195)
          ·
            refine ⟨2089017883877658139749293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392678589251772093166195 2089017883877658139749293)
            ·
              refine ⟨783381706454121802405985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2089017883877658139749293 783381706454121802405985)
              ·
                refine ⟨587536279840591351804489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783381706454121802405985 587536279840591351804489)
                ·
                  refine ⟨440652209880443513853367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587536279840591351804489 440652209880443513853367)
                  ·
                    rfl

theorem cell20_965438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_965438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965438 prefixEnd_965438 := by exact prefixLift 965438
  have htrace : WordTrace (prefixWord ++ tailWord_965438) baseStart_965438 baseEnd_965438 := by
    simpa [prefixWord, tailWord_965438, baseEnd_965438] using wordTrace_append hprefix tailTrace_965438
  have hstable : (prefixWord ++ tailWord_965438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965438).length < 2 ^ (prefixWord ++ tailWord_965438).sum := by decide
  have hdescent : baseEnd_965438 < baseStart_965438 := by decide
  rcases family_descends (prefixWord ++ tailWord_965438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965439 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_965439 : Nat := 118140960795 + 965439 * 2 ^ 59
def prefixEnd_965439 : Nat := 4983230072969 + 3 ^ 40 * 965439 * 2
def baseEnd_965439 : Nat := 440652666307691954820029

theorem tailTrace_965439 : CollatzResearch.WordTrace tailWord_965439 prefixEnd_965439 440652666307691954820029 := by
  unfold tailWord_965439
  simp only [CollatzResearch.WordTrace]
  refine ⟨35212453149386861699235371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23474968766257907799490247 35212453149386861699235371)
  ·
    refine ⟨52818679724080292548853057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35212453149386861699235371 52818679724080292548853057)
    ·
      refine ⟨39614009793060219411639793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52818679724080292548853057 39614009793060219411639793)
      ·
        refine ⟨29710507344795164558729845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39614009793060219411639793 29710507344795164558729845)
        ·
          refine ⟨2785360063574546677380923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29710507344795164558729845 2785360063574546677380923)
          ·
            refine ⟨4178040095361820016071385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785360063574546677380923 4178040095361820016071385)
            ·
              refine ⟨3133530071521365012053539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178040095361820016071385 3133530071521365012053539)
              ·
                refine ⟨4700295107282047518080309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133530071521365012053539 4700295107282047518080309)
                ·
                  refine ⟨440652666307691954820029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700295107282047518080309 440652666307691954820029)
                  ·
                    rfl

theorem cell20_965439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_965439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965439 prefixEnd_965439 := by exact prefixLift 965439
  have htrace : WordTrace (prefixWord ++ tailWord_965439) baseStart_965439 baseEnd_965439 := by
    simpa [prefixWord, tailWord_965439, baseEnd_965439] using wordTrace_append hprefix tailTrace_965439
  have hstable : (prefixWord ++ tailWord_965439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965439).length < 2 ^ (prefixWord ++ tailWord_965439).sum := by decide
  have hdescent : baseEnd_965439 < baseStart_965439 := by decide
  rcases family_descends (prefixWord ++ tailWord_965439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965456 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_965456 : Nat := 118140960795 + 965456 * 2 ^ 59
def prefixEnd_965456 : Nat := 4983230072969 + 3 ^ 40 * 965456 * 2
def baseEnd_965456 : Nat := 440660425570915451253293

theorem tailTrace_965456 : CollatzResearch.WordTrace tailWord_965456 prefixEnd_965456 440660425570915451253293 := by
  unfold tailWord_965456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17606536595162636801302111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23475382126883515735069481 17606536595162636801302111)
  ·
    refine ⟨26409804892743955201953167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17606536595162636801302111 26409804892743955201953167)
    ·
      refine ⟨39614707339115932802929751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26409804892743955201953167 39614707339115932802929751)
      ·
        refine ⟨59422061008673899204394627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39614707339115932802929751 59422061008673899204394627)
        ·
          refine ⟨89133091513010848806591941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59422061008673899204394627 89133091513010848806591941)
          ·
            refine ⟨16712454658689534151235989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89133091513010848806591941 16712454658689534151235989)
            ·
              refine ⟨783396312126071913339187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16712454658689534151235989 783396312126071913339187)
              ·
                refine ⟨1175094468189107870008781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783396312126071913339187 1175094468189107870008781)
                ·
                  refine ⟨440660425570915451253293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175094468189107870008781 440660425570915451253293)
                  ·
                    rfl

theorem cell20_965456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_965456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965456 prefixEnd_965456 := by exact prefixLift 965456
  have htrace : WordTrace (prefixWord ++ tailWord_965456) baseStart_965456 baseEnd_965456 := by
    simpa [prefixWord, tailWord_965456, baseEnd_965456] using wordTrace_append hprefix tailTrace_965456
  have hstable : (prefixWord ++ tailWord_965456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965456).length < 2 ^ (prefixWord ++ tailWord_965456).sum := by decide
  have hdescent : baseEnd_965456 < baseStart_965456 := by decide
  rcases family_descends (prefixWord ++ tailWord_965456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965497 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 2]
def baseStart_965497 : Nat := 118140960795 + 965497 * 2 ^ 59
def prefixEnd_965497 : Nat := 4983230072969 + 3 ^ 40 * 965497 * 2
def baseEnd_965497 : Nat := 440679139088101530886459

theorem tailTrace_965497 : CollatzResearch.WordTrace tailWord_965497 prefixEnd_965497 440679139088101530886459 := by
  unfold tailWord_965497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35214568583176737604846745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23476379055451158403231163 35214568583176737604846745)
  ·
    refine ⟨26410926437382553203635059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35214568583176737604846745 26410926437382553203635059)
    ·
      refine ⟨39616389656073829805452589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26410926437382553203635059 39616389656073829805452589)
      ·
        refine ⟨14856146121027686177044721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39616389656073829805452589 14856146121027686177044721)
        ·
          refine ⟨11142109590770764632783541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14856146121027686177044721 11142109590770764632783541)
          ·
            refine ⟨1044572774134759184323457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11142109590770764632783541 1044572774134759184323457)
            ·
              refine ⟨783429580601069388242593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044572774134759184323457 783429580601069388242593)
              ·
                refine ⟨587572185450802041181945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783429580601069388242593 587572185450802041181945)
                ·
                  refine ⟨440679139088101530886459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587572185450802041181945 440679139088101530886459)
                  ·
                    rfl

theorem cell20_965497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_965497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965497 prefixEnd_965497 := by exact prefixLift 965497
  have htrace : WordTrace (prefixWord ++ tailWord_965497) baseStart_965497 baseEnd_965497 := by
    simpa [prefixWord, tailWord_965497, baseEnd_965497] using wordTrace_append hprefix tailTrace_965497
  have hstable : (prefixWord ++ tailWord_965497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965497).length < 2 ^ (prefixWord ++ tailWord_965497).sum := by decide
  have hdescent : baseEnd_965497 < baseStart_965497 := by decide
  rcases family_descends (prefixWord ++ tailWord_965497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965515 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_965515 : Nat := 118140960795 + 965515 * 2 ^ 59
def prefixEnd_965515 : Nat := 4983230072969 + 3 ^ 40 * 965515 * 2
def baseEnd_965515 : Nat := 440687354778573468286385

theorem tailTrace_965515 : CollatzResearch.WordTrace tailWord_965515 prefixEnd_965515 440687354778573468286385 := by
  unfold tailWord_965515
  simp only [CollatzResearch.WordTrace]
  refine ⟨35215225097111526679001999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23476816731407684452667999 35215225097111526679001999)
  ·
    refine ⟨52822837645667290018502999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35215225097111526679001999 52822837645667290018502999)
    ·
      refine ⟨79234256468500935027754499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52822837645667290018502999 79234256468500935027754499)
      ·
        refine ⟨118851384702751402541631749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79234256468500935027754499 118851384702751402541631749)
        ·
          refine ⟨22284634631765887976555953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118851384702751402541631749 22284634631765887976555953)
          ·
            refine ⟨16713475973824415982416965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22284634631765887976555953 16713475973824415982416965)
            ·
              refine ⟨3133776745092077996703181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16713475973824415982416965 3133776745092077996703181)
              ·
                refine ⟨1175166279409529248763693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133776745092077996703181 1175166279409529248763693)
                ·
                  refine ⟨440687354778573468286385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175166279409529248763693 440687354778573468286385)
                  ·
                    rfl

theorem cell20_965515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_965515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965515 prefixEnd_965515 := by exact prefixLift 965515
  have htrace : WordTrace (prefixWord ++ tailWord_965515) baseStart_965515 baseEnd_965515 := by
    simpa [prefixWord, tailWord_965515, baseEnd_965515] using wordTrace_append hprefix tailTrace_965515
  have hstable : (prefixWord ++ tailWord_965515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965515).length < 2 ^ (prefixWord ++ tailWord_965515).sum := by decide
  have hdescent : baseEnd_965515 < baseStart_965515 := by decide
  rcases family_descends (prefixWord ++ tailWord_965515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965539 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 2]
def baseStart_965539 : Nat := 118140960795 + 965539 * 2 ^ 59
def prefixEnd_965539 : Nat := 4983230072969 + 3 ^ 40 * 965539 * 2
def baseEnd_965539 : Nat := 440698309032536051486287

theorem tailTrace_965539 : CollatzResearch.WordTrace tailWord_965539 prefixEnd_965539 440698309032536051486287 := by
  unfold tailWord_965539
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216100449024578777875671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23477400299349719185250447 35216100449024578777875671)
  ·
    refine ⟨52824150673536868166813507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35216100449024578777875671 52824150673536868166813507)
    ·
      refine ⟨79236226010305302250220261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52824150673536868166813507 79236226010305302250220261)
      ·
        refine ⟨14856792376932244171916299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79236226010305302250220261 14856792376932244171916299)
        ·
          refine ⟨22285188565398366257874449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14856792376932244171916299 22285188565398366257874449)
          ·
            refine ⟨16713891424048774693405837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22285188565398366257874449 16713891424048774693405837)
            ·
              refine ⟨6267709284018290510027189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16713891424048774693405837 6267709284018290510027189)
              ·
                refine ⟨587597745376714735315049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6267709284018290510027189 587597745376714735315049)
                ·
                  refine ⟨440698309032536051486287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587597745376714735315049 440698309032536051486287)
                  ·
                    rfl

theorem cell20_965539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 2].length) (baseStart_965539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965539 prefixEnd_965539 := by exact prefixLift 965539
  have htrace : WordTrace (prefixWord ++ tailWord_965539) baseStart_965539 baseEnd_965539 := by
    simpa [prefixWord, tailWord_965539, baseEnd_965539] using wordTrace_append hprefix tailTrace_965539
  have hstable : (prefixWord ++ tailWord_965539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965539).length < 2 ^ (prefixWord ++ tailWord_965539).sum := by decide
  have hdescent : baseEnd_965539 < baseStart_965539 := by decide
  rcases family_descends (prefixWord ++ tailWord_965539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965549 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 5]
def baseStart_965549 : Nat := 118140960795 + 965549 * 2 ^ 59
def prefixEnd_965549 : Nat := 4983230072969 + 3 ^ 40 * 965549 * 2
def baseEnd_965549 : Nat := 440702873305020461152913

theorem tailTrace_965549 : CollatzResearch.WordTrace tailWord_965549 prefixEnd_965549 440702873305020461152913 := by
  unfold tailWord_965549
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216465178988350485739701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23477643452658900323826467 35216465178988350485739701)
  ·
    refine ⟨3301543610530157858038097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35216465178988350485739701 3301543610530157858038097)
    ·
      refine ⟨2476157707897618393528573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3301543610530157858038097 2476157707897618393528573)
      ·
        refine ⟨928559140461606897573215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2476157707897618393528573 928559140461606897573215)
        ·
          refine ⟨1392838710692410346359823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928559140461606897573215 1392838710692410346359823)
          ·
            refine ⟨2089258066038615519539735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392838710692410346359823 2089258066038615519539735)
            ·
              refine ⟨3133887099057923279309603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089258066038615519539735 3133887099057923279309603)
              ·
                refine ⟨4700830648586884918964405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3133887099057923279309603 4700830648586884918964405)
                ·
                  refine ⟨440702873305020461152913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700830648586884918964405 440702873305020461152913)
                  ·
                    rfl

theorem cell20_965549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_965549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965549 prefixEnd_965549 := by exact prefixLift 965549
  have htrace : WordTrace (prefixWord ++ tailWord_965549) baseStart_965549 baseEnd_965549 := by
    simpa [prefixWord, tailWord_965549, baseEnd_965549] using wordTrace_append hprefix tailTrace_965549
  have hstable : (prefixWord ++ tailWord_965549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965549).length < 2 ^ (prefixWord ++ tailWord_965549).sum := by decide
  have hdescent : baseEnd_965549 < baseStart_965549 := by decide
  rcases family_descends (prefixWord ++ tailWord_965549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965556 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_965556 : Nat := 118140960795 + 965556 * 2 ^ 59
def prefixEnd_965556 : Nat := 4983230072969 + 3 ^ 40 * 965556 * 2
def baseEnd_965556 : Nat := 440706068295759547919551

theorem tailTrace_965556 : CollatzResearch.WordTrace tailWord_965556 prefixEnd_965556 440706068295759547919551 := by
  unfold tailWord_965556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608360244981495340622261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23477813659975327120829681 17608360244981495340622261)
  ·
    refine ⟨1650783772967015188183337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17608360244981495340622261 1650783772967015188183337)
    ·
      refine ⟨1238087829725261391137503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1650783772967015188183337 1238087829725261391137503)
      ·
        refine ⟨1857131744587892086706255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238087829725261391137503 1857131744587892086706255)
        ·
          refine ⟨2785697616881838130059383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857131744587892086706255 2785697616881838130059383)
          ·
            refine ⟨4178546425322757195089075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785697616881838130059383 4178546425322757195089075)
            ·
              refine ⟨6267819637984135792633613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178546425322757195089075 6267819637984135792633613)
              ·
                refine ⟨2350432364244050922237605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6267819637984135792633613 2350432364244050922237605)
                ·
                  refine ⟨440706068295759547919551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350432364244050922237605 440706068295759547919551)
                  ·
                    rfl

theorem cell20_965556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_965556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965556 prefixEnd_965556 := by exact prefixLift 965556
  have htrace : WordTrace (prefixWord ++ tailWord_965556) baseStart_965556 baseEnd_965556 := by
    simpa [prefixWord, tailWord_965556, baseEnd_965556] using wordTrace_append hprefix tailTrace_965556
  have hstable : (prefixWord ++ tailWord_965556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965556).length < 2 ^ (prefixWord ++ tailWord_965556).sum := by decide
  have hdescent : baseEnd_965556 < baseStart_965556 := by decide
  rcases family_descends (prefixWord ++ tailWord_965556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965560 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_965560 : Nat := 118140960795 + 965560 * 2 ^ 59
def prefixEnd_965560 : Nat := 4983230072969 + 3 ^ 40 * 965560 * 2
def baseEnd_965560 : Nat := 440707894004753311786201

theorem tailTrace_965560 : CollatzResearch.WordTrace tailWord_965560 prefixEnd_965560 440707894004753311786201 := by
  unfold tailWord_965560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608433190974249682195067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23477910921298999576260089 17608433190974249682195067)
  ·
    refine ⟨26412649786461374523292601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17608433190974249682195067 26412649786461374523292601)
    ·
      refine ⟨19809487339846030892469451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26412649786461374523292601 19809487339846030892469451)
      ·
        refine ⟨29714231009769046338704177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19809487339846030892469451 29714231009769046338704177)
        ·
          refine ⟨22285673257326784754028133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29714231009769046338704177 22285673257326784754028133)
          ·
            refine ⟨4178563735748772141380275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22285673257326784754028133 4178563735748772141380275)
            ·
              refine ⟨6267845603623158212070413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178563735748772141380275 6267845603623158212070413)
              ·
                refine ⟨2350442101358684329526405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6267845603623158212070413 2350442101358684329526405)
                ·
                  refine ⟨440707894004753311786201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350442101358684329526405 440707894004753311786201)
                  ·
                    rfl

theorem cell20_965560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_965560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965560 prefixEnd_965560 := by exact prefixLift 965560
  have htrace : WordTrace (prefixWord ++ tailWord_965560) baseStart_965560 baseEnd_965560 := by
    simpa [prefixWord, tailWord_965560, baseEnd_965560] using wordTrace_append hprefix tailTrace_965560
  have hstable : (prefixWord ++ tailWord_965560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965560).length < 2 ^ (prefixWord ++ tailWord_965560).sum := by decide
  have hdescent : baseEnd_965560 < baseStart_965560 := by decide
  rcases family_descends (prefixWord ++ tailWord_965560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965590 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_965590 : Nat := 118140960795 + 965590 * 2 ^ 59
def prefixEnd_965590 : Nat := 4983230072969 + 3 ^ 40 * 965590 * 2
def baseEnd_965590 : Nat := 440721586822206540786079

theorem tailTrace_965590 : CollatzResearch.WordTrace tailWord_965590 prefixEnd_965590 440721586822206540786079 := by
  unfold tailWord_965590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201122535739988405498889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23478640381226542991988149 2201122535739988405498889)
  ·
    refine ⟨1650841901804991304124167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2201122535739988405498889 1650841901804991304124167)
    ·
      refine ⟨2476262852707486956186251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650841901804991304124167 2476262852707486956186251)
      ·
        refine ⟨3714394279061230434279377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476262852707486956186251 3714394279061230434279377)
        ·
          refine ⟨2785795709295922825709533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3714394279061230434279377 2785795709295922825709533)
          ·
            refine ⟨1044673390985971059641075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2785795709295922825709533 1044673390985971059641075)
            ·
              refine ⟨1567010086478956589461613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044673390985971059641075 1567010086478956589461613)
              ·
                refine ⟨587628782429608721048105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567010086478956589461613 587628782429608721048105)
                ·
                  refine ⟨440721586822206540786079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587628782429608721048105 440721586822206540786079)
                  ·
                    rfl

theorem cell20_965590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_965590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965590 prefixEnd_965590 := by exact prefixLift 965590
  have htrace : WordTrace (prefixWord ++ tailWord_965590) baseStart_965590 baseEnd_965590 := by
    simpa [prefixWord, tailWord_965590, baseEnd_965590] using wordTrace_append hprefix tailTrace_965590
  have hstable : (prefixWord ++ tailWord_965590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965590).length < 2 ^ (prefixWord ++ tailWord_965590).sum := by decide
  have hdescent : baseEnd_965590 < baseStart_965590 := by decide
  rcases family_descends (prefixWord ++ tailWord_965590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965594 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_965594 : Nat := 118140960795 + 965594 * 2 ^ 59
def prefixEnd_965594 : Nat := 4983230072969 + 3 ^ 40 * 965594 * 2
def baseEnd_965594 : Nat := 440723412531200304652729

theorem tailTrace_965594 : CollatzResearch.WordTrace tailWord_965594 prefixEnd_965594 440723412531200304652729 := by
  unfold tailWord_965594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8804526615956330792781959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23478737642550215447418557 8804526615956330792781959)
  ·
    refine ⟨13206789923934496189172939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8804526615956330792781959 13206789923934496189172939)
    ·
      refine ⟨19810184885901744283759409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13206789923934496189172939 19810184885901744283759409)
      ·
        refine ⟨14857638664426308212819557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19810184885901744283759409 14857638664426308212819557)
        ·
          refine ⟨2785807249579932789903667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14857638664426308212819557 2785807249579932789903667)
          ·
            refine ⟨4178710874369899184855501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785807249579932789903667 4178710874369899184855501)
            ·
              refine ⟨1567016577888712194320813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4178710874369899184855501 1567016577888712194320813)
              ·
                refine ⟨587631216708267072870305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567016577888712194320813 587631216708267072870305)
                ·
                  refine ⟨440723412531200304652729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587631216708267072870305 440723412531200304652729)
                  ·
                    rfl

theorem cell20_965594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_965594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965594 prefixEnd_965594 := by exact prefixLift 965594
  have htrace : WordTrace (prefixWord ++ tailWord_965594) baseStart_965594 baseEnd_965594 := by
    simpa [prefixWord, tailWord_965594, baseEnd_965594] using wordTrace_append hprefix tailTrace_965594
  have hstable : (prefixWord ++ tailWord_965594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965594).length < 2 ^ (prefixWord ++ tailWord_965594).sum := by decide
  have hdescent : baseEnd_965594 < baseStart_965594 := by decide
  rcases family_descends (prefixWord ++ tailWord_965594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965615 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 4]
def baseStart_965615 : Nat := 118140960795 + 965615 * 2 ^ 59
def prefixEnd_965615 : Nat := 4983230072969 + 3 ^ 40 * 965615 * 2
def baseEnd_965615 : Nat := 440732997503417564952643

theorem tailTrace_965615 : CollatzResearch.WordTrace tailWord_965615 prefixEnd_965615 440732997503417564952643 := by
  unfold tailWord_965615
  simp only [CollatzResearch.WordTrace]
  refine ⟨35218872396749243757642299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23479248264499495838428199 35218872396749243757642299)
  ·
    refine ⟨52828308595123865636463449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35218872396749243757642299 52828308595123865636463449)
    ·
      refine ⟨39621231446342899227347587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52828308595123865636463449 39621231446342899227347587)
      ·
        refine ⟨59431847169514348841021381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39621231446342899227347587 59431847169514348841021381)
        ·
          refine ⟨11143471344283940407691509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59431847169514348841021381 11143471344283940407691509)
          ·
            refine ⟨1044700438526619413221079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11143471344283940407691509 1044700438526619413221079)
            ·
              refine ⟨1567050657789929119831619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044700438526619413221079 1567050657789929119831619)
              ·
                refine ⟨2350575986684893679747429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567050657789929119831619 2350575986684893679747429)
                ·
                  refine ⟨440732997503417564952643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350575986684893679747429 440732997503417564952643)
                  ·
                    rfl

theorem cell20_965615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_965615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965615 prefixEnd_965615 := by exact prefixLift 965615
  have htrace : WordTrace (prefixWord ++ tailWord_965615) baseStart_965615 baseEnd_965615 := by
    simpa [prefixWord, tailWord_965615, baseEnd_965615] using wordTrace_append hprefix tailTrace_965615
  have hstable : (prefixWord ++ tailWord_965615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965615).length < 2 ^ (prefixWord ++ tailWord_965615).sum := by decide
  have hdescent : baseEnd_965615 < baseStart_965615 := by decide
  rcases family_descends (prefixWord ++ tailWord_965615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965621 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 3]
def baseStart_965621 : Nat := 118140960795 + 965621 * 2 ^ 59
def prefixEnd_965621 : Nat := 4983230072969 + 3 ^ 40 * 965621 * 2
def baseEnd_965621 : Nat := 440735736066908210752619

theorem tailTrace_965621 : CollatzResearch.WordTrace tailWord_965621 prefixEnd_965621 440735736066908210752619 := by
  unfold tailWord_965621
  simp only [CollatzResearch.WordTrace]
  refine ⟨35219091234727506782360717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23479394156485004521573811 35219091234727506782360717)
  ·
    refine ⟨13207159213022815043385269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35219091234727506782360717 13207159213022815043385269)
    ·
      refine ⟨1238171176220888910317369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13207159213022815043385269 1238171176220888910317369)
      ·
        refine ⟨928628382165666682738027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238171176220888910317369 928628382165666682738027)
        ·
          refine ⟨1392942573248500024107041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928628382165666682738027 1392942573248500024107041)
          ·
            refine ⟨1044706929936375018080281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392942573248500024107041 1044706929936375018080281)
            ·
              refine ⟨783530197452281263560211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044706929936375018080281 783530197452281263560211)
              ·
                refine ⟨1175295296178421895340317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783530197452281263560211 1175295296178421895340317)
                ·
                  refine ⟨440735736066908210752619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175295296178421895340317 440735736066908210752619)
                  ·
                    rfl

theorem cell20_965621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_965621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965621 prefixEnd_965621 := by exact prefixLift 965621
  have htrace : WordTrace (prefixWord ++ tailWord_965621) baseStart_965621 baseEnd_965621 := by
    simpa [prefixWord, tailWord_965621, baseEnd_965621] using wordTrace_append hprefix tailTrace_965621
  have hstable : (prefixWord ++ tailWord_965621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965621).length < 2 ^ (prefixWord ++ tailWord_965621).sum := by decide
  have hdescent : baseEnd_965621 < baseStart_965621 := by decide
  rcases family_descends (prefixWord ++ tailWord_965621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965622 : List Nat := [5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_965622 : Nat := 118140960795 + 965622 * 2 ^ 59
def prefixEnd_965622 : Nat := 4983230072969 + 3 ^ 40 * 965622 * 2
def baseEnd_965622 : Nat := 146912064164718883906427

theorem tailTrace_965622 : CollatzResearch.WordTrace tailWord_965622 prefixEnd_965622 146912064164718883906427 := by
  unfold tailWord_965622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201195481732742747071695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23479418471815922635431413 2201195481732742747071695)
  ·
    refine ⟨3301793222599114120607543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201195481732742747071695 3301793222599114120607543)
    ·
      refine ⟨4952689833898671180911315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301793222599114120607543 4952689833898671180911315)
      ·
        refine ⟨7429034750848006771366973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952689833898671180911315 7429034750848006771366973)
        ·
          refine ⟨2785888031568002539262615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7429034750848006771366973 2785888031568002539262615)
          ·
            refine ⟨4178832047352003808893923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785888031568002539262615 4178832047352003808893923)
            ·
              refine ⟨6268248071028005713340885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178832047352003808893923 6268248071028005713340885)
              ·
                refine ⟨146912064164718883906427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6268248071028005713340885 146912064164718883906427)
                ·
                  rfl

theorem cell20_965622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_965622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965622 prefixEnd_965622 := by exact prefixLift 965622
  have htrace : WordTrace (prefixWord ++ tailWord_965622) baseStart_965622 baseEnd_965622 := by
    simpa [prefixWord, tailWord_965622, baseEnd_965622] using wordTrace_append hprefix tailTrace_965622
  have hstable : (prefixWord ++ tailWord_965622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965622).length < 2 ^ (prefixWord ++ tailWord_965622).sum := by decide
  have hdescent : baseEnd_965622 < baseStart_965622 := by decide
  rcases family_descends (prefixWord ++ tailWord_965622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965643 : List Nat := [1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_965643 : Nat := 118140960795 + 965643 * 2 ^ 59
def prefixEnd_965643 : Nat := 4983230072969 + 3 ^ 40 * 965643 * 2
def baseEnd_965643 : Nat := 146915259155457970673065

theorem tailTrace_965643 : CollatzResearch.WordTrace tailWord_965643 prefixEnd_965643 146915259155457970673065 := by
  unfold tailWord_965643
  simp only [CollatzResearch.WordTrace]
  refine ⟨35219893640647804539661583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23479929093765203026441055 35219893640647804539661583)
  ·
    refine ⟨52829840460971706809492375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35219893640647804539661583 52829840460971706809492375)
    ·
      refine ⟨79244760691457560214238563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52829840460971706809492375 79244760691457560214238563)
      ·
        refine ⟨118867141037186340321357845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79244760691457560214238563 118867141037186340321357845)
        ·
          refine ⟨5571897236118109702563649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118867141037186340321357845 5571897236118109702563649)
          ·
            refine ⟨4178922927088582276922737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571897236118109702563649 4178922927088582276922737)
            ·
              refine ⟨3134192195316436707692053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178922927088582276922737 3134192195316436707692053)
              ·
                refine ⟨146915259155457970673065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3134192195316436707692053 146915259155457970673065)
                ·
                  rfl

theorem cell20_965643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_965643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965643 prefixEnd_965643 := by exact prefixLift 965643
  have htrace : WordTrace (prefixWord ++ tailWord_965643) baseStart_965643 baseEnd_965643 := by
    simpa [prefixWord, tailWord_965643, baseEnd_965643] using wordTrace_append hprefix tailTrace_965643
  have hstable : (prefixWord ++ tailWord_965643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965643).length < 2 ^ (prefixWord ++ tailWord_965643).sum := by decide
  have hdescent : baseEnd_965643 < baseStart_965643 := by decide
  rcases family_descends (prefixWord ++ tailWord_965643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965660 : List Nat := [2, 2, 3, 1, 5, 7]
def baseStart_965660 : Nat := 118140960795 + 965660 * 2 ^ 59
def prefixEnd_965660 : Nat := 4983230072969 + 3 ^ 40 * 965660 * 2
def baseEnd_965660 : Nat := 16324205064059163276017

theorem tailTrace_965660 : CollatzResearch.WordTrace tailWord_965660 prefixEnd_965660 16324205064059163276017 := by
  unfold tailWord_965660
  simp only [CollatzResearch.WordTrace]
  refine ⟨17610256840793108221515217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23480342454390810962020289 17610256840793108221515217)
  ·
    refine ⟨13207692630594831166136413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17610256840793108221515217 13207692630594831166136413)
    ·
      refine ⟨4952884736473061687301155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13207692630594831166136413 4952884736473061687301155)
      ·
        refine ⟨7429327104709592530951733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952884736473061687301155 7429327104709592530951733)
        ·
          refine ⟨696499416066524299776725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7429327104709592530951733 696499416066524299776725)
          ·
            refine ⟨16324205064059163276017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 696499416066524299776725 16324205064059163276017)
            ·
              rfl

theorem cell20_965660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 7].length) (baseStart_965660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965660 prefixEnd_965660 := by exact prefixLift 965660
  have htrace : WordTrace (prefixWord ++ tailWord_965660) baseStart_965660 baseEnd_965660 := by
    simpa [prefixWord, tailWord_965660, baseEnd_965660] using wordTrace_append hprefix tailTrace_965660
  have hstable : (prefixWord ++ tailWord_965660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965660).length < 2 ^ (prefixWord ++ tailWord_965660).sum := by decide
  have hdescent : baseEnd_965660 < baseStart_965660 := by decide
  rcases family_descends (prefixWord ++ tailWord_965660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965667 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_965667 : Nat := 118140960795 + 965667 * 2 ^ 59
def prefixEnd_965667 : Nat := 4983230072969 + 3 ^ 40 * 965667 * 2
def baseEnd_965667 : Nat := 440756731720336495219097

theorem tailTrace_965667 : CollatzResearch.WordTrace tailWord_965667 prefixEnd_965667 440756731720336495219097 := by
  unfold tailWord_965667
  simp only [CollatzResearch.WordTrace]
  refine ⟨35220768992560856638535255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23480512661707237759023503 35220768992560856638535255)
  ·
    refine ⟨52831153488841284957802883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35220768992560856638535255 52831153488841284957802883)
    ·
      refine ⟨79246730233261927436704325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52831153488841284957802883 79246730233261927436704325)
      ·
        refine ⟨14858761918736611394382061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79246730233261927436704325 14858761918736611394382061)
        ·
          refine ⟨5572035719526229272893273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14858761918736611394382061 5572035719526229272893273)
          ·
            refine ⟨4179026789644671954669955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572035719526229272893273 4179026789644671954669955)
            ·
              refine ⟨6268540184467007932004933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179026789644671954669955 6268540184467007932004933)
              ·
                refine ⟨1175351284587563987250925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6268540184467007932004933 1175351284587563987250925)
                ·
                  refine ⟨440756731720336495219097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175351284587563987250925 440756731720336495219097)
                  ·
                    rfl

theorem cell20_965667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_965667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965667 prefixEnd_965667 := by exact prefixLift 965667
  have htrace : WordTrace (prefixWord ++ tailWord_965667) baseStart_965667 baseEnd_965667 := by
    simpa [prefixWord, tailWord_965667, baseEnd_965667] using wordTrace_append hprefix tailTrace_965667
  have hstable : (prefixWord ++ tailWord_965667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965667).length < 2 ^ (prefixWord ++ tailWord_965667).sum := by decide
  have hdescent : baseEnd_965667 < baseStart_965667 := by decide
  rcases family_descends (prefixWord ++ tailWord_965667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965729 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 2]
def baseStart_965729 : Nat := 118140960795 + 965729 * 2 ^ 59
def prefixEnd_965729 : Nat := 4983230072969 + 3 ^ 40 * 965729 * 2
def baseEnd_965729 : Nat := 440785030209739835152177

theorem tailTrace_965729 : CollatzResearch.WordTrace tailWord_965729 prefixEnd_965729 440785030209739835152177 := by
  unfold tailWord_965729
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223030318336241227292241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23482020212224160818194827 35223030318336241227292241)
  ·
    refine ⟨26417272738752180920469181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35223030318336241227292241 26417272738752180920469181)
    ·
      refine ⟨9906477277032067845175943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26417272738752180920469181 9906477277032067845175943)
      ·
        refine ⟨14859715915548101767763915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906477277032067845175943 14859715915548101767763915)
        ·
          refine ⟨22289573873322152651645873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14859715915548101767763915 22289573873322152651645873)
          ·
            refine ⟨16717180404991614488734405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22289573873322152651645873 16717180404991614488734405)
            ·
              refine ⟨3134471325935927716637701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16717180404991614488734405 3134471325935927716637701)
              ·
                refine ⟨587713373612986446869569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3134471325935927716637701 587713373612986446869569)
                ·
                  refine ⟨440785030209739835152177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587713373612986446869569 440785030209739835152177)
                  ·
                    rfl

theorem cell20_965729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_965729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965729 prefixEnd_965729 := by exact prefixLift 965729
  have htrace : WordTrace (prefixWord ++ tailWord_965729) baseStart_965729 baseEnd_965729 := by
    simpa [prefixWord, tailWord_965729, baseEnd_965729] using wordTrace_append hprefix tailTrace_965729
  have hstable : (prefixWord ++ tailWord_965729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965729).length < 2 ^ (prefixWord ++ tailWord_965729).sum := by decide
  have hdescent : baseEnd_965729 < baseStart_965729 := by decide
  rcases family_descends (prefixWord ++ tailWord_965729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965749 : List Nat := [1, 3, 4, 3, 2, 1, 2, 4]
def baseStart_965749 : Nat := 118140960795 + 965749 * 2 ^ 59
def prefixEnd_965749 : Nat := 4983230072969 + 3 ^ 40 * 965749 * 2
def baseEnd_965749 : Nat := 146931386251569551495143

theorem tailTrace_965749 : CollatzResearch.WordTrace tailWord_965749 prefixEnd_965749 146931386251569551495143 := by
  unfold tailWord_965749
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223759778263784643020301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23482506518842523095346867 35223759778263784643020301)
  ·
    refine ⟨13208909916848919241132613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35223759778263784643020301 13208909916848919241132613)
    ·
      refine ⟨2476670609409172357712365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13208909916848919241132613 2476670609409172357712365)
      ·
        refine ⟨928751478528439634142137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2476670609409172357712365 928751478528439634142137)
        ·
          refine ⟨696563608896329725606603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928751478528439634142137 696563608896329725606603)
          ·
            refine ⟨1044845413344494588409905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696563608896329725606603 1044845413344494588409905)
            ·
              refine ⟨783634060008370941307429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044845413344494588409905 783634060008370941307429)
              ·
                refine ⟨146931386251569551495143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783634060008370941307429 146931386251569551495143)
                ·
                  rfl

theorem cell20_965749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].length) (baseStart_965749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965749 prefixEnd_965749 := by exact prefixLift 965749
  have htrace : WordTrace (prefixWord ++ tailWord_965749) baseStart_965749 baseEnd_965749 := by
    simpa [prefixWord, tailWord_965749, baseEnd_965749] using wordTrace_append hprefix tailTrace_965749
  have hstable : (prefixWord ++ tailWord_965749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965749).length < 2 ^ (prefixWord ++ tailWord_965749).sum := by decide
  have hdescent : baseEnd_965749 < baseStart_965749 := by decide
  rcases family_descends (prefixWord ++ tailWord_965749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965753 : List Nat := [1, 2, 1, 3, 5, 2, 2, 4]
def baseStart_965753 : Nat := 118140960795 + 965753 * 2 ^ 59
def prefixEnd_965753 : Nat := 4983230072969 + 3 ^ 40 * 965753 * 2
def baseEnd_965753 : Nat := 146931994821234139450693

theorem tailTrace_965753 : CollatzResearch.WordTrace tailWord_965753 prefixEnd_965753 146931994821234139450693 := by
  unfold tailWord_965753
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223905670249293326165913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23482603780166195550777275 35223905670249293326165913)
  ·
    refine ⟨26417929252686969994624435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35223905670249293326165913 26417929252686969994624435)
    ·
      refine ⟨39626893879030454991936653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26417929252686969994624435 39626893879030454991936653)
      ·
        refine ⟨14860085204636420621976245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39626893879030454991936653 14860085204636420621976245)
        ·
          refine ⟨1393132987934664433310273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14860085204636420621976245 1393132987934664433310273)
          ·
            refine ⟨1044849740950998324982705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393132987934664433310273 1044849740950998324982705)
            ·
              refine ⟨783637305713248743737029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044849740950998324982705 783637305713248743737029)
              ·
                refine ⟨146931994821234139450693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783637305713248743737029 146931994821234139450693)
                ·
                  rfl

theorem cell20_965753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_965753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965753 prefixEnd_965753 := by exact prefixLift 965753
  have htrace : WordTrace (prefixWord ++ tailWord_965753) baseStart_965753 baseEnd_965753 := by
    simpa [prefixWord, tailWord_965753, baseEnd_965753] using wordTrace_append hprefix tailTrace_965753
  have hstable : (prefixWord ++ tailWord_965753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965753).length < 2 ^ (prefixWord ++ tailWord_965753).sum := by decide
  have hdescent : baseEnd_965753 < baseStart_965753 := by decide
  rcases family_descends (prefixWord ++ tailWord_965753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965757 : List Nat := [1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_965757 : Nat := 118140960795 + 965757 * 2 ^ 59
def prefixEnd_965757 : Nat := 4983230072969 + 3 ^ 40 * 965757 * 2
def baseEnd_965757 : Nat := 146932603390898727406243

theorem tailTrace_965757 : CollatzResearch.WordTrace tailWord_965757 prefixEnd_965757 146932603390898727406243 := by
  unfold tailWord_965757
  simp only [CollatzResearch.WordTrace]
  refine ⟨35224051562234802009311525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23482701041489868006207683 35224051562234802009311525)
  ·
    refine ⟨6604509667919025376745911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35224051562234802009311525 6604509667919025376745911)
    ·
      refine ⟨9906764501878538065118867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604509667919025376745911 9906764501878538065118867)
      ·
        refine ⟨14860146752817807097678301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906764501878538065118867 14860146752817807097678301)
        ·
          refine ⟨5572555032306677661629363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14860146752817807097678301 5572555032306677661629363)
          ·
            refine ⟨8358832548460016492444045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572555032306677661629363 8358832548460016492444045)
            ·
              refine ⟨3134562205672506184666517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8358832548460016492444045 3134562205672506184666517)
              ·
                refine ⟨146932603390898727406243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3134562205672506184666517 146932603390898727406243)
                ·
                  rfl

theorem cell20_965757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_965757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965757 prefixEnd_965757 := by exact prefixLift 965757
  have htrace : WordTrace (prefixWord ++ tailWord_965757) baseStart_965757 baseEnd_965757 := by
    simpa [prefixWord, tailWord_965757, baseEnd_965757] using wordTrace_append hprefix tailTrace_965757
  have hstable : (prefixWord ++ tailWord_965757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965757).length < 2 ^ (prefixWord ++ tailWord_965757).sum := by decide
  have hdescent : baseEnd_965757 < baseStart_965757 := by decide
  rcases family_descends (prefixWord ++ tailWord_965757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965771 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_965771 : Nat := 118140960795 + 965771 * 2 ^ 59
def prefixEnd_965771 : Nat := 4983230072969 + 3 ^ 40 * 965771 * 2
def baseEnd_965771 : Nat := 440804200154174355752005

theorem tailTrace_965771 : CollatzResearch.WordTrace tailWord_965771 prefixEnd_965771 440804200154174355752005 := by
  unfold tailWord_965771
  simp only [CollatzResearch.WordTrace]
  refine ⟨35224562184184082400321167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23483041456122721600214111 35224562184184082400321167)
  ·
    refine ⟨52836843276276123600481751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35224562184184082400321167 52836843276276123600481751)
    ·
      refine ⟨79255264914414185400722627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52836843276276123600481751 79255264914414185400722627)
      ·
        refine ⟨118882897371621278101083941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79255264914414185400722627 118882897371621278101083941)
        ·
          refine ⟨22290543257178989643953239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118882897371621278101083941 22290543257178989643953239)
          ·
            refine ⟨33435814885768484465929859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22290543257178989643953239 33435814885768484465929859)
            ·
              refine ⟨50153722328652726698894789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33435814885768484465929859 50153722328652726698894789)
              ·
                refine ⟨9403822936622386256042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50153722328652726698894789 9403822936622386256042773)
                ·
                  refine ⟨440804200154174355752005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9403822936622386256042773 440804200154174355752005)
                  ·
                    rfl

theorem cell20_965771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_965771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965771 prefixEnd_965771 := by exact prefixLift 965771
  have htrace : WordTrace (prefixWord ++ tailWord_965771) baseStart_965771 baseEnd_965771 := by
    simpa [prefixWord, tailWord_965771, baseEnd_965771] using wordTrace_append hprefix tailTrace_965771
  have hstable : (prefixWord ++ tailWord_965771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965771).length < 2 ^ (prefixWord ++ tailWord_965771).sum := by decide
  have hdescent : baseEnd_965771 < baseStart_965771 := by decide
  rcases family_descends (prefixWord ++ tailWord_965771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965774 : List Nat := [4, 1, 1, 3, 2, 3, 6]
def baseStart_965774 : Nat := 118140960795 + 965774 * 2 ^ 59
def prefixEnd_965774 : Nat := 4983230072969 + 3 ^ 40 * 965774 * 2
def baseEnd_965774 : Nat := 48978396603991075405777

theorem tailTrace_965774 : CollatzResearch.WordTrace tailWord_965774 prefixEnd_965774 48978396603991075405777 := by
  unfold tailWord_965774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403083950396651739085047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23483114402115475941786917 4403083950396651739085047)
  ·
    refine ⟨6604625925594977608627571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4403083950396651739085047 6604625925594977608627571)
    ·
      refine ⟨9906938888392466412941357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604625925594977608627571 9906938888392466412941357)
      ·
        refine ⟨3715102083147174904853009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9906938888392466412941357 3715102083147174904853009)
        ·
          refine ⟨2786326562360381178639757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3715102083147174904853009 2786326562360381178639757)
          ·
            refine ⟨1044872460885142941989909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2786326562360381178639757 1044872460885142941989909)
            ·
              refine ⟨48978396603991075405777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1044872460885142941989909 48978396603991075405777)
              ·
                rfl

theorem cell20_965774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 6].length) (baseStart_965774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965774 prefixEnd_965774 := by exact prefixLift 965774
  have htrace : WordTrace (prefixWord ++ tailWord_965774) baseStart_965774 baseEnd_965774 := by
    simpa [prefixWord, tailWord_965774, baseEnd_965774] using wordTrace_append hprefix tailTrace_965774
  have hstable : (prefixWord ++ tailWord_965774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965774).length < 2 ^ (prefixWord ++ tailWord_965774).sum := by decide
  have hdescent : baseEnd_965774 < baseStart_965774 := by decide
  rcases family_descends (prefixWord ++ tailWord_965774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965794 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_965794 : Nat := 118140960795 + 965794 * 2 ^ 59
def prefixEnd_965794 : Nat := 4983230072969 + 3 ^ 40 * 965794 * 2
def baseEnd_965794 : Nat := 440814697980888497985245

theorem tailTrace_965794 : CollatzResearch.WordTrace tailWord_965794 prefixEnd_965794 440814697980888497985245 := by
  unfold tailWord_965794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806350265775189332102109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23483600708733838218938957 8806350265775189332102109)
  ·
    refine ⟨3302381349665695999538291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8806350265775189332102109 3302381349665695999538291)
    ·
      refine ⟨4953572024498543999307437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302381349665695999538291 4953572024498543999307437)
      ·
        refine ⟨1857589509186953999740289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4953572024498543999307437 1857589509186953999740289)
        ·
          refine ⟨1393192131890215499805217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857589509186953999740289 1393192131890215499805217)
          ·
            refine ⟨1044894098917661624853913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393192131890215499805217 1044894098917661624853913)
            ·
              refine ⟨783670574188246218640435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044894098917661624853913 783670574188246218640435)
              ·
                refine ⟨1175505861282369327960653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783670574188246218640435 1175505861282369327960653)
                ·
                  refine ⟨440814697980888497985245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175505861282369327960653 440814697980888497985245)
                  ·
                    rfl

theorem cell20_965794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_965794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965794 prefixEnd_965794 := by exact prefixLift 965794
  have htrace : WordTrace (prefixWord ++ tailWord_965794) baseStart_965794 baseEnd_965794 := by
    simpa [prefixWord, tailWord_965794, baseEnd_965794] using wordTrace_append hprefix tailTrace_965794
  have hstable : (prefixWord ++ tailWord_965794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965794).length < 2 ^ (prefixWord ++ tailWord_965794).sum := by decide
  have hdescent : baseEnd_965794 < baseStart_965794 := by decide
  rcases family_descends (prefixWord ++ tailWord_965794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965846 : List Nat := [5, 2, 1, 2, 2, 2, 1, 5]
def baseStart_965846 : Nat := 118140960795 + 965846 * 2 ^ 59
def prefixEnd_965846 : Nat := 4983230072969 + 3 ^ 40 * 965846 * 2
def baseEnd_965846 : Nat := 146946144065935809417233

theorem tailTrace_965846 : CollatzResearch.WordTrace tailWord_965846 prefixEnd_965846 146946144065935809417233 := by
  unfold tailWord_965846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201706103682023138081337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23484865105941580139534261 2201706103682023138081337)
  ·
    refine ⟨1651279577761517353561003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2201706103682023138081337 1651279577761517353561003)
    ·
      refine ⟨2476919366642276030341505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1651279577761517353561003 2476919366642276030341505)
      ·
        refine ⟨1857689524981707022756129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2476919366642276030341505 1857689524981707022756129)
        ·
          refine ⟨1393267143736280267067097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857689524981707022756129 1393267143736280267067097)
          ·
            refine ⟨1044950357802210200300323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393267143736280267067097 1044950357802210200300323)
            ·
              refine ⟨1567425536703315300450485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044950357802210200300323 1567425536703315300450485)
              ·
                refine ⟨146946144065935809417233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1567425536703315300450485 146946144065935809417233)
                ·
                  rfl

theorem cell20_965846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_965846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965846 prefixEnd_965846 := by exact prefixLift 965846
  have htrace : WordTrace (prefixWord ++ tailWord_965846) baseStart_965846 baseEnd_965846 := by
    simpa [prefixWord, tailWord_965846, baseEnd_965846] using wordTrace_append hprefix tailTrace_965846
  have hstable : (prefixWord ++ tailWord_965846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965846).length < 2 ^ (prefixWord ++ tailWord_965846).sum := by decide
  have hdescent : baseEnd_965846 < baseStart_965846 := by decide
  rcases family_descends (prefixWord ++ tailWord_965846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965857 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_965857 : Nat := 118140960795 + 965857 * 2 ^ 59
def prefixEnd_965857 : Nat := 4983230072969 + 3 ^ 40 * 965857 * 2
def baseEnd_965857 : Nat := 440843452897540278884987

theorem tailTrace_965857 : CollatzResearch.WordTrace tailWord_965857 prefixEnd_965857 440843452897540278884987 := by
  unfold tailWord_965857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35227698861872519087951825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23485132574581679391967883 35227698861872519087951825)
  ·
    refine ⟨26420774146404389315963869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35227698861872519087951825 26420774146404389315963869)
    ·
      refine ⟨9907790304901645993486451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26420774146404389315963869 9907790304901645993486451)
      ·
        refine ⟨14861685457352468990229677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907790304901645993486451 14861685457352468990229677)
        ·
          refine ⟨5573132046507175871336129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14861685457352468990229677 5573132046507175871336129)
          ·
            refine ⟨4179849034880381903502097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5573132046507175871336129 4179849034880381903502097)
            ·
              refine ⟨3134886776160286427626573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179849034880381903502097 3134886776160286427626573)
              ·
                refine ⟨1175582541060107410359965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3134886776160286427626573 1175582541060107410359965)
                ·
                  refine ⟨440843452897540278884987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175582541060107410359965 440843452897540278884987)
                  ·
                    rfl

theorem cell20_965857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_965857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965857 prefixEnd_965857 := by exact prefixLift 965857
  have htrace : WordTrace (prefixWord ++ tailWord_965857) baseStart_965857 baseEnd_965857 := by
    simpa [prefixWord, tailWord_965857, baseEnd_965857] using wordTrace_append hprefix tailTrace_965857
  have hstable : (prefixWord ++ tailWord_965857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965857).length < 2 ^ (prefixWord ++ tailWord_965857).sum := by decide
  have hdescent : baseEnd_965857 < baseStart_965857 := by decide
  rcases family_descends (prefixWord ++ tailWord_965857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965864 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_965864 : Nat := 118140960795 + 965864 * 2 ^ 59
def prefixEnd_965864 : Nat := 4983230072969 + 3 ^ 40 * 965864 * 2
def baseEnd_965864 : Nat := 440846647888279365651625

theorem tailTrace_965864 : CollatzResearch.WordTrace tailWord_965864 prefixEnd_965864 440846647888279365651625 := by
  unfold tailWord_965864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17613977086423579641728323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23485302781898106188971097 17613977086423579641728323)
  ·
    refine ⟨26420965629635369462592485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17613977086423579641728323 26420965629635369462592485)
    ·
      refine ⟨4953931055556631774236091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26420965629635369462592485 4953931055556631774236091)
      ·
        refine ⟨7430896583334947661354137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4953931055556631774236091 7430896583334947661354137)
        ·
          refine ⟨5573172437501210746015603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7430896583334947661354137 5573172437501210746015603)
          ·
            refine ⟨8359758656251816119023405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573172437501210746015603 8359758656251816119023405)
            ·
              refine ⟨3134909496094431044633777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8359758656251816119023405 3134909496094431044633777)
              ·
                refine ⟨2351182122070823283475333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3134909496094431044633777 2351182122070823283475333)
                ·
                  refine ⟨440846647888279365651625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351182122070823283475333 440846647888279365651625)
                  ·
                    rfl

theorem cell20_965864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_965864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965864 prefixEnd_965864 := by exact prefixLift 965864
  have htrace : WordTrace (prefixWord ++ tailWord_965864) baseStart_965864 baseEnd_965864 := by
    simpa [prefixWord, tailWord_965864, baseEnd_965864] using wordTrace_append hprefix tailTrace_965864
  have hstable : (prefixWord ++ tailWord_965864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965864).length < 2 ^ (prefixWord ++ tailWord_965864).sum := by decide
  have hdescent : baseEnd_965864 < baseStart_965864 := by decide
  rcases family_descends (prefixWord ++ tailWord_965864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965881 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 2]
def baseStart_965881 : Nat := 118140960795 + 965881 * 2 ^ 59
def prefixEnd_965881 : Nat := 4983230072969 + 3 ^ 40 * 965881 * 2
def baseEnd_965881 : Nat := 440854407151502862084889

theorem tailTrace_965881 : CollatzResearch.WordTrace tailWord_965881 prefixEnd_965881 440854407151502862084889 := by
  unfold tailWord_965881
  simp only [CollatzResearch.WordTrace]
  refine ⟨35228574213785571186825497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23485716142523714124550331 35228574213785571186825497)
  ·
    refine ⟨26421430660339178390119123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35228574213785571186825497 26421430660339178390119123)
    ·
      refine ⟨39632145990508767585178685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26421430660339178390119123 39632145990508767585178685)
      ·
        refine ⟨14862054746440787844442007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39632145990508767585178685 14862054746440787844442007)
        ·
          refine ⟨22293082119661181766663011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14862054746440787844442007 22293082119661181766663011)
          ·
            refine ⟨33439623179491772649994517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22293082119661181766663011 33439623179491772649994517)
            ·
              refine ⟨1567482336538676842968493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33439623179491772649994517 1567482336538676842968493)
              ·
                refine ⟨587805876202003816113185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567482336538676842968493 587805876202003816113185)
                ·
                  refine ⟨440854407151502862084889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587805876202003816113185 440854407151502862084889)
                  ·
                    rfl

theorem cell20_965881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_965881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965881 prefixEnd_965881 := by exact prefixLift 965881
  have htrace : WordTrace (prefixWord ++ tailWord_965881) baseStart_965881 baseEnd_965881 := by
    simpa [prefixWord, tailWord_965881, baseEnd_965881] using wordTrace_append hprefix tailTrace_965881
  have hstable : (prefixWord ++ tailWord_965881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965881).length < 2 ^ (prefixWord ++ tailWord_965881).sum := by decide
  have hdescent : baseEnd_965881 < baseStart_965881 := by decide
  rcases family_descends (prefixWord ++ tailWord_965881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965902 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_965902 : Nat := 118140960795 + 965902 * 2 ^ 59
def prefixEnd_965902 : Nat := 4983230072969 + 3 ^ 40 * 965902 * 2
def baseEnd_965902 : Nat := 440863992123720122384803

theorem tailTrace_965902 : CollatzResearch.WordTrace tailWord_965902 prefixEnd_965902 440863992123720122384803 := by
  unfold tailWord_965902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403667518338686471667495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23486226764472994515559973 4403667518338686471667495)
  ·
    refine ⟨6605501277508029707501243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4403667518338686471667495 6605501277508029707501243)
    ·
      refine ⟨9908251916262044561251865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6605501277508029707501243 9908251916262044561251865)
      ·
        refine ⟨7431188937196533420938899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9908251916262044561251865 7431188937196533420938899)
        ·
          refine ⟨11146783405794800131408349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431188937196533420938899 11146783405794800131408349)
          ·
            refine ⟨4180043777173050049278131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11146783405794800131408349 4180043777173050049278131)
            ·
              refine ⟨6270065665759575073917197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180043777173050049278131 6270065665759575073917197)
              ·
                refine ⟨2351274624659840652718949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6270065665759575073917197 2351274624659840652718949)
                ·
                  refine ⟨440863992123720122384803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351274624659840652718949 440863992123720122384803)
                  ·
                    rfl

theorem cell20_965902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_965902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965902 prefixEnd_965902 := by exact prefixLift 965902
  have htrace : WordTrace (prefixWord ++ tailWord_965902) baseStart_965902 baseEnd_965902 := by
    simpa [prefixWord, tailWord_965902, baseEnd_965902] using wordTrace_append hprefix tailTrace_965902
  have hstable : (prefixWord ++ tailWord_965902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965902).length < 2 ^ (prefixWord ++ tailWord_965902).sum := by decide
  have hdescent : baseEnd_965902 < baseStart_965902 := by decide
  rcases family_descends (prefixWord ++ tailWord_965902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965912 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_965912 : Nat := 118140960795 + 965912 * 2 ^ 59
def prefixEnd_965912 : Nat := 4983230072969 + 3 ^ 40 * 965912 * 2
def baseEnd_965912 : Nat := 440868556396204532051429

theorem tailTrace_965912 : CollatzResearch.WordTrace tailWord_965912 prefixEnd_965912 440868556396204532051429 := by
  unfold tailWord_965912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17614852438336631740601995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23486469917782175654135993 17614852438336631740601995)
  ·
    refine ⟨26422278657504947610902993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17614852438336631740601995 26422278657504947610902993)
    ·
      refine ⟨19816708993128710708177245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26422278657504947610902993 19816708993128710708177245)
      ·
        refine ⟨7431265872423266515566467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19816708993128710708177245 7431265872423266515566467)
        ·
          refine ⟨11146898808634899773349701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431265872423266515566467 11146898808634899773349701)
          ·
            refine ⟨2090043526619043707503069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11146898808634899773349701 2090043526619043707503069)
            ·
              refine ⟨783766322482141390313651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2090043526619043707503069 783766322482141390313651)
              ·
                refine ⟨1175649483723212085470477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783766322482141390313651 1175649483723212085470477)
                ·
                  refine ⟨440868556396204532051429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175649483723212085470477 440868556396204532051429)
                  ·
                    rfl

theorem cell20_965912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_965912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965912 prefixEnd_965912 := by exact prefixLift 965912
  have htrace : WordTrace (prefixWord ++ tailWord_965912) baseStart_965912 baseEnd_965912 := by
    simpa [prefixWord, tailWord_965912, baseEnd_965912] using wordTrace_append hprefix tailTrace_965912
  have hstable : (prefixWord ++ tailWord_965912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965912).length < 2 ^ (prefixWord ++ tailWord_965912).sum := by decide
  have hdescent : baseEnd_965912 < baseStart_965912 := by decide
  rcases family_descends (prefixWord ++ tailWord_965912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965922 : List Nat := [3, 3, 1, 1, 5, 1, 2, 4]
def baseStart_965922 : Nat := 118140960795 + 965922 * 2 ^ 59
def prefixEnd_965922 : Nat := 4983230072969 + 3 ^ 40 * 965922 * 2
def baseEnd_965922 : Nat := 146957706889562980572685

theorem tailTrace_965922 : CollatzResearch.WordTrace tailWord_965922 prefixEnd_965922 146957706889562980572685 := by
  unfold tailWord_965922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8807517401659258797267005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23486713071091356792712013 8807517401659258797267005)
  ·
    refine ⟨3302819025622222048975127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8807517401659258797267005 3302819025622222048975127)
    ·
      refine ⟨4954228538433333073462691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302819025622222048975127 4954228538433333073462691)
      ·
        refine ⟨7431342807649999610194037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4954228538433333073462691 7431342807649999610194037)
        ·
          refine ⟨696688388217187463455691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7431342807649999610194037 696688388217187463455691)
          ·
            refine ⟨1045032582325781195183537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696688388217187463455691 1045032582325781195183537)
            ·
              refine ⟨783774436744335896387653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045032582325781195183537 783774436744335896387653)
              ·
                refine ⟨146957706889562980572685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783774436744335896387653 146957706889562980572685)
                ·
                  rfl

theorem cell20_965922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_965922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965922 prefixEnd_965922 := by exact prefixLift 965922
  have htrace : WordTrace (prefixWord ++ tailWord_965922) baseStart_965922 baseEnd_965922 := by
    simpa [prefixWord, tailWord_965922, baseEnd_965922] using wordTrace_append hprefix tailTrace_965922
  have hstable : (prefixWord ++ tailWord_965922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965922).length < 2 ^ (prefixWord ++ tailWord_965922).sum := by decide
  have hdescent : baseEnd_965922 < baseStart_965922 := by decide
  rcases family_descends (prefixWord ++ tailWord_965922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965953 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 2]
def baseStart_965953 : Nat := 118140960795 + 965953 * 2 ^ 59
def prefixEnd_965953 : Nat := 4983230072969 + 3 ^ 40 * 965953 * 2
def baseEnd_965953 : Nat := 440887269913390611684595

theorem tailTrace_965953 : CollatzResearch.WordTrace tailWord_965953 prefixEnd_965953 440887269913390611684595 := by
  unfold tailWord_965953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35231200269524727483446513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23487466846349818322297675 35231200269524727483446513)
  ·
    refine ⟨26423400202143545612584885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35231200269524727483446513 26423400202143545612584885)
    ·
      refine ⟨2477193768950957401179833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26423400202143545612584885 2477193768950957401179833)
      ·
        refine ⟨1857895326713218050884875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477193768950957401179833 1857895326713218050884875)
        ·
          refine ⟨2786842990069827076327313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857895326713218050884875 2786842990069827076327313)
          ·
            refine ⟨2090132242552370307245485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2786842990069827076327313 2090132242552370307245485)
            ·
              refine ⟨783799590957138865217057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2090132242552370307245485 783799590957138865217057)
              ·
                refine ⟨587849693217854148912793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783799590957138865217057 587849693217854148912793)
                ·
                  refine ⟨440887269913390611684595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587849693217854148912793 440887269913390611684595)
                  ·
                    rfl

theorem cell20_965953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_965953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_965953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_965953 prefixEnd_965953 := by exact prefixLift 965953
  have htrace : WordTrace (prefixWord ++ tailWord_965953) baseStart_965953 baseEnd_965953 := by
    simpa [prefixWord, tailWord_965953, baseEnd_965953] using wordTrace_append hprefix tailTrace_965953
  have hstable : (prefixWord ++ tailWord_965953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965953).length < 2 ^ (prefixWord ++ tailWord_965953).sum := by decide
  have hdescent : baseEnd_965953 < baseStart_965953 := by decide
  rcases family_descends (prefixWord ++ tailWord_965953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966023 : List Nat := [1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_966023 : Nat := 118140960795 + 966023 * 2 ^ 59
def prefixEnd_966023 : Nat := 4983230072969 + 3 ^ 40 * 966023 * 2
def baseEnd_966023 : Nat := 146973073273593826450325

theorem tailTrace_966023 : CollatzResearch.WordTrace tailWord_966023 prefixEnd_966023 146973073273593826450325 := by
  unfold tailWord_966023
  simp only [CollatzResearch.WordTrace]
  refine ⟨35233753379271129438494723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23489168919514086292329815 35233753379271129438494723)
  ·
    refine ⟨52850630068906694157742085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35233753379271129438494723 52850630068906694157742085)
    ·
      refine ⟨9909493137920005154576641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52850630068906694157742085 9909493137920005154576641)
      ·
        refine ⟨7432119853440003865932481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9909493137920005154576641 7432119853440003865932481)
        ·
          refine ⟨5574089890080002899449361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7432119853440003865932481 5574089890080002899449361)
          ·
            refine ⟨4180567417560002174587021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5574089890080002899449361 4180567417560002174587021)
            ·
              refine ⟨1567712781585000815470133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4180567417560002174587021 1567712781585000815470133)
              ·
                refine ⟨146973073273593826450325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1567712781585000815470133 146973073273593826450325)
                ·
                  rfl

theorem cell20_966023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_966023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966023 prefixEnd_966023 := by exact prefixLift 966023
  have htrace : WordTrace (prefixWord ++ tailWord_966023) baseStart_966023 baseEnd_966023 := by
    simpa [prefixWord, tailWord_966023, baseEnd_966023] using wordTrace_append hprefix tailTrace_966023
  have hstable : (prefixWord ++ tailWord_966023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966023).length < 2 ^ (prefixWord ++ tailWord_966023).sum := by decide
  have hdescent : baseEnd_966023 < baseStart_966023 := by decide
  rcases family_descends (prefixWord ++ tailWord_966023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966037 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_966037 : Nat := 118140960795 + 966037 * 2 ^ 59
def prefixEnd_966037 : Nat := 4983230072969 + 3 ^ 40 * 966037 * 2
def baseEnd_966037 : Nat := 440925609802259652884251

theorem tailTrace_966037 : CollatzResearch.WordTrace tailWord_966037 prefixEnd_966037 440925609802259652884251 := by
  unfold tailWord_966037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35234264001220409829504365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23489509334146939886336243 35234264001220409829504365)
  ·
    refine ⟨13212849000457653686064137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35234264001220409829504365 13212849000457653686064137)
    ·
      refine ⟨9909636750343240264548103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13212849000457653686064137 9909636750343240264548103)
      ·
        refine ⟨14864455125514860396822155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9909636750343240264548103 14864455125514860396822155)
        ·
          refine ⟨22296682688272290595233233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14864455125514860396822155 22296682688272290595233233)
          ·
            refine ⟨16722512016204217946424925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22296682688272290595233233 16722512016204217946424925)
            ·
              refine ⟨6270942006076581729909347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16722512016204217946424925 6270942006076581729909347)
              ·
                refine ⟨9406413009114872594864021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270942006076581729909347 9406413009114872594864021)
                ·
                  refine ⟨440925609802259652884251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9406413009114872594864021 440925609802259652884251)
                  ·
                    rfl

theorem cell20_966037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_966037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966037 prefixEnd_966037 := by exact prefixLift 966037
  have htrace : WordTrace (prefixWord ++ tailWord_966037) baseStart_966037 baseEnd_966037 := by
    simpa [prefixWord, tailWord_966037, baseEnd_966037] using wordTrace_append hprefix tailTrace_966037
  have hstable : (prefixWord ++ tailWord_966037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966037).length < 2 ^ (prefixWord ++ tailWord_966037).sum := by decide
  have hdescent : baseEnd_966037 < baseStart_966037 := by decide
  rcases family_descends (prefixWord ++ tailWord_966037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966050 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_966050 : Nat := 118140960795 + 966050 * 2 ^ 59
def prefixEnd_966050 : Nat := 4983230072969 + 3 ^ 40 * 966050 * 2
def baseEnd_966050 : Nat := 440931543356489385450865

theorem tailTrace_966050 : CollatzResearch.WordTrace tailWord_966050 prefixEnd_966050 440931543356489385450865 := by
  unfold tailWord_966050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808684537543328262431901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23489825433448875366485069 8808684537543328262431901)
  ·
    refine ⟨3303256701578748098411963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8808684537543328262431901 3303256701578748098411963)
    ·
      refine ⟨4954885052368122147617945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303256701578748098411963 4954885052368122147617945)
      ·
        refine ⟨3716163789276091610713459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4954885052368122147617945 3716163789276091610713459)
        ·
          refine ⟨5574245683914137416070189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716163789276091610713459 5574245683914137416070189)
          ·
            refine ⟨2090342131467801531026321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5574245683914137416070189 2090342131467801531026321)
            ·
              refine ⟨1567756598600851148269741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090342131467801531026321 1567756598600851148269741)
              ·
                refine ⟨587908724475319180601153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567756598600851148269741 587908724475319180601153)
                ·
                  refine ⟨440931543356489385450865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587908724475319180601153 440931543356489385450865)
                  ·
                    rfl

theorem cell20_966050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_966050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966050 prefixEnd_966050 := by exact prefixLift 966050
  have htrace : WordTrace (prefixWord ++ tailWord_966050) baseStart_966050 baseEnd_966050 := by
    simpa [prefixWord, tailWord_966050, baseEnd_966050] using wordTrace_append hprefix tailTrace_966050
  have hstable : (prefixWord ++ tailWord_966050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966050).length < 2 ^ (prefixWord ++ tailWord_966050).sum := by decide
  have hdescent : baseEnd_966050 < baseStart_966050 := by decide
  rcases family_descends (prefixWord ++ tailWord_966050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966092 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_966092 : Nat := 118140960795 + 966092 * 2 ^ 59
def prefixEnd_966092 : Nat := 4983230072969 + 3 ^ 40 * 966092 * 2
def baseEnd_966092 : Nat := 440950713300923906050693

theorem tailTrace_966092 : CollatzResearch.WordTrace tailWord_966092 prefixEnd_966092 440950713300923906050693 := by
  unfold tailWord_966092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618135008010577111378265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23490846677347436148504353 17618135008010577111378265)
  ·
    refine ⟨13213601256007932833533699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17618135008010577111378265 13213601256007932833533699)
    ·
      refine ⟨19820401884011899250300549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13213601256007932833533699 19820401884011899250300549)
      ·
        refine ⟨3716325353252231109431353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19820401884011899250300549 3716325353252231109431353)
        ·
          refine ⟨2787244014939173332073515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716325353252231109431353 2787244014939173332073515)
          ·
            refine ⟨4180866022408759998110273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787244014939173332073515 4180866022408759998110273)
            ·
              refine ⟨3135649516806569998582705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180866022408759998110273 3135649516806569998582705)
              ·
                refine ⟨2351737137604927498937029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135649516806569998582705 2351737137604927498937029)
                ·
                  refine ⟨440950713300923906050693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351737137604927498937029 440950713300923906050693)
                  ·
                    rfl

theorem cell20_966092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_966092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966092 prefixEnd_966092 := by exact prefixLift 966092
  have htrace : WordTrace (prefixWord ++ tailWord_966092) baseStart_966092 baseEnd_966092 := by
    simpa [prefixWord, tailWord_966092, baseEnd_966092] using wordTrace_append hprefix tailTrace_966092
  have hstable : (prefixWord ++ tailWord_966092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966092).length < 2 ^ (prefixWord ++ tailWord_966092).sum := by decide
  have hdescent : baseEnd_966092 < baseStart_966092 := by decide
  rcases family_descends (prefixWord ++ tailWord_966092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966106 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_966106 : Nat := 118140960795 + 966106 * 2 ^ 59
def prefixEnd_966106 : Nat := 4983230072969 + 3 ^ 40 * 966106 * 2
def baseEnd_966106 : Nat := 440957103282402079583969

theorem tailTrace_966106 : CollatzResearch.WordTrace tailWord_966106 prefixEnd_966106 440957103282402079583969 := by
  unfold tailWord_966106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809195159492608653441543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23491187091980289742510781 8809195159492608653441543)
  ·
    refine ⟨13213792739238912980162315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8809195159492608653441543 13213792739238912980162315)
    ·
      refine ⟨19820689108858369470243473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13213792739238912980162315 19820689108858369470243473)
      ·
        refine ⟨14865516831643777102682605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19820689108858369470243473 14865516831643777102682605)
        ·
          refine ⟨5574568811866416413505977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14865516831643777102682605 5574568811866416413505977)
          ·
            refine ⟨4180926608899812310129483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5574568811866416413505977 4180926608899812310129483)
            ·
              refine ⟨6271389913349718465194225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180926608899812310129483 6271389913349718465194225)
              ·
                refine ⟨4703542435012288848895669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6271389913349718465194225 4703542435012288848895669)
                ·
                  refine ⟨440957103282402079583969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4703542435012288848895669 440957103282402079583969)
                  ·
                    rfl

theorem cell20_966106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_966106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966106 prefixEnd_966106 := by exact prefixLift 966106
  have htrace : WordTrace (prefixWord ++ tailWord_966106) baseStart_966106 baseEnd_966106 := by
    simpa [prefixWord, tailWord_966106, baseEnd_966106] using wordTrace_append hprefix tailTrace_966106
  have hstable : (prefixWord ++ tailWord_966106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966106).length < 2 ^ (prefixWord ++ tailWord_966106).sum := by decide
  have hdescent : baseEnd_966106 < baseStart_966106 := by decide
  rcases family_descends (prefixWord ++ tailWord_966106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966126 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_966126 : Nat := 118140960795 + 966126 * 2 ^ 59
def prefixEnd_966126 : Nat := 4983230072969 + 3 ^ 40 * 966126 * 2
def baseEnd_966126 : Nat := 440966231827370898917221

theorem tailTrace_966126 : CollatzResearch.WordTrace tailWord_966126 prefixEnd_966126 440966231827370898917221 := by
  unfold tailWord_966126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404688762237247253686779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23491673398598652019662821 4404688762237247253686779)
  ·
    refine ⟨6607033143355870880530169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4404688762237247253686779 6607033143355870880530169)
    ·
      refine ⟨4955274857516903160397627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6607033143355870880530169 4955274857516903160397627)
      ·
        refine ⟨7432912286275354740596441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955274857516903160397627 7432912286275354740596441)
        ·
          refine ⟨5574684214706516055447331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7432912286275354740596441 5574684214706516055447331)
          ·
            refine ⟨8362026322059774083170997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5574684214706516055447331 8362026322059774083170997)
            ·
              refine ⟨783939967693103820297281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8362026322059774083170997 783939967693103820297281)
              ·
                refine ⟨587954975769827865222961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783939967693103820297281 587954975769827865222961)
                ·
                  refine ⟨440966231827370898917221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587954975769827865222961 440966231827370898917221)
                  ·
                    rfl

theorem cell20_966126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_966126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966126 prefixEnd_966126 := by exact prefixLift 966126
  have htrace : WordTrace (prefixWord ++ tailWord_966126) baseStart_966126 baseEnd_966126 := by
    simpa [prefixWord, tailWord_966126, baseEnd_966126] using wordTrace_append hprefix tailTrace_966126
  have hstable : (prefixWord ++ tailWord_966126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966126).length < 2 ^ (prefixWord ++ tailWord_966126).sum := by decide
  have hdescent : baseEnd_966126 < baseStart_966126 := by decide
  rcases family_descends (prefixWord ++ tailWord_966126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966213 : List Nat := [1, 3, 1, 1, 1, 4, 5, 4]
def baseStart_966213 : Nat := 118140960795 + 966213 * 2 ^ 59
def prefixEnd_966213 : Nat := 4983230072969 + 3 ^ 40 * 966213 * 2
def baseEnd_966213 : Nat := 147001980332661754338955

theorem tailTrace_966213 : CollatzResearch.WordTrace tailWord_966213 prefixEnd_966213 147001980332661754338955 := by
  unfold tailWord_966213
  simp only [CollatzResearch.WordTrace]
  refine ⟨35240683248582791887911293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23493788832388527925274195 35240683248582791887911293)
  ·
    refine ⟨13215256218218546957966735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35240683248582791887911293 13215256218218546957966735)
    ·
      refine ⟨19822884327327820436950103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13215256218218546957966735 19822884327327820436950103)
      ·
        refine ⟨29734326490991730655425155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19822884327327820436950103 29734326490991730655425155)
        ·
          refine ⟨44601489736487595983137733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29734326490991730655425155 44601489736487595983137733)
          ·
            refine ⟨8362779325591424246838325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44601489736487595983137733 8362779325591424246838325)
            ·
              refine ⟨784010561774196023141093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8362779325591424246838325 784010561774196023141093)
              ·
                refine ⟨147001980332661754338955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784010561774196023141093 147001980332661754338955)
                ·
                  rfl

theorem cell20_966213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_966213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966213 prefixEnd_966213 := by exact prefixLift 966213
  have htrace : WordTrace (prefixWord ++ tailWord_966213) baseStart_966213 baseEnd_966213 := by
    simpa [prefixWord, tailWord_966213, baseEnd_966213] using wordTrace_append hprefix tailTrace_966213
  have hstable : (prefixWord ++ tailWord_966213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966213).length < 2 ^ (prefixWord ++ tailWord_966213).sum := by decide
  have hdescent : baseEnd_966213 < baseStart_966213 := by decide
  rcases family_descends (prefixWord ++ tailWord_966213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966244 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_966244 : Nat := 118140960795 + 966244 * 2 ^ 59
def prefixEnd_966244 : Nat := 4983230072969 + 3 ^ 40 * 966244 * 2
def baseEnd_966244 : Nat := 441020090242686932983405

theorem tailTrace_966244 : CollatzResearch.WordTrace tailWord_966244 prefixEnd_966244 441020090242686932983405 := by
  unfold tailWord_966244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17620906955735242091144893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23494542607646989454859857 17620906955735242091144893)
  ·
    refine ⟨6607840108400715784179335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17620906955735242091144893 6607840108400715784179335)
    ·
      refine ⟨9911760162601073676269003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607840108400715784179335 9911760162601073676269003)
      ·
        refine ⟨14867640243901610514403505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9911760162601073676269003 14867640243901610514403505)
        ·
          refine ⟨11150730182926207885802629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14867640243901610514403505 11150730182926207885802629)
          ·
            refine ⟨2090761909298663978587993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11150730182926207885802629 2090761909298663978587993)
            ·
              refine ⟨1568071431973997983940995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090761909298663978587993 1568071431973997983940995)
              ·
                refine ⟨2352107147960996975911493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568071431973997983940995 2352107147960996975911493)
                ·
                  refine ⟨441020090242686932983405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352107147960996975911493 441020090242686932983405)
                  ·
                    rfl

theorem cell20_966244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_966244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966244 prefixEnd_966244 := by exact prefixLift 966244
  have htrace : WordTrace (prefixWord ++ tailWord_966244) baseStart_966244 baseEnd_966244 := by
    simpa [prefixWord, tailWord_966244, baseEnd_966244] using wordTrace_append hprefix tailTrace_966244
  have hstable : (prefixWord ++ tailWord_966244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966244).length < 2 ^ (prefixWord ++ tailWord_966244).sum := by decide
  have hdescent : baseEnd_966244 < baseStart_966244 := by decide
  rcases family_descends (prefixWord ++ tailWord_966244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966265 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_966265 : Nat := 118140960795 + 966265 * 2 ^ 59
def prefixEnd_966265 : Nat := 4983230072969 + 3 ^ 40 * 966265 * 2
def baseEnd_966265 : Nat := 441029675214904193283319

theorem tailTrace_966265 : CollatzResearch.WordTrace tailWord_966265 prefixEnd_966265 441029675214904193283319 := by
  unfold tailWord_966265
  simp only [CollatzResearch.WordTrace]
  refine ⟨35242579844394404768804249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23495053229596269845869499 35242579844394404768804249)
  ·
    refine ⟨26431934883295803576603187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35242579844394404768804249 26431934883295803576603187)
    ·
      refine ⟨39647902324943705364904781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26431934883295803576603187 39647902324943705364904781)
      ·
        refine ⟨14867963371853889511839293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39647902324943705364904781 14867963371853889511839293)
        ·
          refine ⟨5575486264445208566939735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14867963371853889511839293 5575486264445208566939735)
          ·
            refine ⟨8363229396667812850409603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575486264445208566939735 8363229396667812850409603)
            ·
              refine ⟨12544844095001719275614405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363229396667812850409603 12544844095001719275614405)
              ·
                refine ⟨2352158267812822364177701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12544844095001719275614405 2352158267812822364177701)
                ·
                  refine ⟨441029675214904193283319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352158267812822364177701 441029675214904193283319)
                  ·
                    rfl

theorem cell20_966265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_966265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966265 prefixEnd_966265 := by exact prefixLift 966265
  have htrace : WordTrace (prefixWord ++ tailWord_966265) baseStart_966265 baseEnd_966265 := by
    simpa [prefixWord, tailWord_966265, baseEnd_966265] using wordTrace_append hprefix tailTrace_966265
  have hstable : (prefixWord ++ tailWord_966265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966265).length < 2 ^ (prefixWord ++ tailWord_966265).sum := by decide
  have hdescent : baseEnd_966265 < baseStart_966265 := by decide
  rcases family_descends (prefixWord ++ tailWord_966265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966272 : List Nat := [2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_966272 : Nat := 118140960795 + 966272 * 2 ^ 59
def prefixEnd_966272 : Nat := 4983230072969 + 3 ^ 40 * 966272 * 2
def baseEnd_966272 : Nat := 147010956735214426683319

theorem tailTrace_966272 : CollatzResearch.WordTrace tailWord_966272 prefixEnd_966272 147010956735214426683319 := by
  unfold tailWord_966272
  simp only [CollatzResearch.WordTrace]
  refine ⟨17621417577684522482154535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23495223436912696642872713 17621417577684522482154535)
  ·
    refine ⟨26432126366526783723231803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17621417577684522482154535 26432126366526783723231803)
    ·
      refine ⟨39648189549790175584847705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26432126366526783723231803 39648189549790175584847705)
      ·
        refine ⟨29736142162342631688635779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39648189549790175584847705 29736142162342631688635779)
        ·
          refine ⟨44604213243513947532953669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29736142162342631688635779 44604213243513947532953669)
          ·
            refine ⟨8363289983158865162428813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44604213243513947532953669 8363289983158865162428813)
            ·
              refine ⟨3136233743684574435910805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8363289983158865162428813 3136233743684574435910805)
              ·
                refine ⟨147010956735214426683319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3136233743684574435910805 147010956735214426683319)
                ·
                  rfl

theorem cell20_966272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_966272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966272 prefixEnd_966272 := by exact prefixLift 966272
  have htrace : WordTrace (prefixWord ++ tailWord_966272) baseStart_966272 baseEnd_966272 := by
    simpa [prefixWord, tailWord_966272, baseEnd_966272] using wordTrace_append hprefix tailTrace_966272
  have hstable : (prefixWord ++ tailWord_966272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966272).length < 2 ^ (prefixWord ++ tailWord_966272).sum := by decide
  have hdescent : baseEnd_966272 < baseStart_966272 := by decide
  rcases family_descends (prefixWord ++ tailWord_966272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966296 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_966296 : Nat := 118140960795 + 966296 * 2 ^ 59
def prefixEnd_966296 : Nat := 4983230072969 + 3 ^ 40 * 966296 * 2
def baseEnd_966296 : Nat := 441043824459605863249859

theorem tailTrace_966296 : CollatzResearch.WordTrace tailWord_966296 prefixEnd_966296 441043824459605863249859 := by
  unfold tailWord_966296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17621855253641048531591371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23495807004854731375455161 17621855253641048531591371)
  ·
    refine ⟨26432782880461572797387057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17621855253641048531591371 26432782880461572797387057)
    ·
      refine ⟨19824587160346179598040293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26432782880461572797387057 19824587160346179598040293)
      ·
        refine ⟨3717110092564908674632555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19824587160346179598040293 3717110092564908674632555)
        ·
          refine ⟨5575665138847363011948833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3717110092564908674632555 5575665138847363011948833)
          ·
            refine ⟨4181748854135522258961625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5575665138847363011948833 4181748854135522258961625)
            ·
              refine ⟨3136311640601641694221219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4181748854135522258961625 3136311640601641694221219)
              ·
                refine ⟨4704467460902462541331829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136311640601641694221219 4704467460902462541331829)
                ·
                  refine ⟨441043824459605863249859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4704467460902462541331829 441043824459605863249859)
                  ·
                    rfl

theorem cell20_966296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_966296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966296 prefixEnd_966296 := by exact prefixLift 966296
  have htrace : WordTrace (prefixWord ++ tailWord_966296) baseStart_966296 baseEnd_966296 := by
    simpa [prefixWord, tailWord_966296, baseEnd_966296] using wordTrace_append hprefix tailTrace_966296
  have hstable : (prefixWord ++ tailWord_966296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966296).length < 2 ^ (prefixWord ++ tailWord_966296).sum := by decide
  have hdescent : baseEnd_966296 < baseStart_966296 := by decide
  rcases family_descends (prefixWord ++ tailWord_966296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966348 : List Nat := [2, 2, 1, 5, 10]
def baseStart_966348 : Nat := 118140960795 + 966348 * 2 ^ 59
def prefixEnd_966348 : Nat := 4983230072969 + 3 ^ 40 * 966348 * 2
def baseEnd_966348 : Nat := 5445278502179318438473

theorem tailTrace_966348 : CollatzResearch.WordTrace tailWord_966348 prefixEnd_966348 5445278502179318438473 := by
  unfold tailWord_966348
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622803551546854972037849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23497071402062473296050465 17622803551546854972037849)
  ·
    refine ⟨13217102663660141229028387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17622803551546854972037849 13217102663660141229028387)
    ·
      refine ⟨19825653995490211843542581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13217102663660141229028387 19825653995490211843542581)
      ·
        refine ⟨1858655062077207360332117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19825653995490211843542581 1858655062077207360332117)
        ·
          refine ⟨5445278502179318438473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1858655062077207360332117 5445278502179318438473)
          ·
            rfl

theorem cell20_966348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 10].length) (baseStart_966348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966348 prefixEnd_966348 := by exact prefixLift 966348
  have htrace : WordTrace (prefixWord ++ tailWord_966348) baseStart_966348 baseEnd_966348 := by
    simpa [prefixWord, tailWord_966348, baseEnd_966348] using wordTrace_append hprefix tailTrace_966348
  have hstable : (prefixWord ++ tailWord_966348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966348).length < 2 ^ (prefixWord ++ tailWord_966348).sum := by decide
  have hdescent : baseEnd_966348 < baseStart_966348 := by decide
  rcases family_descends (prefixWord ++ tailWord_966348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966354 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_966354 : Nat := 118140960795 + 966354 * 2 ^ 59
def prefixEnd_966354 : Nat := 4983230072969 + 3 ^ 40 * 966354 * 2
def baseEnd_966354 : Nat := 441070297240015439316289

theorem tailTrace_966354 : CollatzResearch.WordTrace tailWord_966354 prefixEnd_966354 441070297240015439316289 := by
  unfold tailWord_966354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811456485267993242198529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23497217294047981979196077 8811456485267993242198529)
  ·
    refine ⟨6608592363950994931648897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8811456485267993242198529 6608592363950994931648897)
    ·
      refine ⟨4956444272963246198736673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6608592363950994931648897 4956444272963246198736673)
      ·
        refine ⟨3717333204722434649052505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4956444272963246198736673 3717333204722434649052505)
        ·
          refine ⟨2787999903541825986789379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717333204722434649052505 2787999903541825986789379)
          ·
            refine ⟨4181999855312738980184069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787999903541825986789379 4181999855312738980184069)
            ·
              refine ⟨784124972871138558784513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4181999855312738980184069 784124972871138558784513)
              ·
                refine ⟨588093729653353919088385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784124972871138558784513 588093729653353919088385)
                ·
                  refine ⟨441070297240015439316289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588093729653353919088385 441070297240015439316289)
                  ·
                    rfl

theorem cell20_966354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_966354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966354 prefixEnd_966354 := by exact prefixLift 966354
  have htrace : WordTrace (prefixWord ++ tailWord_966354) baseStart_966354 baseEnd_966354 := by
    simpa [prefixWord, tailWord_966354, baseEnd_966354] using wordTrace_append hprefix tailTrace_966354
  have hstable : (prefixWord ++ tailWord_966354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966354).length < 2 ^ (prefixWord ++ tailWord_966354).sum := by decide
  have hdescent : baseEnd_966354 < baseStart_966354 := by decide
  rcases family_descends (prefixWord ++ tailWord_966354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966372 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_966372 : Nat := 118140960795 + 966372 * 2 ^ 59
def prefixEnd_966372 : Nat := 4983230072969 + 3 ^ 40 * 966372 * 2
def baseEnd_966372 : Nat := 441078512930487376716215

theorem tailTrace_966372 : CollatzResearch.WordTrace tailWord_966372 prefixEnd_966372 441078512930487376716215 := by
  unfold tailWord_966372
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623241227503381021474685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23497654970004508028632913 17623241227503381021474685)
  ·
    refine ⟨6608715460313767883053007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17623241227503381021474685 6608715460313767883053007)
    ·
      refine ⟨9913073190470651824579511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6608715460313767883053007 9913073190470651824579511)
      ·
        refine ⟨14869609785705977736869267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9913073190470651824579511 14869609785705977736869267)
        ·
          refine ⟨22304414678558966605303901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14869609785705977736869267 22304414678558966605303901)
          ·
            refine ⟨8364155504459612476988963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22304414678558966605303901 8364155504459612476988963)
            ·
              refine ⟨12546233256689418715483445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364155504459612476988963 12546233256689418715483445)
              ·
                refine ⟨1176209367814633004576573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12546233256689418715483445 1176209367814633004576573)
                ·
                  refine ⟨441078512930487376716215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176209367814633004576573 441078512930487376716215)
                  ·
                    rfl

theorem cell20_966372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_966372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966372 prefixEnd_966372 := by exact prefixLift 966372
  have htrace : WordTrace (prefixWord ++ tailWord_966372) baseStart_966372 baseEnd_966372 := by
    simpa [prefixWord, tailWord_966372, baseEnd_966372] using wordTrace_append hprefix tailTrace_966372
  have hstable : (prefixWord ++ tailWord_966372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966372).length < 2 ^ (prefixWord ++ tailWord_966372).sum := by decide
  have hdescent : baseEnd_966372 < baseStart_966372 := by decide
  rcases family_descends (prefixWord ++ tailWord_966372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966375 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 4]
def baseStart_966375 : Nat := 118140960795 + 966375 * 2 ^ 59
def prefixEnd_966375 : Nat := 4983230072969 + 3 ^ 40 * 966375 * 2
def baseEnd_966375 : Nat := 441079882212232699616203

theorem tailTrace_966375 : CollatzResearch.WordTrace tailWord_966375 prefixEnd_966375 441079882212232699616203 := by
  unfold tailWord_966375
  simp only [CollatzResearch.WordTrace]
  refine ⟨35246591873995893555308579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23497727915997262370205719 35246591873995893555308579)
  ·
    refine ⟨52869887810993840332962869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35246591873995893555308579 52869887810993840332962869)
    ·
      refine ⟨4956551982280672531215269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52869887810993840332962869 4956551982280672531215269)
      ·
        refine ⟨929353496677626099602863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4956551982280672531215269 929353496677626099602863)
        ·
          refine ⟨1394030245016439149404295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929353496677626099602863 1394030245016439149404295)
          ·
            refine ⟨2091045367524658724106443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394030245016439149404295 2091045367524658724106443)
            ·
              refine ⟨3136568051286988086159665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091045367524658724106443 3136568051286988086159665)
              ·
                refine ⟨2352426038465241064619749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3136568051286988086159665 2352426038465241064619749)
                ·
                  refine ⟨441079882212232699616203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352426038465241064619749 441079882212232699616203)
                  ·
                    rfl

theorem cell20_966375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_966375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966375 prefixEnd_966375 := by exact prefixLift 966375
  have htrace : WordTrace (prefixWord ++ tailWord_966375) baseStart_966375 baseEnd_966375 := by
    simpa [prefixWord, tailWord_966375, baseEnd_966375] using wordTrace_append hprefix tailTrace_966375
  have hstable : (prefixWord ++ tailWord_966375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966375).length < 2 ^ (prefixWord ++ tailWord_966375).sum := by decide
  have hdescent : baseEnd_966375 < baseStart_966375 := by decide
  rcases family_descends (prefixWord ++ tailWord_966375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966410 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_966410 : Nat := 118140960795 + 966410 * 2 ^ 59
def prefixEnd_966410 : Nat := 4983230072969 + 3 ^ 40 * 966410 * 2
def baseEnd_966410 : Nat := 441095857165928133449393

theorem tailTrace_966410 : CollatzResearch.WordTrace tailWord_966410 prefixEnd_966410 441095857165928133449393 := by
  unfold tailWord_966410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811967107217273633208171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23498578952579396355221789 8811967107217273633208171)
  ·
    refine ⟨13217950660825910449812257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8811967107217273633208171 13217950660825910449812257)
    ·
      refine ⟨9913462995619432837359193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13217950660825910449812257 9913462995619432837359193)
      ·
        refine ⟨7435097246714574628019395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9913462995619432837359193 7435097246714574628019395)
        ·
          refine ⟨11152645870071861942029093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435097246714574628019395 11152645870071861942029093)
          ·
            refine ⟨2091121100638474114130455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11152645870071861942029093 2091121100638474114130455)
            ·
              refine ⟨3136681650957711171195683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091121100638474114130455 3136681650957711171195683)
              ·
                refine ⟨4705022476436566756793525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136681650957711171195683 4705022476436566756793525)
                ·
                  refine ⟨441095857165928133449393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4705022476436566756793525 441095857165928133449393)
                  ·
                    rfl

theorem cell20_966410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_966410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966410 prefixEnd_966410 := by exact prefixLift 966410
  have htrace : WordTrace (prefixWord ++ tailWord_966410) baseStart_966410 baseEnd_966410 := by
    simpa [prefixWord, tailWord_966410, baseEnd_966410] using wordTrace_append hprefix tailTrace_966410
  have hstable : (prefixWord ++ tailWord_966410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966410).length < 2 ^ (prefixWord ++ tailWord_966410).sum := by decide
  have hdescent : baseEnd_966410 < baseStart_966410 := by decide
  rcases family_descends (prefixWord ++ tailWord_966410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966469 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_966469 : Nat := 118140960795 + 966469 * 2 ^ 59
def prefixEnd_966469 : Nat := 4983230072969 + 3 ^ 40 * 966469 * 2
def baseEnd_966469 : Nat := 441122786373586150482485

theorem tailTrace_966469 : CollatzResearch.WordTrace tailWord_966469 prefixEnd_966469 441122786373586150482485 := by
  unfold tailWord_966469
  simp only [CollatzResearch.WordTrace]
  refine ⟨35250020335655347609230461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23500013557103565072820307 35250020335655347609230461)
  ·
    refine ⟨13218757625870755353461423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35250020335655347609230461 13218757625870755353461423)
    ·
      refine ⟨19828136438806133030192135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13218757625870755353461423 19828136438806133030192135)
      ·
        refine ⟨29742204658209199545288203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19828136438806133030192135 29742204658209199545288203)
        ·
          refine ⟨44613306987313799317932305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29742204658209199545288203 44613306987313799317932305)
          ·
            refine ⟨33459980240485349488449229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44613306987313799317932305 33459980240485349488449229)
            ·
              refine ⟨12547492590182006058168461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33459980240485349488449229 12547492590182006058168461)
              ·
                refine ⟨4705309721318252271813173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12547492590182006058168461 4705309721318252271813173)
                ·
                  refine ⟨441122786373586150482485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4705309721318252271813173 441122786373586150482485)
                  ·
                    rfl

theorem cell20_966469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_966469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966469 prefixEnd_966469 := by exact prefixLift 966469
  have htrace : WordTrace (prefixWord ++ tailWord_966469) baseStart_966469 baseEnd_966469 := by
    simpa [prefixWord, tailWord_966469, baseEnd_966469] using wordTrace_append hprefix tailTrace_966469
  have hstable : (prefixWord ++ tailWord_966469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966469).length < 2 ^ (prefixWord ++ tailWord_966469).sum := by decide
  have hdescent : baseEnd_966469 < baseStart_966469 := by decide
  rcases family_descends (prefixWord ++ tailWord_966469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966472 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_966472 : Nat := 118140960795 + 966472 * 2 ^ 59
def prefixEnd_966472 : Nat := 4983230072969 + 3 ^ 40 * 966472 * 2
def baseEnd_966472 : Nat := 441124155655331473382473

theorem tailTrace_966472 : CollatzResearch.WordTrace tailWord_966472 prefixEnd_966472 441124155655331473382473 := by
  unfold tailWord_966472
  simp only [CollatzResearch.WordTrace]
  refine ⟨17625064877322239560794835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23500086503096319414393113 17625064877322239560794835)
  ·
    refine ⟨26437597315983359341192253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17625064877322239560794835 26437597315983359341192253)
    ·
      refine ⟨9914098993493759752947095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26437597315983359341192253 9914098993493759752947095)
      ·
        refine ⟨14871148490240639629420643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914098993493759752947095 14871148490240639629420643)
        ·
          refine ⟨22306722735360959444130965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14871148490240639629420643 22306722735360959444130965)
          ·
            refine ⟨1045627628220044973943639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22306722735360959444130965 1045627628220044973943639)
            ·
              refine ⟨1568441442330067460915459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045627628220044973943639 1568441442330067460915459)
              ·
                refine ⟨2352662163495101191373189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568441442330067460915459 2352662163495101191373189)
                ·
                  refine ⟨441124155655331473382473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352662163495101191373189 441124155655331473382473)
                  ·
                    rfl

theorem cell20_966472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_966472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966472 prefixEnd_966472 := by exact prefixLift 966472
  have htrace : WordTrace (prefixWord ++ tailWord_966472) baseStart_966472 baseEnd_966472 := by
    simpa [prefixWord, tailWord_966472, baseEnd_966472] using wordTrace_append hprefix tailTrace_966472
  have hstable : (prefixWord ++ tailWord_966472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966472).length < 2 ^ (prefixWord ++ tailWord_966472).sum := by decide
  have hdescent : baseEnd_966472 < baseStart_966472 := by decide
  rcases family_descends (prefixWord ++ tailWord_966472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966482 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_966482 : Nat := 118140960795 + 966482 * 2 ^ 59
def prefixEnd_966482 : Nat := 4983230072969 + 3 ^ 40 * 966482 * 2
def baseEnd_966482 : Nat := 441128719927815883049099

theorem tailTrace_966482 : CollatzResearch.WordTrace tailWord_966482 prefixEnd_966482 441128719927815883049099 := by
  unfold tailWord_966482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8812623621152062707363425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23500329656405500552969133 8812623621152062707363425)
  ·
    refine ⟨6609467715864047030522569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8812623621152062707363425 6609467715864047030522569)
    ·
      refine ⟨4957100786898035272891927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6609467715864047030522569 4957100786898035272891927)
      ·
        refine ⟨7435651180347052909337891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957100786898035272891927 7435651180347052909337891)
        ·
          refine ⟨11153476770520579364006837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435651180347052909337891 11153476770520579364006837)
          ·
            refine ⟨1045638447236304315375641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11153476770520579364006837 1045638447236304315375641)
            ·
              refine ⟨784228835427228236531731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045638447236304315375641 784228835427228236531731)
              ·
                refine ⟨1176343253140842354797597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784228835427228236531731 1176343253140842354797597)
                ·
                  refine ⟨441128719927815883049099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176343253140842354797597 441128719927815883049099)
                  ·
                    rfl

theorem cell20_966482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_966482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966482 prefixEnd_966482 := by exact prefixLift 966482
  have htrace : WordTrace (prefixWord ++ tailWord_966482) baseStart_966482 baseEnd_966482 := by
    simpa [prefixWord, tailWord_966482, baseEnd_966482] using wordTrace_append hprefix tailTrace_966482
  have hstable : (prefixWord ++ tailWord_966482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966482).length < 2 ^ (prefixWord ++ tailWord_966482).sum := by decide
  have hdescent : baseEnd_966482 < baseStart_966482 := by decide
  rcases family_descends (prefixWord ++ tailWord_966482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966548 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_966548 : Nat := 118140960795 + 966548 * 2 ^ 59
def prefixEnd_966548 : Nat := 4983230072969 + 3 ^ 40 * 966548 * 2
def baseEnd_966548 : Nat := 441158844126212986848829

theorem tailTrace_966548 : CollatzResearch.WordTrace tailWord_966548 prefixEnd_966548 441158844126212986848829 := by
  unfold tailWord_966548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626450851184572050678149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23501934468246096067570865 17626450851184572050678149)
  ·
    refine ⟨3304959534597107259502153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17626450851184572050678149 3304959534597107259502153)
    ·
      refine ⟨2478719650947830444626615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3304959534597107259502153 2478719650947830444626615)
      ·
        refine ⟨3718079476421745666939923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478719650947830444626615 3718079476421745666939923)
        ·
          refine ⟨5577119214632618500409885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718079476421745666939923 5577119214632618500409885)
          ·
            refine ⟨2091419705487231937653707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5577119214632618500409885 2091419705487231937653707)
            ·
              refine ⟨3137129558230847906480561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091419705487231937653707 3137129558230847906480561)
              ·
                refine ⟨2352847168673135929860421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137129558230847906480561 2352847168673135929860421)
                ·
                  refine ⟨441158844126212986848829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352847168673135929860421 441158844126212986848829)
                  ·
                    rfl

theorem cell20_966548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_966548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966548 prefixEnd_966548 := by exact prefixLift 966548
  have htrace : WordTrace (prefixWord ++ tailWord_966548) baseStart_966548 baseEnd_966548 := by
    simpa [prefixWord, tailWord_966548, baseEnd_966548] using wordTrace_append hprefix tailTrace_966548
  have hstable : (prefixWord ++ tailWord_966548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966548).length < 2 ^ (prefixWord ++ tailWord_966548).sum := by decide
  have hdescent : baseEnd_966548 < baseStart_966548 := by decide
  rcases family_descends (prefixWord ++ tailWord_966548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966631 : List Nat := [1, 1, 5, 2, 3, 2, 6]
def baseStart_966631 : Nat := 118140960795 + 966631 * 2 ^ 59
def prefixEnd_966631 : Nat := 4983230072969 + 3 ^ 40 * 966631 * 2
def baseEnd_966631 : Nat := 49021858620870398564647

theorem tailTrace_966631 : CollatzResearch.WordTrace tailWord_966631 prefixEnd_966631 49021858620870398564647 := by
  unfold tailWord_966631
  simp only [CollatzResearch.WordTrace]
  refine ⟨35255928961068449276627747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23503952640712299517751831 35255928961068449276627747)
  ·
    refine ⟨52883893441602673914941621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35255928961068449276627747 52883893441602673914941621)
    ·
      refine ⟨4957865010150250679525777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52883893441602673914941621 4957865010150250679525777)
      ·
        refine ⟨3718398757612688009644333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4957865010150250679525777 3718398757612688009644333)
        ·
          refine ⟨1394399534104758003616625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3718398757612688009644333 1394399534104758003616625)
          ·
            refine ⟨1045799650578568502712469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394399534104758003616625 1045799650578568502712469)
            ·
              refine ⟨49021858620870398564647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1045799650578568502712469 49021858620870398564647)
              ·
                rfl

theorem cell20_966631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_966631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966631 prefixEnd_966631 := by exact prefixLift 966631
  have htrace : WordTrace (prefixWord ++ tailWord_966631) baseStart_966631 baseEnd_966631 := by
    simpa [prefixWord, tailWord_966631, baseEnd_966631] using wordTrace_append hprefix tailTrace_966631
  have hstable : (prefixWord ++ tailWord_966631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966631).length < 2 ^ (prefixWord ++ tailWord_966631).sum := by decide
  have hdescent : baseEnd_966631 < baseStart_966631 := by decide
  rcases family_descends (prefixWord ++ tailWord_966631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966637 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 2]
def baseStart_966637 : Nat := 118140960795 + 966637 * 2 ^ 59
def prefixEnd_966637 : Nat := 4983230072969 + 3 ^ 40 * 966637 * 2
def baseEnd_966637 : Nat := 441199466151324232881799

theorem tailTrace_966637 : CollatzResearch.WordTrace tailWord_966637 prefixEnd_966637 441199466151324232881799 := by
  unfold tailWord_966637
  simp only [CollatzResearch.WordTrace]
  refine ⟨35256147799046712301346165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23504098532697808200897443 35256147799046712301346165)
  ·
    refine ⟨3305263856160629278251203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35256147799046712301346165 3305263856160629278251203)
    ·
      refine ⟨4957895784240943917376805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3305263856160629278251203 4957895784240943917376805)
      ·
        refine ⟨929605459545176984508151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4957895784240943917376805 929605459545176984508151)
        ·
          refine ⟨1394408189317765476762227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929605459545176984508151 1394408189317765476762227)
          ·
            refine ⟨2091612283976648215143341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394408189317765476762227 2091612283976648215143341)
            ·
              refine ⟨784354606491243080678753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2091612283976648215143341 784354606491243080678753)
              ·
                refine ⟨588265954868432310509065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784354606491243080678753 588265954868432310509065)
                ·
                  refine ⟨441199466151324232881799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588265954868432310509065 441199466151324232881799)
                  ·
                    rfl

theorem cell20_966637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_966637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966637 prefixEnd_966637 := by exact prefixLift 966637
  have htrace : WordTrace (prefixWord ++ tailWord_966637) baseStart_966637 baseEnd_966637 := by
    simpa [prefixWord, tailWord_966637, baseEnd_966637] using wordTrace_append hprefix tailTrace_966637
  have hstable : (prefixWord ++ tailWord_966637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966637).length < 2 ^ (prefixWord ++ tailWord_966637).sum := by decide
  have hdescent : baseEnd_966637 < baseStart_966637 := by decide
  rcases family_descends (prefixWord ++ tailWord_966637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966638 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_966638 : Nat := 118140960795 + 966638 * 2 ^ 59
def prefixEnd_966638 : Nat := 4983230072969 + 3 ^ 40 * 966638 * 2
def baseEnd_966638 : Nat := 441199922578572673848461

theorem tailTrace_966638 : CollatzResearch.WordTrace tailWord_966638 prefixEnd_966638 441199922578572673848461 := by
  unfold tailWord_966638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407023034005386184016571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23504122848028726314755045 4407023034005386184016571)
  ·
    refine ⟨6610534551008079276024857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407023034005386184016571 6610534551008079276024857)
    ·
      refine ⟨4957900913256059457018643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6610534551008079276024857 4957900913256059457018643)
      ·
        refine ⟨7436851369884089185527965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957900913256059457018643 7436851369884089185527965)
        ·
          refine ⟨2788819263706533444572987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7436851369884089185527965 2788819263706533444572987)
          ·
            refine ⟨4183228895559800166859481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788819263706533444572987 4183228895559800166859481)
            ·
              refine ⟨3137421671669850125144611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183228895559800166859481 3137421671669850125144611)
              ·
                refine ⟨4706132507504775187716917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137421671669850125144611 4706132507504775187716917)
                ·
                  refine ⟨441199922578572673848461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706132507504775187716917 441199922578572673848461)
                  ·
                    rfl

theorem cell20_966638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_966638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966638 prefixEnd_966638 := by exact prefixLift 966638
  have htrace : WordTrace (prefixWord ++ tailWord_966638) baseStart_966638 baseEnd_966638 := by
    simpa [prefixWord, tailWord_966638, baseEnd_966638] using wordTrace_append hprefix tailTrace_966638
  have hstable : (prefixWord ++ tailWord_966638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966638).length < 2 ^ (prefixWord ++ tailWord_966638).sum := by decide
  have hdescent : baseEnd_966638 < baseStart_966638 := by decide
  rcases family_descends (prefixWord ++ tailWord_966638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966641 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 4]
def baseStart_966641 : Nat := 118140960795 + 966641 * 2 ^ 59
def prefixEnd_966641 : Nat := 4983230072969 + 3 ^ 40 * 966641 * 2
def baseEnd_966641 : Nat := 441201291860317996748449

theorem tailTrace_966641 : CollatzResearch.WordTrace tailWord_966641 prefixEnd_966641 441201291860317996748449 := by
  unfold tailWord_966641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35256293691032220984491777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23504195794021480656327851 35256293691032220984491777)
  ·
    refine ⟨26442220268274165738368833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35256293691032220984491777 26442220268274165738368833)
    ·
      refine ⟨19831665201205624303776625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26442220268274165738368833 19831665201205624303776625)
      ·
        refine ⟨14873748900904218227832469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19831665201205624303776625 14873748900904218227832469)
        ·
          refine ⟨697206979729885229429647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14873748900904218227832469 697206979729885229429647)
          ·
            refine ⟨1045810469594827844144471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697206979729885229429647 1045810469594827844144471)
            ·
              refine ⟨1568715704392241766216707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045810469594827844144471 1568715704392241766216707)
              ·
                refine ⟨2353073556588362649325061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568715704392241766216707 2353073556588362649325061)
                ·
                  refine ⟨441201291860317996748449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353073556588362649325061 441201291860317996748449)
                  ·
                    rfl

theorem cell20_966641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_966641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966641 prefixEnd_966641 := by exact prefixLift 966641
  have htrace : WordTrace (prefixWord ++ tailWord_966641) baseStart_966641 baseEnd_966641 := by
    simpa [prefixWord, tailWord_966641, baseEnd_966641] using wordTrace_append hprefix tailTrace_966641
  have hstable : (prefixWord ++ tailWord_966641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966641).length < 2 ^ (prefixWord ++ tailWord_966641).sum := by decide
  have hdescent : baseEnd_966641 < baseStart_966641 := by decide
  rcases family_descends (prefixWord ++ tailWord_966641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966652 : List Nat := [2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_966652 : Nat := 118140960795 + 966652 * 2 ^ 59
def prefixEnd_966652 : Nat := 4983230072969 + 3 ^ 40 * 966652 * 2
def baseEnd_966652 : Nat := 147068770853350282460579

theorem tailTrace_966652 : CollatzResearch.WordTrace tailWord_966652 prefixEnd_966652 147068770853350282460579 := by
  unfold tailWord_966652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628347446996184931571105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23504463262661579908761473 17628347446996184931571105)
  ·
    refine ⟨13221260585247138698678329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17628347446996184931571105 13221260585247138698678329)
    ·
      refine ⟨9915945438935354024008747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13221260585247138698678329 9915945438935354024008747)
      ·
        refine ⟨14873918158403031036013121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9915945438935354024008747 14873918158403031036013121)
        ·
          refine ⟨11155438618802273277009841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14873918158403031036013121 11155438618802273277009841)
          ·
            refine ⟨8366578964101704957757381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11155438618802273277009841 8366578964101704957757381)
            ·
              refine ⟨1568733555769069679579509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8366578964101704957757381 1568733555769069679579509)
              ·
                refine ⟨147068770853350282460579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1568733555769069679579509 147068770853350282460579)
                ·
                  rfl

theorem cell20_966652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_966652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966652 prefixEnd_966652 := by exact prefixLift 966652
  have htrace : WordTrace (prefixWord ++ tailWord_966652) baseStart_966652 baseEnd_966652 := by
    simpa [prefixWord, tailWord_966652, baseEnd_966652] using wordTrace_append hprefix tailTrace_966652
  have hstable : (prefixWord ++ tailWord_966652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966652).length < 2 ^ (prefixWord ++ tailWord_966652).sum := by decide
  have hdescent : baseEnd_966652 < baseStart_966652 := by decide
  rcases family_descends (prefixWord ++ tailWord_966652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966696 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 2]
def baseStart_966696 : Nat := 118140960795 + 966696 * 2 ^ 59
def prefixEnd_966696 : Nat := 4983230072969 + 3 ^ 40 * 966696 * 2
def baseEnd_966696 : Nat := 441226395358982249914891

theorem tailTrace_966696 : CollatzResearch.WordTrace tailWord_966696 prefixEnd_966696 441226395358982249914891 := by
  unfold tailWord_966696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629149852916482688871971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23505533137221976918495961 17629149852916482688871971)
  ·
    refine ⟨26443724779374724033307957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17629149852916482688871971 26443724779374724033307957)
    ·
      refine ⟨2479099198066380378122621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26443724779374724033307957 2479099198066380378122621)
      ·
        refine ⟨929662199274892641795983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2479099198066380378122621 929662199274892641795983)
        ·
          refine ⟨1394493298912338962693975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929662199274892641795983 1394493298912338962693975)
          ·
            refine ⟨2091739948368508444040963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394493298912338962693975 2091739948368508444040963)
            ·
              refine ⟨3137609922552762666061445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091739948368508444040963 3137609922552762666061445)
              ·
                refine ⟨588301860478642999886521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3137609922552762666061445 588301860478642999886521)
                ·
                  refine ⟨441226395358982249914891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588301860478642999886521 441226395358982249914891)
                  ·
                    rfl

theorem cell20_966696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_966696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966696 prefixEnd_966696 := by exact prefixLift 966696
  have htrace : WordTrace (prefixWord ++ tailWord_966696) baseStart_966696 baseEnd_966696 := by
    simpa [prefixWord, tailWord_966696, baseEnd_966696] using wordTrace_append hprefix tailTrace_966696
  have hstable : (prefixWord ++ tailWord_966696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966696).length < 2 ^ (prefixWord ++ tailWord_966696).sum := by decide
  have hdescent : baseEnd_966696 < baseStart_966696 := by decide
  rcases family_descends (prefixWord ++ tailWord_966696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966721 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_966721 : Nat := 118140960795 + 966721 * 2 ^ 59
def prefixEnd_966721 : Nat := 4983230072969 + 3 ^ 40 * 966721 * 2
def baseEnd_966721 : Nat := 441237806040193274081455

theorem tailTrace_966721 : CollatzResearch.WordTrace tailWord_966721 prefixEnd_966721 441237806040193274081455 := by
  unfold tailWord_966721
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259211530742394647404017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23506141020494929764936011 35259211530742394647404017)
  ·
    refine ⟨26444408648056795985553013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35259211530742394647404017 26444408648056795985553013)
    ·
      refine ⟨2479163310755324623645595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26444408648056795985553013 2479163310755324623645595)
      ·
        refine ⟨3718744966132986935468393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479163310755324623645595 3718744966132986935468393)
        ·
          refine ⟨2789058724599740201601295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3718744966132986935468393 2789058724599740201601295)
          ·
            refine ⟨4183588086899610302401943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789058724599740201601295 4183588086899610302401943)
            ·
              refine ⟨6275382130349415453602915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183588086899610302401943 6275382130349415453602915)
              ·
                refine ⟨9413073195524123180404373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275382130349415453602915 9413073195524123180404373)
                ·
                  refine ⟨441237806040193274081455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9413073195524123180404373 441237806040193274081455)
                  ·
                    rfl

theorem cell20_966721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_966721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966721 prefixEnd_966721 := by exact prefixLift 966721
  have htrace : WordTrace (prefixWord ++ tailWord_966721) baseStart_966721 baseEnd_966721 := by
    simpa [prefixWord, tailWord_966721, baseEnd_966721] using wordTrace_append hprefix tailTrace_966721
  have hstable : (prefixWord ++ tailWord_966721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966721).length < 2 ^ (prefixWord ++ tailWord_966721).sum := by decide
  have hdescent : baseEnd_966721 < baseStart_966721 := by decide
  rcases family_descends (prefixWord ++ tailWord_966721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966752 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_966752 : Nat := 118140960795 + 966752 * 2 ^ 59
def prefixEnd_966752 : Nat := 4983230072969 + 3 ^ 40 * 966752 * 2
def baseEnd_966752 : Nat := 441251955284894944047995

theorem tailTrace_966752 : CollatzResearch.WordTrace tailWord_966752 prefixEnd_966752 441251955284894944047995 := by
  unfold tailWord_966752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17630171096815043470891255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23506894795753391294521673 17630171096815043470891255)
  ·
    refine ⟨26445256645222565206336883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17630171096815043470891255 26445256645222565206336883)
    ·
      refine ⟨39667884967833847809505325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26445256645222565206336883 39667884967833847809505325)
      ·
        refine ⟨14875456862937692928564497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39667884967833847809505325 14875456862937692928564497)
        ·
          refine ⟨11156592647203269696423373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14875456862937692928564497 11156592647203269696423373)
          ·
            refine ⟨4183722242701226136158765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11156592647203269696423373 4183722242701226136158765)
            ·
              refine ⟨1568895841012959801059537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4183722242701226136158765 1568895841012959801059537)
              ·
                refine ⟨1176671880759719850794653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568895841012959801059537 1176671880759719850794653)
                ·
                  refine ⟨441251955284894944047995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176671880759719850794653 441251955284894944047995)
                  ·
                    rfl

theorem cell20_966752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_966752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966752 prefixEnd_966752 := by exact prefixLift 966752
  have htrace : WordTrace (prefixWord ++ tailWord_966752) baseStart_966752 baseEnd_966752 := by
    simpa [prefixWord, tailWord_966752, baseEnd_966752] using wordTrace_append hprefix tailTrace_966752
  have hstable : (prefixWord ++ tailWord_966752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966752).length < 2 ^ (prefixWord ++ tailWord_966752).sum := by decide
  have hdescent : baseEnd_966752 < baseStart_966752 := by decide
  rcases family_descends (prefixWord ++ tailWord_966752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966759 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_966759 : Nat := 118140960795 + 966759 * 2 ^ 59
def prefixEnd_966759 : Nat := 4983230072969 + 3 ^ 40 * 966759 * 2
def baseEnd_966759 : Nat := 441255150275634030814633

theorem tailTrace_966759 : CollatzResearch.WordTrace tailWord_966759 prefixEnd_966759 441255150275634030814633 := by
  unfold tailWord_966759
  simp only [CollatzResearch.WordTrace]
  refine ⟨35260597504604727137287331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23507065003069818091524887 35260597504604727137287331)
  ·
    refine ⟨52890896256907090705930997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35260597504604727137287331 52890896256907090705930997)
    ·
      refine ⟨4958521524085039753681031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52890896256907090705930997 4958521524085039753681031)
      ·
        refine ⟨7437782286127559630521547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958521524085039753681031 7437782286127559630521547)
        ·
          refine ⟨11156673429191339445782321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437782286127559630521547 11156673429191339445782321)
          ·
            refine ⟨8367505071893504584336741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11156673429191339445782321 8367505071893504584336741)
            ·
              refine ⟨1568907200980032109563139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8367505071893504584336741 1568907200980032109563139)
              ·
                refine ⟨2353360801470048164344709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568907200980032109563139 2353360801470048164344709)
                ·
                  refine ⟨441255150275634030814633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353360801470048164344709 441255150275634030814633)
                  ·
                    rfl

theorem cell20_966759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_966759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966759 prefixEnd_966759 := by exact prefixLift 966759
  have htrace : WordTrace (prefixWord ++ tailWord_966759) baseStart_966759 baseEnd_966759 := by
    simpa [prefixWord, tailWord_966759, baseEnd_966759] using wordTrace_append hprefix tailTrace_966759
  have hstable : (prefixWord ++ tailWord_966759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966759).length < 2 ^ (prefixWord ++ tailWord_966759).sum := by decide
  have hdescent : baseEnd_966759 < baseStart_966759 := by decide
  rcases family_descends (prefixWord ++ tailWord_966759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966766 : List Nat := [4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_966766 : Nat := 118140960795 + 966766 * 2 ^ 59
def prefixEnd_966766 : Nat := 4983230072969 + 3 ^ 40 * 966766 * 2
def baseEnd_966766 : Nat := 147086115088791039193757

theorem tailTrace_966766 : CollatzResearch.WordTrace tailWord_966766 prefixEnd_966766 147086115088791039193757 := by
  unfold tailWord_966766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407606601947420916599019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23507235210386244888528101 4407606601947420916599019)
  ·
    refine ⟨6611409902921131374898529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407606601947420916599019 6611409902921131374898529)
    ·
      refine ⟨4958557427190848531173897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6611409902921131374898529 4958557427190848531173897)
      ·
        refine ⟨3718918070393136398380423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4958557427190848531173897 3718918070393136398380423)
        ·
          refine ⟨5578377105589704597570635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718918070393136398380423 5578377105589704597570635)
          ·
            refine ⟨8367565658384556896355953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578377105589704597570635 8367565658384556896355953)
            ·
              refine ⟨6275674243788417672266965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8367565658384556896355953 6275674243788417672266965)
              ·
                refine ⟨147086115088791039193757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6275674243788417672266965 147086115088791039193757)
                ·
                  rfl

theorem cell20_966766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_966766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966766 prefixEnd_966766 := by exact prefixLift 966766
  have htrace : WordTrace (prefixWord ++ tailWord_966766) baseStart_966766 baseEnd_966766 := by
    simpa [prefixWord, tailWord_966766, baseEnd_966766] using wordTrace_append hprefix tailTrace_966766
  have hstable : (prefixWord ++ tailWord_966766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966766).length < 2 ^ (prefixWord ++ tailWord_966766).sum := by decide
  have hdescent : baseEnd_966766 < baseStart_966766 := by decide
  rcases family_descends (prefixWord ++ tailWord_966766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966806 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_966806 : Nat := 118140960795 + 966806 * 2 ^ 59
def prefixEnd_966806 : Nat := 4983230072969 + 3 ^ 40 * 966806 * 2
def baseEnd_966806 : Nat := 441276602356310756247775

theorem tailTrace_966806 : CollatzResearch.WordTrace tailWord_966806 prefixEnd_966806 441276602356310756247775 := by
  unfold tailWord_966806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203894483464653385265517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23508207823622969442832181 2203894483464653385265517)
  ·
    refine ⟨826460431299245019474569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2203894483464653385265517 826460431299245019474569)
    ·
      refine ⟨619845323474433764605927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 826460431299245019474569 619845323474433764605927)
      ·
        refine ⟨929767985211650646908891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619845323474433764605927 929767985211650646908891)
        ·
          refine ⟨1394651977817475970363337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929767985211650646908891 1394651977817475970363337)
          ·
            refine ⟨1045988983363106977772503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394651977817475970363337 1045988983363106977772503)
            ·
              refine ⟨1568983475044660466658755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045988983363106977772503 1568983475044660466658755)
              ·
                refine ⟨2353475212566990699988133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568983475044660466658755 2353475212566990699988133)
                ·
                  refine ⟨441276602356310756247775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353475212566990699988133 441276602356310756247775)
                  ·
                    rfl

theorem cell20_966806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_966806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966806 prefixEnd_966806 := by exact prefixLift 966806
  have htrace : WordTrace (prefixWord ++ tailWord_966806) baseStart_966806 baseEnd_966806 := by
    simpa [prefixWord, tailWord_966806, baseEnd_966806] using wordTrace_append hprefix tailTrace_966806
  have hstable : (prefixWord ++ tailWord_966806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966806).length < 2 ^ (prefixWord ++ tailWord_966806).sum := by decide
  have hdescent : baseEnd_966806 < baseStart_966806 := by decide
  rcases family_descends (prefixWord ++ tailWord_966806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966810 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_966810 : Nat := 118140960795 + 966810 * 2 ^ 59
def prefixEnd_966810 : Nat := 4983230072969 + 3 ^ 40 * 966810 * 2
def baseEnd_966810 : Nat := 441278428065304520114425

theorem tailTrace_966810 : CollatzResearch.WordTrace tailWord_966810 prefixEnd_966810 441278428065304520114425 := by
  unfold tailWord_966810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815614406854990711848471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23508305084946641898262589 8815614406854990711848471)
  ·
    refine ⟨13223421610282486067772707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8815614406854990711848471 13223421610282486067772707)
    ·
      refine ⟨19835132415423729101659061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13223421610282486067772707 19835132415423729101659061)
      ·
        refine ⟨1859543663945974603280537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19835132415423729101659061 1859543663945974603280537)
        ·
          refine ⟨1394657747959480952460403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859543663945974603280537 1394657747959480952460403)
          ·
            refine ⟨2091986621939221428690605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394657747959480952460403 2091986621939221428690605)
            ·
              refine ⟨784494983227208035758977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2091986621939221428690605 784494983227208035758977)
              ·
                refine ⟨588371237420406026819233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784494983227208035758977 588371237420406026819233)
                ·
                  refine ⟨441278428065304520114425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588371237420406026819233 441278428065304520114425)
                  ·
                    rfl

theorem cell20_966810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_966810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966810 prefixEnd_966810 := by exact prefixLift 966810
  have htrace : WordTrace (prefixWord ++ tailWord_966810) baseStart_966810 baseEnd_966810 := by
    simpa [prefixWord, tailWord_966810, baseEnd_966810] using wordTrace_append hprefix tailTrace_966810
  have hstable : (prefixWord ++ tailWord_966810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966810).length < 2 ^ (prefixWord ++ tailWord_966810).sum := by decide
  have hdescent : baseEnd_966810 < baseStart_966810 := by decide
  rcases family_descends (prefixWord ++ tailWord_966810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966866 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_966866 : Nat := 118140960795 + 966866 * 2 ^ 59
def prefixEnd_966866 : Nat := 4983230072969 + 3 ^ 40 * 966866 * 2
def baseEnd_966866 : Nat := 441303987991217214247529

theorem tailTrace_966866 : CollatzResearch.WordTrace tailWord_966866 prefixEnd_966866 441303987991217214247529 := by
  unfold tailWord_966866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816125028804271102858113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23509666743478056274288301 8816125028804271102858113)
  ·
    refine ⟨6612093771603203327143585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8816125028804271102858113 6612093771603203327143585)
    ·
      refine ⟨4959070328702402495357689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6612093771603203327143585 4959070328702402495357689)
      ·
        refine ⟨3719302746526801871518267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4959070328702402495357689 3719302746526801871518267)
        ·
          refine ⟨5578954119790202807277401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719302746526801871518267 5578954119790202807277401)
          ·
            refine ⟨4184215589842652105458051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5578954119790202807277401 4184215589842652105458051)
            ·
              refine ⟨6276323384763978158187077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184215589842652105458051 6276323384763978158187077)
              ·
                refine ⟨1176810634643245904660077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6276323384763978158187077 1176810634643245904660077)
                ·
                  refine ⟨441303987991217214247529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176810634643245904660077 441303987991217214247529)
                  ·
                    rfl

theorem cell20_966866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_966866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966866 prefixEnd_966866 := by exact prefixLift 966866
  have htrace : WordTrace (prefixWord ++ tailWord_966866) baseStart_966866 baseEnd_966866 := by
    simpa [prefixWord, tailWord_966866, baseEnd_966866] using wordTrace_append hprefix tailTrace_966866
  have hstable : (prefixWord ++ tailWord_966866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966866).length < 2 ^ (prefixWord ++ tailWord_966866).sum := by decide
  have hdescent : baseEnd_966866 < baseStart_966866 := by decide
  rcases family_descends (prefixWord ++ tailWord_966866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966869 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 2]
def baseStart_966869 : Nat := 118140960795 + 966869 * 2 ^ 59
def prefixEnd_966869 : Nat := 4983230072969 + 3 ^ 40 * 966869 * 2
def baseEnd_966869 : Nat := 441305357272962537147517

theorem tailTrace_966869 : CollatzResearch.WordTrace tailWord_966869 prefixEnd_966869 441305357272962537147517 := by
  unfold tailWord_966869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35264609534206215923791661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23509739689470810615861107 35264609534206215923791661)
  ·
    refine ⟨13224228575327330971421873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35264609534206215923791661 13224228575327330971421873)
    ·
      refine ⟨9918171431495498228566405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13224228575327330971421873 9918171431495498228566405)
      ·
        refine ⟨1859657143405405917856201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9918171431495498228566405 1859657143405405917856201)
        ·
          refine ⟨1394742857554054438392151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859657143405405917856201 1394742857554054438392151)
          ·
            refine ⟨2092114286331081657588227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394742857554054438392151 2092114286331081657588227)
            ·
              refine ⟨3138171429496622486382341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092114286331081657588227 3138171429496622486382341)
              ·
                refine ⟨588407143030616716196689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3138171429496622486382341 588407143030616716196689)
                ·
                  refine ⟨441305357272962537147517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588407143030616716196689 441305357272962537147517)
                  ·
                    rfl

theorem cell20_966869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_966869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966869 prefixEnd_966869 := by exact prefixLift 966869
  have htrace : WordTrace (prefixWord ++ tailWord_966869) baseStart_966869 baseEnd_966869 := by
    simpa [prefixWord, tailWord_966869, baseEnd_966869] using wordTrace_append hprefix tailTrace_966869
  have hstable : (prefixWord ++ tailWord_966869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966869).length < 2 ^ (prefixWord ++ tailWord_966869).sum := by decide
  have hdescent : baseEnd_966869 < baseStart_966869 := by decide
  rcases family_descends (prefixWord ++ tailWord_966869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966952 : List Nat := [2, 1, 5, 1, 3, 2, 2, 4]
def baseStart_966952 : Nat := 118140960795 + 966952 * 2 ^ 59
def prefixEnd_966952 : Nat := 4983230072969 + 3 ^ 40 * 966952 * 2
def baseEnd_966952 : Nat := 147114413578194379126837

theorem tailTrace_966952 : CollatzResearch.WordTrace tailWord_966952 prefixEnd_966952 147114413578194379126837 := by
  unfold tailWord_966952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17633818396452760549531555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23511757861937014066042073 17633818396452760549531555)
  ·
    refine ⟨26450727594679140824297333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17633818396452760549531555 26450727594679140824297333)
    ·
      refine ⟨2479755712001169452277875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26450727594679140824297333 2479755712001169452277875)
      ·
        refine ⟨3719633568001754178416813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479755712001169452277875 3719633568001754178416813)
        ·
          refine ⟨1394862588000657816906305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3719633568001754178416813 1394862588000657816906305)
          ·
            refine ⟨1046146941000493362679729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394862588000657816906305 1046146941000493362679729)
            ·
              refine ⟨784610205750370022009797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046146941000493362679729 784610205750370022009797)
              ·
                refine ⟨147114413578194379126837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784610205750370022009797 147114413578194379126837)
                ·
                  rfl

theorem cell20_966952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_966952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966952 prefixEnd_966952 := by exact prefixLift 966952
  have htrace : WordTrace (prefixWord ++ tailWord_966952) baseStart_966952 baseEnd_966952 := by
    simpa [prefixWord, tailWord_966952, baseEnd_966952] using wordTrace_append hprefix tailTrace_966952
  have hstable : (prefixWord ++ tailWord_966952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966952).length < 2 ^ (prefixWord ++ tailWord_966952).sum := by decide
  have hdescent : baseEnd_966952 < baseStart_966952 := by decide
  rcases family_descends (prefixWord ++ tailWord_966952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966956 : List Nat := [2, 2, 1, 1, 1, 3, 6, 4]
def baseStart_966956 : Nat := 118140960795 + 966956 * 2 ^ 59
def prefixEnd_966956 : Nat := 4983230072969 + 3 ^ 40 * 966956 * 2
def baseEnd_966956 : Nat := 147115022147858967082387

theorem tailTrace_966956 : CollatzResearch.WordTrace tailWord_966956 prefixEnd_966956 147115022147858967082387 := by
  unfold tailWord_966956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17633891342445514891104361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23511855123260686521472481 17633891342445514891104361)
  ·
    refine ⟨13225418506834136168328271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17633891342445514891104361 13225418506834136168328271)
    ·
      refine ⟨19838127760251204252492407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13225418506834136168328271 19838127760251204252492407)
      ·
        refine ⟨29757191640376806378738611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19838127760251204252492407 29757191640376806378738611)
        ·
          refine ⟨44635787460565209568107917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29757191640376806378738611 44635787460565209568107917)
          ·
            refine ⟨16738420297711953588040469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44635787460565209568107917 16738420297711953588040469)
            ·
              refine ⟨784613451455247824439397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16738420297711953588040469 784613451455247824439397)
              ·
                refine ⟨147115022147858967082387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784613451455247824439397 147115022147858967082387)
                ·
                  rfl

theorem cell20_966956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_966956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966956 prefixEnd_966956 := by exact prefixLift 966956
  have htrace : WordTrace (prefixWord ++ tailWord_966956) baseStart_966956 baseEnd_966956 := by
    simpa [prefixWord, tailWord_966956, baseEnd_966956] using wordTrace_append hprefix tailTrace_966956
  have hstable : (prefixWord ++ tailWord_966956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966956).length < 2 ^ (prefixWord ++ tailWord_966956).sum := by decide
  have hdescent : baseEnd_966956 < baseStart_966956 := by decide
  rcases family_descends (prefixWord ++ tailWord_966956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966962 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_966962 : Nat := 118140960795 + 966962 * 2 ^ 59
def prefixEnd_966962 : Nat := 4983230072969 + 3 ^ 40 * 966962 * 2
def baseEnd_966962 : Nat := 441347805007067547047137

theorem tailTrace_966962 : CollatzResearch.WordTrace tailWord_966962 prefixEnd_966962 441347805007067547047137 := by
  unfold tailWord_966962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8817000380717323201731785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23512001015246195204618093 8817000380717323201731785)
  ·
    refine ⟨6612750285537992401298839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8817000380717323201731785 6612750285537992401298839)
    ·
      refine ⟨9919125428306988601948259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6612750285537992401298839 9919125428306988601948259)
      ·
        refine ⟨14878688142460482902922389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919125428306988601948259 14878688142460482902922389)
        ·
          refine ⟨697438506677835136074487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14878688142460482902922389 697438506677835136074487)
          ·
            refine ⟨1046157760016752704111731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697438506677835136074487 1046157760016752704111731)
            ·
              refine ⟨1569236640025129056167597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046157760016752704111731 1569236640025129056167597)
              ·
                refine ⟨588463740009423396062849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1569236640025129056167597 588463740009423396062849)
                ·
                  refine ⟨441347805007067547047137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588463740009423396062849 441347805007067547047137)
                  ·
                    rfl

theorem cell20_966962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_966962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_966962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_966962 prefixEnd_966962 := by exact prefixLift 966962
  have htrace : WordTrace (prefixWord ++ tailWord_966962) baseStart_966962 baseEnd_966962 := by
    simpa [prefixWord, tailWord_966962, baseEnd_966962] using wordTrace_append hprefix tailTrace_966962
  have hstable : (prefixWord ++ tailWord_966962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966962).length < 2 ^ (prefixWord ++ tailWord_966962).sum := by decide
  have hdescent : baseEnd_966962 < baseStart_966962 := by decide
  rcases family_descends (prefixWord ++ tailWord_966962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967025 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 2]
def baseStart_967025 : Nat := 118140960795 + 967025 * 2 ^ 59
def prefixEnd_967025 : Nat := 4983230072969 + 3 ^ 40 * 967025 * 2
def baseEnd_967025 : Nat := 441376559923719327946879

theorem tailTrace_967025 : CollatzResearch.WordTrace tailWord_967025 prefixEnd_967025 441376559923719327946879 := by
  unfold tailWord_967025
  simp only [CollatzResearch.WordTrace]
  refine ⟨35270299321641054566470529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23513532881094036377647019 35270299321641054566470529)
  ·
    refine ⟨26452724491230790924852897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35270299321641054566470529 26452724491230790924852897)
    ·
      refine ⟨19839543368423093193639673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26452724491230790924852897 19839543368423093193639673)
      ·
        refine ⟨14879657526317319895229755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19839543368423093193639673 14879657526317319895229755)
        ·
          refine ⟨22319486289475979842844633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14879657526317319895229755 22319486289475979842844633)
          ·
            refine ⟨16739614717106984882133475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22319486289475979842844633 16739614717106984882133475)
            ·
              refine ⟨25109422075660477323200213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16739614717106984882133475 25109422075660477323200213)
              ·
                refine ⟨588502079898292437262505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25109422075660477323200213 588502079898292437262505)
                ·
                  refine ⟨441376559923719327946879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588502079898292437262505 441376559923719327946879)
                  ·
                    rfl

theorem cell20_967025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_967025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967025 prefixEnd_967025 := by exact prefixLift 967025
  have htrace : WordTrace (prefixWord ++ tailWord_967025) baseStart_967025 baseEnd_967025 := by
    simpa [prefixWord, tailWord_967025, baseEnd_967025] using wordTrace_append hprefix tailTrace_967025
  have hstable : (prefixWord ++ tailWord_967025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967025).length < 2 ^ (prefixWord ++ tailWord_967025).sum := by decide
  have hdescent : baseEnd_967025 < baseStart_967025 := by decide
  rcases family_descends (prefixWord ++ tailWord_967025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967062 : List Nat := [5, 3, 1, 2, 1, 1, 3, 4]
def baseStart_967062 : Nat := 118140960795 + 967062 * 2 ^ 59
def prefixEnd_967062 : Nat := 4983230072969 + 3 ^ 40 * 967062 * 2
def baseEnd_967062 : Nat := 147131149243970547904465

theorem tailTrace_967062 : CollatzResearch.WordTrace tailWord_967062 prefixEnd_967062 147131149243970547904465 := by
  unfold tailWord_967062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204478051406688117847965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23514432548338006590378293 2204478051406688117847965)
  ·
    refine ⟨826679269277508044192987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2204478051406688117847965 826679269277508044192987)
    ·
      refine ⟨1240018903916262066289481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826679269277508044192987 1240018903916262066289481)
      ·
        refine ⟨930014177937196549717111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240018903916262066289481 930014177937196549717111)
        ·
          refine ⟨1395021266905794824575667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930014177937196549717111 1395021266905794824575667)
          ·
            refine ⟨2092531900358692236863501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395021266905794824575667 2092531900358692236863501)
            ·
              refine ⟨784699462634509588823813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2092531900358692236863501 784699462634509588823813)
              ·
                refine ⟨147131149243970547904465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784699462634509588823813 147131149243970547904465)
                ·
                  rfl

theorem cell20_967062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_967062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967062 prefixEnd_967062 := by exact prefixLift 967062
  have htrace : WordTrace (prefixWord ++ tailWord_967062) baseStart_967062 baseEnd_967062 := by
    simpa [prefixWord, tailWord_967062, baseEnd_967062] using wordTrace_append hprefix tailTrace_967062
  have hstable : (prefixWord ++ tailWord_967062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967062).length < 2 ^ (prefixWord ++ tailWord_967062).sum := by decide
  have hdescent : baseEnd_967062 < baseStart_967062 := by decide
  rcases family_descends (prefixWord ++ tailWord_967062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967101 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_967101 : Nat := 118140960795 + 967101 * 2 ^ 59
def prefixEnd_967101 : Nat := 4983230072969 + 3 ^ 40 * 967101 * 2
def baseEnd_967101 : Nat := 441411248394600841413235

theorem tailTrace_967101 : CollatzResearch.WordTrace tailWord_967101 prefixEnd_967101 441411248394600841413235 := by
  unfold tailWord_967101
  simp only [CollatzResearch.WordTrace]
  refine ⟨35273071269365719546237157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23515380846243813030824771 35273071269365719546237157)
  ·
    refine ⟨6613700863006072414919467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35273071269365719546237157 6613700863006072414919467)
    ·
      refine ⟨9920551294509108622379201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6613700863006072414919467 9920551294509108622379201)
      ·
        refine ⟨7440413470881831466784401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9920551294509108622379201 7440413470881831466784401)
        ·
          refine ⟨5580310103161373600088301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7440413470881831466784401 5580310103161373600088301)
          ·
            refine ⟨2092616288685515100033113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5580310103161373600088301 2092616288685515100033113)
            ·
              refine ⟨1569462216514136325024835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092616288685515100033113 1569462216514136325024835)
              ·
                refine ⟨2354193324771204487537253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569462216514136325024835 2354193324771204487537253)
                ·
                  refine ⟨441411248394600841413235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354193324771204487537253 441411248394600841413235)
                  ·
                    rfl

theorem cell20_967101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_967101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967101 prefixEnd_967101 := by exact prefixLift 967101
  have htrace : WordTrace (prefixWord ++ tailWord_967101) baseStart_967101 baseEnd_967101 := by
    simpa [prefixWord, tailWord_967101, baseEnd_967101] using wordTrace_append hprefix tailTrace_967101
  have hstable : (prefixWord ++ tailWord_967101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967101).length < 2 ^ (prefixWord ++ tailWord_967101).sum := by decide
  have hdescent : baseEnd_967101 < baseStart_967101 := by decide
  rcases family_descends (prefixWord ++ tailWord_967101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967125 : List Nat := [1, 3, 2, 3, 1, 4, 2, 4]
def baseStart_967125 : Nat := 118140960795 + 967125 * 2 ^ 59
def prefixEnd_967125 : Nat := 4983230072969 + 3 ^ 40 * 967125 * 2
def baseEnd_967125 : Nat := 147140734216187808204379

theorem tailTrace_967125 : CollatzResearch.WordTrace tailWord_967125 prefixEnd_967125 147140734216187808204379 := by
  unfold tailWord_967125
  simp only [CollatzResearch.WordTrace]
  refine ⟨35273946621278771645110829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23515964414185847763407219 35273946621278771645110829)
  ·
    refine ⟨13227729982979539366916561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35273946621278771645110829 13227729982979539366916561)
    ·
      refine ⟨9920797487234654525187421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227729982979539366916561 9920797487234654525187421)
      ·
        refine ⟨3720299057712995446945283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9920797487234654525187421 3720299057712995446945283)
        ·
          refine ⟨5580448586569493170417925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720299057712995446945283 5580448586569493170417925)
          ·
            refine ⟨1046334109981779969453361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5580448586569493170417925 1046334109981779969453361)
            ·
              refine ⟨784750582486334977090021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046334109981779969453361 784750582486334977090021)
              ·
                refine ⟨147140734216187808204379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784750582486334977090021 147140734216187808204379)
                ·
                  rfl

theorem cell20_967125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_967125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967125 prefixEnd_967125 := by exact prefixLift 967125
  have htrace : WordTrace (prefixWord ++ tailWord_967125) baseStart_967125 baseEnd_967125 := by
    simpa [prefixWord, tailWord_967125, baseEnd_967125] using wordTrace_append hprefix tailTrace_967125
  have hstable : (prefixWord ++ tailWord_967125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967125).length < 2 ^ (prefixWord ++ tailWord_967125).sum := by decide
  have hdescent : baseEnd_967125 < baseStart_967125 := by decide
  rcases family_descends (prefixWord ++ tailWord_967125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967129 : List Nat := [1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_967129 : Nat := 118140960795 + 967129 * 2 ^ 59
def prefixEnd_967129 : Nat := 4983230072969 + 3 ^ 40 * 967129 * 2
def baseEnd_967129 : Nat := 147141342785852396159929

theorem tailTrace_967129 : CollatzResearch.WordTrace tailWord_967129 prefixEnd_967129 147141342785852396159929 := by
  unfold tailWord_967129
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274092513264280328256441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23516061675509520218837627 35274092513264280328256441)
  ·
    refine ⟨26455569384948210246192331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35274092513264280328256441 26455569384948210246192331)
    ·
      refine ⟨39683354077422315369288497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26455569384948210246192331 39683354077422315369288497)
      ·
        refine ⟨29762515558066736526966373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39683354077422315369288497 29762515558066736526966373)
        ·
          refine ⟨5580471667137513098806195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29762515558066736526966373 5580471667137513098806195)
          ·
            refine ⟨8370707500706269648209293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580471667137513098806195 8370707500706269648209293)
            ·
              refine ⟨3139015312764851118078485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8370707500706269648209293 3139015312764851118078485)
              ·
                refine ⟨147141342785852396159929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3139015312764851118078485 147141342785852396159929)
                ·
                  rfl

theorem cell20_967129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_967129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967129 prefixEnd_967129 := by exact prefixLift 967129
  have htrace : WordTrace (prefixWord ++ tailWord_967129) baseStart_967129 baseEnd_967129 := by
    simpa [prefixWord, tailWord_967129, baseEnd_967129] using wordTrace_append hprefix tailTrace_967129
  have hstable : (prefixWord ++ tailWord_967129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967129).length < 2 ^ (prefixWord ++ tailWord_967129).sum := by decide
  have hdescent : baseEnd_967129 < baseStart_967129 := by decide
  rcases family_descends (prefixWord ++ tailWord_967129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967136 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_967136 : Nat := 118140960795 + 967136 * 2 ^ 59
def prefixEnd_967136 : Nat := 4983230072969 + 3 ^ 40 * 967136 * 2
def baseEnd_967136 : Nat := 441427223348296275246425

theorem tailTrace_967136 : CollatzResearch.WordTrace tailWord_967136 prefixEnd_967136 441427223348296275246425 := by
  unfold tailWord_967136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637173912119460261880631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23516231882825947015840841 17637173912119460261880631)
  ·
    refine ⟨26455760868179190392820947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17637173912119460261880631 26455760868179190392820947)
    ·
      refine ⟨39683641302268785589231421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26455760868179190392820947 39683641302268785589231421)
      ·
        refine ⟨14881365488350794595961783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39683641302268785589231421 14881365488350794595961783)
        ·
          refine ⟨22322048232526191893942675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14881365488350794595961783 22322048232526191893942675)
          ·
            refine ⟨33483072348789287840914013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22322048232526191893942675 33483072348789287840914013)
            ·
              refine ⟨12556152130795982940342755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33483072348789287840914013 12556152130795982940342755)
              ·
                refine ⟨18834228196193974410514133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556152130795982940342755 18834228196193974410514133)
                ·
                  refine ⟨441427223348296275246425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18834228196193974410514133 441427223348296275246425)
                  ·
                    rfl

theorem cell20_967136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_967136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967136 prefixEnd_967136 := by exact prefixLift 967136
  have htrace : WordTrace (prefixWord ++ tailWord_967136) baseStart_967136 baseEnd_967136 := by
    simpa [prefixWord, tailWord_967136, baseEnd_967136] using wordTrace_append hprefix tailTrace_967136
  have hstable : (prefixWord ++ tailWord_967136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967136).length < 2 ^ (prefixWord ++ tailWord_967136).sum := by decide
  have hdescent : baseEnd_967136 < baseStart_967136 := by decide
  rcases family_descends (prefixWord ++ tailWord_967136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967146 : List Nat := [3, 1, 3, 1, 3, 3, 6]
def baseStart_967146 : Nat := 118140960795 + 967146 * 2 ^ 59
def prefixEnd_967146 : Nat := 4983230072969 + 3 ^ 40 * 967146 * 2
def baseEnd_967146 : Nat := 49047976402308964990339

theorem tailTrace_967146 : CollatzResearch.WordTrace tailWord_967146 prefixEnd_967146 49047976402308964990339 := by
  unfold tailWord_967146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818678138550673057906323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23516475036135128154416861 8818678138550673057906323)
  ·
    refine ⟨13228017207826009586859485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8818678138550673057906323 13228017207826009586859485)
    ·
      refine ⟨4960506452934753595072307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13228017207826009586859485 4960506452934753595072307)
      ·
        refine ⟨7440759679402130392608461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960506452934753595072307 7440759679402130392608461)
        ·
          refine ⟨2790284879775798897228173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7440759679402130392608461 2790284879775798897228173)
          ·
            refine ⟨1046356829915924586460565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2790284879775798897228173 1046356829915924586460565)
            ·
              refine ⟨49047976402308964990339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1046356829915924586460565 49047976402308964990339)
              ·
                rfl

theorem cell20_967146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 6].length) (baseStart_967146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967146 prefixEnd_967146 := by exact prefixLift 967146
  have htrace : WordTrace (prefixWord ++ tailWord_967146) baseStart_967146 baseEnd_967146 := by
    simpa [prefixWord, tailWord_967146, baseEnd_967146] using wordTrace_append hprefix tailTrace_967146
  have hstable : (prefixWord ++ tailWord_967146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967146).length < 2 ^ (prefixWord ++ tailWord_967146).sum := by decide
  have hdescent : baseEnd_967146 < baseStart_967146 := by decide
  rcases family_descends (prefixWord ++ tailWord_967146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967153 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_967153 : Nat := 118140960795 + 967153 * 2 ^ 59
def prefixEnd_967153 : Nat := 4983230072969 + 3 ^ 40 * 967153 * 2
def baseEnd_967153 : Nat := 441434982611519771679689

theorem tailTrace_967153 : CollatzResearch.WordTrace tailWord_967153 prefixEnd_967153 441434982611519771679689 := by
  unfold tailWord_967153
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274967865177332427130113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23516645243451554951420075 35274967865177332427130113)
  ·
    refine ⟨26456225898882999320347585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35274967865177332427130113 26456225898882999320347585)
    ·
      refine ⟨19842169424162249490260689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26456225898882999320347585 19842169424162249490260689)
      ·
        refine ⟨14881627068121687117695517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19842169424162249490260689 14881627068121687117695517)
        ·
          refine ⟨5580610150545632669135819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14881627068121687117695517 5580610150545632669135819)
          ·
            refine ⟨8370915225818449003703729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580610150545632669135819 8370915225818449003703729)
            ·
              refine ⟨6278186419363836752777797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8370915225818449003703729 6278186419363836752777797)
              ·
                refine ⟨1177159953630719391145837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6278186419363836752777797 1177159953630719391145837)
                ·
                  refine ⟨441434982611519771679689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177159953630719391145837 441434982611519771679689)
                  ·
                    rfl

theorem cell20_967153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_967153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967153 prefixEnd_967153 := by exact prefixLift 967153
  have htrace : WordTrace (prefixWord ++ tailWord_967153) baseStart_967153 baseEnd_967153 := by
    simpa [prefixWord, tailWord_967153, baseEnd_967153] using wordTrace_append hprefix tailTrace_967153
  have hstable : (prefixWord ++ tailWord_967153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967153).length < 2 ^ (prefixWord ++ tailWord_967153).sum := by decide
  have hdescent : baseEnd_967153 < baseStart_967153 := by decide
  rcases family_descends (prefixWord ++ tailWord_967153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967167 : List Nat := [1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_967167 : Nat := 118140960795 + 967167 * 2 ^ 59
def prefixEnd_967167 : Nat := 4983230072969 + 3 ^ 40 * 967167 * 2
def baseEnd_967167 : Nat := 147147124197665981737655

theorem tailTrace_967167 : CollatzResearch.WordTrace tailWord_967167 prefixEnd_967167 147147124197665981737655 := by
  unfold tailWord_967167
  simp only [CollatzResearch.WordTrace]
  refine ⟨35275478487126612818139755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23516985658084408545426503 35275478487126612818139755)
  ·
    refine ⟨52913217730689919227209633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35275478487126612818139755 52913217730689919227209633)
    ·
      refine ⟨39684913298017439420407225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52913217730689919227209633 39684913298017439420407225)
      ·
        refine ⟨29763684973513079565305419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39684913298017439420407225 29763684973513079565305419)
        ·
          refine ⟨44645527460269619347958129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29763684973513079565305419 44645527460269619347958129)
          ·
            refine ⟨33484145595202214510968597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44645527460269619347958129 33484145595202214510968597)
            ·
              refine ⟨1569569324775103805201653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33484145595202214510968597 1569569324775103805201653)
              ·
                refine ⟨147147124197665981737655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1569569324775103805201653 147147124197665981737655)
                ·
                  rfl

theorem cell20_967167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_967167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967167 prefixEnd_967167 := by exact prefixLift 967167
  have htrace : WordTrace (prefixWord ++ tailWord_967167) baseStart_967167 baseEnd_967167 := by
    simpa [prefixWord, tailWord_967167, baseEnd_967167] using wordTrace_append hprefix tailTrace_967167
  have hstable : (prefixWord ++ tailWord_967167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967167).length < 2 ^ (prefixWord ++ tailWord_967167).sum := by decide
  have hdescent : baseEnd_967167 < baseStart_967167 := by decide
  rcases family_descends (prefixWord ++ tailWord_967167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967207 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 2]
def baseStart_967207 : Nat := 118140960795 + 967207 * 2 ^ 59
def prefixEnd_967207 : Nat := 4983230072969 + 3 ^ 40 * 967207 * 2
def baseEnd_967207 : Nat := 441459629682935583879469

theorem tailTrace_967207 : CollatzResearch.WordTrace tailWord_967207 prefixEnd_967207 441459629682935583879469 := by
  unfold tailWord_967207
  simp only [CollatzResearch.WordTrace]
  refine ⟨35276937406981699649595875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23517958271321133099730583 35276937406981699649595875)
  ·
    refine ⟨52915406110472549474393813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35276937406981699649595875 52915406110472549474393813)
    ·
      refine ⟨1240204830714200378306105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 52915406110472549474393813 1240204830714200378306105)
      ·
        refine ⟨930153623035650283729579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240204830714200378306105 930153623035650283729579)
        ·
          refine ⟨1395230434553475425594369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930153623035650283729579 1395230434553475425594369)
          ·
            refine ⟨1046422825915106569195777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395230434553475425594369 1046422825915106569195777)
            ·
              refine ⟨784817119436329926896833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046422825915106569195777 784817119436329926896833)
              ·
                refine ⟨588612839577247445172625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784817119436329926896833 588612839577247445172625)
                ·
                  refine ⟨441459629682935583879469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588612839577247445172625 441459629682935583879469)
                  ·
                    rfl

theorem cell20_967207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 2].length) (baseStart_967207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967207 prefixEnd_967207 := by exact prefixLift 967207
  have htrace : WordTrace (prefixWord ++ tailWord_967207) baseStart_967207 baseEnd_967207 := by
    simpa [prefixWord, tailWord_967207, baseEnd_967207] using wordTrace_append hprefix tailTrace_967207
  have hstable : (prefixWord ++ tailWord_967207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967207).length < 2 ^ (prefixWord ++ tailWord_967207).sum := by decide
  have hdescent : baseEnd_967207 < baseStart_967207 := by decide
  rcases family_descends (prefixWord ++ tailWord_967207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967208 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_967208 : Nat := 118140960795 + 967208 * 2 ^ 59
def prefixEnd_967208 : Nat := 4983230072969 + 3 ^ 40 * 967208 * 2
def baseEnd_967208 : Nat := 441460086110184024846131

theorem tailTrace_967208 : CollatzResearch.WordTrace tailWord_967208 prefixEnd_967208 441460086110184024846131 := by
  unfold tailWord_967208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638486939989038410191139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23517982586652051213588185 17638486939989038410191139)
  ·
    refine ⟨26457730409983557615286709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17638486939989038410191139 26457730409983557615286709)
    ·
      refine ⟨2480412225935958526433129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26457730409983557615286709 2480412225935958526433129)
      ·
        refine ⟨1860309169451968894824847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2480412225935958526433129 1860309169451968894824847)
        ·
          refine ⟨2790463754177953342237271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860309169451968894824847 2790463754177953342237271)
          ·
            refine ⟨4185695631266930013355907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790463754177953342237271 4185695631266930013355907)
            ·
              refine ⟨6278543446900395020033861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185695631266930013355907 6278543446900395020033861)
              ·
                refine ⟨1177226896293824066256349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6278543446900395020033861 1177226896293824066256349)
                ·
                  refine ⟨441460086110184024846131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177226896293824066256349 441460086110184024846131)
                  ·
                    rfl

theorem cell20_967208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_967208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967208 prefixEnd_967208 := by exact prefixLift 967208
  have htrace : WordTrace (prefixWord ++ tailWord_967208) baseStart_967208 baseEnd_967208 := by
    simpa [prefixWord, tailWord_967208, baseEnd_967208] using wordTrace_append hprefix tailTrace_967208
  have hstable : (prefixWord ++ tailWord_967208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967208).length < 2 ^ (prefixWord ++ tailWord_967208).sum := by decide
  have hdescent : baseEnd_967208 < baseStart_967208 := by decide
  rcases family_descends (prefixWord ++ tailWord_967208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967212 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_967212 : Nat := 118140960795 + 967212 * 2 ^ 59
def prefixEnd_967212 : Nat := 4983230072969 + 3 ^ 40 * 967212 * 2
def baseEnd_967212 : Nat := 441461911819177788712781

theorem tailTrace_967212 : CollatzResearch.WordTrace tailWord_967212 prefixEnd_967212 441461911819177788712781 := by
  unfold tailWord_967212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638559885981792751763945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23518079847975723669018593 17638559885981792751763945)
  ·
    refine ⟨13228919914486344563822959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17638559885981792751763945 13228919914486344563822959)
    ·
      refine ⟨19843379871729516845734439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13228919914486344563822959 19843379871729516845734439)
      ·
        refine ⟨29765069807594275268601659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19843379871729516845734439 29765069807594275268601659)
        ·
          refine ⟨44647604711391412902902489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29765069807594275268601659 44647604711391412902902489)
          ·
            refine ⟨33485703533543559677176867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44647604711391412902902489 33485703533543559677176867)
            ·
              refine ⟨50228555300315339515765301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33485703533543559677176867 50228555300315339515765301)
              ·
                refine ⟨4708927059404563079602997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50228555300315339515765301 4708927059404563079602997)
                ·
                  refine ⟨441461911819177788712781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4708927059404563079602997 441461911819177788712781)
                  ·
                    rfl

theorem cell20_967212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_967212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967212 prefixEnd_967212 := by exact prefixLift 967212
  have htrace : WordTrace (prefixWord ++ tailWord_967212) baseStart_967212 baseEnd_967212 := by
    simpa [prefixWord, tailWord_967212, baseEnd_967212] using wordTrace_append hprefix tailTrace_967212
  have hstable : (prefixWord ++ tailWord_967212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967212).length < 2 ^ (prefixWord ++ tailWord_967212).sum := by decide
  have hdescent : baseEnd_967212 < baseStart_967212 := by decide
  rcases family_descends (prefixWord ++ tailWord_967212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967253 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 2]
def baseStart_967253 : Nat := 118140960795 + 967253 * 2 ^ 59
def prefixEnd_967253 : Nat := 4983230072969 + 3 ^ 40 * 967253 * 2
def baseEnd_967253 : Nat := 441480625336363868345947

theorem tailTrace_967253 : CollatzResearch.WordTrace tailWord_967253 prefixEnd_967253 441480625336363868345947 := by
  unfold tailWord_967253
  simp only [CollatzResearch.WordTrace]
  refine ⟨35278615164815049505770413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23519076776543366337180275 35278615164815049505770413)
  ·
    refine ⟨13229480686805643564663905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35278615164815049505770413 13229480686805643564663905)
    ·
      refine ⟨9922110515104232673497929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13229480686805643564663905 9922110515104232673497929)
      ·
        refine ⟨7441582886328174505123447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9922110515104232673497929 7441582886328174505123447)
        ·
          refine ⟨11162374329492261757685171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7441582886328174505123447 11162374329492261757685171)
          ·
            refine ⟨16743561494238392636527757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11162374329492261757685171 16743561494238392636527757)
            ·
              refine ⟨6278835560339397238697909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16743561494238392636527757 6278835560339397238697909)
              ·
                refine ⟨588640833781818491127929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6278835560339397238697909 588640833781818491127929)
                ·
                  refine ⟨441480625336363868345947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588640833781818491127929 441480625336363868345947)
                  ·
                    rfl

theorem cell20_967253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_967253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967253 prefixEnd_967253 := by exact prefixLift 967253
  have htrace : WordTrace (prefixWord ++ tailWord_967253) baseStart_967253 baseEnd_967253 := by
    simpa [prefixWord, tailWord_967253, baseEnd_967253] using wordTrace_append hprefix tailTrace_967253
  have hstable : (prefixWord ++ tailWord_967253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967253).length < 2 ^ (prefixWord ++ tailWord_967253).sum := by decide
  have hdescent : baseEnd_967253 < baseStart_967253 := by decide
  rcases family_descends (prefixWord ++ tailWord_967253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967260 : List Nat := [2, 2, 4, 1, 3, 1, 7]
def baseStart_967260 : Nat := 118140960795 + 967260 * 2 ^ 59
def prefixEnd_967260 : Nat := 4983230072969 + 3 ^ 40 * 967260 * 2
def baseEnd_967260 : Nat := 49053757814122550568065

theorem tailTrace_967260 : CollatzResearch.WordTrace tailWord_967260 prefixEnd_967260 49053757814122550568065 := by
  unfold tailWord_967260
  simp only [CollatzResearch.WordTrace]
  refine ⟨17639435237894844850637617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23519246983859793134183489 17639435237894844850637617)
  ·
    refine ⟨13229576428421133637978213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17639435237894844850637617 13229576428421133637978213)
    ·
      refine ⟨2480545580328962557120915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13229576428421133637978213 2480545580328962557120915)
      ·
        refine ⟨3720818370493443835681373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480545580328962557120915 3720818370493443835681373)
        ·
          refine ⟨1395306888935041438380515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3720818370493443835681373 1395306888935041438380515)
          ·
            refine ⟨2092960333402562157570773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395306888935041438380515 2092960333402562157570773)
            ·
              refine ⟨49053757814122550568065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2092960333402562157570773 49053757814122550568065)
              ·
                rfl

theorem cell20_967260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 7].length) (baseStart_967260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967260 prefixEnd_967260 := by exact prefixLift 967260
  have htrace : WordTrace (prefixWord ++ tailWord_967260) baseStart_967260 baseEnd_967260 := by
    simpa [prefixWord, tailWord_967260, baseEnd_967260] using wordTrace_append hprefix tailTrace_967260
  have hstable : (prefixWord ++ tailWord_967260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967260).length < 2 ^ (prefixWord ++ tailWord_967260).sum := by decide
  have hdescent : baseEnd_967260 < baseStart_967260 := by decide
  rcases family_descends (prefixWord ++ tailWord_967260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967295 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_967295 : Nat := 118140960795 + 967295 * 2 ^ 59
def prefixEnd_967295 : Nat := 4983230072969 + 3 ^ 40 * 967295 * 2
def baseEnd_967295 : Nat := 441499795280798388945775

theorem tailTrace_967295 : CollatzResearch.WordTrace tailWord_967295 prefixEnd_967295 441499795280798388945775 := by
  unfold tailWord_967295
  simp only [CollatzResearch.WordTrace]
  refine ⟨35280147030662890678799339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23520098020441927119199559 35280147030662890678799339)
  ·
    refine ⟨52920220545994336018199009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35280147030662890678799339 52920220545994336018199009)
    ·
      refine ⟨39690165409495752013649257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52920220545994336018199009 39690165409495752013649257)
      ·
        refine ⟨29767624057121814010236943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39690165409495752013649257 29767624057121814010236943)
        ·
          refine ⟨44651436085682721015355415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29767624057121814010236943 44651436085682721015355415)
          ·
            refine ⟨66977154128524081523033123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44651436085682721015355415 66977154128524081523033123)
            ·
              refine ⟨100465731192786122284549685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66977154128524081523033123 100465731192786122284549685)
              ·
                refine ⟨9418662299323698964176533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100465731192786122284549685 9418662299323698964176533)
                ·
                  refine ⟨441499795280798388945775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9418662299323698964176533 441499795280798388945775)
                  ·
                    rfl

theorem cell20_967295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_967295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967295 prefixEnd_967295 := by exact prefixLift 967295
  have htrace : WordTrace (prefixWord ++ tailWord_967295) baseStart_967295 baseEnd_967295 := by
    simpa [prefixWord, tailWord_967295, baseEnd_967295] using wordTrace_append hprefix tailTrace_967295
  have hstable : (prefixWord ++ tailWord_967295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967295).length < 2 ^ (prefixWord ++ tailWord_967295).sum := by decide
  have hdescent : baseEnd_967295 < baseStart_967295 := by decide
  rcases family_descends (prefixWord ++ tailWord_967295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967335 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 3]
def baseStart_967335 : Nat := 118140960795 + 967335 * 2 ^ 59
def prefixEnd_967335 : Nat := 4983230072969 + 3 ^ 40 * 967335 * 2
def baseEnd_967335 : Nat := 441518052370736027612279

theorem tailTrace_967335 : CollatzResearch.WordTrace tailWord_967335 prefixEnd_967335 441518052370736027612279 := by
  unfold tailWord_967335
  simp only [CollatzResearch.WordTrace]
  refine ⟨35281605950517977510255459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23521070633678651673503639 35281605950517977510255459)
  ·
    refine ⟨52922408925776966265383189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35281605950517977510255459 52922408925776966265383189)
    ·
      refine ⟨2480737918395795293689837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52922408925776966265383189 2480737918395795293689837)
      ·
        refine ⟨930276719398423235133689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2480737918395795293689837 930276719398423235133689)
        ·
          refine ⟨697707539548817426350267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930276719398423235133689 697707539548817426350267)
          ·
            refine ⟨1046561309323226139525401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697707539548817426350267 1046561309323226139525401)
            ·
              refine ⟨784920981992419604644051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046561309323226139525401 784920981992419604644051)
              ·
                refine ⟨1177381472988629406966077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784920981992419604644051 1177381472988629406966077)
                ·
                  refine ⟨441518052370736027612279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177381472988629406966077 441518052370736027612279)
                  ·
                    rfl

theorem cell20_967335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 3].length) (baseStart_967335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967335 prefixEnd_967335 := by exact prefixLift 967335
  have htrace : WordTrace (prefixWord ++ tailWord_967335) baseStart_967335 baseEnd_967335 := by
    simpa [prefixWord, tailWord_967335, baseEnd_967335] using wordTrace_append hprefix tailTrace_967335
  have hstable : (prefixWord ++ tailWord_967335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967335).length < 2 ^ (prefixWord ++ tailWord_967335).sum := by decide
  have hdescent : baseEnd_967335 < baseStart_967335 := by decide
  rcases family_descends (prefixWord ++ tailWord_967335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967343 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_967343 : Nat := 118140960795 + 967343 * 2 ^ 59
def prefixEnd_967343 : Nat := 4983230072969 + 3 ^ 40 * 967343 * 2
def baseEnd_967343 : Nat := 441521703788723555345579

theorem tailTrace_967343 : CollatzResearch.WordTrace tailWord_967343 prefixEnd_967343 441521703788723555345579 := by
  unfold tailWord_967343
  simp only [CollatzResearch.WordTrace]
  refine ⟨35281897734488994876546683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23521265156325996584364455 35281897734488994876546683)
  ·
    refine ⟨52922846601733492314820025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35281897734488994876546683 52922846601733492314820025)
    ·
      refine ⟨39692134951300119236115019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52922846601733492314820025 39692134951300119236115019)
      ·
        refine ⟨59538202426950178854172529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39692134951300119236115019 59538202426950178854172529)
        ·
          refine ⟨44653651820212634140629397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59538202426950178854172529 44653651820212634140629397)
          ·
            refine ⟨2093139929072467225342003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44653651820212634140629397 2093139929072467225342003)
            ·
              refine ⟨3139709893608700838013005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093139929072467225342003 3139709893608700838013005)
              ·
                refine ⟨1177391210103262814254877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3139709893608700838013005 1177391210103262814254877)
                ·
                  refine ⟨441521703788723555345579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177391210103262814254877 441521703788723555345579)
                  ·
                    rfl

theorem cell20_967343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_967343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967343 prefixEnd_967343 := by exact prefixLift 967343
  have htrace : WordTrace (prefixWord ++ tailWord_967343) baseStart_967343 baseEnd_967343 := by
    simpa [prefixWord, tailWord_967343, baseEnd_967343] using wordTrace_append hprefix tailTrace_967343
  have hstable : (prefixWord ++ tailWord_967343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967343).length < 2 ^ (prefixWord ++ tailWord_967343).sum := by decide
  have hdescent : baseEnd_967343 < baseStart_967343 := by decide
  rcases family_descends (prefixWord ++ tailWord_967343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967357 : List Nat := [1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_967357 : Nat := 118140960795 + 967357 * 2 ^ 59
def prefixEnd_967357 : Nat := 4983230072969 + 3 ^ 40 * 967357 * 2
def baseEnd_967357 : Nat := 147176031256733909626285

theorem tailTrace_967357 : CollatzResearch.WordTrace tailWord_967357 prefixEnd_967357 147176031256733909626285 := by
  unfold tailWord_967357
  simp only [CollatzResearch.WordTrace]
  refine ⟨35282408356438275267556325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23521605570958850178370883 35282408356438275267556325)
  ·
    refine ⟨6615451566832176612666811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35282408356438275267556325 6615451566832176612666811)
    ·
      refine ⟨9923177350248264919000217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615451566832176612666811 9923177350248264919000217)
      ·
        refine ⟨7442383012686198689250163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9923177350248264919000217 7442383012686198689250163)
        ·
          refine ⟨11163574519029298033875245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442383012686198689250163 11163574519029298033875245)
          ·
            refine ⟨4186340444635986762703217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11163574519029298033875245 4186340444635986762703217)
            ·
              refine ⟨3139755333476990072027413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186340444635986762703217 3139755333476990072027413)
              ·
                refine ⟨147176031256733909626285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3139755333476990072027413 147176031256733909626285)
                ·
                  rfl

theorem cell20_967357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_967357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967357 prefixEnd_967357 := by exact prefixLift 967357
  have htrace : WordTrace (prefixWord ++ tailWord_967357) baseStart_967357 baseEnd_967357 := by
    simpa [prefixWord, tailWord_967357, baseEnd_967357] using wordTrace_append hprefix tailTrace_967357
  have hstable : (prefixWord ++ tailWord_967357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967357).length < 2 ^ (prefixWord ++ tailWord_967357).sum := by decide
  have hdescent : baseEnd_967357 < baseStart_967357 := by decide
  rcases family_descends (prefixWord ++ tailWord_967357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967380 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 2]
def baseStart_967380 : Nat := 118140960795 + 967380 * 2 ^ 59
def prefixEnd_967380 : Nat := 4983230072969 + 3 ^ 40 * 967380 * 2
def baseEnd_967380 : Nat := 441538591596915871112095

theorem tailTrace_967380 : CollatzResearch.WordTrace tailWord_967380 prefixEnd_967380 441538591596915871112095 := by
  unfold tailWord_967380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641623617677475097821797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23522164823569966797095729 17641623617677475097821797)
  ·
    refine ⟨3307804428314526580841587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17641623617677475097821797 3307804428314526580841587)
    ·
      refine ⟨4961706642471789871262381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3307804428314526580841587 4961706642471789871262381)
      ·
        refine ⟨1860639990926921201723393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4961706642471789871262381 1860639990926921201723393)
        ·
          refine ⟨1395479993195190901292545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860639990926921201723393 1395479993195190901292545)
          ·
            refine ⟨1046609994896393175969409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395479993195190901292545 1046609994896393175969409)
            ·
              refine ⟨784957496172294881977057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046609994896393175969409 784957496172294881977057)
              ·
                refine ⟨588718122129221161482793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784957496172294881977057 588718122129221161482793)
                ·
                  refine ⟨441538591596915871112095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588718122129221161482793 441538591596915871112095)
                  ·
                    rfl

theorem cell20_967380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_967380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967380 prefixEnd_967380 := by exact prefixLift 967380
  have htrace : WordTrace (prefixWord ++ tailWord_967380) baseStart_967380 baseEnd_967380 := by
    simpa [prefixWord, tailWord_967380, baseEnd_967380] using wordTrace_append hprefix tailTrace_967380
  have hstable : (prefixWord ++ tailWord_967380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967380).length < 2 ^ (prefixWord ++ tailWord_967380).sum := by decide
  have hdescent : baseEnd_967380 < baseStart_967380 := by decide
  rcases family_descends (prefixWord ++ tailWord_967380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967384 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 2]
def baseStart_967384 : Nat := 118140960795 + 967384 * 2 ^ 59
def prefixEnd_967384 : Nat := 4983230072969 + 3 ^ 40 * 967384 * 2
def baseEnd_967384 : Nat := 441540417305909634978745

theorem tailTrace_967384 : CollatzResearch.WordTrace tailWord_967384 prefixEnd_967384 441540417305909634978745 := by
  unfold tailWord_967384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641696563670229439394603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23522262084893639252526137 17641696563670229439394603)
  ·
    refine ⟨26462544845505344159091905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17641696563670229439394603 26462544845505344159091905)
    ·
      refine ⟨19846908634129008119318929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26462544845505344159091905 19846908634129008119318929)
      ·
        refine ⟨14885181475596756089489197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19846908634129008119318929 14885181475596756089489197)
        ·
          refine ⟨5581943053348783533558449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14885181475596756089489197 5581943053348783533558449)
          ·
            refine ⟨4186457290011587650168837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5581943053348783533558449 4186457290011587650168837)
            ·
              refine ⟨784960741877172684406657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4186457290011587650168837 784960741877172684406657)
              ·
                refine ⟨588720556407879513304993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784960741877172684406657 588720556407879513304993)
                ·
                  refine ⟨441540417305909634978745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588720556407879513304993 441540417305909634978745)
                  ·
                    rfl

theorem cell20_967384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_967384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967384 prefixEnd_967384 := by exact prefixLift 967384
  have htrace : WordTrace (prefixWord ++ tailWord_967384) baseStart_967384 baseEnd_967384 := by
    simpa [prefixWord, tailWord_967384, baseEnd_967384] using wordTrace_append hprefix tailTrace_967384
  have hstable : (prefixWord ++ tailWord_967384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967384).length < 2 ^ (prefixWord ++ tailWord_967384).sum := by decide
  have hdescent : baseEnd_967384 < baseStart_967384 := by decide
  rcases family_descends (prefixWord ++ tailWord_967384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967402 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_967402 : Nat := 118140960795 + 967402 * 2 ^ 59
def prefixEnd_967402 : Nat := 4983230072969 + 3 ^ 40 * 967402 * 2
def baseEnd_967402 : Nat := 441548632996381572378671

theorem tailTrace_967402 : CollatzResearch.WordTrace tailWord_967402 prefixEnd_967402 441548632996381572378671 := by
  unfold tailWord_967402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8821012410318811988236115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23522699760850165301962973 8821012410318811988236115)
  ·
    refine ⟨13231518615478217982354173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8821012410318811988236115 13231518615478217982354173)
    ·
      refine ⟨4961819480804331743382815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13231518615478217982354173 4961819480804331743382815)
      ·
        refine ⟨7442729221206497615074223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4961819480804331743382815 7442729221206497615074223)
        ·
          refine ⟨11164093831809746422611335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442729221206497615074223 11164093831809746422611335)
          ·
            refine ⟨16746140747714619633917003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164093831809746422611335 16746140747714619633917003)
            ·
              refine ⟨25119211121571929450875505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16746140747714619633917003 25119211121571929450875505)
              ·
                refine ⟨18839408341178947088156629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25119211121571929450875505 18839408341178947088156629)
                ·
                  refine ⟨441548632996381572378671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18839408341178947088156629 441548632996381572378671)
                  ·
                    rfl

theorem cell20_967402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_967402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967402 prefixEnd_967402 := by exact prefixLift 967402
  have htrace : WordTrace (prefixWord ++ tailWord_967402) baseStart_967402 baseEnd_967402 := by
    simpa [prefixWord, tailWord_967402, baseEnd_967402] using wordTrace_append hprefix tailTrace_967402
  have hstable : (prefixWord ++ tailWord_967402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967402).length < 2 ^ (prefixWord ++ tailWord_967402).sum := by decide
  have hdescent : baseEnd_967402 < baseStart_967402 := by decide
  rcases family_descends (prefixWord ++ tailWord_967402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967422 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_967422 : Nat := 118140960795 + 967422 * 2 ^ 59
def prefixEnd_967422 : Nat := 4983230072969 + 3 ^ 40 * 967422 * 2
def baseEnd_967422 : Nat := 441557761541350391711923

theorem tailTrace_967422 : CollatzResearch.WordTrace tailWord_967422 prefixEnd_967422 441557761541350391711923 := by
  unfold tailWord_967422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410597387650348921084065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23523186067468527579115013 4410597387650348921084065)
  ·
    refine ⟨3307948040737761690813049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4410597387650348921084065 3307948040737761690813049)
    ·
      refine ⟨2480961030553321268109787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3307948040737761690813049 2480961030553321268109787)
      ·
        refine ⟨3721441545829981902164681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480961030553321268109787 3721441545829981902164681)
        ·
          refine ⟨2791081159372486426623511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721441545829981902164681 2791081159372486426623511)
          ·
            refine ⟨4186621739058729639935267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791081159372486426623511 4186621739058729639935267)
            ·
              refine ⟨6279932608588094459902901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186621739058729639935267 6279932608588094459902901)
              ·
                refine ⟨588743682055133855615897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6279932608588094459902901 588743682055133855615897)
                ·
                  refine ⟨441557761541350391711923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588743682055133855615897 441557761541350391711923)
                  ·
                    rfl

theorem cell20_967422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_967422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967422 prefixEnd_967422 := by exact prefixLift 967422
  have htrace : WordTrace (prefixWord ++ tailWord_967422) baseStart_967422 baseEnd_967422 := by
    simpa [prefixWord, tailWord_967422, baseEnd_967422] using wordTrace_append hprefix tailTrace_967422
  have hstable : (prefixWord ++ tailWord_967422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967422).length < 2 ^ (prefixWord ++ tailWord_967422).sum := by decide
  have hdescent : baseEnd_967422 < baseStart_967422 := by decide
  rcases family_descends (prefixWord ++ tailWord_967422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967464 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_967464 : Nat := 118140960795 + 967464 * 2 ^ 59
def prefixEnd_967464 : Nat := 4983230072969 + 3 ^ 40 * 967464 * 2
def baseEnd_967464 : Nat := 441576931485784912311751

theorem tailTrace_967464 : CollatzResearch.WordTrace tailWord_967464 prefixEnd_967464 441576931485784912311751 := by
  unfold tailWord_967464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643155483525316270850723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23524207311367088361134297 17643155483525316270850723)
  ·
    refine ⟨26464733225287974406276085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17643155483525316270850723 26464733225287974406276085)
    ·
      refine ⟨2481068739870747600588383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26464733225287974406276085 2481068739870747600588383)
      ·
        refine ⟨3721603109806121400882575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481068739870747600588383 3721603109806121400882575)
        ·
          refine ⟨5582404664709182101323863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721603109806121400882575 5582404664709182101323863)
          ·
            refine ⟨8373606997063773151985795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582404664709182101323863 8373606997063773151985795)
            ·
              refine ⟨12560410495595659727978693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373606997063773151985795 12560410495595659727978693)
              ·
                refine ⟨2355076967924186198996005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12560410495595659727978693 2355076967924186198996005)
                ·
                  refine ⟨441576931485784912311751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355076967924186198996005 441576931485784912311751)
                  ·
                    rfl

theorem cell20_967464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_967464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967464 prefixEnd_967464 := by exact prefixLift 967464
  have htrace : WordTrace (prefixWord ++ tailWord_967464) baseStart_967464 baseEnd_967464 := by
    simpa [prefixWord, tailWord_967464, baseEnd_967464] using wordTrace_append hprefix tailTrace_967464
  have hstable : (prefixWord ++ tailWord_967464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967464).length < 2 ^ (prefixWord ++ tailWord_967464).sum := by decide
  have hdescent : baseEnd_967464 < baseStart_967464 := by decide
  rcases family_descends (prefixWord ++ tailWord_967464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967494 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_967494 : Nat := 118140960795 + 967494 * 2 ^ 59
def prefixEnd_967494 : Nat := 4983230072969 + 3 ^ 40 * 967494 * 2
def baseEnd_967494 : Nat := 441590624303238141311629

theorem tailTrace_967494 : CollatzResearch.WordTrace tailWord_967494 prefixEnd_967494 441590624303238141311629 := by
  unfold tailWord_967494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102731411154435864540423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23524936771294631776862357 1102731411154435864540423)
  ·
    refine ⟨1654097116731653796810635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102731411154435864540423 1654097116731653796810635)
    ·
      refine ⟨2481145675097480695215953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654097116731653796810635 2481145675097480695215953)
      ·
        refine ⟨1860859256323110521411965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2481145675097480695215953 1860859256323110521411965)
        ·
          refine ⟨697822221121166445529487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1860859256323110521411965 697822221121166445529487)
          ·
            refine ⟨1046733331681749668294231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697822221121166445529487 1046733331681749668294231)
            ·
              refine ⟨1570099997522624502441347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046733331681749668294231 1570099997522624502441347)
              ·
                refine ⟨2355149996283936753662021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570099997522624502441347 2355149996283936753662021)
                ·
                  refine ⟨441590624303238141311629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355149996283936753662021 441590624303238141311629)
                  ·
                    rfl

theorem cell20_967494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_967494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967494 prefixEnd_967494 := by exact prefixLift 967494
  have htrace : WordTrace (prefixWord ++ tailWord_967494) baseStart_967494 baseEnd_967494 := by
    simpa [prefixWord, tailWord_967494, baseEnd_967494] using wordTrace_append hprefix tailTrace_967494
  have hstable : (prefixWord ++ tailWord_967494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967494).length < 2 ^ (prefixWord ++ tailWord_967494).sum := by decide
  have hdescent : baseEnd_967494 < baseStart_967494 := by decide
  rcases family_descends (prefixWord ++ tailWord_967494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967508 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 3]
def baseStart_967508 : Nat := 118140960795 + 967508 * 2 ^ 59
def prefixEnd_967508 : Nat := 4983230072969 + 3 ^ 40 * 967508 * 2
def baseEnd_967508 : Nat := 441597014284716314844905

theorem tailTrace_967508 : CollatzResearch.WordTrace tailWord_967508 prefixEnd_967508 441597014284716314844905 := by
  unfold tailWord_967508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643957889445614028151589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23525277185927485370868785 17643957889445614028151589)
  ·
    refine ⟨3308242104271052630278423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17643957889445614028151589 3308242104271052630278423)
    ·
      refine ⟨4962363156406578945417635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308242104271052630278423 4962363156406578945417635)
      ·
        refine ⟨7443544734609868418126453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962363156406578945417635 7443544734609868418126453)
        ·
          refine ⟨697832318869675164199355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7443544734609868418126453 697832318869675164199355)
          ·
            refine ⟨1046748478304512746299033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697832318869675164199355 1046748478304512746299033)
            ·
              refine ⟨785061358728384559724275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046748478304512746299033 785061358728384559724275)
              ·
                refine ⟨1177592038092576839586413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785061358728384559724275 1177592038092576839586413)
                ·
                  refine ⟨441597014284716314844905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177592038092576839586413 441597014284716314844905)
                  ·
                    rfl

theorem cell20_967508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_967508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967508 prefixEnd_967508 := by exact prefixLift 967508
  have htrace : WordTrace (prefixWord ++ tailWord_967508) baseStart_967508 baseEnd_967508 := by
    simpa [prefixWord, tailWord_967508, baseEnd_967508] using wordTrace_append hprefix tailTrace_967508
  have hstable : (prefixWord ++ tailWord_967508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967508).length < 2 ^ (prefixWord ++ tailWord_967508).sum := by decide
  have hdescent : baseEnd_967508 < baseStart_967508 := by decide
  rcases family_descends (prefixWord ++ tailWord_967508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967509 : List Nat := [1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_967509 : Nat := 118140960795 + 967509 * 2 ^ 59
def prefixEnd_967509 : Nat := 4983230072969 + 3 ^ 40 * 967509 * 2
def baseEnd_967509 : Nat := 147199156903988251937189

theorem tailTrace_967509 : CollatzResearch.WordTrace tailWord_967509 prefixEnd_967509 147199156903988251937189 := by
  unfold tailWord_967509
  simp only [CollatzResearch.WordTrace]
  refine ⟨35287952251887605227089581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23525301501258403484726387 35287952251887605227089581)
  ·
    refine ⟨13232982094457851960158593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35287952251887605227089581 13232982094457851960158593)
    ·
      refine ⟨9924736570843388970118945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13232982094457851960158593 9924736570843388970118945)
      ·
        refine ⟨7443552428132541727589209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9924736570843388970118945 7443552428132541727589209)
        ·
          refine ⟨5582664321099406295691907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7443552428132541727589209 5582664321099406295691907)
          ·
            refine ⟨8373996481649109443537861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582664321099406295691907 8373996481649109443537861)
            ·
              refine ⟨1570124340309208020663349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8373996481649109443537861 1570124340309208020663349)
              ·
                refine ⟨147199156903988251937189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1570124340309208020663349 147199156903988251937189)
                ·
                  rfl

theorem cell20_967509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_967509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967509 prefixEnd_967509 := by exact prefixLift 967509
  have htrace : WordTrace (prefixWord ++ tailWord_967509) baseStart_967509 baseEnd_967509 := by
    simpa [prefixWord, tailWord_967509, baseEnd_967509] using wordTrace_append hprefix tailTrace_967509
  have hstable : (prefixWord ++ tailWord_967509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967509).length < 2 ^ (prefixWord ++ tailWord_967509).sum := by decide
  have hdescent : baseEnd_967509 < baseStart_967509 := by decide
  rcases family_descends (prefixWord ++ tailWord_967509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967557 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 2]
def baseStart_967557 : Nat := 118140960795 + 967557 * 2 ^ 59
def prefixEnd_967557 : Nat := 4983230072969 + 3 ^ 40 * 967557 * 2
def baseEnd_967557 : Nat := 441619379219889922211371

theorem tailTrace_967557 : CollatzResearch.WordTrace tailWord_967557 prefixEnd_967557 441619379219889922211371 := by
  unfold tailWord_967557
  simp only [CollatzResearch.WordTrace]
  refine ⟨35289702955713709424836925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23526468637142472949891283 35289702955713709424836925)
  ·
    refine ⟨13233638608392641034313847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35289702955713709424836925 13233638608392641034313847)
    ·
      refine ⟨19850457912588961551470771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13233638608392641034313847 19850457912588961551470771)
      ·
        refine ⟨29775686868883442327206157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19850457912588961551470771 29775686868883442327206157)
        ·
          refine ⟨11165882575831290872702309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29775686868883442327206157 11165882575831290872702309)
          ·
            refine ⟨2093602982968367038631683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11165882575831290872702309 2093602982968367038631683)
            ·
              refine ⟨3140404474452550557947525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093602982968367038631683 3140404474452550557947525)
              ·
                refine ⟨588825838959853229615161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3140404474452550557947525 588825838959853229615161)
                ·
                  refine ⟨441619379219889922211371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588825838959853229615161 441619379219889922211371)
                  ·
                    rfl

theorem cell20_967557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_967557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967557 prefixEnd_967557 := by exact prefixLift 967557
  have htrace : WordTrace (prefixWord ++ tailWord_967557) baseStart_967557 baseEnd_967557 := by
    simpa [prefixWord, tailWord_967557, baseEnd_967557] using wordTrace_append hprefix tailTrace_967557
  have hstable : (prefixWord ++ tailWord_967557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967557).length < 2 ^ (prefixWord ++ tailWord_967557).sum := by decide
  have hdescent : baseEnd_967557 < baseStart_967557 := by decide
  rcases family_descends (prefixWord ++ tailWord_967557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967574 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_967574 : Nat := 118140960795 + 967574 * 2 ^ 59
def prefixEnd_967574 : Nat := 4983230072969 + 3 ^ 40 * 967574 * 2
def baseEnd_967574 : Nat := 441627138483113418644635

theorem tailTrace_967574 : CollatzResearch.WordTrace tailWord_967574 prefixEnd_967574 441627138483113418644635 := by
  unfold tailWord_967574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205645187290757583012861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23526881997768080885470517 2205645187290757583012861)
  ·
    refine ⟨827116945234034093629823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2205645187290757583012861 827116945234034093629823)
    ·
      refine ⟨1240675417851051140444735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827116945234034093629823 1240675417851051140444735)
      ·
        refine ⟨1861013126776576710667103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240675417851051140444735 1861013126776576710667103)
        ·
          refine ⟨2791519690164865066000655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861013126776576710667103 2791519690164865066000655)
          ·
            refine ⟨4187279535247297599000983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791519690164865066000655 4187279535247297599000983)
            ·
              refine ⟨6280919302870946398501475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187279535247297599000983 6280919302870946398501475)
              ·
                refine ⟨9421378954306419597752213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280919302870946398501475 9421378954306419597752213)
                ·
                  refine ⟨441627138483113418644635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9421378954306419597752213 441627138483113418644635)
                  ·
                    rfl

theorem cell20_967574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_967574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967574 prefixEnd_967574 := by exact prefixLift 967574
  have htrace : WordTrace (prefixWord ++ tailWord_967574) baseStart_967574 baseEnd_967574 := by
    simpa [prefixWord, tailWord_967574, baseEnd_967574] using wordTrace_append hprefix tailTrace_967574
  have hstable : (prefixWord ++ tailWord_967574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967574).length < 2 ^ (prefixWord ++ tailWord_967574).sum := by decide
  have hdescent : baseEnd_967574 < baseStart_967574 := by decide
  rcases family_descends (prefixWord ++ tailWord_967574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967609 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_967609 : Nat := 118140960795 + 967609 * 2 ^ 59
def prefixEnd_967609 : Nat := 4983230072969 + 3 ^ 40 * 967609 * 2
def baseEnd_967609 : Nat := 441643113436808852477825

theorem tailTrace_967609 : CollatzResearch.WordTrace tailWord_967609 prefixEnd_967609 441643113436808852477825 := by
  unfold tailWord_967609
  simp only [CollatzResearch.WordTrace]
  refine ⟨35291599551525322305729881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23527733034350214870486587 35291599551525322305729881)
  ·
    refine ⟨26468699663643991729297411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35291599551525322305729881 26468699663643991729297411)
    ·
      refine ⟨39703049495465987593946117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26468699663643991729297411 39703049495465987593946117)
      ·
        refine ⟨7444321780399872673864897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39703049495465987593946117 7444321780399872673864897)
        ·
          refine ⟨5583241335299904505398673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7444321780399872673864897 5583241335299904505398673)
          ·
            refine ⟨4187431001474928379049005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5583241335299904505398673 4187431001474928379049005)
            ·
              refine ⟨1570286625553098142143377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4187431001474928379049005 1570286625553098142143377)
              ·
                refine ⟨1177714969164823606607533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570286625553098142143377 1177714969164823606607533)
                ·
                  refine ⟨441643113436808852477825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177714969164823606607533 441643113436808852477825)
                  ·
                    rfl

theorem cell20_967609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_967609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967609 prefixEnd_967609 := by exact prefixLift 967609
  have htrace : WordTrace (prefixWord ++ tailWord_967609) baseStart_967609 baseEnd_967609 := by
    simpa [prefixWord, tailWord_967609, baseEnd_967609] using wordTrace_append hprefix tailTrace_967609
  have hstable : (prefixWord ++ tailWord_967609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967609).length < 2 ^ (prefixWord ++ tailWord_967609).sum := by decide
  have hdescent : baseEnd_967609 < baseStart_967609 := by decide
  rcases family_descends (prefixWord ++ tailWord_967609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967616 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_967616 : Nat := 118140960795 + 967616 * 2 ^ 59
def prefixEnd_967616 : Nat := 4983230072969 + 3 ^ 40 * 967616 * 2
def baseEnd_967616 : Nat := 441646308427547939244463

theorem tailTrace_967616 : CollatzResearch.WordTrace tailWord_967616 prefixEnd_967616 441646308427547939244463 := by
  unfold tailWord_967616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17645927431249981250617351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23527903241666641667489801 17645927431249981250617351)
  ·
    refine ⟨26468891146874971875926027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17645927431249981250617351 26468891146874971875926027)
    ·
      refine ⟨39703336720312457813889041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26468891146874971875926027 39703336720312457813889041)
      ·
        refine ⟨29777502540234343360416781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39703336720312457813889041 29777502540234343360416781)
        ·
          refine ⟨11166563452587878760156293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29777502540234343360416781 11166563452587878760156293)
          ·
            refine ⟨2093730647360227267529305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11166563452587878760156293 2093730647360227267529305)
            ·
              refine ⟨1570297985520170450646979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093730647360227267529305 1570297985520170450646979)
              ·
                refine ⟨2355446978280255675970469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570297985520170450646979 2355446978280255675970469)
                ·
                  refine ⟨441646308427547939244463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355446978280255675970469 441646308427547939244463)
                  ·
                    rfl

theorem cell20_967616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_967616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967616 prefixEnd_967616 := by exact prefixLift 967616
  have htrace : WordTrace (prefixWord ++ tailWord_967616) baseStart_967616 baseEnd_967616 := by
    simpa [prefixWord, tailWord_967616, baseEnd_967616] using wordTrace_append hprefix tailTrace_967616
  have hstable : (prefixWord ++ tailWord_967616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967616).length < 2 ^ (prefixWord ++ tailWord_967616).sum := by decide
  have hdescent : baseEnd_967616 < baseStart_967616 := by decide
  rcases family_descends (prefixWord ++ tailWord_967616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967640 : List Nat := [2, 1, 2, 2, 2, 5, 2, 4]
def baseStart_967640 : Nat := 118140960795 + 967640 * 2 ^ 59
def prefixEnd_967640 : Nat := 4983230072969 + 3 ^ 40 * 967640 * 2
def baseEnd_967640 : Nat := 147219087560503507481455

theorem tailTrace_967640 : CollatzResearch.WordTrace tailWord_967640 prefixEnd_967640 147219087560503507481455 := by
  unfold tailWord_967640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646365107206507300054187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23528486809608676400072249 17646365107206507300054187)
  ·
    refine ⟨26469547660809760950081281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17646365107206507300054187 26469547660809760950081281)
    ·
      refine ⟨19852160745607320712560961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26469547660809760950081281 19852160745607320712560961)
      ·
        refine ⟨14889120559205490534420721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19852160745607320712560961 14889120559205490534420721)
        ·
          refine ⟨11166840419404117900815541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14889120559205490534420721 11166840419404117900815541)
          ·
            refine ⟨1046891289319136053201457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11166840419404117900815541 1046891289319136053201457)
            ·
              refine ⟨785168466989352039901093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046891289319136053201457 785168466989352039901093)
              ·
                refine ⟨147219087560503507481455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785168466989352039901093 147219087560503507481455)
                ·
                  rfl

theorem cell20_967640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_967640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967640 prefixEnd_967640 := by exact prefixLift 967640
  have htrace : WordTrace (prefixWord ++ tailWord_967640) baseStart_967640 baseEnd_967640 := by
    simpa [prefixWord, tailWord_967640, baseEnd_967640] using wordTrace_append hprefix tailTrace_967640
  have hstable : (prefixWord ++ tailWord_967640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967640).length < 2 ^ (prefixWord ++ tailWord_967640).sum := by decide
  have hdescent : baseEnd_967640 < baseStart_967640 := by decide
  rcases family_descends (prefixWord ++ tailWord_967640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967720 : List Nat := [2, 1, 5, 12]
def baseStart_967720 : Nat := 118140960795 + 967720 * 2 ^ 59
def prefixEnd_967720 : Nat := 4983230072969 + 3 ^ 40 * 967720 * 2
def baseEnd_967720 : Nat := 1817669863627102056697

theorem tailTrace_967720 : CollatzResearch.WordTrace tailWord_967720 prefixEnd_967720 1817669863627102056697 := by
  unfold tailWord_967720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647824027061594131510307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23530432036082125508680409 17647824027061594131510307)
  ·
    refine ⟨26471736040592391197265461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17647824027061594131510307 26471736040592391197265461)
    ·
      refine ⟨2481725253805536674743637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26471736040592391197265461 2481725253805536674743637)
      ·
        refine ⟨1817669863627102056697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2481725253805536674743637 1817669863627102056697)
        ·
          rfl

theorem cell20_967720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 12].length) (baseStart_967720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967720 prefixEnd_967720 := by exact prefixLift 967720
  have htrace : WordTrace (prefixWord ++ tailWord_967720) baseStart_967720 baseEnd_967720 := by
    simpa [prefixWord, tailWord_967720, baseEnd_967720] using wordTrace_append hprefix tailTrace_967720
  have hstable : (prefixWord ++ tailWord_967720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967720).length < 2 ^ (prefixWord ++ tailWord_967720).sum := by decide
  have hdescent : baseEnd_967720 < baseStart_967720 := by decide
  rcases family_descends (prefixWord ++ tailWord_967720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967722 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_967722 : Nat := 118140960795 + 967722 * 2 ^ 59
def prefixEnd_967722 : Nat := 4983230072969 + 3 ^ 40 * 967722 * 2
def baseEnd_967722 : Nat := 441694689715882681710697

theorem tailTrace_967722 : CollatzResearch.WordTrace tailWord_967722 prefixEnd_967722 441694689715882681710697 := by
  unfold tailWord_967722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823930250028985651148355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23530480666743961736395613 8823930250028985651148355)
  ·
    refine ⟨13235895375043478476722533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8823930250028985651148355 13235895375043478476722533)
    ·
      refine ⟨2481730382820652214385475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13235895375043478476722533 2481730382820652214385475)
      ·
        refine ⟨3722595574230978321578213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481730382820652214385475 3722595574230978321578213)
        ·
          refine ⟨697986670168308435295915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3722595574230978321578213 697986670168308435295915)
          ·
            refine ⟨1046980005252462652943873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697986670168308435295915 1046980005252462652943873)
            ·
              refine ⟨785235003939346989707905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046980005252462652943873 785235003939346989707905)
              ·
                refine ⟨588926252954510242280929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785235003939346989707905 588926252954510242280929)
                ·
                  refine ⟨441694689715882681710697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588926252954510242280929 441694689715882681710697)
                  ·
                    rfl

theorem cell20_967722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_967722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967722 prefixEnd_967722 := by exact prefixLift 967722
  have htrace : WordTrace (prefixWord ++ tailWord_967722) baseStart_967722 baseEnd_967722 := by
    simpa [prefixWord, tailWord_967722, baseEnd_967722] using wordTrace_append hprefix tailTrace_967722
  have hstable : (prefixWord ++ tailWord_967722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967722).length < 2 ^ (prefixWord ++ tailWord_967722).sum := by decide
  have hdescent : baseEnd_967722 < baseStart_967722 := by decide
  rcases family_descends (prefixWord ++ tailWord_967722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967727 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_967727 : Nat := 118140960795 + 967727 * 2 ^ 59
def prefixEnd_967727 : Nat := 4983230072969 + 3 ^ 40 * 967727 * 2
def baseEnd_967727 : Nat := 441696971852124886544009

theorem tailTrace_967727 : CollatzResearch.WordTrace tailWord_967727 prefixEnd_967727 441696971852124886544009 := by
  unfold tailWord_967727
  simp only [CollatzResearch.WordTrace]
  refine ⟨35295903365097828458525435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23530602243398552305683623 35295903365097828458525435)
  ·
    refine ⟨52943855047646742687788153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35295903365097828458525435 52943855047646742687788153)
    ·
      refine ⟨39707891285735057015841115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52943855047646742687788153 39707891285735057015841115)
      ·
        refine ⟨59561836928602585523761673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39707891285735057015841115 59561836928602585523761673)
        ·
          refine ⟨44671377696451939142821255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59561836928602585523761673 44671377696451939142821255)
          ·
            refine ⟨67007066544677908714231883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44671377696451939142821255 67007066544677908714231883)
            ·
              refine ⟨100510599817016863071347825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67007066544677908714231883 100510599817016863071347825)
              ·
                refine ⟨75382949862762647303510869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100510599817016863071347825 75382949862762647303510869)
                ·
                  refine ⟨441696971852124886544009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75382949862762647303510869 441696971852124886544009)
                  ·
                    rfl

theorem cell20_967727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_967727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967727 prefixEnd_967727 := by exact prefixLift 967727
  have htrace : WordTrace (prefixWord ++ tailWord_967727) baseStart_967727 baseEnd_967727 := by
    simpa [prefixWord, tailWord_967727, baseEnd_967727] using wordTrace_append hprefix tailTrace_967727
  have hstable : (prefixWord ++ tailWord_967727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967727).length < 2 ^ (prefixWord ++ tailWord_967727).sum := by decide
  have hdescent : baseEnd_967727 < baseStart_967727 := by decide
  rcases family_descends (prefixWord ++ tailWord_967727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967737 : List Nat := [1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_967737 : Nat := 118140960795 + 967737 * 2 ^ 59
def prefixEnd_967737 : Nat := 4983230072969 + 3 ^ 40 * 967737 * 2
def baseEnd_967737 : Nat := 147233845374869765403545

theorem tailTrace_967737 : CollatzResearch.WordTrace tailWord_967737 prefixEnd_967737 147233845374869765403545 := by
  unfold tailWord_967737
  simp only [CollatzResearch.WordTrace]
  refine ⟨35296268095061600166389465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23530845396707733444259643 35296268095061600166389465)
  ·
    refine ⟨26472201071296200124792099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35296268095061600166389465 26472201071296200124792099)
    ·
      refine ⟨39708301606944300187188149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26472201071296200124792099 39708301606944300187188149)
      ·
        refine ⟨3722653275651028142548889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39708301606944300187188149 3722653275651028142548889)
        ·
          refine ⟨2791989956738271106911667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3722653275651028142548889 2791989956738271106911667)
          ·
            refine ⟨4187984935107406660367501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791989956738271106911667 4187984935107406660367501)
            ·
              refine ⟨1570494350665277497637813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4187984935107406660367501 1570494350665277497637813)
              ·
                refine ⟨147233845374869765403545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1570494350665277497637813 147233845374869765403545)
                ·
                  rfl

theorem cell20_967737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_967737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967737 prefixEnd_967737 := by exact prefixLift 967737
  have htrace : WordTrace (prefixWord ++ tailWord_967737) baseStart_967737 baseEnd_967737 := by
    simpa [prefixWord, tailWord_967737, baseEnd_967737] using wordTrace_append hprefix tailTrace_967737
  have hstable : (prefixWord ++ tailWord_967737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967737).length < 2 ^ (prefixWord ++ tailWord_967737).sum := by decide
  have hdescent : baseEnd_967737 < baseStart_967737 := by decide
  rcases family_descends (prefixWord ++ tailWord_967737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967744 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_967744 : Nat := 118140960795 + 967744 * 2 ^ 59
def prefixEnd_967744 : Nat := 4983230072969 + 3 ^ 40 * 967744 * 2
def baseEnd_967744 : Nat := 441704731115348382977273

theorem tailTrace_967744 : CollatzResearch.WordTrace tailWord_967744 prefixEnd_967744 441704731115348382977273 := by
  unfold tailWord_967744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648261703018120180947143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23531015604024160241262857 17648261703018120180947143)
  ·
    refine ⟨26472392554527180271420715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17648261703018120180947143 26472392554527180271420715)
    ·
      refine ⟨39708588831790770407131073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26472392554527180271420715 39708588831790770407131073)
      ·
        refine ⟨29781441623843077805348305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39708588831790770407131073 29781441623843077805348305)
        ·
          refine ⟨22336081217882308354011229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29781441623843077805348305 22336081217882308354011229)
          ·
            refine ⟨8376030456705865632754211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22336081217882308354011229 8376030456705865632754211)
            ·
              refine ⟨12564045685058798449131317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376030456705865632754211 12564045685058798449131317)
              ·
                refine ⟨1177879282974262354606061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12564045685058798449131317 1177879282974262354606061)
                ·
                  refine ⟨441704731115348382977273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177879282974262354606061 441704731115348382977273)
                  ·
                    rfl

theorem cell20_967744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_967744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967744 prefixEnd_967744 := by exact prefixLift 967744
  have htrace : WordTrace (prefixWord ++ tailWord_967744) baseStart_967744 baseEnd_967744 := by
    simpa [prefixWord, tailWord_967744, baseEnd_967744] using wordTrace_append hprefix tailTrace_967744
  have hstable : (prefixWord ++ tailWord_967744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967744).length < 2 ^ (prefixWord ++ tailWord_967744).sum := by decide
  have hdescent : baseEnd_967744 < baseStart_967744 := by decide
  rcases family_descends (prefixWord ++ tailWord_967744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
