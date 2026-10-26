import V185TrunkScan22Chunk217

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1942795 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 1, 4]
def baseStart_1942795 : Nat := 118140960795 + 1942795 * 2 ^ 59
def prefixEnd_1942795 : Nat := 4983230072969 + 3 ^ 40 * 1942795 * 2
def baseEnd_1942795 : Nat := 665058432101221026218503

theorem tailTrace_1942795 : CollatzResearch.WordTrace tailWord_1942795 prefixEnd_1942795 665058432101221026218503 := by
  unfold tailWord_1942795
  simp only [CollatzResearch.WordTrace]
  refine ⟨70859554996592992814925839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47239703331061995209950559 70859554996592992814925839)
  ·
    refine ⟨106289332494889489222388759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70859554996592992814925839 106289332494889489222388759)
    ·
      refine ⟨159433998742334233833583139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106289332494889489222388759 159433998742334233833583139)
      ·
        refine ⟨239150998113501350750374709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159433998742334233833583139 239150998113501350750374709)
        ·
          refine ⟨22420406073140751632847629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239150998113501350750374709 22420406073140751632847629)
          ·
            refine ⟨8407652277427781862317861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22420406073140751632847629 8407652277427781862317861)
            ·
              refine ⟨1576434802017709099184599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8407652277427781862317861 1576434802017709099184599)
              ·
                refine ⟨2364652203026563648776899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576434802017709099184599 2364652203026563648776899)
                ·
                  refine ⟨3546978304539845473165349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364652203026563648776899 3546978304539845473165349)
                  ·
                    refine ⟨665058432101221026218503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3546978304539845473165349 665058432101221026218503)
                    ·
                      rfl

theorem cell22_1942795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 4].length) (baseStart_1942795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942795 prefixEnd_1942795 := by exact prefixLift 1942795
  have htrace : WordTrace (prefixWord ++ tailWord_1942795) baseStart_1942795 baseEnd_1942795 := by
    simpa [prefixWord, tailWord_1942795, baseEnd_1942795] using wordTrace_append hprefix tailTrace_1942795
  have hstable : (prefixWord ++ tailWord_1942795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942795).length < 2 ^ (prefixWord ++ tailWord_1942795).sum := by decide
  have hdescent : baseEnd_1942795 < baseStart_1942795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942810 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_1942810 : Nat := 118140960795 + 1942810 * 2 ^ 59
def prefixEnd_1942810 : Nat := 4983230072969 + 3 ^ 40 * 1942810 * 2
def baseEnd_1942810 : Nat := 221687855635921995697819

theorem tailTrace_1942810 : CollatzResearch.WordTrace tailWord_1942810 prefixEnd_1942810 221687855635921995697819 := by
  unfold tailWord_1942810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17715025522884662594180471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47240068061025766917814589 17715025522884662594180471)
  ·
    refine ⟨26572538284326993891270707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17715025522884662594180471 26572538284326993891270707)
    ·
      refine ⟨39858807426490490836906061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26572538284326993891270707 39858807426490490836906061)
      ·
        refine ⟨14947052784933934063839773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39858807426490490836906061 14947052784933934063839773)
        ·
          refine ⟨5605144794350225273939915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14947052784933934063839773 5605144794350225273939915)
          ·
            refine ⟨8407717191525337910909873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5605144794350225273939915 8407717191525337910909873)
            ·
              refine ⟨6305787893644003433182405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407717191525337910909873 6305787893644003433182405)
              ·
                refine ⟨1182335230058250643721701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6305787893644003433182405 1182335230058250643721701)
                ·
                  refine ⟨221687855635921995697819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182335230058250643721701 221687855635921995697819)
                  ·
                    rfl

theorem cell22_1942810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_1942810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942810 prefixEnd_1942810 := by exact prefixLift 1942810
  have htrace : WordTrace (prefixWord ++ tailWord_1942810) baseStart_1942810 baseEnd_1942810 := by
    simpa [prefixWord, tailWord_1942810, baseEnd_1942810] using wordTrace_append hprefix tailTrace_1942810
  have hstable : (prefixWord ++ tailWord_1942810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942810).length < 2 ^ (prefixWord ++ tailWord_1942810).sum := by decide
  have hdescent : baseEnd_1942810 < baseStart_1942810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942851 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_1942851 : Nat := 118140960795 + 1942851 * 2 ^ 59
def prefixEnd_1942851 : Nat := 4983230072969 + 3 ^ 40 * 1942851 * 2
def baseEnd_1942851 : Nat := 665077602045655546818331

theorem tailTrace_1942851 : CollatzResearch.WordTrace tailWord_1942851 prefixEnd_1942851 665077602045655546818331 := by
  unfold tailWord_1942851
  simp only [CollatzResearch.WordTrace]
  refine ⟨70861597484390114378964407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47241064989593409585976271 70861597484390114378964407)
  ·
    refine ⟨106292396226585171568446611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70861597484390114378964407 106292396226585171568446611)
    ·
      refine ⟨159438594339877757352669917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106292396226585171568446611 159438594339877757352669917)
      ·
        refine ⟨59789472877454159007251219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159438594339877757352669917 59789472877454159007251219)
        ·
          refine ⟨89684209316181238510876829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59789472877454159007251219 89684209316181238510876829)
          ·
            refine ⟨33631578493567964441578811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89684209316181238510876829 33631578493567964441578811)
            ·
              refine ⟨50447367740351946662368217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33631578493567964441578811 50447367740351946662368217)
              ·
                refine ⟨37835525805263959996776163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50447367740351946662368217 37835525805263959996776163)
                ·
                  refine ⟨56753288707895939995164245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37835525805263959996776163 56753288707895939995164245)
                  ·
                    refine ⟨665077602045655546818331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56753288707895939995164245 665077602045655546818331)
                    ·
                      rfl

theorem cell22_1942851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_1942851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942851 prefixEnd_1942851 := by exact prefixLift 1942851
  have htrace : WordTrace (prefixWord ++ tailWord_1942851) baseStart_1942851 baseEnd_1942851 := by
    simpa [prefixWord, tailWord_1942851, baseEnd_1942851] using wordTrace_append hprefix tailTrace_1942851
  have hstable : (prefixWord ++ tailWord_1942851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942851).length < 2 ^ (prefixWord ++ tailWord_1942851).sum := by decide
  have hdescent : baseEnd_1942851 < baseStart_1942851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942853 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_1942853 : Nat := 118140960795 + 1942853 * 2 ^ 59
def prefixEnd_1942853 : Nat := 4983230072969 + 3 ^ 40 * 1942853 * 2
def baseEnd_1942853 : Nat := 665078286686528208268325

theorem tailTrace_1942853 : CollatzResearch.WordTrace tailWord_1942853 prefixEnd_1942853 665078286686528208268325 := by
  unfold tailWord_1942853
  simp only [CollatzResearch.WordTrace]
  refine ⟨70861670430382868720537213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47241113620255245813691475 70861670430382868720537213)
  ·
    refine ⟨26573126411393575770201455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70861670430382868720537213 26573126411393575770201455)
    ·
      refine ⟨39859689617090363655302183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26573126411393575770201455 39859689617090363655302183)
      ·
        refine ⟨59789534425635545482953275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39859689617090363655302183 59789534425635545482953275)
        ·
          refine ⟨89684301638453318224429913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59789534425635545482953275 89684301638453318224429913)
          ·
            refine ⟨67263226228839988668322435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89684301638453318224429913 67263226228839988668322435)
            ·
              refine ⟨100894839343259983002483653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67263226228839988668322435 100894839343259983002483653)
              ·
                refine ⟨18917782376861246812965685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100894839343259983002483653 18917782376861246812965685)
                ·
                  refine ⟨1773542097830741888715533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18917782376861246812965685 1773542097830741888715533)
                  ·
                    refine ⟨665078286686528208268325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773542097830741888715533 665078286686528208268325)
                    ·
                      rfl

theorem cell22_1942853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_1942853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942853 prefixEnd_1942853 := by exact prefixLift 1942853
  have htrace : WordTrace (prefixWord ++ tailWord_1942853) baseStart_1942853 baseEnd_1942853 := by
    simpa [prefixWord, tailWord_1942853, baseEnd_1942853] using wordTrace_append hprefix tailTrace_1942853
  have hstable : (prefixWord ++ tailWord_1942853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942853).length < 2 ^ (prefixWord ++ tailWord_1942853).sum := by decide
  have hdescent : baseEnd_1942853 < baseStart_1942853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942861 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1942861 : Nat := 118140960795 + 1942861 * 2 ^ 59
def prefixEnd_1942861 : Nat := 4983230072969 + 3 ^ 40 * 1942861 * 2
def baseEnd_1942861 : Nat := 221693675083339618022767

theorem tailTrace_1942861 : CollatzResearch.WordTrace tailWord_1942861 prefixEnd_1942861 221693675083339618022767 := by
  unfold tailWord_1942861
  simp only [CollatzResearch.WordTrace]
  refine ⟨70861962214353886086828437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47241308142902590724552291 70861962214353886086828437)
  ·
    refine ⟨3321654478797838410320083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70861962214353886086828437 3321654478797838410320083)
    ·
      refine ⟨4982481718196757615480125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321654478797838410320083 4982481718196757615480125)
      ·
        refine ⟨1868430644323784105805047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4982481718196757615480125 1868430644323784105805047)
        ·
          refine ⟨2802645966485676158707571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868430644323784105805047 2802645966485676158707571)
          ·
            refine ⟨4203968949728514238061357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802645966485676158707571 4203968949728514238061357)
            ·
              refine ⟨1576488356148192839273009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4203968949728514238061357 1576488356148192839273009)
              ·
                refine ⟨1182366267111144629454757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576488356148192839273009 1182366267111144629454757)
                ·
                  refine ⟨221693675083339618022767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182366267111144629454757 221693675083339618022767)
                  ·
                    rfl

theorem cell22_1942861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1942861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942861 prefixEnd_1942861 := by exact prefixLift 1942861
  have htrace : WordTrace (prefixWord ++ tailWord_1942861) baseStart_1942861 baseEnd_1942861 := by
    simpa [prefixWord, tailWord_1942861, baseEnd_1942861] using wordTrace_append hprefix tailTrace_1942861
  have hstable : (prefixWord ++ tailWord_1942861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942861).length < 2 ^ (prefixWord ++ tailWord_1942861).sum := by decide
  have hdescent : baseEnd_1942861 < baseStart_1942861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942868 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1942868 : Nat := 118140960795 + 1942868 * 2 ^ 59
def prefixEnd_1942868 : Nat := 4983230072969 + 3 ^ 40 * 1942868 * 2
def baseEnd_1942868 : Nat := 665083421493073169143279

theorem tailTrace_1942868 : CollatzResearch.WordTrace tailWord_1942868 prefixEnd_1942868 665083421493073169143279 := by
  unfold tailWord_1942868
  simp only [CollatzResearch.WordTrace]
  refine ⟨35431108762664263141166629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47241478350219017521555505 35431108762664263141166629)
  ·
    refine ⟨6643332892999549338968743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35431108762664263141166629 6643332892999549338968743)
    ·
      refine ⟨9964999339499324008453115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6643332892999549338968743 9964999339499324008453115)
      ·
        refine ⟨14947499009248986012679673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9964999339499324008453115 14947499009248986012679673)
        ·
          refine ⟨11210624256936739509509755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14947499009248986012679673 11210624256936739509509755)
          ·
            refine ⟨16815936385405109264264633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11210624256936739509509755 16815936385405109264264633)
            ·
              refine ⟨12611952289053831948198475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16815936385405109264264633 12611952289053831948198475)
              ·
                refine ⟨18917928433580747922297713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12611952289053831948198475 18917928433580747922297713)
                ·
                  refine ⟨14188446325185560941723285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18917928433580747922297713 14188446325185560941723285)
                  ·
                    refine ⟨665083421493073169143279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14188446325185560941723285 665083421493073169143279)
                    ·
                      rfl

theorem cell22_1942868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1942868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942868 prefixEnd_1942868 := by exact prefixLift 1942868
  have htrace : WordTrace (prefixWord ++ tailWord_1942868) baseStart_1942868 baseEnd_1942868 := by
    simpa [prefixWord, tailWord_1942868, baseEnd_1942868] using wordTrace_append hprefix tailTrace_1942868
  have hstable : (prefixWord ++ tailWord_1942868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942868).length < 2 ^ (prefixWord ++ tailWord_1942868).sum := by decide
  have hdescent : baseEnd_1942868 < baseStart_1942868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942921 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 1, 3]
def baseStart_1942921 : Nat := 118140960795 + 1942921 * 2 ^ 59
def prefixEnd_1942921 : Nat := 4983230072969 + 3 ^ 40 * 1942921 * 2
def baseEnd_1942921 : Nat := 665101564476198697568117

theorem tailTrace_1942921 : CollatzResearch.WordTrace tailWord_1942921 prefixEnd_1942921 665101564476198697568117 := by
  unfold tailWord_1942921
  simp only [CollatzResearch.WordTrace]
  refine ⟨70864150594136516334012617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47242767062757677556008411 70864150594136516334012617)
  ·
    refine ⟨53148112945602387250509463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70864150594136516334012617 53148112945602387250509463)
    ·
      refine ⟨79722169418403580875764195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53148112945602387250509463 79722169418403580875764195)
      ·
        refine ⟨119583254127605371313646293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79722169418403580875764195 119583254127605371313646293)
        ·
          refine ⟨2802732518615750890163585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 119583254127605371313646293 2802732518615750890163585)
          ·
            refine ⟨2102049388961813167622689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802732518615750890163585 2102049388961813167622689)
            ·
              refine ⟨1576537041721359875717017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102049388961813167622689 1576537041721359875717017)
              ·
                refine ⟨1182402781291019906787763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576537041721359875717017 1182402781291019906787763)
                ·
                  refine ⟨1773604171936529860181645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182402781291019906787763 1773604171936529860181645)
                  ·
                    refine ⟨665101564476198697568117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773604171936529860181645 665101564476198697568117)
                    ·
                      rfl

theorem cell22_1942921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_1942921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942921 prefixEnd_1942921 := by exact prefixLift 1942921
  have htrace : WordTrace (prefixWord ++ tailWord_1942921) baseStart_1942921 baseEnd_1942921 := by
    simpa [prefixWord, tailWord_1942921, baseEnd_1942921] using wordTrace_append hprefix tailTrace_1942921
  have hstable : (prefixWord ++ tailWord_1942921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942921).length < 2 ^ (prefixWord ++ tailWord_1942921).sum := by decide
  have hdescent : baseEnd_1942921 < baseStart_1942921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942973 : List Nat := [1, 4, 1, 2, 2, 1, 11]
def baseStart_1942973 : Nat := 118140960795 + 1942973 * 2 ^ 59
def prefixEnd_1942973 : Nat := 4983230072969 + 3 ^ 40 * 1942973 * 2
def baseEnd_1942973 : Nat := 24634050560699551676591

theorem tailTrace_1942973 : CollatzResearch.WordTrace tailWord_1942973 prefixEnd_1942973 24634050560699551676591 := by
  unfold tailWord_1942973
  simp only [CollatzResearch.WordTrace]
  refine ⟨70866047189948129214905573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47244031459965419476603715 70866047189948129214905573)
  ·
    refine ⟨13287383848115274227794795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70866047189948129214905573 13287383848115274227794795)
    ·
      refine ⟨19931075772172911341692193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13287383848115274227794795 19931075772172911341692193)
      ·
        refine ⟨14948306829129683506269145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19931075772172911341692193 14948306829129683506269145)
        ·
          refine ⟨11211230121847262629701859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14948306829129683506269145 11211230121847262629701859)
          ·
            refine ⟨16816845182770893944552789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11211230121847262629701859 16816845182770893944552789)
            ·
              refine ⟨24634050560699551676591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16816845182770893944552789 24634050560699551676591)
              ·
                rfl

theorem cell22_1942973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 11].length) (baseStart_1942973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942973 prefixEnd_1942973 := by exact prefixLift 1942973
  have htrace : WordTrace (prefixWord ++ tailWord_1942973) baseStart_1942973 baseEnd_1942973 := by
    simpa [prefixWord, tailWord_1942973, baseEnd_1942973] using wordTrace_append hprefix tailTrace_1942973
  have hstable : (prefixWord ++ tailWord_1942973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942973).length < 2 ^ (prefixWord ++ tailWord_1942973).sum := by decide
  have hdescent : baseEnd_1942973 < baseStart_1942973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943052 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_1943052 : Nat := 118140960795 + 1943052 * 2 ^ 59
def prefixEnd_1943052 : Nat := 4983230072969 + 3 ^ 40 * 1943052 * 2
def baseEnd_1943052 : Nat := 221715469484452674180905

theorem tailTrace_1943052 : CollatzResearch.WordTrace tailWord_1943052 prefixEnd_1943052 221715469484452674180905 := by
  unfold tailWord_1943052
  simp only [CollatzResearch.WordTrace]
  refine ⟨35434464278330962853515705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47245952371107950471354273 35434464278330962853515705)
  ·
    refine ⟨26575848208748222140136779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35434464278330962853515705 26575848208748222140136779)
    ·
      refine ⟨39863772313122333210205169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26575848208748222140136779 39863772313122333210205169)
      ·
        refine ⟨29897829234841749907653877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39863772313122333210205169 29897829234841749907653877)
        ·
          refine ⟨2802921490766414053842551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29897829234841749907653877 2802921490766414053842551)
          ·
            refine ⟨4204382236149621080763827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802921490766414053842551 4204382236149621080763827)
            ·
              refine ⟨6306573354224431621145741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204382236149621080763827 6306573354224431621145741)
              ·
                refine ⟨2364965007834161857929653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6306573354224431621145741 2364965007834161857929653)
                ·
                  refine ⟨221715469484452674180905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2364965007834161857929653 221715469484452674180905)
                  ·
                    rfl

theorem cell22_1943052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_1943052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943052 prefixEnd_1943052 := by exact prefixLift 1943052
  have htrace : WordTrace (prefixWord ++ tailWord_1943052) baseStart_1943052 baseEnd_1943052 := by
    simpa [prefixWord, tailWord_1943052, baseEnd_1943052] using wordTrace_append hprefix tailTrace_1943052
  have hstable : (prefixWord ++ tailWord_1943052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943052).length < 2 ^ (prefixWord ++ tailWord_1943052).sum := by decide
  have hdescent : baseEnd_1943052 < baseStart_1943052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943127 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1943127 : Nat := 118140960795 + 1943127 * 2 ^ 59
def prefixEnd_1943127 : Nat := 4983230072969 + 3 ^ 40 * 1943127 * 2
def baseEnd_1943127 : Nat := 665172082486082826917485

theorem tailTrace_1943127 : CollatzResearch.WordTrace tailWord_1943127 prefixEnd_1943127 665172082486082826917485 := by
  unfold tailWord_1943127
  simp only [CollatzResearch.WordTrace]
  refine ⟨70871664031390213516011635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47247776020926809010674423 70871664031390213516011635)
  ·
    refine ⟨106307496047085320274017453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70871664031390213516011635 106307496047085320274017453)
    ·
      refine ⟨39865311017656995102756545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106307496047085320274017453 39865311017656995102756545)
      ·
        refine ⟨29898983263242746327067409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39865311017656995102756545 29898983263242746327067409)
        ·
          refine ⟨22424237447432059745300557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29898983263242746327067409 22424237447432059745300557)
          ·
            refine ⟨8409089042787022404487709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22424237447432059745300557 8409089042787022404487709)
            ·
              refine ⟨3153408391045133401682891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8409089042787022404487709 3153408391045133401682891)
              ·
                refine ⟨4730112586567700102524337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153408391045133401682891 4730112586567700102524337)
                ·
                  refine ⟨3547584439925775076893253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4730112586567700102524337 3547584439925775076893253)
                  ·
                    refine ⟨665172082486082826917485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3547584439925775076893253 665172082486082826917485)
                    ·
                      rfl

theorem cell22_1943127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1943127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943127 prefixEnd_1943127 := by exact prefixLift 1943127
  have htrace : WordTrace (prefixWord ++ tailWord_1943127) baseStart_1943127 baseEnd_1943127 := by
    simpa [prefixWord, tailWord_1943127, baseEnd_1943127] using wordTrace_append hprefix tailTrace_1943127
  have hstable : (prefixWord ++ tailWord_1943127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943127).length < 2 ^ (prefixWord ++ tailWord_1943127).sum := by decide
  have hdescent : baseEnd_1943127 < baseStart_1943127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943146 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1943146 : Nat := 118140960795 + 1943146 * 2 ^ 59
def prefixEnd_1943146 : Nat := 4983230072969 + 3 ^ 40 * 1943146 * 2
def baseEnd_1943146 : Nat := 665178586574373110692427

theorem tailTrace_1943146 : CollatzResearch.WordTrace tailWord_1943146 prefixEnd_1943146 665178586574373110692427 := by
  unfold tailWord_1943146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718089254580344940238323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47248238012214253173968861 17718089254580344940238323)
  ·
    refine ⟨26577133881870517410357485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17718089254580344940238323 26577133881870517410357485)
    ·
      refine ⟨9966425205701444028884057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26577133881870517410357485 9966425205701444028884057)
      ·
        refine ⟨7474818904276083021663043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9966425205701444028884057 7474818904276083021663043)
        ·
          refine ⟨11212228356414124532494565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7474818904276083021663043 11212228356414124532494565)
          ·
            refine ⟨2102292816827648349842731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11212228356414124532494565 2102292816827648349842731)
            ·
              refine ⟨3153439225241472524764097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102292816827648349842731 3153439225241472524764097)
              ·
                refine ⟨2365079418931104393573073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153439225241472524764097 2365079418931104393573073)
                ·
                  refine ⟨1773809564198328295179805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365079418931104393573073 1773809564198328295179805)
                  ·
                    refine ⟨665178586574373110692427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773809564198328295179805 665178586574373110692427)
                    ·
                      rfl

theorem cell22_1943146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1943146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943146 prefixEnd_1943146 := by exact prefixLift 1943146
  have htrace : WordTrace (prefixWord ++ tailWord_1943146) baseStart_1943146 baseEnd_1943146 := by
    simpa [prefixWord, tailWord_1943146, baseEnd_1943146] using wordTrace_append hprefix tailTrace_1943146
  have hstable : (prefixWord ++ tailWord_1943146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943146).length < 2 ^ (prefixWord ++ tailWord_1943146).sum := by decide
  have hdescent : baseEnd_1943146 < baseStart_1943146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943176 : List Nat := [2, 1, 3, 5, 1, 2, 2, 6]
def baseStart_1943176 : Nat := 118140960795 + 1943176 * 2 ^ 59
def prefixEnd_1943176 : Nat := 4983230072969 + 3 ^ 40 * 1943176 * 2
def baseEnd_1943176 : Nat := 73909872909718114715815

theorem tailTrace_1943176 : CollatzResearch.WordTrace tailWord_1943176 prefixEnd_1943176 73909872909718114715815 := by
  unfold tailWord_1943176
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436725604106347442272691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47248967472141796589696921 35436725604106347442272691)
  ·
    refine ⟨53155088406159521163409037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35436725604106347442272691 53155088406159521163409037)
    ·
      refine ⟨19933158152309820436278389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53155088406159521163409037 19933158152309820436278389)
      ·
        refine ⟨1868733576779045665901099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19933158152309820436278389 1868733576779045665901099)
        ·
          refine ⟨2803100365168568498851649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868733576779045665901099 2803100365168568498851649)
          ·
            refine ⟨2102325273876426374138737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803100365168568498851649 2102325273876426374138737)
            ·
              refine ⟨1576743955407319780604053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102325273876426374138737 1576743955407319780604053)
              ·
                refine ⟨73909872909718114715815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1576743955407319780604053 73909872909718114715815)
                ·
                  rfl

theorem cell22_1943176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_1943176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943176 prefixEnd_1943176 := by exact prefixLift 1943176
  have htrace : WordTrace (prefixWord ++ tailWord_1943176) baseStart_1943176 baseEnd_1943176 := by
    simpa [prefixWord, tailWord_1943176, baseEnd_1943176] using wordTrace_append hprefix tailTrace_1943176
  have hstable : (prefixWord ++ tailWord_1943176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943176).length < 2 ^ (prefixWord ++ tailWord_1943176).sum := by decide
  have hdescent : baseEnd_1943176 < baseStart_1943176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943185 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1943185 : Nat := 118140960795 + 1943185 * 2 ^ 59
def prefixEnd_1943185 : Nat := 4983230072969 + 3 ^ 40 * 1943185 * 2
def baseEnd_1943185 : Nat := 665191937071390008967307

theorem tailTrace_1943185 : CollatzResearch.WordTrace tailWord_1943185 prefixEnd_1943185 665191937071390008967307 := by
  unfold tailWord_1943185
  simp only [CollatzResearch.WordTrace]
  refine ⟨70873779465180089421623009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47249186310120059614415339 70873779465180089421623009)
  ·
    refine ⟨53155334598885067066217257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70873779465180089421623009 53155334598885067066217257)
    ·
      refine ⟨39866500949163800299662943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53155334598885067066217257 39866500949163800299662943)
      ·
        refine ⟨59799751423745700449494415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39866500949163800299662943 59799751423745700449494415)
        ·
          refine ⟨89699627135618550674241623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59799751423745700449494415 89699627135618550674241623)
          ·
            refine ⟨134549440703427826011362435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89699627135618550674241623 134549440703427826011362435)
            ·
              refine ⟨201824161055141739017043653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134549440703427826011362435 201824161055141739017043653)
              ·
                refine ⟨37842030197839076065695685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201824161055141739017043653 37842030197839076065695685)
                ·
                  refine ⟨7095380662094826762317941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37842030197839076065695685 7095380662094826762317941)
                  ·
                    refine ⟨665191937071390008967307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7095380662094826762317941 665191937071390008967307)
                    ·
                      rfl

theorem cell22_1943185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1943185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943185 prefixEnd_1943185 := by exact prefixLift 1943185
  have htrace : WordTrace (prefixWord ++ tailWord_1943185) baseStart_1943185 baseEnd_1943185 := by
    simpa [prefixWord, tailWord_1943185, baseEnd_1943185] using wordTrace_append hprefix tailTrace_1943185
  have hstable : (prefixWord ++ tailWord_1943185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943185).length < 2 ^ (prefixWord ++ tailWord_1943185).sum := by decide
  have hdescent : baseEnd_1943185 < baseStart_1943185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943191 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 1, 3]
def baseStart_1943191 : Nat := 118140960795 + 1943191 * 2 ^ 59
def prefixEnd_1943191 : Nat := 4983230072969 + 3 ^ 40 * 1943191 * 2
def baseEnd_1943191 : Nat := 665193990994007993317289

theorem tailTrace_1943191 : CollatzResearch.WordTrace tailWord_1943191 prefixEnd_1943191 665193990994007993317289 := by
  unfold tailWord_1943191
  simp only [CollatzResearch.WordTrace]
  refine ⟨70873998303158352446341427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47249332202105568297560951 70873998303158352446341427)
  ·
    refine ⟨106310997454737528669512141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70873998303158352446341427 106310997454737528669512141)
    ·
      refine ⟨39866624045526573251067053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106310997454737528669512141 39866624045526573251067053)
      ·
        refine ⟨14949984017072464969150145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39866624045526573251067053 14949984017072464969150145)
        ·
          refine ⟨11212488012804348726862609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14949984017072464969150145 11212488012804348726862609)
          ·
            refine ⟨8409366009603261545146957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11212488012804348726862609 8409366009603261545146957)
            ·
              refine ⟨3153512253601223079430109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8409366009603261545146957 3153512253601223079430109)
              ·
                refine ⟨1182567095100458654786291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3153512253601223079430109 1182567095100458654786291)
                ·
                  refine ⟨1773850642650687982179437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182567095100458654786291 1773850642650687982179437)
                  ·
                    refine ⟨665193990994007993317289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773850642650687982179437 665193990994007993317289)
                    ·
                      rfl

theorem cell22_1943191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_1943191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943191 prefixEnd_1943191 := by exact prefixLift 1943191
  have htrace : WordTrace (prefixWord ++ tailWord_1943191) baseStart_1943191 baseEnd_1943191 := by
    simpa [prefixWord, tailWord_1943191, baseEnd_1943191] using wordTrace_append hprefix tailTrace_1943191
  have hstable : (prefixWord ++ tailWord_1943191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943191).length < 2 ^ (prefixWord ++ tailWord_1943191).sum := by decide
  have hdescent : baseEnd_1943191 < baseStart_1943191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943247 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 6, 3]
def baseStart_1943247 : Nat := 118140960795 + 1943247 * 2 ^ 59
def prefixEnd_1943247 : Nat := 4983230072969 + 3 ^ 40 * 1943247 * 2
def baseEnd_1943247 : Nat := 665213160938442513917117

theorem tailTrace_1943247 : CollatzResearch.WordTrace tailWord_1943247 prefixEnd_1943247 665213160938442513917117 := by
  unfold tailWord_1943247
  simp only [CollatzResearch.WordTrace]
  refine ⟨70876040790955474010379995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47250693860636982673586663 70876040790955474010379995)
  ·
    refine ⟨106314061186433211015569993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70876040790955474010379995 106314061186433211015569993)
    ·
      refine ⟨79735545889824908261677495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106314061186433211015569993 79735545889824908261677495)
      ·
        refine ⟨119603318834737362392516243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79735545889824908261677495 119603318834737362392516243)
        ·
          refine ⟨179404978252106043588774365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119603318834737362392516243 179404978252106043588774365)
          ·
            refine ⟨67276866844539766345790387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179404978252106043588774365 67276866844539766345790387)
            ·
              refine ⟨100915300266809649518685581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67276866844539766345790387 100915300266809649518685581)
              ·
                refine ⟨37843237600053618569507093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100915300266809649518685581 37843237600053618569507093)
                ·
                  refine ⟨1773901762502513370445645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37843237600053618569507093 1773901762502513370445645)
                  ·
                    refine ⟨665213160938442513917117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773901762502513370445645 665213160938442513917117)
                    ·
                      rfl

theorem cell22_1943247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_1943247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943247 prefixEnd_1943247 := by exact prefixLift 1943247
  have htrace : WordTrace (prefixWord ++ tailWord_1943247) baseStart_1943247 baseEnd_1943247 := by
    simpa [prefixWord, tailWord_1943247, baseEnd_1943247] using wordTrace_append hprefix tailTrace_1943247
  have hstable : (prefixWord ++ tailWord_1943247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943247).length < 2 ^ (prefixWord ++ tailWord_1943247).sum := by decide
  have hdescent : baseEnd_1943247 < baseStart_1943247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943264 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_1943264 : Nat := 118140960795 + 1943264 * 2 ^ 59
def prefixEnd_1943264 : Nat := 4983230072969 + 3 ^ 40 * 1943264 * 2
def baseEnd_1943264 : Nat := 665218980385860136242065

theorem tailTrace_1943264 : CollatzResearch.WordTrace tailWord_1943264 prefixEnd_1943264 665218980385860136242065 := by
  unfold tailWord_1943264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35438330415946942956874423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47251107221262590609165897 35438330415946942956874423)
  ·
    refine ⟨53157495623920414435311635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35438330415946942956874423 53157495623920414435311635)
    ·
      refine ⟨79736243435880621652967453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53157495623920414435311635 79736243435880621652967453)
      ·
        refine ⟨29901091288455233119862795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79736243435880621652967453 29901091288455233119862795)
        ·
          refine ⟨44851636932682849679794193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29901091288455233119862795 44851636932682849679794193)
          ·
            refine ⟨33638727699512137259845645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44851636932682849679794193 33638727699512137259845645)
            ·
              refine ⟨12614522887317051472442117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33638727699512137259845645 12614522887317051472442117)
              ·
                refine ⟨2365223041371947151082897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12614522887317051472442117 2365223041371947151082897)
                ·
                  refine ⟨1773917281028960363312173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365223041371947151082897 1773917281028960363312173)
                  ·
                    refine ⟨665218980385860136242065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773917281028960363312173 665218980385860136242065)
                    ·
                      rfl

theorem cell22_1943264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_1943264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943264 prefixEnd_1943264 := by exact prefixLift 1943264
  have htrace : WordTrace (prefixWord ++ tailWord_1943264) baseStart_1943264 baseEnd_1943264 := by
    simpa [prefixWord, tailWord_1943264, baseEnd_1943264] using wordTrace_append hprefix tailTrace_1943264
  have hstable : (prefixWord ++ tailWord_1943264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943264).length < 2 ^ (prefixWord ++ tailWord_1943264).sum := by decide
  have hdescent : baseEnd_1943264 < baseStart_1943264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943367 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 8]
def baseStart_1943367 : Nat := 118140960795 + 1943367 * 2 ^ 59
def prefixEnd_1943367 : Nat := 4983230072969 + 3 ^ 40 * 1943367 * 2
def baseEnd_1943367 : Nat := 221751413130267400305583

theorem tailTrace_1943367 : CollatzResearch.WordTrace tailWord_1943367 prefixEnd_1943367 221751413130267400305583 := by
  unfold tailWord_1943367
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880417550520734504748355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47253611700347156336498903 70880417550520734504748355)
  ·
    refine ⟨106320626325781101757122533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70880417550520734504748355 106320626325781101757122533)
    ·
      refine ⟨19935117436083956579460475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106320626325781101757122533 19935117436083956579460475)
      ·
        refine ⟨29902676154125934869190713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19935117436083956579460475 29902676154125934869190713)
        ·
          refine ⟨22427007115594451151893035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29902676154125934869190713 22427007115594451151893035)
          ·
            refine ⟨33640510673391676727839553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22427007115594451151893035 33640510673391676727839553)
            ·
              refine ⟨25230383005043757545879665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33640510673391676727839553 25230383005043757545879665)
              ·
                refine ⟨18922787253782818159409749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25230383005043757545879665 18922787253782818159409749)
                ·
                  refine ⟨221751413130267400305583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18922787253782818159409749 221751413130267400305583)
                  ·
                    rfl

theorem cell22_1943367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_1943367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943367 prefixEnd_1943367 := by exact prefixLift 1943367
  have htrace : WordTrace (prefixWord ++ tailWord_1943367) baseStart_1943367 baseEnd_1943367 := by
    simpa [prefixWord, tailWord_1943367, baseEnd_1943367] using wordTrace_append hprefix tailTrace_1943367
  have hstable : (prefixWord ++ tailWord_1943367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943367).length < 2 ^ (prefixWord ++ tailWord_1943367).sum := by decide
  have hdescent : baseEnd_1943367 < baseStart_1943367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943369 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_1943369 : Nat := 118140960795 + 1943369 * 2 ^ 59
def prefixEnd_1943369 : Nat := 4983230072969 + 3 ^ 40 * 1943369 * 2
def baseEnd_1943369 : Nat := 665254924031674862366743

theorem tailTrace_1943369 : CollatzResearch.WordTrace tailWord_1943369 prefixEnd_1943369 665254924031674862366743 := by
  unfold tailWord_1943369
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880490496513488846321161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47253660331008992564214107 70880490496513488846321161)
  ·
    refine ⟨53160367872385116634740871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70880490496513488846321161 53160367872385116634740871)
    ·
      refine ⟨79740551808577674952111307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53160367872385116634740871 79740551808577674952111307)
      ·
        refine ⟨119610827712866512428166961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79740551808577674952111307 119610827712866512428166961)
        ·
          refine ⟨89708120784649884321125221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119610827712866512428166961 89708120784649884321125221)
          ·
            refine ⟨16820272647121853310210979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89708120784649884321125221 16820272647121853310210979)
            ·
              refine ⟨25230408970682779965316469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16820272647121853310210979 25230408970682779965316469)
              ·
                refine ⟨2365350841001510621748419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25230408970682779965316469 2365350841001510621748419)
                ·
                  refine ⟨3548026261502265932622629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365350841001510621748419 3548026261502265932622629)
                  ·
                    refine ⟨665254924031674862366743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548026261502265932622629 665254924031674862366743)
                    ·
                      rfl

theorem cell22_1943369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_1943369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943369 prefixEnd_1943369 := by exact prefixLift 1943369
  have htrace : WordTrace (prefixWord ++ tailWord_1943369) baseStart_1943369 baseEnd_1943369 := by
    simpa [prefixWord, tailWord_1943369, baseEnd_1943369] using wordTrace_append hprefix tailTrace_1943369
  have hstable : (prefixWord ++ tailWord_1943369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943369).length < 2 ^ (prefixWord ++ tailWord_1943369).sum := by decide
  have hdescent : baseEnd_1943369 < baseStart_1943369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943399 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1943399 : Nat := 118140960795 + 1943399 * 2 ^ 59
def prefixEnd_1943399 : Nat := 4983230072969 + 3 ^ 40 * 1943399 * 2
def baseEnd_1943399 : Nat := 665265193644764784116651

theorem tailTrace_1943399 : CollatzResearch.WordTrace tailWord_1943399 prefixEnd_1943399 665265193644764784116651 := by
  unfold tailWord_1943399
  simp only [CollatzResearch.WordTrace]
  refine ⟨70881584686404803969913251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47254389790936535979942167 70881584686404803969913251)
  ·
    refine ⟨106322377029607205954869877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70881584686404803969913251 106322377029607205954869877)
    ·
      refine ⟨9967722846525675558269051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106322377029607205954869877 9967722846525675558269051)
      ·
        refine ⟨14951584269788513337403577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967722846525675558269051 14951584269788513337403577)
        ·
          refine ⟨11213688202341385003052683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14951584269788513337403577 11213688202341385003052683)
          ·
            refine ⟨16820532303512077504579025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11213688202341385003052683 16820532303512077504579025)
            ·
              refine ⟨12615399227634058128434269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16820532303512077504579025 12615399227634058128434269)
              ·
                refine ⟨4730774710362771798162851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12615399227634058128434269 4730774710362771798162851)
                ·
                  refine ⟨7096162065544157697244277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730774710362771798162851 7096162065544157697244277)
                  ·
                    refine ⟨665265193644764784116651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7096162065544157697244277 665265193644764784116651)
                    ·
                      rfl

theorem cell22_1943399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1943399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943399 prefixEnd_1943399 := by exact prefixLift 1943399
  have htrace : WordTrace (prefixWord ++ tailWord_1943399) baseStart_1943399 baseEnd_1943399 := by
    simpa [prefixWord, tailWord_1943399, baseEnd_1943399] using wordTrace_append hprefix tailTrace_1943399
  have hstable : (prefixWord ++ tailWord_1943399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943399).length < 2 ^ (prefixWord ++ tailWord_1943399).sum := by decide
  have hdescent : baseEnd_1943399 < baseStart_1943399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943504 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_1943504 : Nat := 118140960795 + 1943504 * 2 ^ 59
def prefixEnd_1943504 : Nat := 4983230072969 + 3 ^ 40 * 1943504 * 2
def baseEnd_1943504 : Nat := 665301137290579510241329

theorem tailTrace_1943504 : CollatzResearch.WordTrace tailWord_1943504 prefixEnd_1943504 665301137290579510241329 := by
  unfold tailWord_1943504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35442707175512203451242783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47256942900682937934990377 35442707175512203451242783)
  ·
    refine ⟨53164060763268305176864175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35442707175512203451242783 53164060763268305176864175)
    ·
      refine ⟨79746091144902457765296263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53164060763268305176864175 79746091144902457765296263)
      ·
        refine ⟨119619136717353686647944395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79746091144902457765296263 119619136717353686647944395)
        ·
          refine ⟨179428705076030529971916593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119619136717353686647944395 179428705076030529971916593)
          ·
            refine ⟨134571528807022897478937445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179428705076030529971916593 134571528807022897478937445)
            ·
              refine ⟨25232161651316793277300771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134571528807022897478937445 25232161651316793277300771)
              ·
                refine ⟨37848242476975189915951157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25232161651316793277300771 37848242476975189915951157)
                ·
                  refine ⟨3548272732216424054620421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37848242476975189915951157 3548272732216424054620421)
                  ·
                    refine ⟨665301137290579510241329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548272732216424054620421 665301137290579510241329)
                    ·
                      rfl

theorem cell22_1943504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_1943504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943504 prefixEnd_1943504 := by exact prefixLift 1943504
  have htrace : WordTrace (prefixWord ++ tailWord_1943504) baseStart_1943504 baseEnd_1943504 := by
    simpa [prefixWord, tailWord_1943504, baseEnd_1943504] using wordTrace_append hprefix tailTrace_1943504
  have hstable : (prefixWord ++ tailWord_1943504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943504).length < 2 ^ (prefixWord ++ tailWord_1943504).sum := by decide
  have hdescent : baseEnd_1943504 < baseStart_1943504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943508 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1943508 : Nat := 118140960795 + 1943508 * 2 ^ 59
def prefixEnd_1943508 : Nat := 4983230072969 + 3 ^ 40 * 1943508 * 2
def baseEnd_1943508 : Nat := 221767502190774944380439

theorem tailTrace_1943508 : CollatzResearch.WordTrace tailWord_1943508 prefixEnd_1943508 221767502190774944380439 := by
  unfold tailWord_1943508
  simp only [CollatzResearch.WordTrace]
  refine ⟨35442780121504957792815589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47257040162006610390420785 35442780121504957792815589)
  ·
    refine ⟨6645521272782179586152923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35442780121504957792815589 6645521272782179586152923)
    ·
      refine ⟨9968281909173269379229385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645521272782179586152923 9968281909173269379229385)
      ·
        refine ⟨7476211431879952034422039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9968281909173269379229385 7476211431879952034422039)
        ·
          refine ⟨11214317147819928051633059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476211431879952034422039 11214317147819928051633059)
          ·
            refine ⟨16821475721729892077449589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214317147819928051633059 16821475721729892077449589)
            ·
              refine ⟨1577013348912177382260899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16821475721729892077449589 1577013348912177382260899)
              ·
                refine ⟨2365520023368266073391349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577013348912177382260899 2365520023368266073391349)
                ·
                  refine ⟨221767502190774944380439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2365520023368266073391349 221767502190774944380439)
                  ·
                    rfl

theorem cell22_1943508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1943508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943508 prefixEnd_1943508 := by exact prefixLift 1943508
  have htrace : WordTrace (prefixWord ++ tailWord_1943508) baseStart_1943508 baseEnd_1943508 := by
    simpa [prefixWord, tailWord_1943508, baseEnd_1943508] using wordTrace_append hprefix tailTrace_1943508
  have hstable : (prefixWord ++ tailWord_1943508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943508).length < 2 ^ (prefixWord ++ tailWord_1943508).sum := by decide
  have hdescent : baseEnd_1943508 < baseStart_1943508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943521 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1943521 : Nat := 118140960795 + 1943521 * 2 ^ 59
def prefixEnd_1943521 : Nat := 4983230072969 + 3 ^ 40 * 1943521 * 2
def baseEnd_1943521 : Nat := 665306956737997132566277

theorem tailTrace_1943521 : CollatzResearch.WordTrace tailWord_1943521 prefixEnd_1943521 665306956737997132566277 := by
  unfold tailWord_1943521
  simp only [CollatzResearch.WordTrace]
  refine ⟨70886034391962818805854417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47257356261308545870569611 70886034391962818805854417)
  ·
    refine ⟨53164525793972114104390813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70886034391962818805854417 53164525793972114104390813)
    ·
      refine ⟨19936697172739542789146555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53164525793972114104390813 19936697172739542789146555)
      ·
        refine ⟨29905045759109314183719833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19936697172739542789146555 29905045759109314183719833)
        ·
          refine ⟨22428784319331985637789875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29905045759109314183719833 22428784319331985637789875)
          ·
            refine ⟨33643176478997978456684813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22428784319331985637789875 33643176478997978456684813)
            ·
              refine ⟨12616191179624241921256805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33643176478997978456684813 12616191179624241921256805)
              ·
                refine ⟨2365535846179545360235651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12616191179624241921256805 2365535846179545360235651)
                ·
                  refine ⟨3548303769269318040353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365535846179545360235651 3548303769269318040353477)
                  ·
                    refine ⟨665306956737997132566277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548303769269318040353477 665306956737997132566277)
                    ·
                      rfl

theorem cell22_1943521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1943521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943521 prefixEnd_1943521 := by exact prefixLift 1943521
  have htrace : WordTrace (prefixWord ++ tailWord_1943521) baseStart_1943521 baseEnd_1943521 := by
    simpa [prefixWord, tailWord_1943521, baseEnd_1943521] using wordTrace_append hprefix tailTrace_1943521
  have hstable : (prefixWord ++ tailWord_1943521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943521).length < 2 ^ (prefixWord ++ tailWord_1943521).sum := by decide
  have hdescent : baseEnd_1943521 < baseStart_1943521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943566 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1943566 : Nat := 118140960795 + 1943566 * 2 ^ 59
def prefixEnd_1943566 : Nat := 4983230072969 + 3 ^ 40 * 1943566 * 2
def baseEnd_1943566 : Nat := 665322361157632015191139

theorem tailTrace_1943566 : CollatzResearch.WordTrace tailWord_1943566 prefixEnd_1943566 665322361157632015191139 := by
  unfold tailWord_1943566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860959459599973936405319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47258450451199860994161701 8860959459599973936405319)
  ·
    refine ⟨13291439189399960904607979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8860959459599973936405319 13291439189399960904607979)
    ·
      refine ⟨19937158784099941356911969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13291439189399960904607979 19937158784099941356911969)
      ·
        refine ⟨14952869088074956017683977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19937158784099941356911969 14952869088074956017683977)
        ·
          refine ⟨11214651816056217013262983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14952869088074956017683977 11214651816056217013262983)
          ·
            refine ⟨16821977724084325519894475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214651816056217013262983 16821977724084325519894475)
            ·
              refine ⟨25232966586126488279841713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16821977724084325519894475 25232966586126488279841713)
              ·
                refine ⟨18924724939594866209881285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25232966586126488279841713 18924724939594866209881285)
                ·
                  refine ⟨3548385926174037414352741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18924724939594866209881285 3548385926174037414352741)
                  ·
                    refine ⟨665322361157632015191139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548385926174037414352741 665322361157632015191139)
                    ·
                      rfl

theorem cell22_1943566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1943566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943566 prefixEnd_1943566 := by exact prefixLift 1943566
  have htrace : WordTrace (prefixWord ++ tailWord_1943566) baseStart_1943566 baseEnd_1943566 := by
    simpa [prefixWord, tailWord_1943566, baseEnd_1943566] using wordTrace_append hprefix tailTrace_1943566
  have hstable : (prefixWord ++ tailWord_1943566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943566).length < 2 ^ (prefixWord ++ tailWord_1943566).sum := by decide
  have hdescent : baseEnd_1943566 < baseStart_1943566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943581 : List Nat := [1, 4, 2, 2, 2, 1, 2, 8]
def baseStart_1943581 : Nat := 118140960795 + 1943581 * 2 ^ 59
def prefixEnd_1943581 : Nat := 4983230072969 + 3 ^ 40 * 1943581 * 2
def baseEnd_1943581 : Nat := 73925277329352997340677

theorem tailTrace_1943581 : CollatzResearch.WordTrace tailWord_1943581 prefixEnd_1943581 73925277329352997340677 := by
  unfold tailWord_1943581
  simp only [CollatzResearch.WordTrace]
  refine ⟨70888222771745449053038597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47258815181163632702025731 70888222771745449053038597)
  ·
    refine ⟨13291541769702271697444737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70888222771745449053038597 13291541769702271697444737)
    ·
      refine ⟨9968656327276703773083553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13291541769702271697444737 9968656327276703773083553)
      ·
        refine ⟨7476492245457527829812665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9968656327276703773083553 7476492245457527829812665)
        ·
          refine ⟨5607369184093145872359499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476492245457527829812665 5607369184093145872359499)
          ·
            refine ⟨8411053776139718808539249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607369184093145872359499 8411053776139718808539249)
            ·
              refine ⟨6308290332104789106404437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411053776139718808539249 6308290332104789106404437)
              ·
                refine ⟨73925277329352997340677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6308290332104789106404437 73925277329352997340677)
                ·
                  rfl

theorem cell22_1943581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 8].length) (baseStart_1943581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943581 prefixEnd_1943581 := by exact prefixLift 1943581
  have htrace : WordTrace (prefixWord ++ tailWord_1943581) baseStart_1943581 baseEnd_1943581 := by
    simpa [prefixWord, tailWord_1943581, baseEnd_1943581] using wordTrace_append hprefix tailTrace_1943581
  have hstable : (prefixWord ++ tailWord_1943581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943581).length < 2 ^ (prefixWord ++ tailWord_1943581).sum := by decide
  have hdescent : baseEnd_1943581 < baseStart_1943581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943596 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_1943596 : Nat := 118140960795 + 1943596 * 2 ^ 59
def prefixEnd_1943596 : Nat := 4983230072969 + 3 ^ 40 * 1943596 * 2
def baseEnd_1943596 : Nat := 665332630770721936941047

theorem tailTrace_1943596 : CollatzResearch.WordTrace tailWord_1943596 prefixEnd_1943596 665332630770721936941047 := by
  unfold tailWord_1943596
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444384933345553307417321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47259179911127404409889761 35444384933345553307417321)
  ·
    refine ⟨26583288700009164980562991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35444384933345553307417321 26583288700009164980562991)
    ·
      refine ⟨39874933050013747470844487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26583288700009164980562991 39874933050013747470844487)
      ·
        refine ⟨59812399575020621206266731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39874933050013747470844487 59812399575020621206266731)
        ·
          refine ⟨89718599362530931809400097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59812399575020621206266731 89718599362530931809400097)
          ·
            refine ⟨67288949521898198857050073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89718599362530931809400097 67288949521898198857050073)
            ·
              refine ⟨50466712141423649142787555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67288949521898198857050073 50466712141423649142787555)
              ·
                refine ⟨75700068212135473714181333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50466712141423649142787555 75700068212135473714181333)
                ·
                  refine ⟨1774220348721925165176125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 75700068212135473714181333 1774220348721925165176125)
                  ·
                    refine ⟨665332630770721936941047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774220348721925165176125 665332630770721936941047)
                    ·
                      rfl

theorem cell22_1943596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_1943596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943596 prefixEnd_1943596 := by exact prefixLift 1943596
  have htrace : WordTrace (prefixWord ++ tailWord_1943596) baseStart_1943596 baseEnd_1943596 := by
    simpa [prefixWord, tailWord_1943596, baseEnd_1943596] using wordTrace_append hprefix tailTrace_1943596
  have hstable : (prefixWord ++ tailWord_1943596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943596).length < 2 ^ (prefixWord ++ tailWord_1943596).sum := by decide
  have hdescent : baseEnd_1943596 < baseStart_1943596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943604 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1943604 : Nat := 118140960795 + 1943604 * 2 ^ 59
def prefixEnd_1943604 : Nat := 4983230072969 + 3 ^ 40 * 1943604 * 2
def baseEnd_1943604 : Nat := 221778456444737527580341

theorem tailTrace_1943604 : CollatzResearch.WordTrace tailWord_1943604 prefixEnd_1943604 221778456444737527580341 := by
  unfold tailWord_1943604
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444530825331061990562933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47259374433774749320750577 35444530825331061990562933)
  ·
    refine ⟨3322924764874787061615275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35444530825331061990562933 3322924764874787061615275)
    ·
      refine ⟨4984387147312180592422913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3322924764874787061615275 4984387147312180592422913)
      ·
        refine ⟨3738290360484135444317185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4984387147312180592422913 3738290360484135444317185)
        ·
          refine ⟨2803717770363101583237889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738290360484135444317185 2803717770363101583237889)
          ·
            refine ⟨2102788327772326187428417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803717770363101583237889 2102788327772326187428417)
            ·
              refine ⟨1577091245829244640571313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102788327772326187428417 1577091245829244640571313)
              ·
                refine ⟨1182818434371933480428485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577091245829244640571313 1182818434371933480428485)
                ·
                  refine ⟨221778456444737527580341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182818434371933480428485 221778456444737527580341)
                  ·
                    rfl

theorem cell22_1943604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1943604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943604 prefixEnd_1943604 := by exact prefixLift 1943604
  have htrace : WordTrace (prefixWord ++ tailWord_1943604) baseStart_1943604 baseEnd_1943604 := by
    simpa [prefixWord, tailWord_1943604, baseEnd_1943604] using wordTrace_append hprefix tailTrace_1943604
  have hstable : (prefixWord ++ tailWord_1943604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943604).length < 2 ^ (prefixWord ++ tailWord_1943604).sum := by decide
  have hdescent : baseEnd_1943604 < baseStart_1943604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943613 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1943613 : Nat := 118140960795 + 1943613 * 2 ^ 59
def prefixEnd_1943613 : Nat := 4983230072969 + 3 ^ 40 * 1943613 * 2
def baseEnd_1943613 : Nat := 665338450218139559265995

theorem tailTrace_1943613 : CollatzResearch.WordTrace tailWord_1943613 prefixEnd_1943613 665338450218139559265995 := by
  unfold tailWord_1943613
  simp only [CollatzResearch.WordTrace]
  refine ⟨70889389907629518518203493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47259593271753012345468995 70889389907629518518203493)
  ·
    refine ⟨13291760607680534722163155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70889389907629518518203493 13291760607680534722163155)
    ·
      refine ⟨19937640911520802083244733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13291760607680534722163155 19937640911520802083244733)
      ·
        refine ⟨7476615341820300781216775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19937640911520802083244733 7476615341820300781216775)
        ·
          refine ⟨11214923012730451171825163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476615341820300781216775 11214923012730451171825163)
          ·
            refine ⟨16822384519095676757737745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214923012730451171825163 16822384519095676757737745)
            ·
              refine ⟨12616788389321757568303309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16822384519095676757737745 12616788389321757568303309)
              ·
                refine ⟨4731295645995659088113741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12616788389321757568303309 4731295645995659088113741)
                ·
                  refine ⟨1774235867248372158042653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4731295645995659088113741 1774235867248372158042653)
                  ·
                    refine ⟨665338450218139559265995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774235867248372158042653 665338450218139559265995)
                    ·
                      rfl

theorem cell22_1943613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1943613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943613 prefixEnd_1943613 := by exact prefixLift 1943613
  have htrace : WordTrace (prefixWord ++ tailWord_1943613) baseStart_1943613 baseEnd_1943613 := by
    simpa [prefixWord, tailWord_1943613, baseEnd_1943613] using wordTrace_append hprefix tailTrace_1943613
  have hstable : (prefixWord ++ tailWord_1943613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943613).length < 2 ^ (prefixWord ++ tailWord_1943613).sum := by decide
  have hdescent : baseEnd_1943613 < baseStart_1943613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943671 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 6]
def baseStart_1943671 : Nat := 118140960795 + 1943671 * 2 ^ 59
def prefixEnd_1943671 : Nat := 4983230072969 + 3 ^ 40 * 1943671 * 2
def baseEnd_1943671 : Nat := 221786101601148913771939

theorem tailTrace_1943671 : CollatzResearch.WordTrace tailWord_1943671 prefixEnd_1943671 221786101601148913771939 := by
  unfold tailWord_1943671
  simp only [CollatzResearch.WordTrace]
  refine ⟨70891505341419394423814867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47261003560946262949209911 70891505341419394423814867)
  ·
    refine ⟨106337258012129091635722301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70891505341419394423814867 106337258012129091635722301)
    ·
      refine ⟨39876471754548409363395863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106337258012129091635722301 39876471754548409363395863)
      ·
        refine ⟨59814707631822614045093795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39876471754548409363395863 59814707631822614045093795)
        ·
          refine ⟨89722061447733921067640693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59814707631822614045093795 89722061447733921067640693)
          ·
            refine ⟨8411443260725055100091315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89722061447733921067640693 8411443260725055100091315)
            ·
              refine ⟨12617164891087582650136973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411443260725055100091315 12617164891087582650136973)
              ·
                refine ⟨4731436834157843493801365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12617164891087582650136973 4731436834157843493801365)
                ·
                  refine ⟨221786101601148913771939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4731436834157843493801365 221786101601148913771939)
                  ·
                    rfl

theorem cell22_1943671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 6].length) (baseStart_1943671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943671 prefixEnd_1943671 := by exact prefixLift 1943671
  have htrace : WordTrace (prefixWord ++ tailWord_1943671) baseStart_1943671 baseEnd_1943671 := by
    simpa [prefixWord, tailWord_1943671, baseEnd_1943671] using wordTrace_append hprefix tailTrace_1943671
  have hstable : (prefixWord ++ tailWord_1943671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943671).length < 2 ^ (prefixWord ++ tailWord_1943671).sum := by decide
  have hdescent : baseEnd_1943671 < baseStart_1943671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943688 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_1943688 : Nat := 118140960795 + 1943688 * 2 ^ 59
def prefixEnd_1943688 : Nat := 4983230072969 + 3 ^ 40 * 1943688 * 2
def baseEnd_1943688 : Nat := 221788041416954787880255

theorem tailTrace_1943688 : CollatzResearch.WordTrace tailWord_1943688 prefixEnd_1943688 221788041416954787880255 := by
  unfold tailWord_1943688
  simp only [CollatzResearch.WordTrace]
  refine ⟨35446062691178903163591859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47261416921571870884789145 35446062691178903163591859)
  ·
    refine ⟨53169094036768354745387789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35446062691178903163591859 53169094036768354745387789)
    ·
      refine ⟨19938410263788133029520421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53169094036768354745387789 19938410263788133029520421)
      ·
        refine ⟨3738451924460274943035079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19938410263788133029520421 3738451924460274943035079)
        ·
          refine ⟨5607677886690412414552619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738451924460274943035079 5607677886690412414552619)
          ·
            refine ⟨8411516830035618621828929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607677886690412414552619 8411516830035618621828929)
            ·
              refine ⟨6308637622526713966371697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411516830035618621828929 6308637622526713966371697)
              ·
                refine ⟨4731478216895035474778773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308637622526713966371697 4731478216895035474778773)
                ·
                  refine ⟨221788041416954787880255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4731478216895035474778773 221788041416954787880255)
                  ·
                    rfl

theorem cell22_1943688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_1943688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943688 prefixEnd_1943688 := by exact prefixLift 1943688
  have htrace : WordTrace (prefixWord ++ tailWord_1943688) baseStart_1943688 baseEnd_1943688 := by
    simpa [prefixWord, tailWord_1943688, baseEnd_1943688] using wordTrace_append hprefix tailTrace_1943688
  have hstable : (prefixWord ++ tailWord_1943688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943688).length < 2 ^ (prefixWord ++ tailWord_1943688).sum := by decide
  have hdescent : baseEnd_1943688 < baseStart_1943688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943690 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_1943690 : Nat := 118140960795 + 1943690 * 2 ^ 59
def prefixEnd_1943690 : Nat := 4983230072969 + 3 ^ 40 * 1943690 * 2
def baseEnd_1943690 : Nat := 665364808891737025090759

theorem tailTrace_1943690 : CollatzResearch.WordTrace tailWord_1943690 prefixEnd_1943690 665364808891737025090759 := by
  unfold tailWord_1943690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17723049582087640167189131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47261465552233707112504349 17723049582087640167189131)
  ·
    refine ⟨26584574373131460250783697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17723049582087640167189131 26584574373131460250783697)
    ·
      refine ⟨19938430779848595188087773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26584574373131460250783697 19938430779848595188087773)
      ·
        refine ⟨7476911542443223195532915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19938430779848595188087773 7476911542443223195532915)
        ·
          refine ⟨11215367313664834793299373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476911542443223195532915 11215367313664834793299373)
          ·
            refine ⟨4205762742624313047487265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11215367313664834793299373 4205762742624313047487265)
            ·
              refine ⟨3154322056968234785615449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205762742624313047487265 3154322056968234785615449)
              ·
                refine ⟨2365741542726176089211587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154322056968234785615449 2365741542726176089211587)
                ·
                  refine ⟨3548612314089264133817381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365741542726176089211587 3548612314089264133817381)
                  ·
                    refine ⟨665364808891737025090759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548612314089264133817381 665364808891737025090759)
                    ·
                      rfl

theorem cell22_1943690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_1943690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943690 prefixEnd_1943690 := by exact prefixLift 1943690
  have htrace : WordTrace (prefixWord ++ tailWord_1943690) baseStart_1943690 baseEnd_1943690 := by
    simpa [prefixWord, tailWord_1943690, baseEnd_1943690] using wordTrace_append hprefix tailTrace_1943690
  have hstable : (prefixWord ++ tailWord_1943690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943690).length < 2 ^ (prefixWord ++ tailWord_1943690).sum := by decide
  have hdescent : baseEnd_1943690 < baseStart_1943690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943701 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1943701 : Nat := 118140960795 + 1943701 * 2 ^ 59
def prefixEnd_1943701 : Nat := 4983230072969 + 3 ^ 40 * 1943701 * 2
def baseEnd_1943701 : Nat := 665368574416536663065725

theorem tailTrace_1943701 : CollatzResearch.WordTrace tailWord_1943701 prefixEnd_1943701 665368574416536663065725 := by
  unfold tailWord_1943701
  simp only [CollatzResearch.WordTrace]
  refine ⟨70892599531310709547406957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47261733020873806364937971 70892599531310709547406957)
  ·
    refine ⟨26584724824241516080277609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70892599531310709547406957 26584724824241516080277609)
    ·
      refine ⟨19938543618181137060208207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26584724824241516080277609 19938543618181137060208207)
      ·
        refine ⟨29907815427271705590312311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19938543618181137060208207 29907815427271705590312311)
        ·
          refine ⟨44861723140907558385468467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29907815427271705590312311 44861723140907558385468467)
          ·
            refine ⟨67292584711361337578202701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44861723140907558385468467 67292584711361337578202701)
            ·
              refine ⟨25234719266760501591826013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67292584711361337578202701 25234719266760501591826013)
              ·
                refine ⟨9463019725035188096934755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25234719266760501591826013 9463019725035188096934755)
                ·
                  refine ⟨14194529587552782145402133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9463019725035188096934755 14194529587552782145402133)
                  ·
                    refine ⟨665368574416536663065725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14194529587552782145402133 665368574416536663065725)
                    ·
                      rfl

theorem cell22_1943701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1943701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943701 prefixEnd_1943701 := by exact prefixLift 1943701
  have htrace : WordTrace (prefixWord ++ tailWord_1943701) baseStart_1943701 baseEnd_1943701 := by
    simpa [prefixWord, tailWord_1943701, baseEnd_1943701] using wordTrace_append hprefix tailTrace_1943701
  have hstable : (prefixWord ++ tailWord_1943701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943701).length < 2 ^ (prefixWord ++ tailWord_1943701).sum := by decide
  have hdescent : baseEnd_1943701 < baseStart_1943701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943722 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_1943722 : Nat := 118140960795 + 1943722 * 2 ^ 59
def prefixEnd_1943722 : Nat := 4983230072969 + 3 ^ 40 * 1943722 * 2
def baseEnd_1943722 : Nat := 221791921048566536096887

theorem tailTrace_1943722 : CollatzResearch.WordTrace tailWord_1943722 prefixEnd_1943722 221791921048566536096887 := by
  unfold tailWord_1943722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17723341366058657533480355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47262243642823086755947613 17723341366058657533480355)
  ·
    refine ⟨26585012049087986300220533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17723341366058657533480355 26585012049087986300220533)
    ·
      refine ⟨2492344879601998715645675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26585012049087986300220533 2492344879601998715645675)
      ·
        refine ⟨3738517319402998073468513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492344879601998715645675 3738517319402998073468513)
        ·
          refine ⟨2803887989552248555101385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738517319402998073468513 2803887989552248555101385)
          ·
            refine ⟨2102915992164186416326039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803887989552248555101385 2102915992164186416326039)
            ·
              refine ⟨3154373988246279624489059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102915992164186416326039 3154373988246279624489059)
              ·
                refine ⟨4731560982369419436733589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154373988246279624489059 4731560982369419436733589)
                ·
                  refine ⟨221791921048566536096887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4731560982369419436733589 221791921048566536096887)
                  ·
                    rfl

theorem cell22_1943722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_1943722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943722 prefixEnd_1943722 := by exact prefixLift 1943722
  have htrace : WordTrace (prefixWord ++ tailWord_1943722) baseStart_1943722 baseEnd_1943722 := by
    simpa [prefixWord, tailWord_1943722, baseEnd_1943722] using wordTrace_append hprefix tailTrace_1943722
  have hstable : (prefixWord ++ tailWord_1943722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943722).length < 2 ^ (prefixWord ++ tailWord_1943722).sum := by decide
  have hdescent : baseEnd_1943722 < baseStart_1943722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943761 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 9]
def baseStart_1943761 : Nat := 118140960795 + 1943761 * 2 ^ 59
def prefixEnd_1943761 : Nat := 4983230072969 + 3 ^ 40 * 1943761 * 2
def baseEnd_1943761 : Nat := 221796371214238835521847

theorem tailTrace_1943761 : CollatzResearch.WordTrace tailWord_1943761 prefixEnd_1943761 221796371214238835521847 := by
  unfold tailWord_1943761
  simp only [CollatzResearch.WordTrace]
  refine ⟨70894787911093339794591137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47263191940728893196394091 70894787911093339794591137)
  ·
    refine ⟨53171090933320004845943353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70894787911093339794591137 53171090933320004845943353)
    ·
      refine ⟨39878318199990003634457515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53171090933320004845943353 39878318199990003634457515)
      ·
        refine ⟨59817477299985005451686273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39878318199990003634457515 59817477299985005451686273)
        ·
          refine ⟨44863107974988754088764705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59817477299985005451686273 44863107974988754088764705)
          ·
            refine ⟨33647330981241565566573529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44863107974988754088764705 33647330981241565566573529)
            ·
              refine ⟨25235498235931174174930147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33647330981241565566573529 25235498235931174174930147)
              ·
                refine ⟨37853247353896761262395221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25235498235931174174930147 37853247353896761262395221)
                ·
                  refine ⟨221796371214238835521847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37853247353896761262395221 221796371214238835521847)
                  ·
                    rfl

theorem cell22_1943761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_1943761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943761 prefixEnd_1943761 := by exact prefixLift 1943761
  have htrace : WordTrace (prefixWord ++ tailWord_1943761) baseStart_1943761 baseEnd_1943761 := by
    simpa [prefixWord, tailWord_1943761, baseEnd_1943761] using wordTrace_append hprefix tailTrace_1943761
  have hstable : (prefixWord ++ tailWord_1943761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943761).length < 2 ^ (prefixWord ++ tailWord_1943761).sum := by decide
  have hdescent : baseEnd_1943761 < baseStart_1943761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943808 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_1943808 : Nat := 118140960795 + 1943808 * 2 ^ 59
def prefixEnd_1943808 : Nat := 4983230072969 + 3 ^ 40 * 1943808 * 2
def baseEnd_1943808 : Nat := 665405202703224050640397

theorem tailTrace_1943808 : CollatzResearch.WordTrace tailWord_1943808 prefixEnd_1943808 665405202703224050640397 := by
  unfold tailWord_1943808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35448251070961533410776039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47264334761282044547701385 35448251070961533410776039)
  ·
    refine ⟨53172376606442300116164059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35448251070961533410776039 53172376606442300116164059)
    ·
      refine ⟨79758564909663450174246089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53172376606442300116164059 79758564909663450174246089)
      ·
        refine ⟨59818923682247587630684567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79758564909663450174246089 59818923682247587630684567)
        ·
          refine ⟨89728385523371381446026851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59818923682247587630684567 89728385523371381446026851)
          ·
            refine ⟨134592578285057072169040277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89728385523371381446026851 134592578285057072169040277)
            ·
              refine ⟨6309027107112050257923763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134592578285057072169040277 6309027107112050257923763)
              ·
                refine ⟨9463540660668075386885645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309027107112050257923763 9463540660668075386885645)
                ·
                  refine ⟨3548827747750528270082117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9463540660668075386885645 3548827747750528270082117)
                  ·
                    refine ⟨665405202703224050640397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548827747750528270082117 665405202703224050640397)
                    ·
                      rfl

theorem cell22_1943808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_1943808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943808 prefixEnd_1943808 := by exact prefixLift 1943808
  have htrace : WordTrace (prefixWord ++ tailWord_1943808) baseStart_1943808 baseEnd_1943808 := by
    simpa [prefixWord, tailWord_1943808, baseEnd_1943808] using wordTrace_append hprefix tailTrace_1943808
  have hstable : (prefixWord ++ tailWord_1943808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943808).length < 2 ^ (prefixWord ++ tailWord_1943808).sum := by decide
  have hdescent : baseEnd_1943808 < baseStart_1943808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943825 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1943825 : Nat := 118140960795 + 1943825 * 2 ^ 59
def prefixEnd_1943825 : Nat := 4983230072969 + 3 ^ 40 * 1943825 * 2
def baseEnd_1943825 : Nat := 665411022150641672965345

theorem tailTrace_1943825 : CollatzResearch.WordTrace tailWord_1943825 prefixEnd_1943825 665411022150641672965345 := by
  unfold tailWord_1943825
  simp only [CollatzResearch.WordTrace]
  refine ⟨70897122182861478724920929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47264748121907652483280619 70897122182861478724920929)
  ·
    refine ⟨53172841637146109043690697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70897122182861478724920929 53172841637146109043690697)
    ·
      refine ⟨39879631227859581782768023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53172841637146109043690697 39879631227859581782768023)
      ·
        refine ⟨59819446841789372674152035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39879631227859581782768023 59819446841789372674152035)
        ·
          refine ⟨89729170262684059011228053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59819446841789372674152035 89729170262684059011228053)
          ·
            refine ⟨4206054856063315266151315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89729170262684059011228053 4206054856063315266151315)
            ·
              refine ⟨6309082284094972899226973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206054856063315266151315 6309082284094972899226973)
              ·
                refine ⟨2365905856535614837210115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6309082284094972899226973 2365905856535614837210115)
                ·
                  refine ⟨3548858784803422255815173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365905856535614837210115 3548858784803422255815173)
                  ·
                    refine ⟨665411022150641672965345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3548858784803422255815173 665411022150641672965345)
                    ·
                      rfl

theorem cell22_1943825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1943825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943825 prefixEnd_1943825 := by exact prefixLift 1943825
  have htrace : WordTrace (prefixWord ++ tailWord_1943825) baseStart_1943825 baseEnd_1943825 := by
    simpa [prefixWord, tailWord_1943825, baseEnd_1943825] using wordTrace_append hprefix tailTrace_1943825
  have hstable : (prefixWord ++ tailWord_1943825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943825).length < 2 ^ (prefixWord ++ tailWord_1943825).sum := by decide
  have hdescent : baseEnd_1943825 < baseStart_1943825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943840 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_1943840 : Nat := 118140960795 + 1943840 * 2 ^ 59
def prefixEnd_1943840 : Nat := 4983230072969 + 3 ^ 40 * 1943840 * 2
def baseEnd_1943840 : Nat := 221805385652395544613433

theorem tailTrace_1943840 : CollatzResearch.WordTrace tailWord_1943840 prefixEnd_1943840 221805385652395544613433 := by
  unfold tailWord_1943840
  simp only [CollatzResearch.WordTrace]
  refine ⟨35448834638903568143358487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47265112851871424191144649 35448834638903568143358487)
  ·
    refine ⟨53173251958355352215037731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35448834638903568143358487 53173251958355352215037731)
    ·
      refine ⟨79759877937533028322556597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53173251958355352215037731 79759877937533028322556597)
      ·
        refine ⟨7477488556643721405239681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79759877937533028322556597 7477488556643721405239681)
        ·
          refine ⟨5608116417482791053929761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7477488556643721405239681 5608116417482791053929761)
          ·
            refine ⟨4206087313112093290447321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5608116417482791053929761 4206087313112093290447321)
            ·
              refine ⟨3154565484834069967835491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4206087313112093290447321 3154565484834069967835491)
              ·
                refine ⟨4731848227251104951753237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154565484834069967835491 4731848227251104951753237)
                ·
                  refine ⟨221805385652395544613433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4731848227251104951753237 221805385652395544613433)
                  ·
                    rfl

theorem cell22_1943840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_1943840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943840 prefixEnd_1943840 := by exact prefixLift 1943840
  have htrace : WordTrace (prefixWord ++ tailWord_1943840) baseStart_1943840 baseEnd_1943840 := by
    simpa [prefixWord, tailWord_1943840, baseEnd_1943840] using wordTrace_append hprefix tailTrace_1943840
  have hstable : (prefixWord ++ tailWord_1943840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943840).length < 2 ^ (prefixWord ++ tailWord_1943840).sum := by decide
  have hdescent : baseEnd_1943840 < baseStart_1943840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943855 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 2, 3]
def baseStart_1943855 : Nat := 118140960795 + 1943855 * 2 ^ 59
def prefixEnd_1943855 : Nat := 4983230072969 + 3 ^ 40 * 1943855 * 2
def baseEnd_1943855 : Nat := 665421291763731594715253

theorem tailTrace_1943855 : CollatzResearch.WordTrace tailWord_1943855 prefixEnd_1943855 665421291763731594715253 := by
  unfold tailWord_1943855
  simp only [CollatzResearch.WordTrace]
  refine ⟨70898216372752793848513019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47265477581835195899008679 70898216372752793848513019)
  ·
    refine ⟨106347324559129190772769529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70898216372752793848513019 106347324559129190772769529)
    ·
      refine ⟨79760493419346893079577147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106347324559129190772769529 79760493419346893079577147)
      ·
        refine ⟨119640740129020339619365721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79760493419346893079577147 119640740129020339619365721)
        ·
          refine ⟨89730555096765254714524291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119640740129020339619365721 89730555096765254714524291)
          ·
            refine ⟨134595832645147882071786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89730555096765254714524291 134595832645147882071786437)
            ·
              refine ⟨25236718620965227888459957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134595832645147882071786437 25236718620965227888459957)
              ·
                refine ⟨2365942370715490114543121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25236718620965227888459957 2365942370715490114543121)
                ·
                  refine ⟨1774456778036617585907341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365942370715490114543121 1774456778036617585907341)
                  ·
                    refine ⟨665421291763731594715253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774456778036617585907341 665421291763731594715253)
                    ·
                      rfl

theorem cell22_1943855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_1943855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943855 prefixEnd_1943855 := by exact prefixLift 1943855
  have htrace : WordTrace (prefixWord ++ tailWord_1943855) baseStart_1943855 baseEnd_1943855 := by
    simpa [prefixWord, tailWord_1943855, baseEnd_1943855] using wordTrace_append hprefix tailTrace_1943855
  have hstable : (prefixWord ++ tailWord_1943855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943855).length < 2 ^ (prefixWord ++ tailWord_1943855).sum := by decide
  have hdescent : baseEnd_1943855 < baseStart_1943855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943868 : List Nat := [2, 2, 2, 2, 1, 2, 3, 8]
def baseStart_1943868 : Nat := 118140960795 + 1943868 * 2 ^ 59
def prefixEnd_1943868 : Nat := 4983230072969 + 3 ^ 40 * 1943868 * 2
def baseEnd_1943868 : Nat := 73936193547711543793357

theorem tailTrace_1943868 : CollatzResearch.WordTrace tailWord_1943868 prefixEnd_1943868 73936193547711543793357 := by
  unfold tailWord_1943868
  simp only [CollatzResearch.WordTrace]
  refine ⟨35449345260852848534368129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47265793681137131379157505 35449345260852848534368129)
  ·
    refine ⟨26587008945639636400776097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35449345260852848534368129 26587008945639636400776097)
    ·
      refine ⟨19940256709229727300582073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26587008945639636400776097 19940256709229727300582073)
      ·
        refine ⟨14955192531922295475436555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19940256709229727300582073 14955192531922295475436555)
        ·
          refine ⟨22432788797883443213154833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955192531922295475436555 22432788797883443213154833)
          ·
            refine ⟨16824591598412582409866125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432788797883443213154833 16824591598412582409866125)
            ·
              refine ⟨6309221849404718403699797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16824591598412582409866125 6309221849404718403699797)
              ·
                refine ⟨73936193547711543793357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6309221849404718403699797 73936193547711543793357)
                ·
                  rfl

theorem cell22_1943868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_1943868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943868 prefixEnd_1943868 := by exact prefixLift 1943868
  have htrace : WordTrace (prefixWord ++ tailWord_1943868) baseStart_1943868 baseEnd_1943868 := by
    simpa [prefixWord, tailWord_1943868, baseEnd_1943868] using wordTrace_append hprefix tailTrace_1943868
  have hstable : (prefixWord ++ tailWord_1943868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943868).length < 2 ^ (prefixWord ++ tailWord_1943868).sum := by decide
  have hdescent : baseEnd_1943868 < baseStart_1943868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943870 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1943870 : Nat := 118140960795 + 1943870 * 2 ^ 59
def prefixEnd_1943870 : Nat := 4983230072969 + 3 ^ 40 * 1943870 * 2
def baseEnd_1943870 : Nat := 665426426570276555590207

theorem tailTrace_1943870 : CollatzResearch.WordTrace tailWord_1943870 prefixEnd_1943870 665426426570276555590207 := by
  unfold tailWord_1943870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862345433462306426288633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47265842311798967606872709 8862345433462306426288633)
  ·
    refine ⟨6646759075096729819716475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8862345433462306426288633 6646759075096729819716475)
    ·
      refine ⟨9970138612645094729574713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646759075096729819716475 9970138612645094729574713)
      ·
        refine ⟨7477603959483821047181035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9970138612645094729574713 7477603959483821047181035)
        ·
          refine ⟨11216405939225731570771553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7477603959483821047181035 11216405939225731570771553)
          ·
            refine ⟨8412304454419298678078665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11216405939225731570771553 8412304454419298678078665)
            ·
              refine ⟨6309228340814474008558999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412304454419298678078665 6309228340814474008558999)
              ·
                refine ⟨9463842511221711012838499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309228340814474008558999 9463842511221711012838499)
                ·
                  refine ⟨14195763766832566519257749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9463842511221711012838499 14195763766832566519257749)
                  ·
                    refine ⟨665426426570276555590207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14195763766832566519257749 665426426570276555590207)
                    ·
                      rfl

theorem cell22_1943870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1943870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943870 prefixEnd_1943870 := by exact prefixLift 1943870
  have htrace : WordTrace (prefixWord ++ tailWord_1943870) baseStart_1943870 baseEnd_1943870 := by
    simpa [prefixWord, tailWord_1943870, baseEnd_1943870] using wordTrace_append hprefix tailTrace_1943870
  have hstable : (prefixWord ++ tailWord_1943870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943870).length < 2 ^ (prefixWord ++ tailWord_1943870).sum := by decide
  have hdescent : baseEnd_1943870 < baseStart_1943870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943898 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1943898 : Nat := 118140960795 + 1943898 * 2 ^ 59
def prefixEnd_1943898 : Nat := 4983230072969 + 3 ^ 40 * 1943898 * 2
def baseEnd_1943898 : Nat := 665436011542493815890121

theorem tailTrace_1943898 : CollatzResearch.WordTrace tailWord_1943898 prefixEnd_1943898 665436011542493815890121 := by
  unfold tailWord_1943898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724946177899253048082087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47266523141064674794885565 17724946177899253048082087)
  ·
    refine ⟨26587419266848879572123131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17724946177899253048082087 26587419266848879572123131)
    ·
      refine ⟨39881128900273319358184697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26587419266848879572123131 39881128900273319358184697)
      ·
        refine ⟨29910846675204989518638523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39881128900273319358184697 29910846675204989518638523)
        ·
          refine ⟨44866270012807484277957785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29910846675204989518638523 44866270012807484277957785)
          ·
            refine ⟨33649702509605613208468339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44866270012807484277957785 33649702509605613208468339)
            ·
              refine ⟨50474553764408419812702509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33649702509605613208468339 50474553764408419812702509)
              ·
                refine ⟨18927957661653157429763441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50474553764408419812702509 18927957661653157429763441)
                ·
                  refine ⟨14195968246239868072322581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18927957661653157429763441 14195968246239868072322581)
                  ·
                    refine ⟨665436011542493815890121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14195968246239868072322581 665436011542493815890121)
                    ·
                      rfl

theorem cell22_1943898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1943898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943898 prefixEnd_1943898 := by exact prefixLift 1943898
  have htrace : WordTrace (prefixWord ++ tailWord_1943898) baseStart_1943898 baseEnd_1943898 := by
    simpa [prefixWord, tailWord_1943898, baseEnd_1943898] using wordTrace_append hprefix tailTrace_1943898
  have hstable : (prefixWord ++ tailWord_1943898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943898).length < 2 ^ (prefixWord ++ tailWord_1943898).sum := by decide
  have hdescent : baseEnd_1943898 < baseStart_1943898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943906 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1943906 : Nat := 118140960795 + 1943906 * 2 ^ 59
def prefixEnd_1943906 : Nat := 4983230072969 + 3 ^ 40 * 1943906 * 2
def baseEnd_1943906 : Nat := 665438750105984461690097

theorem tailTrace_1943906 : CollatzResearch.WordTrace tailWord_1943906 prefixEnd_1943906 665438750105984461690097 := by
  unfold tailWord_1943906
  simp only [CollatzResearch.WordTrace]
  refine ⟨17725019123892007389654893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47266717663712019705746381 17725019123892007389654893)
  ·
    refine ⟨6646882171459502771120585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17725019123892007389654893 6646882171459502771120585)
    ·
      refine ⟨4985161628594627078340439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6646882171459502771120585 4985161628594627078340439)
      ·
        refine ⟨7477742442891940617510659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985161628594627078340439 7477742442891940617510659)
        ·
          refine ⟨11216613664337910926265989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7477742442891940617510659 11216613664337910926265989)
          ·
            refine ⟨2103115062063358298674873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11216613664337910926265989 2103115062063358298674873)
            ·
              refine ⟨1577336296547518724006155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103115062063358298674873 1577336296547518724006155)
              ·
                refine ⟨2366004444821278086009233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577336296547518724006155 2366004444821278086009233)
                ·
                  refine ⟨1774503333615958564506925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366004444821278086009233 1774503333615958564506925)
                  ·
                    refine ⟨665438750105984461690097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774503333615958564506925 665438750105984461690097)
                    ·
                      rfl

theorem cell22_1943906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1943906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943906 prefixEnd_1943906 := by exact prefixLift 1943906
  have htrace : WordTrace (prefixWord ++ tailWord_1943906) baseStart_1943906 baseEnd_1943906 := by
    simpa [prefixWord, tailWord_1943906, baseEnd_1943906] using wordTrace_append hprefix tailTrace_1943906
  have hstable : (prefixWord ++ tailWord_1943906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943906).length < 2 ^ (prefixWord ++ tailWord_1943906).sum := by decide
  have hdescent : baseEnd_1943906 < baseStart_1943906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943975 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 8]
def baseStart_1943975 : Nat := 118140960795 + 1943975 * 2 ^ 59
def prefixEnd_1943975 : Nat := 4983230072969 + 3 ^ 40 * 1943975 * 2
def baseEnd_1943975 : Nat := 221820790072030427238295

theorem tailTrace_1943975 : CollatzResearch.WordTrace tailWord_1943975 prefixEnd_1943975 221820790072030427238295 := by
  unfold tailWord_1943975
  simp only [CollatzResearch.WordTrace]
  refine ⟨70902593132318054342881379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47268395421545369561920919 70902593132318054342881379)
  ·
    refine ⟨106353889698477081514322069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70902593132318054342881379 106353889698477081514322069)
    ·
      refine ⟨4985338579616113195983847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106353889698477081514322069 4985338579616113195983847)
      ·
        refine ⟨7478007869424169793975771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985338579616113195983847 7478007869424169793975771)
        ·
          refine ⟨11217011804136254690963657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478007869424169793975771 11217011804136254690963657)
          ·
            refine ⟨8412758853102191018222743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11217011804136254690963657 8412758853102191018222743)
            ·
              refine ⟨12619138279653286527334115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412758853102191018222743 12619138279653286527334115)
              ·
                refine ⟨18928707419479929791001173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12619138279653286527334115 18928707419479929791001173)
                ·
                  refine ⟨221820790072030427238295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18928707419479929791001173 221820790072030427238295)
                  ·
                    rfl

theorem cell22_1943975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 8].length) (baseStart_1943975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1943975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1943975 prefixEnd_1943975 := by exact prefixLift 1943975
  have htrace : WordTrace (prefixWord ++ tailWord_1943975) baseStart_1943975 baseEnd_1943975 := by
    simpa [prefixWord, tailWord_1943975, baseEnd_1943975] using wordTrace_append hprefix tailTrace_1943975
  have hstable : (prefixWord ++ tailWord_1943975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943975).length < 2 ^ (prefixWord ++ tailWord_1943975).sum := by decide
  have hdescent : baseEnd_1943975 < baseStart_1943975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944007 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1944007 : Nat := 118140960795 + 1944007 * 2 ^ 59
def prefixEnd_1944007 : Nat := 4983230072969 + 3 ^ 40 * 1944007 * 2
def baseEnd_1944007 : Nat := 665473324470053864914787

theorem tailTrace_1944007 : CollatzResearch.WordTrace tailWord_1944007 prefixEnd_1944007 665473324470053864914787 := by
  unfold tailWord_1944007
  simp only [CollatzResearch.WordTrace]
  refine ⟨70903760268202123808046275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47269173512134749205364183 70903760268202123808046275)
  ·
    refine ⟨106355640402303185712069413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70903760268202123808046275 106355640402303185712069413)
    ·
      refine ⟨19941682575431847321013015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106355640402303185712069413 19941682575431847321013015)
      ·
        refine ⟨29912523863147770981519523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19941682575431847321013015 29912523863147770981519523)
        ·
          refine ⟨44868785794721656472279285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29912523863147770981519523 44868785794721656472279285)
          ·
            refine ⟨4206448668255155294276183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44868785794721656472279285 4206448668255155294276183)
            ·
              refine ⟨6309673002382732941414275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206448668255155294276183 6309673002382732941414275)
              ·
                refine ⟨9464509503574099412121413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309673002382732941414275 9464509503574099412121413)
                ·
                  refine ⟨1774595531920143639772765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9464509503574099412121413 1774595531920143639772765)
                  ·
                    refine ⟨665473324470053864914787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774595531920143639772765 665473324470053864914787)
                    ·
                      rfl

theorem cell22_1944007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1944007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944007 prefixEnd_1944007 := by exact prefixLift 1944007
  have htrace : WordTrace (prefixWord ++ tailWord_1944007) baseStart_1944007 baseEnd_1944007 := by
    simpa [prefixWord, tailWord_1944007, baseEnd_1944007] using wordTrace_append hprefix tailTrace_1944007
  have hstable : (prefixWord ++ tailWord_1944007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944007).length < 2 ^ (prefixWord ++ tailWord_1944007).sum := by decide
  have hdescent : baseEnd_1944007 < baseStart_1944007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944022 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1944022 : Nat := 118140960795 + 1944022 * 2 ^ 59
def prefixEnd_1944022 : Nat := 4983230072969 + 3 ^ 40 * 1944022 * 2
def baseEnd_1944022 : Nat := 665478459276598825789741

theorem tailTrace_1944022 : CollatzResearch.WordTrace tailWord_1944022 prefixEnd_1944022 665478459276598825789741 := by
  unfold tailWord_1944022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431519210196736335615145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47269538242098520913228213 4431519210196736335615145)
  ·
    refine ⟨3323639407647552251711359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4431519210196736335615145 3323639407647552251711359)
    ·
      refine ⟨4985459111471328377567039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323639407647552251711359 4985459111471328377567039)
      ·
        refine ⟨7478188667206992566350559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985459111471328377567039 7478188667206992566350559)
        ·
          refine ⟨11217283000810488849525839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478188667206992566350559 11217283000810488849525839)
          ·
            refine ⟨16825924501215733274288759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217283000810488849525839 16825924501215733274288759)
            ·
              refine ⟨25238886751823599911433139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16825924501215733274288759 25238886751823599911433139)
              ·
                refine ⟨37858330127735399867149709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25238886751823599911433139 37858330127735399867149709)
                ·
                  refine ⟨14196873797900774950181141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37858330127735399867149709 14196873797900774950181141)
                  ·
                    refine ⟨665478459276598825789741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14196873797900774950181141 665478459276598825789741)
                    ·
                      rfl

theorem cell22_1944022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1944022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944022 prefixEnd_1944022 := by exact prefixLift 1944022
  have htrace : WordTrace (prefixWord ++ tailWord_1944022) baseStart_1944022 baseEnd_1944022 := by
    simpa [prefixWord, tailWord_1944022, baseEnd_1944022] using wordTrace_append hprefix tailTrace_1944022
  have hstable : (prefixWord ++ tailWord_1944022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944022).length < 2 ^ (prefixWord ++ tailWord_1944022).sum := by decide
  have hdescent : baseEnd_1944022 < baseStart_1944022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944037 : List Nat := [1, 3, 1, 5, 2, 1, 1, 8]
def baseStart_1944037 : Nat := 118140960795 + 1944037 * 2 ^ 59
def prefixEnd_1944037 : Nat := 4983230072969 + 3 ^ 40 * 1944037 * 2
def baseEnd_1944037 : Nat := 73942621564793754073855

theorem tailTrace_1944037 : CollatzResearch.WordTrace tailWord_1944037 prefixEnd_1944037 73942621564793754073855 := by
  unfold tailWord_1944037
  simp only [CollatzResearch.WordTrace]
  refine ⟨70904854458093438931638365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47269902972062292621092243 70904854458093438931638365)
  ·
    refine ⟨26589320421785039599364387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70904854458093438931638365 26589320421785039599364387)
    ·
      refine ⟨39883980632677559399046581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26589320421785039599364387 39883980632677559399046581)
      ·
        refine ⟨3739123184313521193660617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39883980632677559399046581 3739123184313521193660617)
        ·
          refine ⟨2804342388235140895245463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739123184313521193660617 2804342388235140895245463)
          ·
            refine ⟨4206513582352711342868195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804342388235140895245463 4206513582352711342868195)
            ·
              refine ⟨6309770373529067014302293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206513582352711342868195 6309770373529067014302293)
              ·
                refine ⟨73942621564793754073855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6309770373529067014302293 73942621564793754073855)
                ·
                  rfl

theorem cell22_1944037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 8].length) (baseStart_1944037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944037 prefixEnd_1944037 := by exact prefixLift 1944037
  have htrace : WordTrace (prefixWord ++ tailWord_1944037) baseStart_1944037 baseEnd_1944037 := by
    simpa [prefixWord, tailWord_1944037, baseEnd_1944037] using wordTrace_append hprefix tailTrace_1944037
  have hstable : (prefixWord ++ tailWord_1944037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944037).length < 2 ^ (prefixWord ++ tailWord_1944037).sum := by decide
  have hdescent : baseEnd_1944037 < baseStart_1944037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944069 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_1944069 : Nat := 118140960795 + 1944069 * 2 ^ 59
def prefixEnd_1944069 : Nat := 4983230072969 + 3 ^ 40 * 1944069 * 2
def baseEnd_1944069 : Nat := 665494548337106369864597

theorem tailTrace_1944069 : CollatzResearch.WordTrace tailWord_1944069 prefixEnd_1944069 665494548337106369864597 := by
  unfold tailWord_1944069
  simp only [CollatzResearch.WordTrace]
  refine ⟨70906021593977508396803261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47270681062651672264535507 70906021593977508396803261)
  ·
    refine ⟨26589758097741565648801223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70906021593977508396803261 26589758097741565648801223)
    ·
      refine ⟨39884637146612348473201835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26589758097741565648801223 39884637146612348473201835)
      ·
        refine ⟨59826955719918522709802753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39884637146612348473201835 59826955719918522709802753)
        ·
          refine ⟨44870216789938892032352065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59826955719918522709802753 44870216789938892032352065)
          ·
            refine ⟨33652662592454169024264049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44870216789938892032352065 33652662592454169024264049)
            ·
              refine ⟨25239496944340626768198037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33652662592454169024264049 25239496944340626768198037)
              ·
                refine ⟨1183101419265966879759283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25239496944340626768198037 1183101419265966879759283)
                ·
                  refine ⟨1774652128898950319638925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183101419265966879759283 1774652128898950319638925)
                  ·
                    refine ⟨665494548337106369864597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774652128898950319638925 665494548337106369864597)
                    ·
                      rfl

theorem cell22_1944069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_1944069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944069 prefixEnd_1944069 := by exact prefixLift 1944069
  have htrace : WordTrace (prefixWord ++ tailWord_1944069) baseStart_1944069 baseEnd_1944069 := by
    simpa [prefixWord, tailWord_1944069, baseEnd_1944069] using wordTrace_append hprefix tailTrace_1944069
  have hstable : (prefixWord ++ tailWord_1944069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944069).length < 2 ^ (prefixWord ++ tailWord_1944069).sum := by decide
  have hdescent : baseEnd_1944069 < baseStart_1944069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944112 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_1944112 : Nat := 118140960795 + 1944112 * 2 ^ 59
def prefixEnd_1944112 : Nat := 4983230072969 + 3 ^ 40 * 1944112 * 2
def baseEnd_1944112 : Nat := 665509268115868591039465

theorem tailTrace_1944112 : CollatzResearch.WordTrace tailWord_1944112 prefixEnd_1944112 665509268115868591039465 := by
  unfold tailWord_1944112
  simp only [CollatzResearch.WordTrace]
  refine ⟨35453794966410863370309295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47271726621881151160412393 35453794966410863370309295)
  ·
    refine ⟨53180692449616295055463943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35453794966410863370309295 53180692449616295055463943)
    ·
      refine ⟨79771038674424442583195915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53180692449616295055463943 79771038674424442583195915)
      ·
        refine ⟨119656558011636663874793873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79771038674424442583195915 119656558011636663874793873)
        ·
          refine ⟨89742418508727497906095405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119656558011636663874793873 89742418508727497906095405)
          ·
            refine ⟨33653406940772811714785777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89742418508727497906095405 33653406940772811714785777)
            ·
              refine ⟨25240055205579608786089333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33653406940772811714785777 25240055205579608786089333)
              ·
                refine ⟨2366255175523088323695875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25240055205579608786089333 2366255175523088323695875)
                ·
                  refine ⟨3549382763284632485543813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366255175523088323695875 3549382763284632485543813)
                  ·
                    refine ⟨665509268115868591039465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549382763284632485543813 665509268115868591039465)
                    ·
                      rfl

theorem cell22_1944112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_1944112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944112 prefixEnd_1944112 := by exact prefixLift 1944112
  have htrace : WordTrace (prefixWord ++ tailWord_1944112) baseStart_1944112 baseEnd_1944112 := by
    simpa [prefixWord, tailWord_1944112, baseEnd_1944112] using wordTrace_append hprefix tailTrace_1944112
  have hstable : (prefixWord ++ tailWord_1944112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944112).length < 2 ^ (prefixWord ++ tailWord_1944112).sum := by decide
  have hdescent : baseEnd_1944112 < baseStart_1944112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944142 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1944142 : Nat := 118140960795 + 1944142 * 2 ^ 59
def prefixEnd_1944142 : Nat := 4983230072969 + 3 ^ 40 * 1944142 * 2
def baseEnd_1944142 : Nat := 665519537728958512789373

theorem tailTrace_1944142 : CollatzResearch.WordTrace tailWord_1944142 prefixEnd_1944142 665519537728958512789373 := by
  unfold tailWord_1944142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863585515339130233026335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47272456081808694576140453 8863585515339130233026335)
  ·
    refine ⟨13295378273008695349539503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8863585515339130233026335 13295378273008695349539503)
    ·
      refine ⟨19943067409513043024309255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13295378273008695349539503 19943067409513043024309255)
      ·
        refine ⟨29914601114269564536463883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19943067409513043024309255 29914601114269564536463883)
        ·
          refine ⟨44871901671404346804695825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29914601114269564536463883 44871901671404346804695825)
          ·
            refine ⟨33653926253553260103521869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44871901671404346804695825 33653926253553260103521869)
            ·
              refine ⟨12620222345082472538820701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33653926253553260103521869 12620222345082472538820701)
              ·
                refine ⟨4732583379405927202057763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12620222345082472538820701 4732583379405927202057763)
                ·
                  refine ⟨7098875069108890803086645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732583379405927202057763 7098875069108890803086645)
                  ·
                    refine ⟨665519537728958512789373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7098875069108890803086645 665519537728958512789373)
                    ·
                      rfl

theorem cell22_1944142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1944142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944142 prefixEnd_1944142 := by exact prefixLift 1944142
  have htrace : WordTrace (prefixWord ++ tailWord_1944142) baseStart_1944142 baseEnd_1944142 := by
    simpa [prefixWord, tailWord_1944142, baseEnd_1944142] using wordTrace_append hprefix tailTrace_1944142
  have hstable : (prefixWord ++ tailWord_1944142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944142).length < 2 ^ (prefixWord ++ tailWord_1944142).sum := by decide
  have hdescent : baseEnd_1944142 < baseStart_1944142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944238 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1944238 : Nat := 118140960795 + 1944238 * 2 ^ 59
def prefixEnd_1944238 : Nat := 4983230072969 + 3 ^ 40 * 1944238 * 2
def baseEnd_1944238 : Nat := 665552400490846262389079

theorem tailTrace_1944238 : CollatzResearch.WordTrace tailWord_1944238 prefixEnd_1944238 665552400490846262389079 := by
  unfold tailWord_1944238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864023191295656282463171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47274790353576833506470245 8864023191295656282463171)
  ·
    refine ⟨13296034786943484423694757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8864023191295656282463171 13296034786943484423694757)
    ·
      refine ⟨2493006522551903329442767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13296034786943484423694757 2493006522551903329442767)
      ·
        refine ⟨3739509783827854994164151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493006522551903329442767 3739509783827854994164151)
        ·
          refine ⟨5609264675741782491246227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3739509783827854994164151 5609264675741782491246227)
          ·
            refine ⟨8413897013612673736869341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609264675741782491246227 8413897013612673736869341)
            ·
              refine ⟨3155211380104752651326003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8413897013612673736869341 3155211380104752651326003)
              ·
                refine ⟨4732817070157128976989005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155211380104752651326003 4732817070157128976989005)
                ·
                  refine ⟨1774806401308923366370877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4732817070157128976989005 1774806401308923366370877)
                  ·
                    refine ⟨665552400490846262389079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774806401308923366370877 665552400490846262389079)
                    ·
                      rfl

theorem cell22_1944238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1944238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944238 prefixEnd_1944238 := by exact prefixLift 1944238
  have htrace : WordTrace (prefixWord ++ tailWord_1944238) baseStart_1944238 baseEnd_1944238 := by
    simpa [prefixWord, tailWord_1944238, baseEnd_1944238] using wordTrace_append hprefix tailTrace_1944238
  have hstable : (prefixWord ++ tailWord_1944238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944238).length < 2 ^ (prefixWord ++ tailWord_1944238).sum := by decide
  have hdescent : baseEnd_1944238 < baseStart_1944238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944264 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_1944264 : Nat := 118140960795 + 1944264 * 2 ^ 59
def prefixEnd_1944264 : Nat := 4983230072969 + 3 ^ 40 * 1944264 * 2
def baseEnd_1944264 : Nat := 665561300822190861238999

theorem tailTrace_1944264 : CollatzResearch.WordTrace tailWord_1944264 prefixEnd_1944264 665561300822190861238999 := by
  unfold tailWord_1944264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456566914135528350075923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47275422552180704466767897 35456566914135528350075923)
  ·
    refine ⟨53184850371203292525113885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35456566914135528350075923 53184850371203292525113885)
    ·
      refine ⟨19944318889201234696917707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53184850371203292525113885 19944318889201234696917707)
      ·
        refine ⟨29916478333801852045376561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19944318889201234696917707 29916478333801852045376561)
        ·
          refine ⟨22437358750351389034032421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29916478333801852045376561 22437358750351389034032421)
          ·
            refine ⟨4207004765690885443881079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22437358750351389034032421 4207004765690885443881079)
            ·
              refine ⟨6310507148536328165821619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207004765690885443881079 6310507148536328165821619)
              ·
                refine ⟨9465760722804492248732429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310507148536328165821619 9465760722804492248732429)
                ·
                  refine ⟨3549660271051684593274661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9465760722804492248732429 3549660271051684593274661)
                  ·
                    refine ⟨665561300822190861238999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549660271051684593274661 665561300822190861238999)
                    ·
                      rfl

theorem cell22_1944264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_1944264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944264 prefixEnd_1944264 := by exact prefixLift 1944264
  have htrace : WordTrace (prefixWord ++ tailWord_1944264) baseStart_1944264 baseEnd_1944264 := by
    simpa [prefixWord, tailWord_1944264, baseEnd_1944264] using wordTrace_append hprefix tailTrace_1944264
  have hstable : (prefixWord ++ tailWord_1944264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944264).length < 2 ^ (prefixWord ++ tailWord_1944264).sum := by decide
  have hdescent : baseEnd_1944264 < baseStart_1944264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944281 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 1, 4]
def baseStart_1944281 : Nat := 118140960795 + 1944281 * 2 ^ 59
def prefixEnd_1944281 : Nat := 4983230072969 + 3 ^ 40 * 1944281 * 2
def baseEnd_1944281 : Nat := 665567120269608483563947

theorem tailTrace_1944281 : CollatzResearch.WordTrace tailWord_1944281 prefixEnd_1944281 665567120269608483563947 := by
  unfold tailWord_1944281
  simp only [CollatzResearch.WordTrace]
  refine ⟨70913753869209468603520697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47275835912806312402347131 70913753869209468603520697)
  ·
    refine ⟨53185315401907101452640523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70913753869209468603520697 53185315401907101452640523)
    ·
      refine ⟨79777973102860652178960785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53185315401907101452640523 79777973102860652178960785)
      ·
        refine ⟨59833479827145489134220589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79777973102860652178960785 59833479827145489134220589)
        ·
          refine ⟨22437554935179558425332721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59833479827145489134220589 22437554935179558425332721)
          ·
            refine ⟨16828166201384668818999541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22437554935179558425332721 16828166201384668818999541)
            ·
              refine ⟨1577640581379812701781207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16828166201384668818999541 1577640581379812701781207)
              ·
                refine ⟨2366460872069719052671811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577640581379812701781207 2366460872069719052671811)
                ·
                  refine ⟨3549691308104578579007717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366460872069719052671811 3549691308104578579007717)
                  ·
                    refine ⟨665567120269608483563947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549691308104578579007717 665567120269608483563947)
                    ·
                      rfl

theorem cell22_1944281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_1944281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944281 prefixEnd_1944281 := by exact prefixLift 1944281
  have htrace : WordTrace (prefixWord ++ tailWord_1944281) baseStart_1944281 baseEnd_1944281 := by
    simpa [prefixWord, tailWord_1944281, baseEnd_1944281] using wordTrace_append hprefix tailTrace_1944281
  have hstable : (prefixWord ++ tailWord_1944281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944281).length < 2 ^ (prefixWord ++ tailWord_1944281).sum := by decide
  have hdescent : baseEnd_1944281 < baseStart_1944281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944339 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 5, 3]
def baseStart_1944339 : Nat := 118140960795 + 1944339 * 2 ^ 59
def prefixEnd_1944339 : Nat := 4983230072969 + 3 ^ 40 * 1944339 * 2
def baseEnd_1944339 : Nat := 665586974854915665613769

theorem tailTrace_1944339 : CollatzResearch.WordTrace tailWord_1944339 prefixEnd_1944339 665586974854915665613769 := by
  unfold tailWord_1944339
  simp only [CollatzResearch.WordTrace]
  refine ⟨70915869302999344509132071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47277246201999563006088047 70915869302999344509132071)
  ·
    refine ⟨106373803954499016763698107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70915869302999344509132071 106373803954499016763698107)
    ·
      refine ⟨159560705931748525145547161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106373803954499016763698107 159560705931748525145547161)
      ·
        refine ⟨119670529448811393859160371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159560705931748525145547161 119670529448811393859160371)
        ·
          refine ⟨179505794173217090788740557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119670529448811393859160371 179505794173217090788740557)
          ·
            refine ⟨67314672814956409045777709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179505794173217090788740557 67314672814956409045777709)
            ·
              refine ⟨25243002305608653392166641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67314672814956409045777709 25243002305608653392166641)
              ·
                refine ⟨18932251729206490044124981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25243002305608653392166641 18932251729206490044124981)
                ·
                  refine ⟨1774898599613108441636717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18932251729206490044124981 1774898599613108441636717)
                  ·
                    refine ⟨665586974854915665613769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774898599613108441636717 665586974854915665613769)
                    ·
                      rfl

theorem cell22_1944339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 3].length) (baseStart_1944339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944339 prefixEnd_1944339 := by exact prefixLift 1944339
  have htrace : WordTrace (prefixWord ++ tailWord_1944339) baseStart_1944339 baseEnd_1944339 := by
    simpa [prefixWord, tailWord_1944339, baseEnd_1944339] using wordTrace_append hprefix tailTrace_1944339
  have hstable : (prefixWord ++ tailWord_1944339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944339).length < 2 ^ (prefixWord ++ tailWord_1944339).sum := by decide
  have hdescent : baseEnd_1944339 < baseStart_1944339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944362 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1944362 : Nat := 118140960795 + 1944362 * 2 ^ 59
def prefixEnd_1944362 : Nat := 4983230072969 + 3 ^ 40 * 1944362 * 2
def baseEnd_1944362 : Nat := 665594848224951272288699

theorem tailTrace_1944362 : CollatzResearch.WordTrace tailWord_1944362 prefixEnd_1944362 665594848224951272288699 := by
  unfold tailWord_1944362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729177045479004859304835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47277805454610679624812893 17729177045479004859304835)
  ·
    refine ⟨26593765568218507288957253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17729177045479004859304835 26593765568218507288957253)
    ·
      refine ⟨4986331044040970116679485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26593765568218507288957253 4986331044040970116679485)
      ·
        refine ⟨1869874141515363793754807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4986331044040970116679485 1869874141515363793754807)
        ·
          refine ⟨2804811212273045690632211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869874141515363793754807 2804811212273045690632211)
          ·
            refine ⟨4207216818409568535948317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804811212273045690632211 4207216818409568535948317)
            ·
              refine ⟨1577706306903588200980619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4207216818409568535948317 1577706306903588200980619)
              ·
                refine ⟨2366559460355382301470929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577706306903588200980619 2366559460355382301470929)
                ·
                  refine ⟨1774919595266536726103197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366559460355382301470929 1774919595266536726103197)
                  ·
                    refine ⟨665594848224951272288699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774919595266536726103197 665594848224951272288699)
                    ·
                      rfl

theorem cell22_1944362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1944362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944362 prefixEnd_1944362 := by exact prefixLift 1944362
  have htrace : WordTrace (prefixWord ++ tailWord_1944362) baseStart_1944362 baseEnd_1944362 := by
    simpa [prefixWord, tailWord_1944362, baseEnd_1944362] using wordTrace_append hprefix tailTrace_1944362
  have hstable : (prefixWord ++ tailWord_1944362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944362).length < 2 ^ (prefixWord ++ tailWord_1944362).sum := by decide
  have hdescent : baseEnd_1944362 < baseStart_1944362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944433 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_1944433 : Nat := 118140960795 + 1944433 * 2 ^ 59
def prefixEnd_1944433 : Nat := 4983230072969 + 3 ^ 40 * 1944433 * 2
def baseEnd_1944433 : Nat := 665619152975930753763481

theorem tailTrace_1944433 : CollatzResearch.WordTrace tailWord_1944433 prefixEnd_1944433 665619152975930753763481 := by
  unfold tailWord_1944433
  simp only [CollatzResearch.WordTrace]
  refine ⟨70919297764658798563053953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47279531843105865708702635 70919297764658798563053953)
  ·
    refine ⟨53189473323494098922290465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70919297764658798563053953 53189473323494098922290465)
    ·
      refine ⟨39892104992620574191717849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53189473323494098922290465 39892104992620574191717849)
      ·
        refine ⟨29919078744465430643788387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39892104992620574191717849 29919078744465430643788387)
        ·
          refine ⟨44878618116698145965682581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29919078744465430643788387 44878618116698145965682581)
          ·
            refine ⟨2103685224220225592141371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44878618116698145965682581 2103685224220225592141371)
            ·
              refine ⟨3155527836330338388212057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103685224220225592141371 3155527836330338388212057)
              ·
                refine ⟨2366645877247753791159043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155527836330338388212057 2366645877247753791159043)
                ·
                  refine ⟨3549968815871630686738565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366645877247753791159043 3549968815871630686738565)
                  ·
                    refine ⟨665619152975930753763481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3549968815871630686738565 665619152975930753763481)
                    ·
                      rfl

theorem cell22_1944433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_1944433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944433 prefixEnd_1944433 := by exact prefixLift 1944433
  have htrace : WordTrace (prefixWord ++ tailWord_1944433) baseStart_1944433 baseEnd_1944433 := by
    simpa [prefixWord, tailWord_1944433, baseEnd_1944433] using wordTrace_append hprefix tailTrace_1944433
  have hstable : (prefixWord ++ tailWord_1944433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944433).length < 2 ^ (prefixWord ++ tailWord_1944433).sum := by decide
  have hdescent : baseEnd_1944433 < baseStart_1944433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944444 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1944444 : Nat := 118140960795 + 1944444 * 2 ^ 59
def prefixEnd_1944444 : Nat := 4983230072969 + 3 ^ 40 * 1944444 * 2
def baseEnd_1944444 : Nat := 665622918500730391738447

theorem tailTrace_1944444 : CollatzResearch.WordTrace tailWord_1944444 prefixEnd_1944444 665622918500730391738447 := by
  unfold tailWord_1944444
  simp only [CollatzResearch.WordTrace]
  refine ⟨35459849483809473720852193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47279799311745964961136257 35459849483809473720852193)
  ·
    refine ⟨26594887112857105290639145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35459849483809473720852193 26594887112857105290639145)
    ·
      refine ⟨19946165334642828967979359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26594887112857105290639145 19946165334642828967979359)
      ·
        refine ⟨29919248001964243451969039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19946165334642828967979359 29919248001964243451969039)
        ·
          refine ⟨44878872002946365177953559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29919248001964243451969039 44878872002946365177953559)
          ·
            refine ⟨67318308004419547766930339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44878872002946365177953559 67318308004419547766930339)
            ·
              refine ⟨100977462006629321650395509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67318308004419547766930339 100977462006629321650395509)
              ·
                refine ⟨9466637063121498904724579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100977462006629321650395509 9466637063121498904724579)
                ·
                  refine ⟨14199955594682248357086869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466637063121498904724579 14199955594682248357086869)
                  ·
                    refine ⟨665622918500730391738447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14199955594682248357086869 665622918500730391738447)
                    ·
                      rfl

theorem cell22_1944444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1944444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944444 prefixEnd_1944444 := by exact prefixLift 1944444
  have htrace : WordTrace (prefixWord ++ tailWord_1944444) baseStart_1944444 baseEnd_1944444 := by
    simpa [prefixWord, tailWord_1944444, baseEnd_1944444] using wordTrace_append hprefix tailTrace_1944444
  have hstable : (prefixWord ++ tailWord_1944444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944444).length < 2 ^ (prefixWord ++ tailWord_1944444).sum := by decide
  have hdescent : baseEnd_1944444 < baseStart_1944444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944489 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_1944489 : Nat := 118140960795 + 1944489 * 2 ^ 59
def prefixEnd_1944489 : Nat := 4983230072969 + 3 ^ 40 * 1944489 * 2
def baseEnd_1944489 : Nat := 665638322920365274363309

theorem tailTrace_1944489 : CollatzResearch.WordTrace tailWord_1944489 prefixEnd_1944489 665638322920365274363309 := by
  unfold tailWord_1944489
  simp only [CollatzResearch.WordTrace]
  refine ⟨70921340252455920127092521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47280893501637280084728347 70921340252455920127092521)
  ·
    refine ⟨53191005189341940095319391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70921340252455920127092521 53191005189341940095319391)
    ·
      refine ⟨79786507784012910142979087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53191005189341940095319391 79786507784012910142979087)
      ·
        refine ⟨119679761676019365214468631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79786507784012910142979087 119679761676019365214468631)
        ·
          refine ⟨179519642514029047821702947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119679761676019365214468631 179519642514029047821702947)
          ·
            refine ⟨269279463771043571732554421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179519642514029047821702947 269279463771043571732554421)
            ·
              refine ⟨25244949728535334849926977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269279463771043571732554421 25244949728535334849926977)
              ·
                refine ⟨18933712296401501137445233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25244949728535334849926977 18933712296401501137445233)
                ·
                  refine ⟨14200284222301125853083925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18933712296401501137445233 14200284222301125853083925)
                  ·
                    refine ⟨665638322920365274363309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14200284222301125853083925 665638322920365274363309)
                    ·
                      rfl

theorem cell22_1944489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_1944489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944489 prefixEnd_1944489 := by exact prefixLift 1944489
  have htrace : WordTrace (prefixWord ++ tailWord_1944489) baseStart_1944489 baseEnd_1944489 := by
    simpa [prefixWord, tailWord_1944489, baseEnd_1944489] using wordTrace_append hprefix tailTrace_1944489
  have hstable : (prefixWord ++ tailWord_1944489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944489).length < 2 ^ (prefixWord ++ tailWord_1944489).sum := by decide
  have hdescent : baseEnd_1944489 < baseStart_1944489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944491 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 3, 3]
def baseStart_1944491 : Nat := 118140960795 + 1944491 * 2 ^ 59
def prefixEnd_1944491 : Nat := 4983230072969 + 3 ^ 40 * 1944491 * 2
def baseEnd_1944491 : Nat := 665639007561237935813303

theorem tailTrace_1944491 : CollatzResearch.WordTrace tailWord_1944491 prefixEnd_1944491 665639007561237935813303 := by
  unfold tailWord_1944491
  simp only [CollatzResearch.WordTrace]
  refine ⟨70921413198448674468665327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47280942132299116312443551 70921413198448674468665327)
  ·
    refine ⟨106382119797673011702997991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70921413198448674468665327 106382119797673011702997991)
    ·
      refine ⟨159573179696509517554496987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106382119797673011702997991 159573179696509517554496987)
      ·
        refine ⟨239359769544764276331745481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159573179696509517554496987 239359769544764276331745481)
        ·
          refine ⟨179519827158573207248809111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239359769544764276331745481 179519827158573207248809111)
          ·
            refine ⟨269279740737859810873213667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179519827158573207248809111 269279740737859810873213667)
            ·
              refine ⟨403919611106789716309820501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269279740737859810873213667 403919611106789716309820501)
              ·
                refine ⟨4733432942657691988005709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 403919611106789716309820501 4733432942657691988005709)
                ·
                  refine ⟨1775037353496634495502141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4733432942657691988005709 1775037353496634495502141)
                  ·
                    refine ⟨665639007561237935813303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775037353496634495502141 665639007561237935813303)
                    ·
                      rfl

theorem cell22_1944491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 3].length) (baseStart_1944491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944491 prefixEnd_1944491 := by exact prefixLift 1944491
  have htrace : WordTrace (prefixWord ++ tailWord_1944491) baseStart_1944491 baseEnd_1944491 := by
    simpa [prefixWord, tailWord_1944491, baseEnd_1944491] using wordTrace_append hprefix tailTrace_1944491
  have hstable : (prefixWord ++ tailWord_1944491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944491).length < 2 ^ (prefixWord ++ tailWord_1944491).sum := by decide
  have hdescent : baseEnd_1944491 < baseStart_1944491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944536 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_1944536 : Nat := 118140960795 + 1944536 * 2 ^ 59
def prefixEnd_1944536 : Nat := 4983230072969 + 3 ^ 40 * 1944536 * 2
def baseEnd_1944536 : Nat := 665654411980872818438165

theorem tailTrace_1944536 : CollatzResearch.WordTrace tailWord_1944536 prefixEnd_1944536 665654411980872818438165 := by
  unfold tailWord_1944536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35461527241642823577026731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47282036322190431436035641 35461527241642823577026731)
  ·
    refine ⟨53192290862464235365540097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35461527241642823577026731 53192290862464235365540097)
    ·
      refine ⟨39894218146848176524155073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53192290862464235365540097 39894218146848176524155073)
      ·
        refine ⟨29920663610136132393116305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39894218146848176524155073 29920663610136132393116305)
        ·
          refine ⟨22440497707602099294837229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29920663610136132393116305 22440497707602099294837229)
          ·
            refine ⟨8415186640350787235563961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22440497707602099294837229 8415186640350787235563961)
            ·
              refine ⟨6311389980263090426672971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8415186640350787235563961 6311389980263090426672971)
              ·
                refine ⟨9467084970394635640009457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311389980263090426672971 9467084970394635640009457)
                ·
                  refine ⟨7100313727795976730007093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9467084970394635640009457 7100313727795976730007093)
                  ·
                    refine ⟨665654411980872818438165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7100313727795976730007093 665654411980872818438165)
                    ·
                      rfl

theorem cell22_1944536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_1944536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944536 prefixEnd_1944536 := by exact prefixLift 1944536
  have htrace : WordTrace (prefixWord ++ tailWord_1944536) baseStart_1944536 baseEnd_1944536 := by
    simpa [prefixWord, tailWord_1944536, baseEnd_1944536] using wordTrace_append hprefix tailTrace_1944536
  have hstable : (prefixWord ++ tailWord_1944536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944536).length < 2 ^ (prefixWord ++ tailWord_1944536).sum := by decide
  have hdescent : baseEnd_1944536 < baseStart_1944536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944611 : List Nat := [1, 1, 1, 4, 3, 2, 2, 8]
def baseStart_1944611 : Nat := 118140960795 + 1944611 * 2 ^ 59
def prefixEnd_1944611 : Nat := 4983230072969 + 3 ^ 40 * 1944611 * 2
def baseEnd_1944611 : Nat := 73964454001510846979215

theorem tailTrace_1944611 : CollatzResearch.WordTrace tailWord_1944611 prefixEnd_1944611 73964454001510846979215 := by
  unfold tailWord_1944611
  simp only [CollatzResearch.WordTrace]
  refine ⟨70925789958013934963033687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47283859972009289975355791 70925789958013934963033687)
  ·
    refine ⟨106388684937020902444550531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70925789958013934963033687 106388684937020902444550531)
    ·
      refine ⟨159583027405531353666825797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106388684937020902444550531 159583027405531353666825797)
      ·
        refine ⟨29921817638537128812529837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159583027405531353666825797 29921817638537128812529837)
        ·
          refine ⟨11220681614451423304698689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29921817638537128812529837 11220681614451423304698689)
          ·
            refine ⟨8415511210838567478524017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11220681614451423304698689 8415511210838567478524017)
            ·
              refine ⟨6311633408128925608893013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8415511210838567478524017 6311633408128925608893013)
              ·
                refine ⟨73964454001510846979215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6311633408128925608893013 73964454001510846979215)
                ·
                  rfl

theorem cell22_1944611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 8].length) (baseStart_1944611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944611 prefixEnd_1944611 := by exact prefixLift 1944611
  have htrace : WordTrace (prefixWord ++ tailWord_1944611) baseStart_1944611 baseEnd_1944611 := by
    simpa [prefixWord, tailWord_1944611, baseEnd_1944611] using wordTrace_append hprefix tailTrace_1944611
  have hstable : (prefixWord ++ tailWord_1944611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944611).length < 2 ^ (prefixWord ++ tailWord_1944611).sum := by decide
  have hdescent : baseEnd_1944611 < baseStart_1944611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944613 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_1944613 : Nat := 118140960795 + 1944613 * 2 ^ 59
def prefixEnd_1944613 : Nat := 4983230072969 + 3 ^ 40 * 1944613 * 2
def baseEnd_1944613 : Nat := 665680770654470284262929

theorem tailTrace_1944613 : CollatzResearch.WordTrace tailWord_1944613 prefixEnd_1944613 665680770654470284262929 := by
  unfold tailWord_1944613
  simp only [CollatzResearch.WordTrace]
  refine ⟨70925862904006689304606493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47283908602671126203070995 70925862904006689304606493)
  ·
    refine ⟨26597198589002508489227435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70925862904006689304606493 26597198589002508489227435)
    ·
      refine ⟨39895797883503762733841153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26597198589002508489227435 39895797883503762733841153)
      ·
        refine ⟨29921848412627822050380865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39895797883503762733841153 29921848412627822050380865)
        ·
          refine ⟨22441386309470866537785649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29921848412627822050380865 22441386309470866537785649)
          ·
            refine ⟨16831039732103149903339237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22441386309470866537785649 16831039732103149903339237)
            ·
              refine ⟨3155819949769340606876107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16831039732103149903339237 3155819949769340606876107)
              ·
                refine ⟨4733729924654010910314161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155819949769340606876107 4733729924654010910314161)
                ·
                  refine ⟨3550297443490508182735621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733729924654010910314161 3550297443490508182735621)
                  ·
                    refine ⟨665680770654470284262929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550297443490508182735621 665680770654470284262929)
                    ·
                      rfl

theorem cell22_1944613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_1944613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944613 prefixEnd_1944613 := by exact prefixLift 1944613
  have htrace : WordTrace (prefixWord ++ tailWord_1944613) baseStart_1944613 baseEnd_1944613 := by
    simpa [prefixWord, tailWord_1944613, baseEnd_1944613] using wordTrace_append hprefix tailTrace_1944613
  have hstable : (prefixWord ++ tailWord_1944613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944613).length < 2 ^ (prefixWord ++ tailWord_1944613).sum := by decide
  have hdescent : baseEnd_1944613 < baseStart_1944613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944615 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1944615 : Nat := 118140960795 + 1944615 * 2 ^ 59
def prefixEnd_1944615 : Nat := 4983230072969 + 3 ^ 40 * 1944615 * 2
def baseEnd_1944615 : Nat := 665681455295342945712923

theorem tailTrace_1944615 : CollatzResearch.WordTrace tailWord_1944615 prefixEnd_1944615 665681455295342945712923 := by
  unfold tailWord_1944615
  simp only [CollatzResearch.WordTrace]
  refine ⟨70925935849999443646179299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47283957233332962430786199 70925935849999443646179299)
  ·
    refine ⟨106388903774999165469268949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70925935849999443646179299 106388903774999165469268949)
    ·
      refine ⟨2493489932226542940685991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 106388903774999165469268949 2493489932226542940685991)
      ·
        refine ⟨3740234898339814411028987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493489932226542940685991 3740234898339814411028987)
        ·
          refine ⟨5610352347509721616543481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740234898339814411028987 5610352347509721616543481)
          ·
            refine ⟨4207764260632291212407611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5610352347509721616543481 4207764260632291212407611)
            ·
              refine ⟨6311646390948436818611417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207764260632291212407611 6311646390948436818611417)
              ·
                refine ⟨4733734793211327613958563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311646390948436818611417 4733734793211327613958563)
                ·
                  refine ⟨7100602189816991420937845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733734793211327613958563 7100602189816991420937845)
                  ·
                    refine ⟨665681455295342945712923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7100602189816991420937845 665681455295342945712923)
                    ·
                      rfl

theorem cell22_1944615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1944615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944615 prefixEnd_1944615 := by exact prefixLift 1944615
  have htrace : WordTrace (prefixWord ++ tailWord_1944615) baseStart_1944615 baseEnd_1944615 := by
    simpa [prefixWord, tailWord_1944615, baseEnd_1944615] using wordTrace_append hprefix tailTrace_1944615
  have hstable : (prefixWord ++ tailWord_1944615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944615).length < 2 ^ (prefixWord ++ tailWord_1944615).sum := by decide
  have hdescent : baseEnd_1944615 < baseStart_1944615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944628 : List Nat := [2, 5, 1, 2, 1, 11]
def baseStart_1944628 : Nat := 118140960795 + 1944628 * 2 ^ 59
def prefixEnd_1944628 : Nat := 4983230072969 + 3 ^ 40 * 1944628 * 2
def baseEnd_1944628 : Nat := 8218344511864385742443

theorem tailTrace_1944628 : CollatzResearch.WordTrace tailWord_1944628 prefixEnd_1944628 8218344511864385742443 := by
  unfold tailWord_1944628
  simp only [CollatzResearch.WordTrace]
  refine ⟨35463204999476173433201269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47284273332634897910935025 35463204999476173433201269)
  ·
    refine ⟨3324675468700891259362619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35463204999476173433201269 3324675468700891259362619)
    ·
      refine ⟨4987013203051336889043929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324675468700891259362619 4987013203051336889043929)
      ·
        refine ⟨3740259902288502666782947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4987013203051336889043929 3740259902288502666782947)
        ·
          refine ⟨5610389853432754000174421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740259902288502666782947 5610389853432754000174421)
          ·
            refine ⟨8218344511864385742443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5610389853432754000174421 8218344511864385742443)
            ·
              rfl

theorem cell22_1944628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 11].length) (baseStart_1944628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944628 prefixEnd_1944628 := by exact prefixLift 1944628
  have htrace : WordTrace (prefixWord ++ tailWord_1944628) baseStart_1944628 baseEnd_1944628 := by
    simpa [prefixWord, tailWord_1944628, baseEnd_1944628] using wordTrace_append hprefix tailTrace_1944628
  have hstable : (prefixWord ++ tailWord_1944628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944628).length < 2 ^ (prefixWord ++ tailWord_1944628).sum := by decide
  have hdescent : baseEnd_1944628 < baseStart_1944628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944630 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1944630 : Nat := 118140960795 + 1944630 * 2 ^ 59
def prefixEnd_1944630 : Nat := 4983230072969 + 3 ^ 40 * 1944630 * 2
def baseEnd_1944630 : Nat := 665686590101887906587877

theorem tailTrace_1944630 : CollatzResearch.WordTrace tailWord_1944630 prefixEnd_1944630 665686590101887906587877 := by
  unfold tailWord_1944630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432905184059068825498459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47284321963296734138650229 4432905184059068825498459)
  ·
    refine ⟨6649357776088603238247689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4432905184059068825498459 6649357776088603238247689)
    ·
      refine ⟨4987018332066452428685767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6649357776088603238247689 4987018332066452428685767)
      ·
        refine ⟨7480527498099678643028651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4987018332066452428685767 7480527498099678643028651)
        ·
          refine ⟨11220791247149517964542977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7480527498099678643028651 11220791247149517964542977)
          ·
            refine ⟨8415593435362138473407233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11220791247149517964542977 8415593435362138473407233)
            ·
              refine ⟨6311695076521603855055425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8415593435362138473407233 6311695076521603855055425)
              ·
                refine ⟨4733771307391202891291569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311695076521603855055425 4733771307391202891291569)
                ·
                  refine ⟨3550328480543402168468677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733771307391202891291569 3550328480543402168468677)
                  ·
                    refine ⟨665686590101887906587877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550328480543402168468677 665686590101887906587877)
                    ·
                      rfl

theorem cell22_1944630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1944630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944630 prefixEnd_1944630 := by exact prefixLift 1944630
  have htrace : WordTrace (prefixWord ++ tailWord_1944630) baseStart_1944630 baseEnd_1944630 := by
    simpa [prefixWord, tailWord_1944630, baseEnd_1944630] using wordTrace_append hprefix tailTrace_1944630
  have hstable : (prefixWord ++ tailWord_1944630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944630).length < 2 ^ (prefixWord ++ tailWord_1944630).sum := by decide
  have hdescent : baseEnd_1944630 < baseStart_1944630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944643 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 3, 3]
def baseStart_1944643 : Nat := 118140960795 + 1944643 * 2 ^ 59
def prefixEnd_1944643 : Nat := 4983230072969 + 3 ^ 40 * 1944643 * 2
def baseEnd_1944643 : Nat := 665691040267560206012837

theorem tailTrace_1944643 : CollatzResearch.WordTrace tailWord_1944643 prefixEnd_1944643 665691040267560206012837 := by
  unfold tailWord_1944643
  simp only [CollatzResearch.WordTrace]
  refine ⟨70926957093898004428198583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47284638062598669618799055 70926957093898004428198583)
  ·
    refine ⟨106390435640847006642297875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70926957093898004428198583 106390435640847006642297875)
    ·
      refine ⟨159585653461270509963446813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106390435640847006642297875 159585653461270509963446813)
      ·
        refine ⟨59844620047976441236292555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159585653461270509963446813 59844620047976441236292555)
        ·
          refine ⟨89766930071964661854438833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59844620047976441236292555 89766930071964661854438833)
          ·
            refine ⟨67325197553973496390829125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89766930071964661854438833 67325197553973496390829125)
            ·
              refine ⟨12623474541370030573280461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67325197553973496390829125 12623474541370030573280461)
              ·
                refine ⟨4733802953013761464980173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12623474541370030573280461 4733802953013761464980173)
                ·
                  refine ⟨1775176107380160549367565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4733802953013761464980173 1775176107380160549367565)
                  ·
                    refine ⟨665691040267560206012837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775176107380160549367565 665691040267560206012837)
                    ·
                      rfl

theorem cell22_1944643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 3].length) (baseStart_1944643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944643 prefixEnd_1944643 := by exact prefixLift 1944643
  have htrace : WordTrace (prefixWord ++ tailWord_1944643) baseStart_1944643 baseEnd_1944643 := by
    simpa [prefixWord, tailWord_1944643, baseEnd_1944643] using wordTrace_append hprefix tailTrace_1944643
  have hstable : (prefixWord ++ tailWord_1944643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944643).length < 2 ^ (prefixWord ++ tailWord_1944643).sum := by decide
  have hdescent : baseEnd_1944643 < baseStart_1944643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944671 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_1944671 : Nat := 118140960795 + 1944671 * 2 ^ 59
def prefixEnd_1944671 : Nat := 4983230072969 + 3 ^ 40 * 1944671 * 2
def baseEnd_1944671 : Nat := 665700625239777466312751

theorem tailTrace_1944671 : CollatzResearch.WordTrace tailWord_1944671 prefixEnd_1944671 665700625239777466312751 := by
  unfold tailWord_1944671
  simp only [CollatzResearch.WordTrace]
  refine ⟨70927978337796565210217867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47285318891864376806811911 70927978337796565210217867)
  ·
    refine ⟨106391967506694847815326801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70927978337796565210217867 106391967506694847815326801)
    ·
      refine ⟨79793975630021135861495101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106391967506694847815326801 79793975630021135861495101)
      ·
        refine ⟨29922740861257925948060663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79793975630021135861495101 29922740861257925948060663)
        ·
          refine ⟨44884111291886888922090995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29922740861257925948060663 44884111291886888922090995)
          ·
            refine ⟨67326166937830333383136493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44884111291886888922090995 67326166937830333383136493)
            ·
              refine ⟨25247312601686375018676185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67326166937830333383136493 25247312601686375018676185)
              ·
                refine ⟨18935484451264781264007139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25247312601686375018676185 18935484451264781264007139)
                ·
                  refine ⟨28403226676897171896010709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18935484451264781264007139 28403226676897171896010709)
                  ·
                    refine ⟨665700625239777466312751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28403226676897171896010709 665700625239777466312751)
                    ·
                      rfl

theorem cell22_1944671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_1944671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944671 prefixEnd_1944671 := by exact prefixLift 1944671
  have htrace : WordTrace (prefixWord ++ tailWord_1944671) baseStart_1944671 baseEnd_1944671 := by
    simpa [prefixWord, tailWord_1944671, baseEnd_1944671] using wordTrace_append hprefix tailTrace_1944671
  have hstable : (prefixWord ++ tailWord_1944671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944671).length < 2 ^ (prefixWord ++ tailWord_1944671).sum := by decide
  have hdescent : baseEnd_1944671 < baseStart_1944671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944677 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_1944677 : Nat := 118140960795 + 1944677 * 2 ^ 59
def prefixEnd_1944677 : Nat := 4983230072969 + 3 ^ 40 * 1944677 * 2
def baseEnd_1944677 : Nat := 665702679162395450662733

theorem tailTrace_1944677 : CollatzResearch.WordTrace tailWord_1944677 prefixEnd_1944677 665702679162395450662733 := by
  unfold tailWord_1944677
  simp only [CollatzResearch.WordTrace]
  refine ⟨70928197175774828234936285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47285464783849885489957523 70928197175774828234936285)
  ·
    refine ⟨26598073940915560588101107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70928197175774828234936285 26598073940915560588101107)
    ·
      refine ⟨39897110911373340882151661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26598073940915560588101107 39897110911373340882151661)
      ·
        refine ⟨14961416591765002830806873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39897110911373340882151661 14961416591765002830806873)
        ·
          refine ⟨11221062443823752123105155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14961416591765002830806873 11221062443823752123105155)
          ·
            refine ⟨16831593665735628184657733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11221062443823752123105155 16831593665735628184657733)
            ·
              refine ⟨3155923812325430284623325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16831593665735628184657733 3155923812325430284623325)
              ·
                refine ⟨1183471429622036356733747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3155923812325430284623325 1183471429622036356733747)
                ·
                  refine ⟨1775207144433054535100621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183471429622036356733747 1775207144433054535100621)
                  ·
                    refine ⟨665702679162395450662733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775207144433054535100621 665702679162395450662733)
                    ·
                      rfl

theorem cell22_1944677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_1944677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944677 prefixEnd_1944677 := by exact prefixLift 1944677
  have htrace : WordTrace (prefixWord ++ tailWord_1944677) baseStart_1944677 baseEnd_1944677 := by
    simpa [prefixWord, tailWord_1944677, baseEnd_1944677] using wordTrace_append hprefix tailTrace_1944677
  have hstable : (prefixWord ++ tailWord_1944677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944677).length < 2 ^ (prefixWord ++ tailWord_1944677).sum := by decide
  have hdescent : baseEnd_1944677 < baseStart_1944677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944733 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1944733 : Nat := 118140960795 + 1944733 * 2 ^ 59
def prefixEnd_1944733 : Nat := 4983230072969 + 3 ^ 40 * 1944733 * 2
def baseEnd_1944733 : Nat := 665721849106829971262561

theorem tailTrace_1944733 : CollatzResearch.WordTrace tailWord_1944733 prefixEnd_1944733 665721849106829971262561 := by
  unfold tailWord_1944733
  simp only [CollatzResearch.WordTrace]
  refine ⟨70930239663571949798974853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47286826442381299865983235 70930239663571949798974853)
  ·
    refine ⟨13299419936919740587307785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70930239663571949798974853 13299419936919740587307785)
    ·
      refine ⟨9974564952689805440480839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13299419936919740587307785 9974564952689805440480839)
      ·
        refine ⟨14961847429034708160721259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9974564952689805440480839 14961847429034708160721259)
        ·
          refine ⟨22442771143552062241081889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14961847429034708160721259 22442771143552062241081889)
          ·
            refine ⟨16832078357664046680811417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22442771143552062241081889 16832078357664046680811417)
            ·
              refine ⟨12624058768248035010608563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16832078357664046680811417 12624058768248035010608563)
              ·
                refine ⟨18936088152372052515912845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12624058768248035010608563 18936088152372052515912845)
                ·
                  refine ⟨7101033057139519693467317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18936088152372052515912845 7101033057139519693467317)
                  ·
                    refine ⟨665721849106829971262561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7101033057139519693467317 665721849106829971262561)
                    ·
                      rfl

theorem cell22_1944733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1944733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944733 prefixEnd_1944733 := by exact prefixLift 1944733
  have htrace : WordTrace (prefixWord ++ tailWord_1944733) baseStart_1944733 baseEnd_1944733 := by
    simpa [prefixWord, tailWord_1944733, baseEnd_1944733] using wordTrace_append hprefix tailTrace_1944733
  have hstable : (prefixWord ++ tailWord_1944733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944733).length < 2 ^ (prefixWord ++ tailWord_1944733).sum := by decide
  have hdescent : baseEnd_1944733 < baseStart_1944733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944758 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1944758 : Nat := 118140960795 + 1944758 * 2 ^ 59
def prefixEnd_1944758 : Nat := 4983230072969 + 3 ^ 40 * 1944758 * 2
def baseEnd_1944758 : Nat := 221910135705912746462495

theorem tailTrace_1944758 : CollatzResearch.WordTrace tailWord_1944758 prefixEnd_1944758 221910135705912746462495 := by
  unfold tailWord_1944758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433196968030086191789683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47287434325654252712423285 4433196968030086191789683)
  ·
    refine ⟨6649795452045129287684525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4433196968030086191789683 6649795452045129287684525)
    ·
      refine ⟨2493673294516923482881697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6649795452045129287684525 2493673294516923482881697)
      ·
        refine ⟨1870254970887692612161273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2493673294516923482881697 1870254970887692612161273)
        ·
          refine ⟨1402691228165769459120955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870254970887692612161273 1402691228165769459120955)
          ·
            refine ⟨2104036842248654188681433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402691228165769459120955 2104036842248654188681433)
            ·
              refine ⟨1578027631686490641511075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104036842248654188681433 1578027631686490641511075)
              ·
                refine ⟨2367041447529735962266613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578027631686490641511075 2367041447529735962266613)
                ·
                  refine ⟨221910135705912746462495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2367041447529735962266613 221910135705912746462495)
                  ·
                    rfl

theorem cell22_1944758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1944758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944758 prefixEnd_1944758 := by exact prefixLift 1944758
  have htrace : WordTrace (prefixWord ++ tailWord_1944758) baseStart_1944758 baseEnd_1944758 := by
    simpa [prefixWord, tailWord_1944758, baseEnd_1944758] using wordTrace_append hprefix tailTrace_1944758
  have hstable : (prefixWord ++ tailWord_1944758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944758).length < 2 ^ (prefixWord ++ tailWord_1944758).sum := by decide
  have hdescent : baseEnd_1944758 < baseStart_1944758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944767 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 2, 3]
def baseStart_1944767 : Nat := 118140960795 + 1944767 * 2 ^ 59
def prefixEnd_1944767 : Nat := 4983230072969 + 3 ^ 40 * 1944767 * 2
def baseEnd_1944767 : Nat := 665733488001665215912457

theorem tailTrace_1944767 : CollatzResearch.WordTrace tailWord_1944767 prefixEnd_1944767 665733488001665215912457 := by
  unfold tailWord_1944767
  simp only [CollatzResearch.WordTrace]
  refine ⟨70931479745448773605712555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47287653163632515737141703 70931479745448773605712555)
  ·
    refine ⟨106397219618173160408568833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70931479745448773605712555 106397219618173160408568833)
    ·
      refine ⟨79797914713629870306426625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106397219618173160408568833 79797914713629870306426625)
      ·
        refine ⟨59848436035222402729819969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79797914713629870306426625 59848436035222402729819969)
        ·
          refine ⟨44886327026416802047364977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59848436035222402729819969 44886327026416802047364977)
          ·
            refine ⟨33664745269812601535523733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44886327026416802047364977 33664745269812601535523733)
            ·
              refine ⟨1578034934522465696977675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33664745269812601535523733 1578034934522465696977675)
              ·
                refine ⟨2367052401783698545466513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578034934522465696977675 2367052401783698545466513)
                ·
                  refine ⟨1775289301337773909099885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367052401783698545466513 1775289301337773909099885)
                  ·
                    refine ⟨665733488001665215912457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775289301337773909099885 665733488001665215912457)
                    ·
                      rfl

theorem cell22_1944767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_1944767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944767 prefixEnd_1944767 := by exact prefixLift 1944767
  have htrace : WordTrace (prefixWord ++ tailWord_1944767) baseStart_1944767 baseEnd_1944767 := by
    simpa [prefixWord, tailWord_1944767, baseEnd_1944767] using wordTrace_append hprefix tailTrace_1944767
  have hstable : (prefixWord ++ tailWord_1944767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944767).length < 2 ^ (prefixWord ++ tailWord_1944767).sum := by decide
  have hdescent : baseEnd_1944767 < baseStart_1944767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944782 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1944782 : Nat := 118140960795 + 1944782 * 2 ^ 59
def prefixEnd_1944782 : Nat := 4983230072969 + 3 ^ 40 * 1944782 * 2
def baseEnd_1944782 : Nat := 665738622808210176787411

theorem tailTrace_1944782 : CollatzResearch.WordTrace tailWord_1944782 prefixEnd_1944782 665738622808210176787411 := by
  unfold tailWord_1944782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866503355049303895938575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47288017893596287445005733 8866503355049303895938575)
  ·
    refine ⟨13299755032573955843907863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8866503355049303895938575 13299755032573955843907863)
    ·
      refine ⟨19949632548860933765861795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13299755032573955843907863 19949632548860933765861795)
      ·
        refine ⟨29924448823291400648792693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19949632548860933765861795 29924448823291400648792693)
        ·
          refine ⟨2805417077183568810824315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29924448823291400648792693 2805417077183568810824315)
          ·
            refine ⟨4208125615775353216236473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805417077183568810824315 4208125615775353216236473)
            ·
              refine ⟨3156094211831514912177355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208125615775353216236473 3156094211831514912177355)
              ·
                refine ⟨4734141317747272368266033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156094211831514912177355 4734141317747272368266033)
                ·
                  refine ⟨3550605988310454276199525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734141317747272368266033 3550605988310454276199525)
                  ·
                    refine ⟨665738622808210176787411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550605988310454276199525 665738622808210176787411)
                    ·
                      rfl

theorem cell22_1944782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1944782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944782 prefixEnd_1944782 := by exact prefixLift 1944782
  have htrace : WordTrace (prefixWord ++ tailWord_1944782) baseStart_1944782 baseEnd_1944782 := by
    simpa [prefixWord, tailWord_1944782, baseEnd_1944782] using wordTrace_append hprefix tailTrace_1944782
  have hstable : (prefixWord ++ tailWord_1944782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944782).length < 2 ^ (prefixWord ++ tailWord_1944782).sum := by decide
  have hdescent : baseEnd_1944782 < baseStart_1944782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944823 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_1944823 : Nat := 118140960795 + 1944823 * 2 ^ 59
def prefixEnd_1944823 : Nat := 4983230072969 + 3 ^ 40 * 1944823 * 2
def baseEnd_1944823 : Nat := 665752657946099736512285

theorem tailTrace_1944823 : CollatzResearch.WordTrace tailWord_1944823 prefixEnd_1944823 665752657946099736512285 := by
  unfold tailWord_1944823
  simp only [CollatzResearch.WordTrace]
  refine ⟨70933522233245895169751123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47289014822163930113167415 70933522233245895169751123)
  ·
    refine ⟨106400283349868842754626685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70933522233245895169751123 106400283349868842754626685)
    ·
      refine ⟨39900106256200816032985007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106400283349868842754626685 39900106256200816032985007)
      ·
        refine ⟨59850159384301224049477511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39900106256200816032985007 59850159384301224049477511)
        ·
          refine ⟨89775239076451836074216267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59850159384301224049477511 89775239076451836074216267)
          ·
            refine ⟨134662858614677754111324401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89775239076451836074216267 134662858614677754111324401)
            ·
              refine ⟨100997143961008315583493301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134662858614677754111324401 100997143961008315583493301)
              ·
                refine ⟨9468482246344529585952497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100997143961008315583493301 9468482246344529585952497)
                ·
                  refine ⟨7101361684758397189464373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9468482246344529585952497 7101361684758397189464373)
                  ·
                    refine ⟨665752657946099736512285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7101361684758397189464373 665752657946099736512285)
                    ·
                      rfl

theorem cell22_1944823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_1944823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944823 prefixEnd_1944823 := by exact prefixLift 1944823
  have htrace : WordTrace (prefixWord ++ tailWord_1944823) baseStart_1944823 baseEnd_1944823 := by
    simpa [prefixWord, tailWord_1944823, baseEnd_1944823] using wordTrace_append hprefix tailTrace_1944823
  have hstable : (prefixWord ++ tailWord_1944823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944823).length < 2 ^ (prefixWord ++ tailWord_1944823).sum := by decide
  have hdescent : baseEnd_1944823 < baseStart_1944823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944853 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 10]
def baseStart_1944853 : Nat := 118140960795 + 1944853 * 2 ^ 59
def prefixEnd_1944853 : Nat := 4983230072969 + 3 ^ 40 * 1944853 * 2
def baseEnd_1944853 : Nat := 221920975853063219420731

theorem tailTrace_1944853 : CollatzResearch.WordTrace tailWord_1944853 prefixEnd_1944853 221920975853063219420731 := by
  unfold tailWord_1944853
  simp only [CollatzResearch.WordTrace]
  refine ⟨70934616423137210293343213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47289744282091473528895475 70934616423137210293343213)
  ·
    refine ⟨26600481158676453860003705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70934616423137210293343213 26600481158676453860003705)
    ·
      refine ⟨19950360869007340395002779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26600481158676453860003705 19950360869007340395002779)
      ·
        refine ⟨29925541303511010592504169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19950360869007340395002779 29925541303511010592504169)
        ·
          refine ⟨22444155977633257944378127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29925541303511010592504169 22444155977633257944378127)
          ·
            refine ⟨33666233966449886916567191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22444155977633257944378127 33666233966449886916567191)
            ·
              refine ⟨50499350949674830374850787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33666233966449886916567191 50499350949674830374850787)
              ·
                refine ⟨75749026424512245562276181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50499350949674830374850787 75749026424512245562276181)
                ·
                  refine ⟨221920975853063219420731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 75749026424512245562276181 221920975853063219420731)
                  ·
                    rfl

theorem cell22_1944853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_1944853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944853 prefixEnd_1944853 := by exact prefixLift 1944853
  have htrace : WordTrace (prefixWord ++ tailWord_1944853) baseStart_1944853 baseEnd_1944853 := by
    simpa [prefixWord, tailWord_1944853, baseEnd_1944853] using wordTrace_append hprefix tailTrace_1944853
  have hstable : (prefixWord ++ tailWord_1944853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944853).length < 2 ^ (prefixWord ++ tailWord_1944853).sum := by decide
  have hdescent : baseEnd_1944853 < baseStart_1944853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944889 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_1944889 : Nat := 118140960795 + 1944889 * 2 ^ 59
def prefixEnd_1944889 : Nat := 4983230072969 + 3 ^ 40 * 1944889 * 2
def baseEnd_1944889 : Nat := 665775251094897564362083

theorem tailTrace_1944889 : CollatzResearch.WordTrace tailWord_1944889 prefixEnd_1944889 665775251094897564362083 := by
  unfold tailWord_1944889
  simp only [CollatzResearch.WordTrace]
  refine ⟨70935929451006788441653721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47290619634004525627769147 70935929451006788441653721)
  ·
    refine ⟨53201947088255091331240291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70935929451006788441653721 53201947088255091331240291)
    ·
      refine ⟨79802920632382636996860437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53201947088255091331240291 79802920632382636996860437)
      ·
        refine ⟨3740761904642936109227833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79802920632382636996860437 3740761904642936109227833)
        ·
          refine ⟨2805571428482202081920875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740761904642936109227833 2805571428482202081920875)
          ·
            refine ⟨4208357142723303122881313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805571428482202081920875 4208357142723303122881313)
            ·
              refine ⟨3156267857042477342160985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208357142723303122881313 3156267857042477342160985)
              ·
                refine ⟨2367200892781858006620739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156267857042477342160985 2367200892781858006620739)
                ·
                  refine ⟨3550801339172787009931109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367200892781858006620739 3550801339172787009931109)
                  ·
                    refine ⟨665775251094897564362083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550801339172787009931109 665775251094897564362083)
                    ·
                      rfl

theorem cell22_1944889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_1944889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944889 prefixEnd_1944889 := by exact prefixLift 1944889
  have htrace : WordTrace (prefixWord ++ tailWord_1944889) baseStart_1944889 baseEnd_1944889 := by
    simpa [prefixWord, tailWord_1944889, baseEnd_1944889] using wordTrace_append hprefix tailTrace_1944889
  have hstable : (prefixWord ++ tailWord_1944889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944889).length < 2 ^ (prefixWord ++ tailWord_1944889).sum := by decide
  have hdescent : baseEnd_1944889 < baseStart_1944889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944917 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1944917 : Nat := 118140960795 + 1944917 * 2 ^ 59
def prefixEnd_1944917 : Nat := 4983230072969 + 3 ^ 40 * 1944917 * 2
def baseEnd_1944917 : Nat := 665784836067114824661997

theorem tailTrace_1944917 : CollatzResearch.WordTrace tailWord_1944917 prefixEnd_1944917 665784836067114824661997 := by
  unfold tailWord_1944917
  simp only [CollatzResearch.WordTrace]
  refine ⟨70936950694905349223673005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47291300463270232815782003 70936950694905349223673005)
  ·
    refine ⟨26601356510589505958877377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70936950694905349223673005 26601356510589505958877377)
    ·
      refine ⟨19951017382942129469158033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26601356510589505958877377 19951017382942129469158033)
      ·
        refine ⟨14963263037206597101868525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19951017382942129469158033 14963263037206597101868525)
        ·
          refine ⟨5611223638952473913200697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14963263037206597101868525 5611223638952473913200697)
          ·
            refine ⟨4208417729214355434900523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5611223638952473913200697 4208417729214355434900523)
            ·
              refine ⟨6312626593821533152350785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208417729214355434900523 6312626593821533152350785)
              ·
                refine ⟨4734469945366149864263089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6312626593821533152350785 4734469945366149864263089)
                ·
                  refine ⟨3550852459024612398197317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734469945366149864263089 3550852459024612398197317)
                  ·
                    refine ⟨665784836067114824661997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550852459024612398197317 665784836067114824661997)
                    ·
                      rfl

theorem cell22_1944917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1944917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944917 prefixEnd_1944917 := by exact prefixLift 1944917
  have htrace : WordTrace (prefixWord ++ tailWord_1944917) baseStart_1944917 baseEnd_1944917 := by
    simpa [prefixWord, tailWord_1944917, baseEnd_1944917] using wordTrace_append hprefix tailTrace_1944917
  have hstable : (prefixWord ++ tailWord_1944917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944917).length < 2 ^ (prefixWord ++ tailWord_1944917).sum := by decide
  have hdescent : baseEnd_1944917 < baseStart_1944917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944981 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_1944981 : Nat := 118140960795 + 1944981 * 2 ^ 59
def prefixEnd_1944981 : Nat := 4983230072969 + 3 ^ 40 * 1944981 * 2
def baseEnd_1944981 : Nat := 665806744575039991061801

theorem tailTrace_1944981 : CollatzResearch.WordTrace tailWord_1944981 prefixEnd_1944981 665806744575039991061801 := by
  unfold tailWord_1944981
  simp only [CollatzResearch.WordTrace]
  refine ⟨70939284966673488154002797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47292856644448992102668531 70939284966673488154002797)
  ·
    refine ⟨26602231862502558057751049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70939284966673488154002797 26602231862502558057751049)
    ·
      refine ⟨19951673896876918543313287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26602231862502558057751049 19951673896876918543313287)
      ·
        refine ⟨29927510845315377814969931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19951673896876918543313287 29927510845315377814969931)
        ·
          refine ⟨44891266267973066722454897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29927510845315377814969931 44891266267973066722454897)
          ·
            refine ⟨33668449700979800041841173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44891266267973066722454897 33668449700979800041841173)
            ·
              refine ⟨1578208579733428126961305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33668449700979800041841173 1578208579733428126961305)
              ·
                refine ⟨1183656434800071095220979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578208579733428126961305 1183656434800071095220979)
                ·
                  refine ⟨1775484652200106642831469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183656434800071095220979 1775484652200106642831469)
                  ·
                    refine ⟨665806744575039991061801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775484652200106642831469 665806744575039991061801)
                    ·
                      rfl

theorem cell22_1944981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_1944981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1944981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1944981 prefixEnd_1944981 := by exact prefixLift 1944981
  have htrace : WordTrace (prefixWord ++ tailWord_1944981) baseStart_1944981 baseEnd_1944981 := by
    simpa [prefixWord, tailWord_1944981, baseEnd_1944981] using wordTrace_append hprefix tailTrace_1944981
  have hstable : (prefixWord ++ tailWord_1944981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944981).length < 2 ^ (prefixWord ++ tailWord_1944981).sum := by decide
  have hdescent : baseEnd_1944981 < baseStart_1944981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945024 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 1, 4]
def baseStart_1945024 : Nat := 118140960795 + 1945024 * 2 ^ 59
def prefixEnd_1945024 : Nat := 4983230072969 + 3 ^ 40 * 1945024 * 2
def baseEnd_1945024 : Nat := 665821464353802212236669

theorem tailTrace_1945024 : CollatzResearch.WordTrace tailWord_1945024 prefixEnd_1945024 665821464353802212236669 := by
  unfold tailWord_1945024
  simp only [CollatzResearch.WordTrace]
  refine ⟨35470426652758853248909063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47293902203678470998545417 35470426652758853248909063)
  ·
    refine ⟨53205639979138279873363595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35470426652758853248909063 53205639979138279873363595)
    ·
      refine ⟨79808459968707419810045393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53205639979138279873363595 79808459968707419810045393)
      ·
        refine ⟨59856344976530564857534045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79808459968707419810045393 59856344976530564857534045)
        ·
          refine ⟨22446129366198961821575267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59856344976530564857534045 22446129366198961821575267)
          ·
            refine ⟨33669194049298442732362901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22446129366198961821575267 33669194049298442732362901)
            ·
              refine ⟨1578243471060864503079511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33669194049298442732362901 1578243471060864503079511)
              ·
                refine ⟨2367365206591296754619267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578243471060864503079511 2367365206591296754619267)
                ·
                  refine ⟨3551047809886945131928901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367365206591296754619267 3551047809886945131928901)
                  ·
                    refine ⟨665821464353802212236669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551047809886945131928901 665821464353802212236669)
                    ·
                      rfl

theorem cell22_1945024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_1945024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945024 prefixEnd_1945024 := by exact prefixLift 1945024
  have htrace : WordTrace (prefixWord ++ tailWord_1945024) baseStart_1945024 baseEnd_1945024 := by
    simpa [prefixWord, tailWord_1945024, baseEnd_1945024] using wordTrace_append hprefix tailTrace_1945024
  have hstable : (prefixWord ++ tailWord_1945024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945024).length < 2 ^ (prefixWord ++ tailWord_1945024).sum := by decide
  have hdescent : baseEnd_1945024 < baseStart_1945024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945157 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 6]
def baseStart_1945157 : Nat := 118140960795 + 1945157 * 2 ^ 59
def prefixEnd_1945157 : Nat := 4983230072969 + 3 ^ 40 * 1945157 * 2
def baseEnd_1945157 : Nat := 221955664323944732887087

theorem tailTrace_1945157 : CollatzResearch.WordTrace tailWord_1945157 prefixEnd_1945157 221955664323944732887087 := by
  unfold tailWord_1945157
  simp only [CollatzResearch.WordTrace]
  refine ⟨70945704214035870212409725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47297136142690580141606483 70945704214035870212409725)
  ·
    refine ⟨26604639080263451329653647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70945704214035870212409725 26604639080263451329653647)
    ·
      refine ⟨39906958620395176994480471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26604639080263451329653647 39906958620395176994480471)
      ·
        refine ⟨59860437930592765491720707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39906958620395176994480471 59860437930592765491720707)
        ·
          refine ⟨89790656895889148237581061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59860437930592765491720707 89790656895889148237581061)
          ·
            refine ⟨16835748167979215294546449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89790656895889148237581061 16835748167979215294546449)
            ·
              refine ⟨12626811125984411470909837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16835748167979215294546449 12626811125984411470909837)
              ·
                refine ⟨4735054172244154301591189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12626811125984411470909837 4735054172244154301591189)
                ·
                  refine ⟨221955664323944732887087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4735054172244154301591189 221955664323944732887087)
                  ·
                    rfl

theorem cell22_1945157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_1945157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945157 prefixEnd_1945157 := by exact prefixLift 1945157
  have htrace : WordTrace (prefixWord ++ tailWord_1945157) baseStart_1945157 baseEnd_1945157 := by
    simpa [prefixWord, tailWord_1945157, baseEnd_1945157] using wordTrace_append hprefix tailTrace_1945157
  have hstable : (prefixWord ++ tailWord_1945157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945157).length < 2 ^ (prefixWord ++ tailWord_1945157).sum := by decide
  have hdescent : baseEnd_1945157 < baseStart_1945157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945189 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1945189 : Nat := 118140960795 + 1945189 * 2 ^ 59
def prefixEnd_1945189 : Nat := 4983230072969 + 3 ^ 40 * 1945189 * 2
def baseEnd_1945189 : Nat := 665877947225796781861163

theorem tailTrace_1945189 : CollatzResearch.WordTrace tailWord_1945189 prefixEnd_1945189 665877947225796781861163 := by
  unfold tailWord_1945189
  simp only [CollatzResearch.WordTrace]
  refine ⟨70946871349919939677574621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47297914233279959785049747 70946871349919939677574621)
  ·
    refine ⟨26605076756219977379090483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70946871349919939677574621 26605076756219977379090483)
    ·
      refine ⟨39907615134329966068635725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26605076756219977379090483 39907615134329966068635725)
      ·
        refine ⟨14965355675373737275738397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39907615134329966068635725 14965355675373737275738397)
        ·
          refine ⟨5612008378265151478401899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14965355675373737275738397 5612008378265151478401899)
          ·
            refine ⟨8418012567397727217602849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612008378265151478401899 8418012567397727217602849)
            ·
              refine ⟨6313509425548295413202137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8418012567397727217602849 6313509425548295413202137)
              ·
                refine ⟨4735132069161221559901603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6313509425548295413202137 4735132069161221559901603)
                ·
                  refine ⟨7102698103741832339852405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735132069161221559901603 7102698103741832339852405)
                  ·
                    refine ⟨665877947225796781861163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7102698103741832339852405 665877947225796781861163)
                    ·
                      rfl

theorem cell22_1945189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1945189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945189 prefixEnd_1945189 := by exact prefixLift 1945189
  have htrace : WordTrace (prefixWord ++ tailWord_1945189) baseStart_1945189 baseEnd_1945189 := by
    simpa [prefixWord, tailWord_1945189, baseEnd_1945189] using wordTrace_append hprefix tailTrace_1945189
  have hstable : (prefixWord ++ tailWord_1945189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945189).length < 2 ^ (prefixWord ++ tailWord_1945189).sum := by decide
  have hdescent : baseEnd_1945189 < baseStart_1945189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945223 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 2, 3]
def baseStart_1945223 : Nat := 118140960795 + 1945223 * 2 ^ 59
def prefixEnd_1945223 : Nat := 4983230072969 + 3 ^ 40 * 1945223 * 2
def baseEnd_1945223 : Nat := 665889586120632026511059

theorem tailTrace_1945223 : CollatzResearch.WordTrace tailWord_1945223 prefixEnd_1945223 665889586120632026511059 := by
  unfold tailWord_1945223
  simp only [CollatzResearch.WordTrace]
  refine ⟨70948111431796763484312323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47298740954531175656208215 70948111431796763484312323)
  ·
    refine ⟨106422167147695145226468485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70948111431796763484312323 106422167147695145226468485)
    ·
      refine ⟨19954156340192839729962841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106422167147695145226468485 19954156340192839729962841)
      ·
        refine ⟨14965617255144629797472131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19954156340192839729962841 14965617255144629797472131)
        ·
          refine ⟨22448425882716944696208197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14965617255144629797472131 22448425882716944696208197)
          ·
            refine ⟨4209079853009427130539037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22448425882716944696208197 4209079853009427130539037)
            ·
              refine ⟨1578404944878535173952139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4209079853009427130539037 1578404944878535173952139)
              ·
                refine ⟨2367607417317802760928209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578404944878535173952139 2367607417317802760928209)
                ·
                  refine ⟨1775705562988352070696157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367607417317802760928209 1775705562988352070696157)
                  ·
                    refine ⟨665889586120632026511059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775705562988352070696157 665889586120632026511059)
                    ·
                      rfl

theorem cell22_1945223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_1945223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945223 prefixEnd_1945223 := by exact prefixLift 1945223
  have htrace : WordTrace (prefixWord ++ tailWord_1945223) baseStart_1945223 baseEnd_1945223 := by
    simpa [prefixWord, tailWord_1945223, baseEnd_1945223] using wordTrace_append hprefix tailTrace_1945223
  have hstable : (prefixWord ++ tailWord_1945223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945223).length < 2 ^ (prefixWord ++ tailWord_1945223).sum := by decide
  have hdescent : baseEnd_1945223 < baseStart_1945223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945232 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_1945232 : Nat := 118140960795 + 1945232 * 2 ^ 59
def prefixEnd_1945232 : Nat := 4983230072969 + 3 ^ 40 * 1945232 * 2
def baseEnd_1945232 : Nat := 665892667004559003036031

theorem tailTrace_1945232 : CollatzResearch.WordTrace tailWord_1945232 prefixEnd_1945232 665892667004559003036031 := by
  unfold tailWord_1945232
  simp only [CollatzResearch.WordTrace]
  refine ⟨35474219844382079010694975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47298959792509438680926633 35474219844382079010694975)
  ·
    refine ⟨53211329766573118516042463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35474219844382079010694975 53211329766573118516042463)
    ·
      refine ⟨79816994649859677774063695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53211329766573118516042463 79816994649859677774063695)
      ·
        refine ⟨119725491974789516661095543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79816994649859677774063695 119725491974789516661095543)
        ·
          refine ⟨179588237962184274991643315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119725491974789516661095543 179588237962184274991643315)
          ·
            refine ⟨269382356943276412487464973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179588237962184274991643315 269382356943276412487464973)
            ·
              refine ⟨101018383853728654682799365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269382356943276412487464973 101018383853728654682799365)
              ·
                refine ⟨18940946972574122753024881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101018383853728654682799365 18940946972574122753024881)
                ·
                  refine ⟨14205710229430592064768661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18940946972574122753024881 14205710229430592064768661)
                  ·
                    refine ⟨665892667004559003036031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14205710229430592064768661 665892667004559003036031)
                    ·
                      rfl

theorem cell22_1945232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_1945232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945232 prefixEnd_1945232 := by exact prefixLift 1945232
  have htrace : WordTrace (prefixWord ++ tailWord_1945232) baseStart_1945232 baseEnd_1945232 := by
    simpa [prefixWord, tailWord_1945232, baseEnd_1945232] using wordTrace_append hprefix tailTrace_1945232
  have hstable : (prefixWord ++ tailWord_1945232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945232).length < 2 ^ (prefixWord ++ tailWord_1945232).sum := by decide
  have hdescent : baseEnd_1945232 < baseStart_1945232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945236 : List Nat := [2, 4, 2, 2, 2, 1, 1, 8]
def baseStart_1945236 : Nat := 118140960795 + 1945236 * 2 ^ 59
def prefixEnd_1945236 : Nat := 4983230072969 + 3 ^ 40 * 1945236 * 2
def baseEnd_1945236 : Nat := 73988226254033813992891

theorem tailTrace_1945236 : CollatzResearch.WordTrace tailWord_1945236 prefixEnd_1945236 73988226254033813992891 := by
  unfold tailWord_1945236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35474292790374833352267781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47299057053833111136357041 35474292790374833352267781)
  ·
    refine ⟨6651429898195281253550209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35474292790374833352267781 6651429898195281253550209)
    ·
      refine ⟨4988572423646460940162657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6651429898195281253550209 4988572423646460940162657)
      ·
        refine ⟨3741429317734845705121993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4988572423646460940162657 3741429317734845705121993)
        ·
          refine ⟨2806071988301134278841495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741429317734845705121993 2806071988301134278841495)
          ·
            refine ⟨4209107982451701418262243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806071988301134278841495 4209107982451701418262243)
            ·
              refine ⟨6313661973677552127393365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209107982451701418262243 6313661973677552127393365)
              ·
                refine ⟨73988226254033813992891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6313661973677552127393365 73988226254033813992891)
                ·
                  rfl

theorem cell22_1945236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_1945236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945236 prefixEnd_1945236 := by exact prefixLift 1945236
  have htrace : WordTrace (prefixWord ++ tailWord_1945236) baseStart_1945236 baseEnd_1945236 := by
    simpa [prefixWord, tailWord_1945236, baseEnd_1945236] using wordTrace_append hprefix tailTrace_1945236
  have hstable : (prefixWord ++ tailWord_1945236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945236).length < 2 ^ (prefixWord ++ tailWord_1945236).sum := by decide
  have hdescent : baseEnd_1945236 < baseStart_1945236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945319 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1945319 : Nat := 118140960795 + 1945319 * 2 ^ 59
def prefixEnd_1945319 : Nat := 4983230072969 + 3 ^ 40 * 1945319 * 2
def baseEnd_1945319 : Nat := 665922448882519776110765

theorem tailTrace_1945319 : CollatzResearch.WordTrace tailWord_1945319 prefixEnd_1945319 665922448882519776110765 := by
  unfold tailWord_1945319
  simp only [CollatzResearch.WordTrace]
  refine ⟨70951612839448971879807011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47301075226299314586538007 70951612839448971879807011)
  ·
    refine ⟨106427419259173457819710517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70951612839448971879807011 106427419259173457819710517)
    ·
      refine ⟨9977570555547511670597861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106427419259173457819710517 9977570555547511670597861)
      ·
        refine ⟨1870794479165158438237099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9977570555547511670597861 1870794479165158438237099)
        ·
          refine ⟨2806191718747737657355649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870794479165158438237099 2806191718747737657355649)
          ·
            refine ⟨2104643789060803243016737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2806191718747737657355649 2104643789060803243016737)
            ·
              refine ⟨1578482841795602432262553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104643789060803243016737 1578482841795602432262553)
              ·
                refine ⟨1183862131346701824196915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578482841795602432262553 1183862131346701824196915)
                ·
                  refine ⟨1775793197020052736295373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183862131346701824196915 1775793197020052736295373)
                  ·
                    refine ⟨665922448882519776110765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775793197020052736295373 665922448882519776110765)
                    ·
                      rfl

theorem cell22_1945319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1945319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945319 prefixEnd_1945319 := by exact prefixLift 1945319
  have htrace : WordTrace (prefixWord ++ tailWord_1945319) baseStart_1945319 baseEnd_1945319 := by
    simpa [prefixWord, tailWord_1945319, baseEnd_1945319] using wordTrace_append hprefix tailTrace_1945319
  have hstable : (prefixWord ++ tailWord_1945319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945319).length < 2 ^ (prefixWord ++ tailWord_1945319).sum := by decide
  have hdescent : baseEnd_1945319 < baseStart_1945319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945356 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_1945356 : Nat := 118140960795 + 1945356 * 2 ^ 59
def prefixEnd_1945356 : Nat := 4983230072969 + 3 ^ 40 * 1945356 * 2
def baseEnd_1945356 : Nat := 665935114738664012935651

theorem tailTrace_1945356 : CollatzResearch.WordTrace tailWord_1945356 prefixEnd_1945356 665935114738664012935651 := by
  unfold tailWord_1945356
  simp only [CollatzResearch.WordTrace]
  refine ⟨35476481170157463599451961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47301974893543284799269281 35476481170157463599451961)
  ·
    refine ⟨26607360877618097699588971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35476481170157463599451961 26607360877618097699588971)
    ·
      refine ⟨39911041316427146549383457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26607360877618097699588971 39911041316427146549383457)
      ·
        refine ⟨29933280987320359912037593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39911041316427146549383457 29933280987320359912037593)
        ·
          refine ⟨22449960740490269934028195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29933280987320359912037593 22449960740490269934028195)
          ·
            refine ⟨33674941110735404901042293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22449960740490269934028195 33674941110735404901042293)
            ·
              refine ⟨3157025729131444209472715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33674941110735404901042293 3157025729131444209472715)
              ·
                refine ⟨4735538593697166314209073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157025729131444209472715 4735538593697166314209073)
                ·
                  refine ⟨3551653945272874735656805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4735538593697166314209073 3551653945272874735656805)
                  ·
                    refine ⟨665935114738664012935651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551653945272874735656805 665935114738664012935651)
                    ·
                      rfl

theorem cell22_1945356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_1945356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945356 prefixEnd_1945356 := by exact prefixLift 1945356
  have htrace : WordTrace (prefixWord ++ tailWord_1945356) baseStart_1945356 baseEnd_1945356 := by
    simpa [prefixWord, tailWord_1945356, baseEnd_1945356] using wordTrace_append hprefix tailTrace_1945356
  have hstable : (prefixWord ++ tailWord_1945356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945356).length < 2 ^ (prefixWord ++ tailWord_1945356).sum := by decide
  have hdescent : baseEnd_1945356 < baseStart_1945356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945362 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1945362 : Nat := 118140960795 + 1945362 * 2 ^ 59
def prefixEnd_1945362 : Nat := 4983230072969 + 3 ^ 40 * 1945362 * 2
def baseEnd_1945362 : Nat := 665937168661281997285633

theorem tailTrace_1945362 : CollatzResearch.WordTrace tailWord_1945362 prefixEnd_1945362 665937168661281997285633 := by
  unfold tailWord_1945362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738295294573297555905585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47302120785528793482414893 17738295294573297555905585)
  ·
    refine ⟨13303721470929973166929189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17738295294573297555905585 13303721470929973166929189)
    ·
      refine ⟨2494447775799369968799223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13303721470929973166929189 2494447775799369968799223)
      ·
        refine ⟨3741671663699054953198835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494447775799369968799223 3741671663699054953198835)
        ·
          refine ⟨5612507495548582429798253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741671663699054953198835 5612507495548582429798253)
          ·
            refine ⟨2104690310830718411174345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5612507495548582429798253 2104690310830718411174345)
            ·
              refine ⟨1578517733123038808380759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104690310830718411174345 1578517733123038808380759)
              ·
                refine ⟨2367776599684558212571139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578517733123038808380759 2367776599684558212571139)
                ·
                  refine ⟨3551664899526837318856709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367776599684558212571139 3551664899526837318856709)
                  ·
                    refine ⟨665937168661281997285633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551664899526837318856709 665937168661281997285633)
                    ·
                      rfl

theorem cell22_1945362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1945362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945362 prefixEnd_1945362 := by exact prefixLift 1945362
  have htrace : WordTrace (prefixWord ++ tailWord_1945362) baseStart_1945362 baseEnd_1945362 := by
    simpa [prefixWord, tailWord_1945362, baseEnd_1945362] using wordTrace_append hprefix tailTrace_1945362
  have hstable : (prefixWord ++ tailWord_1945362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945362).length < 2 ^ (prefixWord ++ tailWord_1945362).sum := by decide
  have hdescent : baseEnd_1945362 < baseStart_1945362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945450 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_1945450 : Nat := 118140960795 + 1945450 * 2 ^ 59
def prefixEnd_1945450 : Nat := 4983230072969 + 3 ^ 40 * 1945450 * 2
def baseEnd_1945450 : Nat := 221989097619893033695121

theorem tailTrace_1945450 : CollatzResearch.WordTrace tailWord_1945450 prefixEnd_1945450 221989097619893033695121 := by
  unfold tailWord_1945450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739097700493595313206451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47304260534649587501883869 17739097700493595313206451)
  ·
    refine ⟨26608646550740392969809677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17739097700493595313206451 26608646550740392969809677)
    ·
      refine ⟨9978242456527647363678629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26608646550740392969809677 9978242456527647363678629)
      ·
        refine ⟨1870920460598933880689743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9978242456527647363678629 1870920460598933880689743)
        ·
          refine ⟨2806380690898400821034615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870920460598933880689743 2806380690898400821034615)
          ·
            refine ⟨4209571036347601231551923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806380690898400821034615 4209571036347601231551923)
            ·
              refine ⟨6314356554521401847327885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209571036347601231551923 6314356554521401847327885)
              ·
                refine ⟨2367883707945525692747957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314356554521401847327885 2367883707945525692747957)
                ·
                  refine ⟨221989097619893033695121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2367883707945525692747957 221989097619893033695121)
                  ·
                    rfl

theorem cell22_1945450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_1945450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945450 prefixEnd_1945450 := by exact prefixLift 1945450
  have htrace : WordTrace (prefixWord ++ tailWord_1945450) baseStart_1945450 baseEnd_1945450 := by
    simpa [prefixWord, tailWord_1945450, baseEnd_1945450] using wordTrace_append hprefix tailTrace_1945450
  have hstable : (prefixWord ++ tailWord_1945450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945450).length < 2 ^ (prefixWord ++ tailWord_1945450).sum := by decide
  have hdescent : baseEnd_1945450 < baseStart_1945450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945461 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 8]
def baseStart_1945461 : Nat := 118140960795 + 1945461 * 2 ^ 59
def prefixEnd_1945461 : Nat := 4983230072969 + 3 ^ 40 * 1945461 * 2
def baseEnd_1945461 : Nat := 221990352794826246353443

theorem tailTrace_1945461 : CollatzResearch.WordTrace tailWord_1945461 prefixEnd_1945461 221990352794826246353443 := by
  unfold tailWord_1945461
  simp only [CollatzResearch.WordTrace]
  refine ⟨70956792004934530131476237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47304528003289686754317491 70956792004934530131476237)
  ·
    refine ⟨26608797001850448799303589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70956792004934530131476237 26608797001850448799303589)
    ·
      refine ⟨4989149437846959149869423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26608797001850448799303589 4989149437846959149869423)
      ·
        refine ⟨7483724156770438724804135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989149437846959149869423 7483724156770438724804135)
        ·
          refine ⟨11225586235155658087206203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483724156770438724804135 11225586235155658087206203)
          ·
            refine ⟨16838379352733487130809305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225586235155658087206203 16838379352733487130809305)
            ·
              refine ⟨12628784514550115348106979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16838379352733487130809305 12628784514550115348106979)
              ·
                refine ⟨18943176771825173022160469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12628784514550115348106979 18943176771825173022160469)
                ·
                  refine ⟨221990352794826246353443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18943176771825173022160469 221990352794826246353443)
                  ·
                    rfl

theorem cell22_1945461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_1945461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945461 prefixEnd_1945461 := by exact prefixLift 1945461
  have htrace : WordTrace (prefixWord ++ tailWord_1945461) baseStart_1945461 baseEnd_1945461 := by
    simpa [prefixWord, tailWord_1945461, baseEnd_1945461] using wordTrace_append hprefix tailTrace_1945461
  have hstable : (prefixWord ++ tailWord_1945461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945461).length < 2 ^ (prefixWord ++ tailWord_1945461).sum := by decide
  have hdescent : baseEnd_1945461 < baseStart_1945461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945476 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1945476 : Nat := 118140960795 + 1945476 * 2 ^ 59
def prefixEnd_1945476 : Nat := 4983230072969 + 3 ^ 40 * 1945476 * 2
def baseEnd_1945476 : Nat := 665976193191023699935283

theorem tailTrace_1945476 : CollatzResearch.WordTrace tailWord_1945476 prefixEnd_1945476 665976193191023699935283 := by
  unfold tailWord_1945476
  simp only [CollatzResearch.WordTrace]
  refine ⟨35478669549940093846636141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47304892733253458462181521 35478669549940093846636141)
  ·
    refine ⟨13304501081227535192488553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35478669549940093846636141 13304501081227535192488553)
    ·
      refine ⟨9978375810920651394366415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13304501081227535192488553 9978375810920651394366415)
      ·
        refine ⟨14967563716380977091549623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9978375810920651394366415 14967563716380977091549623)
        ·
          refine ⟨22451345574571465637324435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14967563716380977091549623 22451345574571465637324435)
          ·
            refine ⟨33677018361857198455986653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22451345574571465637324435 33677018361857198455986653)
            ·
              refine ⟨12628881885696449420994995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33677018361857198455986653 12628881885696449420994995)
              ·
                refine ⟨18943322828544674131492493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12628881885696449420994995 18943322828544674131492493)
                ·
                  refine ⟨7103746060704252799309685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18943322828544674131492493 7103746060704252799309685)
                  ·
                    refine ⟨665976193191023699935283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7103746060704252799309685 665976193191023699935283)
                    ·
                      rfl

theorem cell22_1945476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1945476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945476 prefixEnd_1945476 := by exact prefixLift 1945476
  have htrace : WordTrace (prefixWord ++ tailWord_1945476) baseStart_1945476 baseEnd_1945476 := by
    simpa [prefixWord, tailWord_1945476, baseEnd_1945476] using wordTrace_append hprefix tailTrace_1945476
  have hstable : (prefixWord ++ tailWord_1945476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945476).length < 2 ^ (prefixWord ++ tailWord_1945476).sum := by decide
  have hdescent : baseEnd_1945476 < baseStart_1945476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945495 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 4]
def baseStart_1945495 : Nat := 118140960795 + 1945495 * 2 ^ 59
def prefixEnd_1945495 : Nat := 4983230072969 + 3 ^ 40 * 1945495 * 2
def baseEnd_1945495 : Nat := 221994232426437994570075

theorem tailTrace_1945495 : CollatzResearch.WordTrace tailWord_1945495 prefixEnd_1945495 221994232426437994570075 := by
  unfold tailWord_1945495
  simp only [CollatzResearch.WordTrace]
  refine ⟨70958032086811353938213939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47305354724540902625475959 70958032086811353938213939)
  ·
    refine ⟨106437048130217030907320909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70958032086811353938213939 106437048130217030907320909)
    ·
      refine ⟨39913893048831386590245341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106437048130217030907320909 39913893048831386590245341)
      ·
        refine ⟨14967709893311769971342003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39913893048831386590245341 14967709893311769971342003)
        ·
          refine ⟨22451564839967654957013005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14967709893311769971342003 22451564839967654957013005)
          ·
            refine ⟨8419336814987870608879877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22451564839967654957013005 8419336814987870608879877)
            ·
              refine ⟨1578625652810225739164977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8419336814987870608879877 1578625652810225739164977)
              ·
                refine ⟨1183969239607669304373733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578625652810225739164977 1183969239607669304373733)
                ·
                  refine ⟨221994232426437994570075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183969239607669304373733 221994232426437994570075)
                  ·
                    rfl

theorem cell22_1945495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 4].length) (baseStart_1945495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945495 prefixEnd_1945495 := by exact prefixLift 1945495
  have htrace : WordTrace (prefixWord ++ tailWord_1945495) baseStart_1945495 baseEnd_1945495 := by
    simpa [prefixWord, tailWord_1945495, baseEnd_1945495] using wordTrace_append hprefix tailTrace_1945495
  have hstable : (prefixWord ++ tailWord_1945495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945495).length < 2 ^ (prefixWord ++ tailWord_1945495).sum := by decide
  have hdescent : baseEnd_1945495 < baseStart_1945495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945525 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1945525 : Nat := 118140960795 + 1945525 * 2 ^ 59
def prefixEnd_1945525 : Nat := 4983230072969 + 3 ^ 40 * 1945525 * 2
def baseEnd_1945525 : Nat := 665992966892403905460133

theorem tailTrace_1945525 : CollatzResearch.WordTrace tailWord_1945525 prefixEnd_1945525 665992966892403905460133 := by
  unfold tailWord_1945525
  simp only [CollatzResearch.WordTrace]
  refine ⟨70959126276702669061806029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47306084184468446041204019 70959126276702669061806029)
  ·
    refine ⟨26609672353763500898177261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70959126276702669061806029 26609672353763500898177261)
    ·
      refine ⟨9978627132661312836816473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26609672353763500898177261 9978627132661312836816473)
      ·
        refine ⟨7483970349495984627612355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9978627132661312836816473 7483970349495984627612355)
        ·
          refine ⟨11225955524243976941418533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483970349495984627612355 11225955524243976941418533)
          ·
            refine ⟨2104866660795745676515975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11225955524243976941418533 2104866660795745676515975)
            ·
              refine ⟨3157299991193618514773963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104866660795745676515975 3157299991193618514773963)
              ·
                refine ⟨4735949986790427772160945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157299991193618514773963 4735949986790427772160945)
                ·
                  refine ⟨3551962490092820829120709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4735949986790427772160945 3551962490092820829120709)
                  ·
                    refine ⟨665992966892403905460133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551962490092820829120709 665992966892403905460133)
                    ·
                      rfl

theorem cell22_1945525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1945525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945525 prefixEnd_1945525 := by exact prefixLift 1945525
  have htrace : WordTrace (prefixWord ++ tailWord_1945525) baseStart_1945525 baseEnd_1945525 := by
    simpa [prefixWord, tailWord_1945525, baseEnd_1945525] using wordTrace_append hprefix tailTrace_1945525
  have hstable : (prefixWord ++ tailWord_1945525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945525).length < 2 ^ (prefixWord ++ tailWord_1945525).sum := by decide
  have hdescent : baseEnd_1945525 < baseStart_1945525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945551 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 7]
def baseStart_1945551 : Nat := 118140960795 + 1945551 * 2 ^ 59
def prefixEnd_1945551 : Nat := 4983230072969 + 3 ^ 40 * 1945551 * 2
def baseEnd_1945551 : Nat := 222000622407916168103351

theorem tailTrace_1945551 : CollatzResearch.WordTrace tailWord_1945551 prefixEnd_1945551 222000622407916168103351 := by
  unfold tailWord_1945551
  simp only [CollatzResearch.WordTrace]
  refine ⟨70960074574608475502252507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47306716383072317001501671 70960074574608475502252507)
  ·
    refine ⟨106440111861912713253378761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70960074574608475502252507 106440111861912713253378761)
    ·
      refine ⟨79830083896434534940034071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106440111861912713253378761 79830083896434534940034071)
      ·
        refine ⟨119745125844651802410051107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79830083896434534940034071 119745125844651802410051107)
        ·
          refine ⟨179617688766977703615076661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119745125844651802410051107 179617688766977703615076661)
          ·
            refine ⟨16839158321904159713913437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179617688766977703615076661 16839158321904159713913437)
            ·
              refine ⟨6314684370714059892717539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16839158321904159713913437 6314684370714059892717539)
              ·
                refine ⟨9472026556071089839076309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314684370714059892717539 9472026556071089839076309)
                ·
                  refine ⟨222000622407916168103351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9472026556071089839076309 222000622407916168103351)
                  ·
                    rfl

theorem cell22_1945551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 7].length) (baseStart_1945551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945551 prefixEnd_1945551 := by exact prefixLift 1945551
  have htrace : WordTrace (prefixWord ++ tailWord_1945551) baseStart_1945551 baseEnd_1945551 := by
    simpa [prefixWord, tailWord_1945551, baseEnd_1945551] using wordTrace_append hprefix tailTrace_1945551
  have hstable : (prefixWord ++ tailWord_1945551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945551).length < 2 ^ (prefixWord ++ tailWord_1945551).sum := by decide
  have hdescent : baseEnd_1945551 < baseStart_1945551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945690 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_1945690 : Nat := 118140960795 + 1945690 * 2 ^ 59
def prefixEnd_1945690 : Nat := 4983230072969 + 3 ^ 40 * 1945690 * 2
def baseEnd_1945690 : Nat := 666049449764398475084627

theorem tailTrace_1945690 : CollatzResearch.WordTrace tailWord_1945690 prefixEnd_1945690 666049449764398475084627 := by
  unfold tailWord_1945690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17741286080276225560390631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47310096214069934827708349 17741286080276225560390631)
  ·
    refine ⟨26611929120414338340585947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17741286080276225560390631 26611929120414338340585947)
    ·
      refine ⟨39917893680621507510878921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26611929120414338340585947 39917893680621507510878921)
      ·
        refine ⟨29938420260466130633159191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39917893680621507510878921 29938420260466130633159191)
        ·
          refine ⟨44907630390699195949738787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29938420260466130633159191 44907630390699195949738787)
          ·
            refine ⟨67361445586048793924608181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44907630390699195949738787 67361445586048793924608181)
            ·
              refine ⟨6315135523692074430432017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67361445586048793924608181 6315135523692074430432017)
              ·
                refine ⟨4736351642769055822824013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315135523692074430432017 4736351642769055822824013)
                ·
                  refine ⟨1776131866038395933559005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4736351642769055822824013 1776131866038395933559005)
                  ·
                    refine ⟨666049449764398475084627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776131866038395933559005 666049449764398475084627)
                    ·
                      rfl

theorem cell22_1945690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_1945690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945690 prefixEnd_1945690 := by exact prefixLift 1945690
  have htrace : WordTrace (prefixWord ++ tailWord_1945690) baseStart_1945690 baseEnd_1945690 := by
    simpa [prefixWord, tailWord_1945690, baseEnd_1945690] using wordTrace_append hprefix tailTrace_1945690
  have hstable : (prefixWord ++ tailWord_1945690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945690).length < 2 ^ (prefixWord ++ tailWord_1945690).sum := by decide
  have hdescent : baseEnd_1945690 < baseStart_1945690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945694 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1945694 : Nat := 118140960795 + 1945694 * 2 ^ 59
def prefixEnd_1945694 : Nat := 4983230072969 + 3 ^ 40 * 1945694 * 2
def baseEnd_1945694 : Nat := 666050819046143797984615

theorem tailTrace_1945694 : CollatzResearch.WordTrace tailWord_1945694 prefixEnd_1945694 666050819046143797984615 := by
  unfold tailWord_1945694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8870661276636301365588517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47310193475393607283138757 8870661276636301365588517)
  ·
    refine ⟨1663248989369306506047847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8870661276636301365588517 1663248989369306506047847)
    ·
      refine ⟨2494873484053959759071771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663248989369306506047847 2494873484053959759071771)
      ·
        refine ⟨3742310226080939638607657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494873484053959759071771 3742310226080939638607657)
        ·
          refine ⟨2806732669560704728955743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742310226080939638607657 2806732669560704728955743)
          ·
            refine ⟨4210099004341057093433615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806732669560704728955743 4210099004341057093433615)
            ·
              refine ⟨6315148506511585640150423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210099004341057093433615 6315148506511585640150423)
              ·
                refine ⟨9472722759767378460225635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315148506511585640150423 9472722759767378460225635)
                ·
                  refine ⟨14209084139651067690338453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9472722759767378460225635 14209084139651067690338453)
                  ·
                    refine ⟨666050819046143797984615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14209084139651067690338453 666050819046143797984615)
                    ·
                      rfl

theorem cell22_1945694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1945694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945694 prefixEnd_1945694 := by exact prefixLift 1945694
  have htrace : WordTrace (prefixWord ++ tailWord_1945694) baseStart_1945694 baseEnd_1945694 := by
    simpa [prefixWord, tailWord_1945694, baseEnd_1945694] using wordTrace_append hprefix tailTrace_1945694
  have hstable : (prefixWord ++ tailWord_1945694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945694).length < 2 ^ (prefixWord ++ tailWord_1945694).sum := by decide
  have hdescent : baseEnd_1945694 < baseStart_1945694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945703 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 7]
def baseStart_1945703 : Nat := 118140960795 + 1945703 * 2 ^ 59
def prefixEnd_1945703 : Nat := 4983230072969 + 3 ^ 40 * 1945703 * 2
def baseEnd_1945703 : Nat := 222017966643356924836529

theorem tailTrace_1945703 : CollatzResearch.WordTrace tailWord_1945703 prefixEnd_1945703 222017966643356924836529 := by
  unfold tailWord_1945703
  simp only [CollatzResearch.WordTrace]
  refine ⟨70965618470057805461785763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47310412313371870307857175 70965618470057805461785763)
  ·
    refine ⟨106448427705086708192678645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70965618470057805461785763 106448427705086708192678645)
    ·
      refine ⟨9979540097351878893063623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106448427705086708192678645 9979540097351878893063623)
      ·
        refine ⟨14969310146027818339595435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9979540097351878893063623 14969310146027818339595435)
        ·
          refine ⟨22453965219041727509393153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14969310146027818339595435 22453965219041727509393153)
          ·
            refine ⟨16840473914281295632044865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22453965219041727509393153 16840473914281295632044865)
            ·
              refine ⟨12630355435710971724033649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16840473914281295632044865 12630355435710971724033649)
              ·
                refine ⟨9472766576783228793025237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12630355435710971724033649 9472766576783228793025237)
                ·
                  refine ⟨222017966643356924836529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9472766576783228793025237 222017966643356924836529)
                  ·
                    rfl

theorem cell22_1945703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_1945703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945703 prefixEnd_1945703 := by exact prefixLift 1945703
  have htrace : WordTrace (prefixWord ++ tailWord_1945703) baseStart_1945703 baseEnd_1945703 := by
    simpa [prefixWord, tailWord_1945703, baseEnd_1945703] using wordTrace_append hprefix tailTrace_1945703
  have hstable : (prefixWord ++ tailWord_1945703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945703).length < 2 ^ (prefixWord ++ tailWord_1945703).sum := by decide
  have hdescent : baseEnd_1945703 < baseStart_1945703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945758 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1945758 : Nat := 118140960795 + 1945758 * 2 ^ 59
def prefixEnd_1945758 : Nat := 4983230072969 + 3 ^ 40 * 1945758 * 2
def baseEnd_1945758 : Nat := 666072727554068964384419

theorem tailTrace_1945758 : CollatzResearch.WordTrace tailWord_1945758 prefixEnd_1945758 666072727554068964384419 := by
  unfold tailWord_1945758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8870953060607318731879741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47311749656572366570025285 8870953060607318731879741)
  ·
    refine ⟨3326607397727744524454903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8870953060607318731879741 3326607397727744524454903)
    ·
      refine ⟨4989911096591616786682355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326607397727744524454903 4989911096591616786682355)
      ·
        refine ⟨7484866644887425180023533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989911096591616786682355 7484866644887425180023533)
        ·
          refine ⟨2806824991832784442508825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7484866644887425180023533 2806824991832784442508825)
          ·
            refine ⟨2105118743874588331881619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2806824991832784442508825 2105118743874588331881619)
            ·
              refine ⟨3157678115811882497822429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105118743874588331881619 3157678115811882497822429)
              ·
                refine ⟨1184129293429455936683411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3157678115811882497822429 1184129293429455936683411)
                ·
                  refine ⟨1776193940144183905025117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184129293429455936683411 1776193940144183905025117)
                  ·
                    refine ⟨666072727554068964384419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776193940144183905025117 666072727554068964384419)
                    ·
                      rfl

theorem cell22_1945758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1945758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945758 prefixEnd_1945758 := by exact prefixLift 1945758
  have htrace : WordTrace (prefixWord ++ tailWord_1945758) baseStart_1945758 baseEnd_1945758 := by
    simpa [prefixWord, tailWord_1945758, baseEnd_1945758] using wordTrace_append hprefix tailTrace_1945758
  have hstable : (prefixWord ++ tailWord_1945758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945758).length < 2 ^ (prefixWord ++ tailWord_1945758).sum := by decide
  have hdescent : baseEnd_1945758 < baseStart_1945758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945810 : List Nat := [3, 2, 2, 2, 1, 2, 2, 8]
def baseStart_1945810 : Nat := 118140960795 + 1945810 * 2 ^ 59
def prefixEnd_1945810 : Nat := 4983230072969 + 3 ^ 40 * 1945810 * 2
def baseEnd_1945810 : Nat := 74010058690750906898251

theorem tailTrace_1945810 : CollatzResearch.WordTrace tailWord_1945810 prefixEnd_1945810 74010058690750906898251 := by
  unfold tailWord_1945810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17742380270167540683982721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47313014053780108490620589 17742380270167540683982721)
  ·
    refine ⟨13306785202625655512987041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17742380270167540683982721 13306785202625655512987041)
    ·
      refine ⟨9980088901969241634740281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13306785202625655512987041 9980088901969241634740281)
      ·
        refine ⟨7485066676476931226055211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9980088901969241634740281 7485066676476931226055211)
        ·
          refine ⟨11227600014715396839082817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7485066676476931226055211 11227600014715396839082817)
          ·
            refine ⟨8420700011036547629312113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11227600014715396839082817 8420700011036547629312113)
            ·
              refine ⟨6315525008277410721984085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8420700011036547629312113 6315525008277410721984085)
              ·
                refine ⟨74010058690750906898251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6315525008277410721984085 74010058690750906898251)
                ·
                  rfl

theorem cell22_1945810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_1945810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945810 prefixEnd_1945810 := by exact prefixLift 1945810
  have htrace : WordTrace (prefixWord ++ tailWord_1945810) baseStart_1945810 baseEnd_1945810 := by
    simpa [prefixWord, tailWord_1945810, baseEnd_1945810] using wordTrace_append hprefix tailTrace_1945810
  have hstable : (prefixWord ++ tailWord_1945810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945810).length < 2 ^ (prefixWord ++ tailWord_1945810).sum := by decide
  have hdescent : baseEnd_1945810 < baseStart_1945810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945814 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1945814 : Nat := 118140960795 + 1945814 * 2 ^ 59
def prefixEnd_1945814 : Nat := 4983230072969 + 3 ^ 40 * 1945814 * 2
def baseEnd_1945814 : Nat := 666091897498503484984247

theorem tailTrace_1945814 : CollatzResearch.WordTrace tailWord_1945814 prefixEnd_1945814 666091897498503484984247 := by
  unfold tailWord_1945814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435604185790979463692281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47313111315103780946050997 4435604185790979463692281)
  ·
    refine ⟨3326703139343234597769211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4435604185790979463692281 3326703139343234597769211)
    ·
      refine ⟨4990054709014851896653817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326703139343234597769211 4990054709014851896653817)
      ·
        refine ⟨3742541031761138922490363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4990054709014851896653817 3742541031761138922490363)
        ·
          refine ⟨5613811547641708383735545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742541031761138922490363 5613811547641708383735545)
          ·
            refine ⟨4210358660731281287801659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5613811547641708383735545 4210358660731281287801659)
            ·
              refine ⟨6315537991096921931702489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210358660731281287801659 6315537991096921931702489)
              ·
                refine ⟨4736653493322691448776867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315537991096921931702489 4736653493322691448776867)
                ·
                  refine ⟨7104980239984037173165301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736653493322691448776867 7104980239984037173165301)
                  ·
                    refine ⟨666091897498503484984247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7104980239984037173165301 666091897498503484984247)
                    ·
                      rfl

theorem cell22_1945814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1945814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945814 prefixEnd_1945814 := by exact prefixLift 1945814
  have htrace : WordTrace (prefixWord ++ tailWord_1945814) baseStart_1945814 baseEnd_1945814 := by
    simpa [prefixWord, tailWord_1945814, baseEnd_1945814] using wordTrace_append hprefix tailTrace_1945814
  have hstable : (prefixWord ++ tailWord_1945814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945814).length < 2 ^ (prefixWord ++ tailWord_1945814).sum := by decide
  have hdescent : baseEnd_1945814 < baseStart_1945814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945827 : List Nat := [1, 1, 1, 8, 2, 9]
def baseStart_1945827 : Nat := 118140960795 + 1945827 * 2 ^ 59
def prefixEnd_1945827 : Nat := 4983230072969 + 3 ^ 40 * 1945827 * 2
def baseEnd_1945827 : Nat := 8223411699557725733447

theorem tailTrace_1945827 : CollatzResearch.WordTrace tailWord_1945827 prefixEnd_1945827 8223411699557725733447 := by
  unfold tailWord_1945827
  simp only [CollatzResearch.WordTrace]
  refine ⟨70970141121608574639299735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47313427414405716426199823 70970141121608574639299735)
  ·
    refine ⟨106455211682412861958949603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70970141121608574639299735 106455211682412861958949603)
    ·
      refine ⟨159682817523619292938424405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106455211682412861958949603 159682817523619292938424405)
      ·
        refine ⟨1871283017854913589122161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 159682817523619292938424405 1871283017854913589122161)
        ·
          refine ⟨1403462263391185191841621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1871283017854913589122161 1403462263391185191841621)
          ·
            refine ⟨8223411699557725733447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1403462263391185191841621 8223411699557725733447)
            ·
              rfl

theorem cell22_1945827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 9].length) (baseStart_1945827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945827 prefixEnd_1945827 := by exact prefixLift 1945827
  have htrace : WordTrace (prefixWord ++ tailWord_1945827) baseStart_1945827 baseEnd_1945827 := by
    simpa [prefixWord, tailWord_1945827, baseEnd_1945827] using wordTrace_append hprefix tailTrace_1945827
  have hstable : (prefixWord ++ tailWord_1945827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945827).length < 2 ^ (prefixWord ++ tailWord_1945827).sum := by decide
  have hdescent : baseEnd_1945827 < baseStart_1945827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945855 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 5]
def baseStart_1945855 : Nat := 118140960795 + 1945855 * 2 ^ 59
def prefixEnd_1945855 : Nat := 4983230072969 + 3 ^ 40 * 1945855 * 2
def baseEnd_1945855 : Nat := 222035310878797681569707

theorem tailTrace_1945855 : CollatzResearch.WordTrace tailWord_1945855 prefixEnd_1945855 222035310878797681569707 := by
  unfold tailWord_1945855
  simp only [CollatzResearch.WordTrace]
  refine ⟨70971162365507135421319019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47314108243671423614212679 70971162365507135421319019)
  ·
    refine ⟨106456743548260703131978529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70971162365507135421319019 106456743548260703131978529)
    ·
      refine ⟨79842557661195527348983897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106456743548260703131978529 79842557661195527348983897)
      ·
        refine ⟨59881918245896645511737923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79842557661195527348983897 59881918245896645511737923)
        ·
          refine ⟨89822877368844968267606885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59881918245896645511737923 89822877368844968267606885)
          ·
            refine ⟨16841789506658431550176291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89822877368844968267606885 16841789506658431550176291)
            ·
              refine ⟨25262684259987647325264437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16841789506658431550176291 25262684259987647325264437)
              ·
                refine ⟨2368376649373841936743541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25262684259987647325264437 2368376649373841936743541)
                ·
                  refine ⟨222035310878797681569707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368376649373841936743541 222035310878797681569707)
                  ·
                    rfl

theorem cell22_1945855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 5].length) (baseStart_1945855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945855 prefixEnd_1945855 := by exact prefixLift 1945855
  have htrace : WordTrace (prefixWord ++ tailWord_1945855) baseStart_1945855 baseEnd_1945855 := by
    simpa [prefixWord, tailWord_1945855, baseEnd_1945855] using wordTrace_append hprefix tailTrace_1945855
  have hstable : (prefixWord ++ tailWord_1945855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945855).length < 2 ^ (prefixWord ++ tailWord_1945855).sum := by decide
  have hdescent : baseEnd_1945855 < baseStart_1945855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945870 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1945870 : Nat := 118140960795 + 1945870 * 2 ^ 59
def prefixEnd_1945870 : Nat := 4983230072969 + 3 ^ 40 * 1945870 * 2
def baseEnd_1945870 : Nat := 666111067442938005584075

theorem tailTrace_1945870 : CollatzResearch.WordTrace tailWord_1945870 prefixEnd_1945870 666111067442938005584075 := by
  unfold tailWord_1945870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8871463682556599122889383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47314472973635195322076709 8871463682556599122889383)
  ·
    refine ⟨13307195523834898684334075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8871463682556599122889383 13307195523834898684334075)
    ·
      refine ⟨19960793285752348026501113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13307195523834898684334075 19960793285752348026501113)
      ·
        refine ⟨14970594964314261019875835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19960793285752348026501113 14970594964314261019875835)
        ·
          refine ⟨22455892446471391529813753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14970594964314261019875835 22455892446471391529813753)
          ·
            refine ⟨16841919334853543647360315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22455892446471391529813753 16841919334853543647360315)
            ·
              refine ⟨25262879002280315471040473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16841919334853543647360315 25262879002280315471040473)
              ·
                refine ⟨18947159251710236603280355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25262879002280315471040473 18947159251710236603280355)
                ·
                  refine ⟨28420738877565354904920533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18947159251710236603280355 28420738877565354904920533)
                  ·
                    refine ⟨666111067442938005584075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28420738877565354904920533 666111067442938005584075)
                    ·
                      rfl

theorem cell22_1945870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1945870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945870 prefixEnd_1945870 := by exact prefixLift 1945870
  have htrace : WordTrace (prefixWord ++ tailWord_1945870) baseStart_1945870 baseEnd_1945870 := by
    simpa [prefixWord, tailWord_1945870, baseEnd_1945870] using wordTrace_append hprefix tailTrace_1945870
  have hstable : (prefixWord ++ tailWord_1945870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945870).length < 2 ^ (prefixWord ++ tailWord_1945870).sum := by decide
  have hdescent : baseEnd_1945870 < baseStart_1945870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945900 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_1945900 : Nat := 118140960795 + 1945900 * 2 ^ 59
def prefixEnd_1945900 : Nat := 4983230072969 + 3 ^ 40 * 1945900 * 2
def baseEnd_1945900 : Nat := 222040445685342642444661

theorem tailTrace_1945900 : CollatzResearch.WordTrace tailWord_1945900 prefixEnd_1945900 222040445685342642444661 := by
  unfold tailWord_1945900
  simp only [CollatzResearch.WordTrace]
  refine ⟨35486401825172054053353577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47315202433562738737804769 35486401825172054053353577)
  ·
    refine ⟨26614801368879040540015183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35486401825172054053353577 26614801368879040540015183)
    ·
      refine ⟨39922202053318560810022775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26614801368879040540015183 39922202053318560810022775)
      ·
        refine ⟨59883303079977841215034163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39922202053318560810022775 59883303079977841215034163)
        ·
          refine ⟨89824954619966761822551245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59883303079977841215034163 89824954619966761822551245)
          ·
            refine ⟨33684357982487535683456717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89824954619966761822551245 33684357982487535683456717)
            ·
              refine ⟨12631634243432825881296269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33684357982487535683456717 12631634243432825881296269)
              ·
                refine ⟨4736862841287309705486101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12631634243432825881296269 4736862841287309705486101)
                ·
                  refine ⟨222040445685342642444661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4736862841287309705486101 222040445685342642444661)
                  ·
                    rfl

theorem cell22_1945900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_1945900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945900 prefixEnd_1945900 := by exact prefixLift 1945900
  have htrace : WordTrace (prefixWord ++ tailWord_1945900) baseStart_1945900 baseEnd_1945900 := by
    simpa [prefixWord, tailWord_1945900, baseEnd_1945900] using wordTrace_append hprefix tailTrace_1945900
  have hstable : (prefixWord ++ tailWord_1945900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945900).length < 2 ^ (prefixWord ++ tailWord_1945900).sum := by decide
  have hdescent : baseEnd_1945900 < baseStart_1945900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945932 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_1945932 : Nat := 118140960795 + 1945932 * 2 ^ 59
def prefixEnd_1945932 : Nat := 4983230072969 + 3 ^ 40 * 1945932 * 2
def baseEnd_1945932 : Nat := 666132291309990510533885

theorem tailTrace_1945932 : CollatzResearch.WordTrace tailWord_1945932 prefixEnd_1945932 666132291309990510533885 := by
  unfold tailWord_1945932
  simp only [CollatzResearch.WordTrace]
  refine ⟨35486985393114088785936025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47315980524152118381248033 35486985393114088785936025)
  ·
    refine ⟨26615239044835566589452019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35486985393114088785936025 26615239044835566589452019)
    ·
      refine ⟨39922858567253349884178029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26615239044835566589452019 39922858567253349884178029)
      ·
        refine ⟨14971071962720006206566761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39922858567253349884178029 14971071962720006206566761)
        ·
          refine ⟨11228303972040004654925071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14971071962720006206566761 11228303972040004654925071)
          ·
            refine ⟨16842455958060006982387607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11228303972040004654925071 16842455958060006982387607)
            ·
              refine ⟨25263683937090010473581411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16842455958060006982387607 25263683937090010473581411)
              ·
                refine ⟨37895525905635015710372117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25263683937090010473581411 37895525905635015710372117)
                ·
                  refine ⟨1776352776826641361423693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37895525905635015710372117 1776352776826641361423693)
                  ·
                    refine ⟨666132291309990510533885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776352776826641361423693 666132291309990510533885)
                    ·
                      rfl

theorem cell22_1945932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_1945932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945932 prefixEnd_1945932 := by exact prefixLift 1945932
  have htrace : WordTrace (prefixWord ++ tailWord_1945932) baseStart_1945932 baseEnd_1945932 := by
    simpa [prefixWord, tailWord_1945932, baseEnd_1945932] using wordTrace_append hprefix tailTrace_1945932
  have hstable : (prefixWord ++ tailWord_1945932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945932).length < 2 ^ (prefixWord ++ tailWord_1945932).sum := by decide
  have hdescent : baseEnd_1945932 < baseStart_1945932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945962 : List Nat := [3, 1, 3, 3, 1, 1, 1, 9]
def baseStart_1945962 : Nat := 118140960795 + 1945962 * 2 ^ 59
def prefixEnd_1945962 : Nat := 4983230072969 + 3 ^ 40 * 1945962 * 2
def baseEnd_1945962 : Nat := 74015840102564492475977

theorem tailTrace_1945962 : CollatzResearch.WordTrace tailWord_1945962 prefixEnd_1945962 74015840102564492475977 := by
  unfold tailWord_1945962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743766244029873173866035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47316709984079661796976093 17743766244029873173866035)
  ·
    refine ⟨26615649366044809760799053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17743766244029873173866035 26615649366044809760799053)
    ·
      refine ⟨9980868512266803660299645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26615649366044809760799053 9980868512266803660299645)
      ·
        refine ⟨3742825692100051372612367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9980868512266803660299645 3742825692100051372612367)
        ·
          refine ⟨5614238538150077058918551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742825692100051372612367 5614238538150077058918551)
          ·
            refine ⟨8421357807225115588377827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614238538150077058918551 8421357807225115588377827)
            ·
              refine ⟨12632036710837673382566741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8421357807225115588377827 12632036710837673382566741)
              ·
                refine ⟨74015840102564492475977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12632036710837673382566741 74015840102564492475977)
                ·
                  rfl

theorem cell22_1945962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_1945962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945962 prefixEnd_1945962 := by exact prefixLift 1945962
  have htrace : WordTrace (prefixWord ++ tailWord_1945962) baseStart_1945962 baseEnd_1945962 := by
    simpa [prefixWord, tailWord_1945962, baseEnd_1945962] using wordTrace_append hprefix tailTrace_1945962
  have hstable : (prefixWord ++ tailWord_1945962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945962).length < 2 ^ (prefixWord ++ tailWord_1945962).sum := by decide
  have hdescent : baseEnd_1945962 < baseStart_1945962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945975 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1945975 : Nat := 118140960795 + 1945975 * 2 ^ 59
def prefixEnd_1945975 : Nat := 4983230072969 + 3 ^ 40 * 1945975 * 2
def baseEnd_1945975 : Nat := 666147011088752731708753

theorem tailTrace_1945975 : CollatzResearch.WordTrace tailWord_1945975 prefixEnd_1945975 666147011088752731708753 := by
  unfold tailWord_1945975
  simp only [CollatzResearch.WordTrace]
  refine ⟨70975539125072395915687379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47317026083381597277124919 70975539125072395915687379)
  ·
    refine ⟨106463308687608593873531069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70975539125072395915687379 106463308687608593873531069)
    ·
      refine ⟨39923740757853222702574151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106463308687608593873531069 39923740757853222702574151)
      ·
        refine ⟨59885611136779834053861227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39923740757853222702574151 59885611136779834053861227)
        ·
          refine ⟨89828416705169751080791841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59885611136779834053861227 89828416705169751080791841)
          ·
            refine ⟨67371312528877313310593881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89828416705169751080791841 67371312528877313310593881)
            ·
              refine ⟨50528484396657984982945411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67371312528877313310593881 50528484396657984982945411)
              ·
                refine ⟨75792726594986977474418117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50528484396657984982945411 75792726594986977474418117)
                ·
                  refine ⟨14211136236560058276453397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75792726594986977474418117 14211136236560058276453397)
                  ·
                    refine ⟨666147011088752731708753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14211136236560058276453397 666147011088752731708753)
                    ·
                      rfl

theorem cell22_1945975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1945975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945975 prefixEnd_1945975 := by exact prefixLift 1945975
  have htrace : WordTrace (prefixWord ++ tailWord_1945975) baseStart_1945975 baseEnd_1945975 := by
    simpa [prefixWord, tailWord_1945975, baseEnd_1945975] using wordTrace_append hprefix tailTrace_1945975
  have hstable : (prefixWord ++ tailWord_1945975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945975).length < 2 ^ (prefixWord ++ tailWord_1945975).sum := by decide
  have hdescent : baseEnd_1945975 < baseStart_1945975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945977 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_1945977 : Nat := 118140960795 + 1945977 * 2 ^ 59
def prefixEnd_1945977 : Nat := 4983230072969 + 3 ^ 40 * 1945977 * 2
def baseEnd_1945977 : Nat := 666147695729625393158747

theorem tailTrace_1945977 : CollatzResearch.WordTrace tailWord_1945977 prefixEnd_1945977 666147695729625393158747 := by
  unfold tailWord_1945977
  simp only [CollatzResearch.WordTrace]
  refine ⟨70975612071065150257260185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47317074714043433504840123 70975612071065150257260185)
  ·
    refine ⟨53231709053298862692945139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70975612071065150257260185 53231709053298862692945139)
    ·
      refine ⟨79847563579948294039417709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53231709053298862692945139 79847563579948294039417709)
      ·
        refine ⟨29942836342480610264781641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79847563579948294039417709 29942836342480610264781641)
        ·
          refine ⟨22457127256860457698586231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29942836342480610264781641 22457127256860457698586231)
          ·
            refine ⟨33685690885290686547879347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22457127256860457698586231 33685690885290686547879347)
            ·
              refine ⟨50528536327936029821819021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33685690885290686547879347 50528536327936029821819021)
              ·
                refine ⟨18948201122976011183182133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50528536327936029821819021 18948201122976011183182133)
                ·
                  refine ⟨1776393855279001048423325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18948201122976011183182133 1776393855279001048423325)
                  ·
                    refine ⟨666147695729625393158747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776393855279001048423325 666147695729625393158747)
                    ·
                      rfl

theorem cell22_1945977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_1945977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1945977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1945977 prefixEnd_1945977 := by exact prefixLift 1945977
  have htrace : WordTrace (prefixWord ++ tailWord_1945977) baseStart_1945977 baseEnd_1945977 := by
    simpa [prefixWord, tailWord_1945977, baseEnd_1945977] using wordTrace_append hprefix tailTrace_1945977
  have hstable : (prefixWord ++ tailWord_1945977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945977).length < 2 ^ (prefixWord ++ tailWord_1945977).sum := by decide
  have hdescent : baseEnd_1945977 < baseStart_1945977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946007 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 5]
def baseStart_1946007 : Nat := 118140960795 + 1946007 * 2 ^ 59
def prefixEnd_1946007 : Nat := 4983230072969 + 3 ^ 40 * 1946007 * 2
def baseEnd_1946007 : Nat := 222052655114238438302885

theorem tailTrace_1946007 : CollatzResearch.WordTrace tailWord_1946007 prefixEnd_1946007 222052655114238438302885 := by
  unfold tailWord_1946007
  simp only [CollatzResearch.WordTrace]
  refine ⟨70976706260956465380852275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47317804173970976920568183 70976706260956465380852275)
  ·
    refine ⟨106465059391434698071278413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70976706260956465380852275 106465059391434698071278413)
    ·
      refine ⟨39924397271788011776729405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106465059391434698071278413 39924397271788011776729405)
      ·
        refine ⟨14971648976920504416273527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39924397271788011776729405 14971648976920504416273527)
        ·
          refine ⟨22457473465380756624410291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14971648976920504416273527 22457473465380756624410291)
          ·
            refine ⟨33686210198071134936615437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22457473465380756624410291 33686210198071134936615437)
            ·
              refine ⟨12632328824276675601230789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33686210198071134936615437 12632328824276675601230789)
              ·
                refine ⟨2368561654551876675230773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12632328824276675601230789 2368561654551876675230773)
                ·
                  refine ⟨222052655114238438302885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368561654551876675230773 222052655114238438302885)
                  ·
                    rfl

theorem cell22_1946007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 5].length) (baseStart_1946007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946007 prefixEnd_1946007 := by exact prefixLift 1946007
  have htrace : WordTrace (prefixWord ++ tailWord_1946007) baseStart_1946007 baseEnd_1946007 := by
    simpa [prefixWord, tailWord_1946007, baseEnd_1946007] using wordTrace_append hprefix tailTrace_1946007
  have hstable : (prefixWord ++ tailWord_1946007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946007).length < 2 ^ (prefixWord ++ tailWord_1946007).sum := by decide
  have hdescent : baseEnd_1946007 < baseStart_1946007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946069 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 6]
def baseStart_1946069 : Nat := 118140960795 + 1946069 * 2 ^ 59
def prefixEnd_1946069 : Nat := 4983230072969 + 3 ^ 40 * 1946069 * 2
def baseEnd_1946069 : Nat := 222059729736589273286155

theorem tailTrace_1946069 : CollatzResearch.WordTrace tailWord_1946069 prefixEnd_1946069 222059729736589273286155 := by
  unfold tailWord_1946069
  simp only [CollatzResearch.WordTrace]
  refine ⟨70978967586731849969609261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47319311724487899979739507 70978967586731849969609261)
  ·
    refine ⟨26617112845024443738603473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70978967586731849969609261 26617112845024443738603473)
    ·
      refine ⟨19962834633768332803952605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26617112845024443738603473 19962834633768332803952605)
      ·
        refine ⟨7486062987663124801482227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19962834633768332803952605 7486062987663124801482227)
        ·
          refine ⟨11229094481494687202223341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486062987663124801482227 11229094481494687202223341)
          ·
            refine ⟨4210910430560507700833753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11229094481494687202223341 4210910430560507700833753)
            ·
              refine ⟨3158182822920380775625315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4210910430560507700833753 3158182822920380775625315)
              ·
                refine ⟨4737274234380571163437973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158182822920380775625315 4737274234380571163437973)
                ·
                  refine ⟨222059729736589273286155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4737274234380571163437973 222059729736589273286155)
                  ·
                    rfl

theorem cell22_1946069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_1946069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946069 prefixEnd_1946069 := by exact prefixLift 1946069
  have htrace : WordTrace (prefixWord ++ tailWord_1946069) baseStart_1946069 baseEnd_1946069 := by
    simpa [prefixWord, tailWord_1946069, baseEnd_1946069] using wordTrace_append hprefix tailTrace_1946069
  have hstable : (prefixWord ++ tailWord_1946069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946069).length < 2 ^ (prefixWord ++ tailWord_1946069).sum := by decide
  have hdescent : baseEnd_1946069 < baseStart_1946069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946097 : List Nat := [1, 2, 2, 2, 3, 1, 3, 8]
def baseStart_1946097 : Nat := 118140960795 + 1946097 * 2 ^ 59
def prefixEnd_1946097 : Nat := 4983230072969 + 3 ^ 40 * 1946097 * 2
def baseEnd_1946097 : Nat := 74020974909109453350931

theorem tailTrace_1946097 : CollatzResearch.WordTrace tailWord_1946097 prefixEnd_1946097 74020974909109453350931 := by
  unfold tailWord_1946097
  simp only [CollatzResearch.WordTrace]
  refine ⟨70979988830630410751628545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47319992553753607167752363 70979988830630410751628545)
  ·
    refine ⟨53234991622972808063721409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70979988830630410751628545 53234991622972808063721409)
    ·
      refine ⟨39926243717229606047791057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53234991622972808063721409 39926243717229606047791057)
      ·
        refine ⟨29944682787922204535843293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39926243717229606047791057 29944682787922204535843293)
        ·
          refine ⟨11229256045470826700941235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29944682787922204535843293 11229256045470826700941235)
          ·
            refine ⟨16843884068206240051411853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229256045470826700941235 16843884068206240051411853)
            ·
              refine ⟨6316456525577340019279445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16843884068206240051411853 6316456525577340019279445)
              ·
                refine ⟨74020974909109453350931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6316456525577340019279445 74020974909109453350931)
                ·
                  rfl

theorem cell22_1946097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 8].length) (baseStart_1946097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946097 prefixEnd_1946097 := by exact prefixLift 1946097
  have htrace : WordTrace (prefixWord ++ tailWord_1946097) baseStart_1946097 baseEnd_1946097 := by
    simpa [prefixWord, tailWord_1946097, baseEnd_1946097] using wordTrace_append hprefix tailTrace_1946097
  have hstable : (prefixWord ++ tailWord_1946097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946097).length < 2 ^ (prefixWord ++ tailWord_1946097).sum := by decide
  have hdescent : baseEnd_1946097 < baseStart_1946097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946116 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1946116 : Nat := 118140960795 + 1946116 * 2 ^ 59
def prefixEnd_1946116 : Nat := 4983230072969 + 3 ^ 40 * 1946116 * 2
def baseEnd_1946116 : Nat := 666195278270275363933321

theorem tailTrace_1946116 : CollatzResearch.WordTrace tailWord_1946116 prefixEnd_1946116 666195278270275363933321 := by
  unfold tailWord_1946116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490340908780788498285101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47320454545041051331046801 35490340908780788498285101)
  ·
    refine ⟨13308877840792795686856913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35490340908780788498285101 13308877840792795686856913)
    ·
      refine ⟨9981658380594596765142685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13308877840792795686856913 9981658380594596765142685)
      ·
        refine ⟨3743121892722973786928507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9981658380594596765142685 3743121892722973786928507)
        ·
          refine ⟨5614682839084460680392761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743121892722973786928507 5614682839084460680392761)
          ·
            refine ⟨4211012129313345510294571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5614682839084460680392761 4211012129313345510294571)
            ·
              refine ⟨6316518193970018265441857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211012129313345510294571 6316518193970018265441857)
              ·
                refine ⟨4737388645477513699081393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6316518193970018265441857 4737388645477513699081393)
                ·
                  refine ⟨3553041484108135274311045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737388645477513699081393 3553041484108135274311045)
                  ·
                    refine ⟨666195278270275363933321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3553041484108135274311045 666195278270275363933321)
                    ·
                      rfl

theorem cell22_1946116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1946116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946116 prefixEnd_1946116 := by exact prefixLift 1946116
  have htrace : WordTrace (prefixWord ++ tailWord_1946116) baseStart_1946116 baseEnd_1946116 := by
    simpa [prefixWord, tailWord_1946116, baseEnd_1946116] using wordTrace_append hprefix tailTrace_1946116
  have hstable : (prefixWord ++ tailWord_1946116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946116).length < 2 ^ (prefixWord ++ tailWord_1946116).sum := by decide
  have hdescent : baseEnd_1946116 < baseStart_1946116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946129 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_1946129 : Nat := 118140960795 + 1946129 * 2 ^ 59
def prefixEnd_1946129 : Nat := 4983230072969 + 3 ^ 40 * 1946129 * 2
def baseEnd_1946129 : Nat := 666199728435947663358281

theorem tailTrace_1946129 : CollatzResearch.WordTrace tailWord_1946129 prefixEnd_1946129 666199728435947663358281 := by
  unfold tailWord_1946129
  simp only [CollatzResearch.WordTrace]
  refine ⟨70981155966514480216793441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47320770644342986811195627 70981155966514480216793441)
  ·
    refine ⟨53235866974885860162595081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70981155966514480216793441 53235866974885860162595081)
    ·
      refine ⟨39926900231164395121946311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53235866974885860162595081 39926900231164395121946311)
      ·
        refine ⟨59890350346746592682919467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39926900231164395121946311 59890350346746592682919467)
        ·
          refine ⟨89835525520119889024379201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59890350346746592682919467 89835525520119889024379201)
          ·
            refine ⟨67376644140089916768284401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89835525520119889024379201 67376644140089916768284401)
            ·
              refine ⟨50532483105067437576213301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67376644140089916768284401 50532483105067437576213301)
              ·
                refine ⟨4737420291100072272769997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50532483105067437576213301 4737420291100072272769997)
                ·
                  refine ⟨1776532609162527102288749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4737420291100072272769997 1776532609162527102288749)
                  ·
                    refine ⟨666199728435947663358281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776532609162527102288749 666199728435947663358281)
                    ·
                      rfl

theorem cell22_1946129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_1946129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946129 prefixEnd_1946129 := by exact prefixLift 1946129
  have htrace : WordTrace (prefixWord ++ tailWord_1946129) baseStart_1946129 baseEnd_1946129 := by
    simpa [prefixWord, tailWord_1946129, baseEnd_1946129] using wordTrace_append hprefix tailTrace_1946129
  have hstable : (prefixWord ++ tailWord_1946129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946129).length < 2 ^ (prefixWord ++ tailWord_1946129).sum := by decide
  have hdescent : baseEnd_1946129 < baseStart_1946129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946264 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_1946264 : Nat := 118140960795 + 1946264 * 2 ^ 59
def prefixEnd_1946264 : Nat := 4983230072969 + 3 ^ 40 * 1946264 * 2
def baseEnd_1946264 : Nat := 666245941694852311232867

theorem tailTrace_1946264 : CollatzResearch.WordTrace tailWord_1946264 prefixEnd_1946264 666245941694852311232867 := by
  unfold tailWord_1946264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35493039910512699136478923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47324053214016932181971897 35493039910512699136478923)
  ·
    refine ⟨53239559865769048704718385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35493039910512699136478923 53239559865769048704718385)
    ·
      refine ⟨39929669899326786528538789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53239559865769048704718385 39929669899326786528538789)
      ·
        refine ⟨7486813106123772474101023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39929669899326786528538789 7486813106123772474101023)
        ·
          refine ⟨11230219659185658711151535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486813106123772474101023 11230219659185658711151535)
          ·
            refine ⟨16845329488778488066727303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11230219659185658711151535 16845329488778488066727303)
            ·
              refine ⟨25267994233167732100090955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16845329488778488066727303 25267994233167732100090955)
              ·
                refine ⟨37901991349751598150136433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25267994233167732100090955 37901991349751598150136433)
                ·
                  refine ⟨28426493512313698612602325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37901991349751598150136433 28426493512313698612602325)
                  ·
                    refine ⟨666245941694852311232867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28426493512313698612602325 666245941694852311232867)
                    ·
                      rfl

theorem cell22_1946264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_1946264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946264 prefixEnd_1946264 := by exact prefixLift 1946264
  have htrace : WordTrace (prefixWord ++ tailWord_1946264) baseStart_1946264 baseEnd_1946264 := by
    simpa [prefixWord, tailWord_1946264, baseEnd_1946264] using wordTrace_append hprefix tailTrace_1946264
  have hstable : (prefixWord ++ tailWord_1946264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946264).length < 2 ^ (prefixWord ++ tailWord_1946264).sum := by decide
  have hdescent : baseEnd_1946264 < baseStart_1946264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946371 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 6, 3]
def baseStart_1946371 : Nat := 118140960795 + 1946371 * 2 ^ 59
def prefixEnd_1946371 : Nat := 4983230072969 + 3 ^ 40 * 1946371 * 2
def baseEnd_1946371 : Nat := 666282569981539698807539

theorem tailTrace_1946371 : CollatzResearch.WordTrace tailWord_1946371 prefixEnd_1946371 666282569981539698807539 := by
  unfold tailWord_1946371
  simp only [CollatzResearch.WordTrace]
  refine ⟨70989982431637755547102967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47326654954425170364735311 70989982431637755547102967)
  ·
    refine ⟨106484973647456633320654451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70989982431637755547102967 106484973647456633320654451)
    ·
      refine ⟨159727460471184949980981677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106484973647456633320654451 159727460471184949980981677)
      ·
        refine ⟨59897797676694356242868129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159727460471184949980981677 59897797676694356242868129)
        ·
          refine ⟨44923348257520767182151097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59897797676694356242868129 44923348257520767182151097)
          ·
            refine ⟨33692511193140575386613323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44923348257520767182151097 33692511193140575386613323)
            ·
              refine ⟨50538766789710863079919985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33692511193140575386613323 50538766789710863079919985)
              ·
                refine ⟨37904075092283147309939989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50538766789710863079919985 37904075092283147309939989)
                ·
                  refine ⟨1776753519950772530153437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37904075092283147309939989 1776753519950772530153437)
                  ·
                    refine ⟨666282569981539698807539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776753519950772530153437 666282569981539698807539)
                    ·
                      rfl

theorem cell22_1946371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 3].length) (baseStart_1946371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946371 prefixEnd_1946371 := by exact prefixLift 1946371
  have htrace : WordTrace (prefixWord ++ tailWord_1946371) baseStart_1946371 baseEnd_1946371 := by
    simpa [prefixWord, tailWord_1946371, baseEnd_1946371] using wordTrace_append hprefix tailTrace_1946371
  have hstable : (prefixWord ++ tailWord_1946371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946371).length < 2 ^ (prefixWord ++ tailWord_1946371).sum := by decide
  have hdescent : baseEnd_1946371 < baseStart_1946371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946422 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1946422 : Nat := 118140960795 + 1946422 * 2 ^ 59
def prefixEnd_1946422 : Nat := 4983230072969 + 3 ^ 40 * 1946422 * 2
def baseEnd_1946422 : Nat := 666300028323792565782383

theorem tailTrace_1946422 : CollatzResearch.WordTrace tailWord_1946422 prefixEnd_1946422 666300028323792565782383 := by
  unfold tailWord_1946422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436990159653311953575595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47327895036301994171473013 4436990159653311953575595)
  ·
    refine ⟨6655485239479967930363393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4436990159653311953575595 6655485239479967930363393)
    ·
      refine ⟨4991613929609975947772545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6655485239479967930363393 4991613929609975947772545)
      ·
        refine ⟨3743710447207481960829409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4991613929609975947772545 3743710447207481960829409)
        ·
          refine ⟨2807782835405611470622057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3743710447207481960829409 2807782835405611470622057)
          ·
            refine ⟨2105837126554208602966543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2807782835405611470622057 2105837126554208602966543)
            ·
              refine ⟨3158755689831312904449815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105837126554208602966543 3158755689831312904449815)
              ·
                refine ⟨4738133534746969356674723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158755689831312904449815 4738133534746969356674723)
                ·
                  refine ⟨7107200302120454035012085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738133534746969356674723 7107200302120454035012085)
                  ·
                    refine ⟨666300028323792565782383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7107200302120454035012085 666300028323792565782383)
                    ·
                      rfl

theorem cell22_1946422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1946422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946422 prefixEnd_1946422 := by exact prefixLift 1946422
  have htrace : WordTrace (prefixWord ++ tailWord_1946422) baseStart_1946422 baseEnd_1946422 := by
    simpa [prefixWord, tailWord_1946422, baseEnd_1946422] using wordTrace_append hprefix tailTrace_1946422
  have hstable : (prefixWord ++ tailWord_1946422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946422).length < 2 ^ (prefixWord ++ tailWord_1946422).sum := by decide
  have hdescent : baseEnd_1946422 < baseStart_1946422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946491 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 6]
def baseStart_1946491 : Nat := 118140960795 + 1946491 * 2 ^ 59
def prefixEnd_1946491 : Nat := 4983230072969 + 3 ^ 40 * 1946491 * 2
def baseEnd_1946491 : Nat := 222107882811299795269057

theorem tailTrace_1946491 : CollatzResearch.WordTrace tailWord_1946491 prefixEnd_1946491 222107882811299795269057 := by
  unfold tailWord_1946491
  simp only [CollatzResearch.WordTrace]
  refine ⟨70994359191203016041471327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47329572794135344027647551 70994359191203016041471327)
  ·
    refine ⟨106491538786804524062206991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70994359191203016041471327 106491538786804524062206991)
    ·
      refine ⟨159737308180206786093310487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106491538786804524062206991 159737308180206786093310487)
      ·
        refine ⟨239605962270310179139965731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159737308180206786093310487 239605962270310179139965731)
        ·
          refine ⟨359408943405465268709948597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239605962270310179139965731 359408943405465268709948597)
          ·
            refine ⟨33694588444262368941557681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359408943405465268709948597 33694588444262368941557681)
            ·
              refine ⟨25270941333196776706168261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33694588444262368941557681 25270941333196776706168261)
              ·
                refine ⟨4738301499974395632406549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25270941333196776706168261 4738301499974395632406549)
                ·
                  refine ⟨222107882811299795269057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4738301499974395632406549 222107882811299795269057)
                  ·
                    rfl

theorem cell22_1946491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_1946491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946491 prefixEnd_1946491 := by exact prefixLift 1946491
  have htrace : WordTrace (prefixWord ++ tailWord_1946491) baseStart_1946491 baseEnd_1946491 := by
    simpa [prefixWord, tailWord_1946491, baseEnd_1946491] using wordTrace_append hprefix tailTrace_1946491
  have hstable : (prefixWord ++ tailWord_1946491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946491).length < 2 ^ (prefixWord ++ tailWord_1946491).sum := by decide
  have hdescent : baseEnd_1946491 < baseStart_1946491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946518 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1946518 : Nat := 118140960795 + 1946518 * 2 ^ 59
def prefixEnd_1946518 : Nat := 4983230072969 + 3 ^ 40 * 1946518 * 2
def baseEnd_1946518 : Nat := 666332891085680315382089

theorem tailTrace_1946518 : CollatzResearch.WordTrace tailWord_1946518 prefixEnd_1946518 666332891085680315382089 := by
  unfold tailWord_1946518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437208997631574978294013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47330229308070133101802805 4437208997631574978294013)
  ·
    refine ⟨1663953374111840616860255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4437208997631574978294013 1663953374111840616860255)
    ·
      refine ⟨2495930061167760925290383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663953374111840616860255 2495930061167760925290383)
      ·
        refine ⟨3743895091751641387935575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495930061167760925290383 3743895091751641387935575)
        ·
          refine ⟨5615842637627462081903363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743895091751641387935575 5615842637627462081903363)
          ·
            refine ⟨8423763956441193122855045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615842637627462081903363 8423763956441193122855045)
            ·
              refine ⟨1579455741832723710535321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8423763956441193122855045 1579455741832723710535321)
              ·
                refine ⟨1184591806374542782901491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579455741832723710535321 1184591806374542782901491)
                ·
                  refine ⟨1776887709561814174352237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184591806374542782901491 1776887709561814174352237)
                  ·
                    refine ⟨666332891085680315382089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776887709561814174352237 666332891085680315382089)
                    ·
                      rfl

theorem cell22_1946518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1946518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946518 prefixEnd_1946518 := by exact prefixLift 1946518
  have htrace : WordTrace (prefixWord ++ tailWord_1946518) baseStart_1946518 baseEnd_1946518 := by
    simpa [prefixWord, tailWord_1946518, baseEnd_1946518] using wordTrace_append hprefix tailTrace_1946518
  have hstable : (prefixWord ++ tailWord_1946518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946518).length < 2 ^ (prefixWord ++ tailWord_1946518).sum := by decide
  have hdescent : baseEnd_1946518 < baseStart_1946518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946521 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_1946521 : Nat := 118140960795 + 1946521 * 2 ^ 59
def prefixEnd_1946521 : Nat := 4983230072969 + 3 ^ 40 * 1946521 * 2
def baseEnd_1946521 : Nat := 666333918046989307557079

theorem tailTrace_1946521 : CollatzResearch.WordTrace tailWord_1946521 prefixEnd_1946521 666333918046989307557079 := by
  unfold tailWord_1946521
  simp only [CollatzResearch.WordTrace]
  refine ⟨70995453381094331165063417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47330302254062887443375611 70995453381094331165063417)
  ·
    refine ⟨53246590035820748373797563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70995453381094331165063417 53246590035820748373797563)
    ·
      refine ⟨79869885053731122560696345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53246590035820748373797563 79869885053731122560696345)
      ·
        refine ⟨59902413790298341920522259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79869885053731122560696345 59902413790298341920522259)
        ·
          refine ⟨89853620685447512880783389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59902413790298341920522259 89853620685447512880783389)
          ·
            refine ⟨33695107757042817330293771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89853620685447512880783389 33695107757042817330293771)
            ·
              refine ⟨50542661635564225995440657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33695107757042817330293771 50542661635564225995440657)
              ·
                refine ⟨37906996226673169496580493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50542661635564225995440657 37906996226673169496580493)
                ·
                  refine ⟨14215123585002438561217685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37906996226673169496580493 14215123585002438561217685)
                  ·
                    refine ⟨666333918046989307557079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14215123585002438561217685 666333918046989307557079)
                    ·
                      rfl

theorem cell22_1946521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_1946521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946521 prefixEnd_1946521 := by exact prefixLift 1946521
  have htrace : WordTrace (prefixWord ++ tailWord_1946521) baseStart_1946521 baseEnd_1946521 := by
    simpa [prefixWord, tailWord_1946521, baseEnd_1946521] using wordTrace_append hprefix tailTrace_1946521
  have hstable : (prefixWord ++ tailWord_1946521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946521).length < 2 ^ (prefixWord ++ tailWord_1946521).sum := by decide
  have hdescent : baseEnd_1946521 < baseStart_1946521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946525 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 4]
def baseStart_1946525 : Nat := 118140960795 + 1946525 * 2 ^ 59
def prefixEnd_1946525 : Nat := 4983230072969 + 3 ^ 40 * 1946525 * 2
def baseEnd_1946525 : Nat := 222111762442911543485689

theorem tailTrace_1946525 : CollatzResearch.WordTrace tailWord_1946525 prefixEnd_1946525 222111762442911543485689 := by
  unfold tailWord_1946525
  simp only [CollatzResearch.WordTrace]
  refine ⟨70995599273079839848209029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47330399515386559898806019 70995599273079839848209029)
  ·
    refine ⟨13311674863702469971539193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70995599273079839848209029 13311674863702469971539193)
    ·
      refine ⟨9983756147776852478654395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13311674863702469971539193 9983756147776852478654395)
      ·
        refine ⟨14975634221665278717981593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983756147776852478654395 14975634221665278717981593)
        ·
          refine ⟨11231725666248959038486195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14975634221665278717981593 11231725666248959038486195)
          ·
            refine ⟨16847588499373438557729293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231725666248959038486195 16847588499373438557729293)
            ·
              refine ⟨6317845687265039459148485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16847588499373438557729293 6317845687265039459148485)
              ·
                refine ⟨1184596066362194898590341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6317845687265039459148485 1184596066362194898590341)
                ·
                  refine ⟨222111762442911543485689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184596066362194898590341 222111762442911543485689)
                  ·
                    rfl

theorem cell22_1946525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_1946525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946525 prefixEnd_1946525 := by exact prefixLift 1946525
  have htrace : WordTrace (prefixWord ++ tailWord_1946525) baseStart_1946525 baseEnd_1946525 := by
    simpa [prefixWord, tailWord_1946525, baseEnd_1946525] using wordTrace_append hprefix tailTrace_1946525
  have hstable : (prefixWord ++ tailWord_1946525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946525).length < 2 ^ (prefixWord ++ tailWord_1946525).sum := by decide
  have hdescent : baseEnd_1946525 < baseStart_1946525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946585 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_1946585 : Nat := 118140960795 + 1946585 * 2 ^ 59
def prefixEnd_1946585 : Nat := 4983230072969 + 3 ^ 40 * 1946585 * 2
def baseEnd_1946585 : Nat := 666355826554914473956883

theorem tailTrace_1946585 : CollatzResearch.WordTrace tailWord_1946585 prefixEnd_1946585 666355826554914473956883 := by
  unfold tailWord_1946585
  simp only [CollatzResearch.WordTrace]
  refine ⟨70997787652862470095393209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47331858435241646730262139 70997787652862470095393209)
  ·
    refine ⟨53248340739646852571544907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70997787652862470095393209 53248340739646852571544907)
    ·
      refine ⟨79872511109470278857317361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53248340739646852571544907 79872511109470278857317361)
      ·
        refine ⟨59904383332102709142988021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79872511109470278857317361 59904383332102709142988021)
        ·
          refine ⟨5616035937384628982155127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59904383332102709142988021 5616035937384628982155127)
          ·
            refine ⟨8424053906076943473232691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616035937384628982155127 8424053906076943473232691)
            ·
              refine ⟨12636080859115415209849037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424053906076943473232691 12636080859115415209849037)
              ·
                refine ⟨4738530322168280703693389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12636080859115415209849037 4738530322168280703693389)
                ·
                  refine ⟨1776948870813105263885021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4738530322168280703693389 1776948870813105263885021)
                  ·
                    refine ⟨666355826554914473956883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776948870813105263885021 666355826554914473956883)
                    ·
                      rfl

theorem cell22_1946585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_1946585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946585 prefixEnd_1946585 := by exact prefixLift 1946585
  have htrace : WordTrace (prefixWord ++ tailWord_1946585) baseStart_1946585 baseEnd_1946585 := by
    simpa [prefixWord, tailWord_1946585, baseEnd_1946585] using wordTrace_append hprefix tailTrace_1946585
  have hstable : (prefixWord ++ tailWord_1946585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946585).length < 2 ^ (prefixWord ++ tailWord_1946585).sum := by decide
  have hdescent : baseEnd_1946585 < baseStart_1946585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946812 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_1946812 : Nat := 118140960795 + 1946812 * 2 ^ 59
def prefixEnd_1946812 : Nat := 4983230072969 + 3 ^ 40 * 1946812 * 2
def baseEnd_1946812 : Nat := 222144511097987182843729

theorem tailTrace_1946812 : CollatzResearch.WordTrace tailWord_1946812 prefixEnd_1946812 222144511097987182843729 := by
  unfold tailWord_1946812
  simp only [CollatzResearch.WordTrace]
  refine ⟨35503033511520043931953345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47337378015360058575937793 35503033511520043931953345)
  ·
    refine ⟨26627275133640032948965009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35503033511520043931953345 26627275133640032948965009)
    ·
      refine ⟨19970456350230024711723757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26627275133640032948965009 19970456350230024711723757)
      ·
        refine ⟨7488921131336259266896409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19970456350230024711723757 7488921131336259266896409)
        ·
          refine ⟨5616690848502194450172307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7488921131336259266896409 5616690848502194450172307)
          ·
            refine ⟨8425036272753291675258461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616690848502194450172307 8425036272753291675258461)
            ·
              refine ⟨3159388602282484378221923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8425036272753291675258461 3159388602282484378221923)
              ·
                refine ⟨4739082903423726567332885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159388602282484378221923 4739082903423726567332885)
                ·
                  refine ⟨222144511097987182843729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4739082903423726567332885 222144511097987182843729)
                  ·
                    rfl

theorem cell22_1946812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_1946812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946812 prefixEnd_1946812 := by exact prefixLift 1946812
  have htrace : WordTrace (prefixWord ++ tailWord_1946812) baseStart_1946812 baseEnd_1946812 := by
    simpa [prefixWord, tailWord_1946812, baseEnd_1946812] using wordTrace_append hprefix tailTrace_1946812
  have hstable : (prefixWord ++ tailWord_1946812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946812).length < 2 ^ (prefixWord ++ tailWord_1946812).sum := by decide
  have hdescent : baseEnd_1946812 < baseStart_1946812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946861 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1946861 : Nat := 118140960795 + 1946861 * 2 ^ 59
def prefixEnd_1946861 : Nat := 4983230072969 + 3 ^ 40 * 1946861 * 2
def baseEnd_1946861 : Nat := 666450306995341754056037

theorem tailTrace_1946861 : CollatzResearch.WordTrace tailWord_1946861 prefixEnd_1946861 666450306995341754056037 := by
  unfold tailWord_1946861
  simp only [CollatzResearch.WordTrace]
  refine ⟨71007854199862569232440437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47338569466575046154960291 71007854199862569232440437)
  ·
    refine ⟨6656986331237115865541291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71007854199862569232440437 6656986331237115865541291)
    ·
      refine ⟨9985479496855673798311937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656986331237115865541291 9985479496855673798311937)
      ·
        refine ⟨7489109622641755348733953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9985479496855673798311937 7489109622641755348733953)
        ·
          refine ⟨5616832216981316511550465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7489109622641755348733953 5616832216981316511550465)
          ·
            refine ⟨4212624162735987383662849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5616832216981316511550465 4212624162735987383662849)
            ·
              refine ⟨3159468122051990537747137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4212624162735987383662849 3159468122051990537747137)
              ·
                refine ⟨2369601091538992903310353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159468122051990537747137 2369601091538992903310353)
                ·
                  refine ⟨1777200818654244677482765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369601091538992903310353 1777200818654244677482765)
                  ·
                    refine ⟨666450306995341754056037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777200818654244677482765 666450306995341754056037)
                    ·
                      rfl

theorem cell22_1946861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1946861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946861 prefixEnd_1946861 := by exact prefixLift 1946861
  have htrace : WordTrace (prefixWord ++ tailWord_1946861) baseStart_1946861 baseEnd_1946861 := by
    simpa [prefixWord, tailWord_1946861, baseEnd_1946861] using wordTrace_append hprefix tailTrace_1946861
  have hstable : (prefixWord ++ tailWord_1946861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946861).length < 2 ^ (prefixWord ++ tailWord_1946861).sum := by decide
  have hdescent : baseEnd_1946861 < baseStart_1946861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946863 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 4]
def baseStart_1946863 : Nat := 118140960795 + 1946863 * 2 ^ 59
def prefixEnd_1946863 : Nat := 4983230072969 + 3 ^ 40 * 1946863 * 2
def baseEnd_1946863 : Nat := 222150330545404805168677

theorem tailTrace_1946863 : CollatzResearch.WordTrace tailWord_1946863 prefixEnd_1946863 222150330545404805168677 := by
  unfold tailWord_1946863
  simp only [CollatzResearch.WordTrace]
  refine ⟨71007927145855323574013243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47338618097236882382675495 71007927145855323574013243)
  ·
    refine ⟨106511890718782985361019865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71007927145855323574013243 106511890718782985361019865)
    ·
      refine ⟨79883918039087239020764899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106511890718782985361019865 79883918039087239020764899)
      ·
        refine ⟨119825877058630858531147349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79883918039087239020764899 119825877058630858531147349)
        ·
          refine ⟨1404209496780830373411883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 119825877058630858531147349 1404209496780830373411883)
          ·
            refine ⟨2106314245171245560117825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404209496780830373411883 2106314245171245560117825)
            ·
              refine ⟨1579735683878434170088369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106314245171245560117825 1579735683878434170088369)
              ·
                refine ⟨1184801762908825627566277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579735683878434170088369 1184801762908825627566277)
                ·
                  refine ⟨222150330545404805168677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184801762908825627566277 222150330545404805168677)
                  ·
                    rfl

theorem cell22_1946863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 4].length) (baseStart_1946863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946863 prefixEnd_1946863 := by exact prefixLift 1946863
  have htrace : WordTrace (prefixWord ++ tailWord_1946863) baseStart_1946863 baseEnd_1946863 := by
    simpa [prefixWord, tailWord_1946863, baseEnd_1946863] using wordTrace_append hprefix tailTrace_1946863
  have hstable : (prefixWord ++ tailWord_1946863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946863).length < 2 ^ (prefixWord ++ tailWord_1946863).sum := by decide
  have hdescent : baseEnd_1946863 < baseStart_1946863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946906 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_1946906 : Nat := 118140960795 + 1946906 * 2 ^ 59
def prefixEnd_1946906 : Nat := 4983230072969 + 3 ^ 40 * 1946906 * 2
def baseEnd_1946906 : Nat := 666465711414976636680899

theorem tailTrace_1946906 : CollatzResearch.WordTrace tailWord_1946906 prefixEnd_1946906 666465711414976636680899 := by
  unfold tailWord_1946906
  simp only [CollatzResearch.WordTrace]
  refine ⟨17752373871174885479457143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47339663656466361278552381 17752373871174885479457143)
  ·
    refine ⟨26628560806762328219185715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17752373871174885479457143 26628560806762328219185715)
    ·
      refine ⟨39942841210143492328778573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26628560806762328219185715 39942841210143492328778573)
      ·
        refine ⟨14978565453803809623291965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39942841210143492328778573 14978565453803809623291965)
        ·
          refine ⟨5616962045176428608734487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14978565453803809623291965 5616962045176428608734487)
          ·
            refine ⟨8425443067764642913101731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616962045176428608734487 8425443067764642913101731)
            ·
              refine ⟨12638164601646964369652597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425443067764642913101731 12638164601646964369652597)
              ·
                refine ⟨1184827931404402909654931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12638164601646964369652597 1184827931404402909654931)
                ·
                  refine ⟨1777241897106604364482397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184827931404402909654931 1777241897106604364482397)
                  ·
                    refine ⟨666465711414976636680899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777241897106604364482397 666465711414976636680899)
                    ·
                      rfl

theorem cell22_1946906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_1946906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946906 prefixEnd_1946906 := by exact prefixLift 1946906
  have htrace : WordTrace (prefixWord ++ tailWord_1946906) baseStart_1946906 baseEnd_1946906 := by
    simpa [prefixWord, tailWord_1946906, baseEnd_1946906] using wordTrace_append hprefix tailTrace_1946906
  have hstable : (prefixWord ++ tailWord_1946906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946906).length < 2 ^ (prefixWord ++ tailWord_1946906).sum := by decide
  have hdescent : baseEnd_1946906 < baseStart_1946906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946917 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1946917 : Nat := 118140960795 + 1946917 * 2 ^ 59
def prefixEnd_1946917 : Nat := 4983230072969 + 3 ^ 40 * 1946917 * 2
def baseEnd_1946917 : Nat := 666469476939776274655865

theorem tailTrace_1946917 : CollatzResearch.WordTrace tailWord_1946917 prefixEnd_1946917 666469476939776274655865 := by
  unfold tailWord_1946917
  simp only [CollatzResearch.WordTrace]
  refine ⟨71009896687659690796479005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47339931125106460530986003 71009896687659690796479005)
  ·
    refine ⟨26628711257872384048679627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71009896687659690796479005 26628711257872384048679627)
    ·
      refine ⟨39943066886808576073019441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26628711257872384048679627 39943066886808576073019441)
      ·
        refine ⟨29957300165106432054764581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39943066886808576073019441 29957300165106432054764581)
        ·
          refine ⟨5616993780957456010268359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29957300165106432054764581 5616993780957456010268359)
          ·
            refine ⟨8425490671436184015402539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616993780957456010268359 8425490671436184015402539)
            ·
              refine ⟨12638236007154276023103809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425490671436184015402539 12638236007154276023103809)
              ·
                refine ⟨9478677005365707017327857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12638236007154276023103809 9478677005365707017327857)
                ·
                  refine ⟨7109007754024280262995893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9478677005365707017327857 7109007754024280262995893)
                  ·
                    refine ⟨666469476939776274655865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7109007754024280262995893 666469476939776274655865)
                    ·
                      rfl

theorem cell22_1946917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1946917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946917 prefixEnd_1946917 := by exact prefixLift 1946917
  have htrace : WordTrace (prefixWord ++ tailWord_1946917) baseStart_1946917 baseEnd_1946917 := by
    simpa [prefixWord, tailWord_1946917, baseEnd_1946917] using wordTrace_append hprefix tailTrace_1946917
  have hstable : (prefixWord ++ tailWord_1946917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946917).length < 2 ^ (prefixWord ++ tailWord_1946917).sum := by decide
  have hdescent : baseEnd_1946917 < baseStart_1946917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946957 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1946957 : Nat := 118140960795 + 1946957 * 2 ^ 59
def prefixEnd_1946957 : Nat := 4983230072969 + 3 ^ 40 * 1946957 * 2
def baseEnd_1946957 : Nat := 666483169757229503655743

theorem tailTrace_1946957 : CollatzResearch.WordTrace tailWord_1946957 prefixEnd_1946957 666483169757229503655743 := by
  unfold tailWord_1946957
  simp only [CollatzResearch.WordTrace]
  refine ⟨71011355607514777627935125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47340903738343185085290083 71011355607514777627935125)
  ·
    refine ⟨3328657294102255201309459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71011355607514777627935125 3328657294102255201309459)
    ·
      refine ⟨4992985941153382801964189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3328657294102255201309459 4992985941153382801964189)
      ·
        refine ⟨1872369727932518550736571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4992985941153382801964189 1872369727932518550736571)
        ·
          refine ⟨2808554591898777826104857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872369727932518550736571 2808554591898777826104857)
          ·
            refine ⟨2106415943924083369578643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2808554591898777826104857 2106415943924083369578643)
            ·
              refine ⟨3159623915886125054367965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106415943924083369578643 3159623915886125054367965)
              ·
                refine ⟨1184858968457296895387987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159623915886125054367965 1184858968457296895387987)
                ·
                  refine ⟨1777288452685945343081981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184858968457296895387987 1777288452685945343081981)
                  ·
                    refine ⟨666483169757229503655743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777288452685945343081981 666483169757229503655743)
                    ·
                      rfl

theorem cell22_1946957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1946957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946957 prefixEnd_1946957 := by exact prefixLift 1946957
  have htrace : WordTrace (prefixWord ++ tailWord_1946957) baseStart_1946957 baseEnd_1946957 := by
    simpa [prefixWord, tailWord_1946957, baseEnd_1946957] using wordTrace_append hprefix tailTrace_1946957
  have hstable : (prefixWord ++ tailWord_1946957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946957).length < 2 ^ (prefixWord ++ tailWord_1946957).sum := by decide
  have hdescent : baseEnd_1946957 < baseStart_1946957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946962 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1946962 : Nat := 118140960795 + 1946962 * 2 ^ 59
def prefixEnd_1946962 : Nat := 4983230072969 + 3 ^ 40 * 1946962 * 2
def baseEnd_1946962 : Nat := 666484881359411157280727

theorem tailTrace_1946962 : CollatzResearch.WordTrace tailWord_1946962 prefixEnd_1946962 666484881359411157280727 := by
  unfold tailWord_1946962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17752884493124165870466785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47341025314997775654578093 17752884493124165870466785)
  ·
    refine ⟨13314663369843124402850089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17752884493124165870466785 13314663369843124402850089)
    ·
      refine ⟨9985997527382343302137567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13314663369843124402850089 9985997527382343302137567)
      ·
        refine ⟨14978996291073514953206351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9985997527382343302137567 14978996291073514953206351)
        ·
          refine ⟨22468494436610272429809527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14978996291073514953206351 22468494436610272429809527)
          ·
            refine ⟨33702741654915408644714291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22468494436610272429809527 33702741654915408644714291)
            ·
              refine ⟨50554112482373112967071437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33702741654915408644714291 50554112482373112967071437)
              ·
                refine ⟨18957792180889917362651789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50554112482373112967071437 18957792180889917362651789)
                ·
                  refine ⟨7109172067833719010994421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18957792180889917362651789 7109172067833719010994421)
                  ·
                    refine ⟨666484881359411157280727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7109172067833719010994421 666484881359411157280727)
                    ·
                      rfl

theorem cell22_1946962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1946962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946962 prefixEnd_1946962 := by exact prefixLift 1946962
  have htrace : WordTrace (prefixWord ++ tailWord_1946962) baseStart_1946962 baseEnd_1946962 := by
    simpa [prefixWord, tailWord_1946962, baseEnd_1946962] using wordTrace_append hprefix tailTrace_1946962
  have hstable : (prefixWord ++ tailWord_1946962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946962).length < 2 ^ (prefixWord ++ tailWord_1946962).sum := by decide
  have hdescent : baseEnd_1946962 < baseStart_1946962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946979 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 4, 3]
def baseStart_1946979 : Nat := 118140960795 + 1946979 * 2 ^ 59
def prefixEnd_1946979 : Nat := 4983230072969 + 3 ^ 40 * 1946979 * 2
def baseEnd_1946979 : Nat := 666490700806828779605675

theorem tailTrace_1946979 : CollatzResearch.WordTrace tailWord_1946979 prefixEnd_1946979 666490700806828779605675 := by
  unfold tailWord_1946979
  simp only [CollatzResearch.WordTrace]
  refine ⟨71012158013435075385235991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47341438675623383590157327 71012158013435075385235991)
  ·
    refine ⟨106518237020152613077853987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71012158013435075385235991 106518237020152613077853987)
    ·
      refine ⟨159777355530228919616780981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106518237020152613077853987 159777355530228919616780981)
      ·
        refine ⟨14979127080958961214073217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159777355530228919616780981 14979127080958961214073217)
        ·
          refine ⟨11234345310719220910554913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14979127080958961214073217 11234345310719220910554913)
          ·
            refine ⟨8425758983039415682916185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11234345310719220910554913 8425758983039415682916185)
            ·
              refine ⟨6319319237279561762187139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425758983039415682916185 6319319237279561762187139)
              ·
                refine ⟨9478978855919342643280709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319319237279561762187139 9478978855919342643280709)
                ·
                  refine ⟨1777308535484876745615133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9478978855919342643280709 1777308535484876745615133)
                  ·
                    refine ⟨666490700806828779605675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777308535484876745615133 666490700806828779605675)
                    ·
                      rfl

theorem cell22_1946979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 3].length) (baseStart_1946979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946979 prefixEnd_1946979 := by exact prefixLift 1946979
  have htrace : WordTrace (prefixWord ++ tailWord_1946979) baseStart_1946979 baseEnd_1946979 := by
    simpa [prefixWord, tailWord_1946979, baseEnd_1946979] using wordTrace_append hprefix tailTrace_1946979
  have hstable : (prefixWord ++ tailWord_1946979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946979).length < 2 ^ (prefixWord ++ tailWord_1946979).sum := by decide
  have hdescent : baseEnd_1946979 < baseStart_1946979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946981 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 4]
def baseStart_1946981 : Nat := 118140960795 + 1946981 * 2 ^ 59
def prefixEnd_1946981 : Nat := 4983230072969 + 3 ^ 40 * 1946981 * 2
def baseEnd_1946981 : Nat := 222163795149233813685223

theorem tailTrace_1946981 : CollatzResearch.WordTrace tailWord_1946981 prefixEnd_1946981 222163795149233813685223 := by
  unfold tailWord_1946981
  simp only [CollatzResearch.WordTrace]
  refine ⟨71012230959427829726808797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47341487306285219817872531 71012230959427829726808797)
  ·
    refine ⟨26629586609785436147553299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71012230959427829726808797 26629586609785436147553299)
    ·
      refine ⟨39944379914678154221329949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26629586609785436147553299 39944379914678154221329949)
      ·
        refine ⟨14979142468004307832998731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39944379914678154221329949 14979142468004307832998731)
        ·
          refine ⟨22468713702006461749498097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14979142468004307832998731 22468713702006461749498097)
          ·
            refine ⟨16851535276504846312123573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22468713702006461749498097 16851535276504846312123573)
            ·
              refine ⟨1579831432172329341761585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16851535276504846312123573 1579831432172329341761585)
              ·
                refine ⟨1184873574129247006321189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579831432172329341761585 1184873574129247006321189)
                ·
                  refine ⟨222163795149233813685223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184873574129247006321189 222163795149233813685223)
                  ·
                    rfl

theorem cell22_1946981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_1946981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946981 prefixEnd_1946981 := by exact prefixLift 1946981
  have htrace : WordTrace (prefixWord ++ tailWord_1946981) baseStart_1946981 baseEnd_1946981 := by
    simpa [prefixWord, tailWord_1946981, baseEnd_1946981] using wordTrace_append hprefix tailTrace_1946981
  have hstable : (prefixWord ++ tailWord_1946981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946981).length < 2 ^ (prefixWord ++ tailWord_1946981).sum := by decide
  have hdescent : baseEnd_1946981 < baseStart_1946981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946992 : List Nat := [2, 1, 1, 1, 4, 2, 4, 7]
def baseStart_1946992 : Nat := 118140960795 + 1946992 * 2 ^ 59
def prefixEnd_1946992 : Nat := 4983230072969 + 3 ^ 40 * 1946992 * 2
def baseEnd_1946992 : Nat := 74055016774722342114515

theorem tailTrace_1946992 : CollatzResearch.WordTrace tailWord_1946992 prefixEnd_1946992 74055016774722342114515 := by
  unfold tailWord_1946992
  simp only [CollatzResearch.WordTrace]
  refine ⟨35506316081193989302729615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47341754774925319070306153 35506316081193989302729615)
  ·
    refine ⟨53259474121790983954094423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35506316081193989302729615 53259474121790983954094423)
    ·
      refine ⟨79889211182686475931141635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53259474121790983954094423 79889211182686475931141635)
      ·
        refine ⟨119833816774029713896712453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79889211182686475931141635 119833816774029713896712453)
        ·
          refine ⟨22468840645130571355633585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119833816774029713896712453 22468840645130571355633585)
          ·
            refine ⟨16851630483847928516725189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22468840645130571355633585 16851630483847928516725189)
            ·
              refine ⟨3159680715721486596885973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16851630483847928516725189 3159680715721486596885973)
              ·
                refine ⟨74055016774722342114515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3159680715721486596885973 74055016774722342114515)
                ·
                  rfl

theorem cell22_1946992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_1946992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1946992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1946992 prefixEnd_1946992 := by exact prefixLift 1946992
  have htrace : WordTrace (prefixWord ++ tailWord_1946992) baseStart_1946992 baseEnd_1946992 := by
    simpa [prefixWord, tailWord_1946992, baseEnd_1946992] using wordTrace_append hprefix tailTrace_1946992
  have hstable : (prefixWord ++ tailWord_1946992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946992).length < 2 ^ (prefixWord ++ tailWord_1946992).sum := by decide
  have hdescent : baseEnd_1946992 < baseStart_1946992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947026 : List Nat := [3, 2, 3, 3, 2, 9]
def baseStart_1947026 : Nat := 118140960795 + 1947026 * 2 ^ 59
def prefixEnd_1947026 : Nat := 4983230072969 + 3 ^ 40 * 1947026 * 2
def baseEnd_1947026 : Nat := 8228478887251065724451

theorem tailTrace_1947026 : CollatzResearch.WordTrace tailWord_1947026 prefixEnd_1947026 8228478887251065724451 := by
  unfold tailWord_1947026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17753468061066200603049233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47342581496176534941464621 17753468061066200603049233)
  ·
    refine ⟨13315101045799650452286925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17753468061066200603049233 13315101045799650452286925)
    ·
      refine ⟨4993162892174868919607597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13315101045799650452286925 4993162892174868919607597)
      ·
        refine ⟨1872436084565575844852849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4993162892174868919607597 1872436084565575844852849)
        ·
          refine ⟨1404327063424181883639637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1872436084565575844852849 1404327063424181883639637)
          ·
            refine ⟨8228478887251065724451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1404327063424181883639637 8228478887251065724451)
            ·
              rfl

theorem cell22_1947026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 9].length) (baseStart_1947026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947026 prefixEnd_1947026 := by exact prefixLift 1947026
  have htrace : WordTrace (prefixWord ++ tailWord_1947026) baseStart_1947026 baseEnd_1947026 := by
    simpa [prefixWord, tailWord_1947026, baseEnd_1947026] using wordTrace_append hprefix tailTrace_1947026
  have hstable : (prefixWord ++ tailWord_1947026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947026).length < 2 ^ (prefixWord ++ tailWord_1947026).sum := by decide
  have hdescent : baseEnd_1947026 < baseStart_1947026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947052 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_1947052 : Nat := 118140960795 + 1947052 * 2 ^ 59
def prefixEnd_1947052 : Nat := 4983230072969 + 3 ^ 40 * 1947052 * 2
def baseEnd_1947052 : Nat := 666515690198680922530451

theorem tailTrace_1947052 : CollatzResearch.WordTrace tailWord_1947052 prefixEnd_1947052 666515690198680922530451 := by
  unfold tailWord_1947052
  simp only [CollatzResearch.WordTrace]
  refine ⟨35507410271085304426321705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47343213694780405901762273 35507410271085304426321705)
  ·
    refine ⟨26630557703313978319741279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35507410271085304426321705 26630557703313978319741279)
    ·
      refine ⟨39945836554970967479611919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26630557703313978319741279 39945836554970967479611919)
      ·
        refine ⟨59918754832456451219417879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39945836554970967479611919 59918754832456451219417879)
        ·
          refine ⟨89878132248684676829126819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59918754832456451219417879 89878132248684676829126819)
          ·
            refine ⟨134817198373027015243690229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89878132248684676829126819 134817198373027015243690229)
            ·
              refine ⟨12639112347471282679095959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134817198373027015243690229 12639112347471282679095959)
              ·
                refine ⟨18958668521206924018643939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12639112347471282679095959 18958668521206924018643939)
                ·
                  refine ⟨28438002781810386027965909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18958668521206924018643939 28438002781810386027965909)
                  ·
                    refine ⟨666515690198680922530451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28438002781810386027965909 666515690198680922530451)
                    ·
                      rfl

theorem cell22_1947052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_1947052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947052 prefixEnd_1947052 := by exact prefixLift 1947052
  have htrace : WordTrace (prefixWord ++ tailWord_1947052) baseStart_1947052 baseEnd_1947052 := by
    simpa [prefixWord, tailWord_1947052, baseEnd_1947052] using wordTrace_append hprefix tailTrace_1947052
  have hstable : (prefixWord ++ tailWord_1947052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947052).length < 2 ^ (prefixWord ++ tailWord_1947052).sum := by decide
  have hdescent : baseEnd_1947052 < baseStart_1947052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947129 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_1947129 : Nat := 118140960795 + 1947129 * 2 ^ 59
def prefixEnd_1947129 : Nat := 4983230072969 + 3 ^ 40 * 1947129 * 2
def baseEnd_1947129 : Nat := 666542048872278388355215

theorem tailTrace_1947129 : CollatzResearch.WordTrace tailWord_1947129 prefixEnd_1947129 666542048872278388355215 := by
  unfold tailWord_1947129
  simp only [CollatzResearch.WordTrace]
  refine ⟨71017628962891651003196441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47345085975261100668797627 71017628962891651003196441)
  ·
    refine ⟨53263221722168738252397331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71017628962891651003196441 53263221722168738252397331)
    ·
      refine ⟨79894832583253107378595997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53263221722168738252397331 79894832583253107378595997)
      ·
        refine ⟨29960562218719915266973499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79894832583253107378595997 29960562218719915266973499)
        ·
          refine ⟨44940843328079872900460249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29960562218719915266973499 44940843328079872900460249)
          ·
            refine ⟨33705632496059904675345187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44940843328079872900460249 33705632496059904675345187)
            ·
              refine ⟨50558448744089857013017781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33705632496059904675345187 50558448744089857013017781)
              ·
                refine ⟨4739854569758424094970417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50558448744089857013017781 4739854569758424094970417)
                ·
                  refine ⟨3554890927318818071227813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739854569758424094970417 3554890927318818071227813)
                  ·
                    refine ⟨666542048872278388355215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554890927318818071227813 666542048872278388355215)
                    ·
                      rfl

theorem cell22_1947129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_1947129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947129 prefixEnd_1947129 := by exact prefixLift 1947129
  have htrace : WordTrace (prefixWord ++ tailWord_1947129) baseStart_1947129 baseEnd_1947129 := by
    simpa [prefixWord, tailWord_1947129, baseEnd_1947129] using wordTrace_append hprefix tailTrace_1947129
  have hstable : (prefixWord ++ tailWord_1947129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947129).length < 2 ^ (prefixWord ++ tailWord_1947129).sum := by decide
  have hdescent : baseEnd_1947129 < baseStart_1947129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947133 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 4]
def baseStart_1947133 : Nat := 118140960795 + 1947133 * 2 ^ 59
def prefixEnd_1947133 : Nat := 4983230072969 + 3 ^ 40 * 1947133 * 2
def baseEnd_1947133 : Nat := 222181139384674570418401

theorem tailTrace_1947133 : CollatzResearch.WordTrace tailWord_1947133 prefixEnd_1947133 222181139384674570418401 := by
  unfold tailWord_1947133
  simp only [CollatzResearch.WordTrace]
  refine ⟨71017774854877159686342053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47345183236584773124228035 71017774854877159686342053)
  ·
    refine ⟨13315832785289467441189135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71017774854877159686342053 13315832785289467441189135)
    ·
      refine ⟨19973749177934201161783703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315832785289467441189135 19973749177934201161783703)
      ·
        refine ⟨29960623766901301742675555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19973749177934201161783703 29960623766901301742675555)
        ·
          refine ⟨44940935650351952614013333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29960623766901301742675555 44940935650351952614013333)
          ·
            refine ⟨2106606358610247778781875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44940935650351952614013333 2106606358610247778781875)
            ·
              refine ⟨3159909537915371668172813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106606358610247778781875 3159909537915371668172813)
              ·
                refine ⟨1184966076718264375564805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159909537915371668172813 1184966076718264375564805)
                ·
                  refine ⟨222181139384674570418401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184966076718264375564805 222181139384674570418401)
                  ·
                    rfl

theorem cell22_1947133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_1947133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947133 prefixEnd_1947133 := by exact prefixLift 1947133
  have htrace : WordTrace (prefixWord ++ tailWord_1947133) baseStart_1947133 baseEnd_1947133 := by
    simpa [prefixWord, tailWord_1947133, baseEnd_1947133] using wordTrace_append hprefix tailTrace_1947133
  have hstable : (prefixWord ++ tailWord_1947133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947133).length < 2 ^ (prefixWord ++ tailWord_1947133).sum := by decide
  have hdescent : baseEnd_1947133 < baseStart_1947133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947146 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_1947146 : Nat := 118140960795 + 1947146 * 2 ^ 59
def prefixEnd_1947146 : Nat := 4983230072969 + 3 ^ 40 * 1947146 * 2
def baseEnd_1947146 : Nat := 666547868319696010680163

theorem tailTrace_1947146 : CollatzResearch.WordTrace tailWord_1947146 prefixEnd_1947146 666547868319696010680163 := by
  unfold tailWord_1947146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17754562250957515726641323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47345499335886708604376861 17754562250957515726641323)
  ·
    refine ⟨26631843376436273589961985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17754562250957515726641323 26631843376436273589961985)
    ·
      refine ⟨19973882532327205192471489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26631843376436273589961985 19973882532327205192471489)
      ·
        refine ⟨14980411899245403894353617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19973882532327205192471489 14980411899245403894353617)
        ·
          refine ⟨11235308924434052920765213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14980411899245403894353617 11235308924434052920765213)
          ·
            refine ⟨4213240846662769845286955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11235308924434052920765213 4213240846662769845286955)
            ·
              refine ⟨6319861269994154767930433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213240846662769845286955 6319861269994154767930433)
              ·
                refine ⟨4739895952495616075947825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319861269994154767930433 4739895952495616075947825)
                ·
                  refine ⟨3554921964371712056960869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739895952495616075947825 3554921964371712056960869)
                  ·
                    refine ⟨666547868319696010680163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3554921964371712056960869 666547868319696010680163)
                    ·
                      rfl

theorem cell22_1947146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_1947146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947146 prefixEnd_1947146 := by exact prefixLift 1947146
  have htrace : WordTrace (prefixWord ++ tailWord_1947146) baseStart_1947146 baseEnd_1947146 := by
    simpa [prefixWord, tailWord_1947146, baseEnd_1947146] using wordTrace_append hprefix tailTrace_1947146
  have hstable : (prefixWord ++ tailWord_1947146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947146).length < 2 ^ (prefixWord ++ tailWord_1947146).sum := by decide
  have hdescent : baseEnd_1947146 < baseStart_1947146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947150 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_1947150 : Nat := 118140960795 + 1947150 * 2 ^ 59
def prefixEnd_1947150 : Nat := 4983230072969 + 3 ^ 40 * 1947150 * 2
def baseEnd_1947150 : Nat := 222183079200480444526717

theorem tailTrace_1947150 : CollatzResearch.WordTrace tailWord_1947150 prefixEnd_1947150 222183079200480444526717 := by
  unfold tailWord_1947150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877299361976946448713863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47345596597210381059807269 8877299361976946448713863)
  ·
    refine ⟨13315949042965419673070795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8877299361976946448713863 13315949042965419673070795)
    ·
      refine ⟨19973923564448129509606193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315949042965419673070795 19973923564448129509606193)
      ·
        refine ⟨14980442673336097132204645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19973923564448129509606193 14980442673336097132204645)
        ·
          refine ⟨2808833001250518212288371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14980442673336097132204645 2808833001250518212288371)
          ·
            refine ⟨4213249501875777318432557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808833001250518212288371 4213249501875777318432557)
            ·
              refine ⟨1579968563203416494412209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4213249501875777318432557 1579968563203416494412209)
              ·
                refine ⟨1184976422402562370809157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579968563203416494412209 1184976422402562370809157)
                ·
                  refine ⟨222183079200480444526717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184976422402562370809157 222183079200480444526717)
                  ·
                    rfl

theorem cell22_1947150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_1947150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947150 prefixEnd_1947150 := by exact prefixLift 1947150
  have htrace : WordTrace (prefixWord ++ tailWord_1947150) baseStart_1947150 baseEnd_1947150 := by
    simpa [prefixWord, tailWord_1947150, baseEnd_1947150] using wordTrace_append hprefix tailTrace_1947150
  have hstable : (prefixWord ++ tailWord_1947150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947150).length < 2 ^ (prefixWord ++ tailWord_1947150).sum := by decide
  have hdescent : baseEnd_1947150 < baseStart_1947150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947236 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1947236 : Nat := 118140960795 + 1947236 * 2 ^ 59
def prefixEnd_1947236 : Nat := 4983230072969 + 3 ^ 40 * 1947236 * 2
def baseEnd_1947236 : Nat := 666578677158965775929887

theorem tailTrace_1947236 : CollatzResearch.WordTrace tailWord_1947236 prefixEnd_1947236 666578677158965775929887 := by
  unfold tailWord_1947236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35510765786752004138670781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47347687715669338851561041 35510765786752004138670781)
  ·
    refine ⟨13316537170032001552001543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35510765786752004138670781 13316537170032001552001543)
    ·
      refine ⟨19974805755048002328002315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13316537170032001552001543 19974805755048002328002315)
      ·
        refine ⟨29962208632572003492003473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19974805755048002328002315 29962208632572003492003473)
        ·
          refine ⟨22471656474429002619002605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29962208632572003492003473 22471656474429002619002605)
          ·
            refine ⟨8426871177910875982125977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22471656474429002619002605 8426871177910875982125977)
            ·
              refine ⟨6320153383433156986594483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426871177910875982125977 6320153383433156986594483)
              ·
                refine ⟨9480230075149735479891725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320153383433156986594483 9480230075149735479891725)
                ·
                  refine ⟨3555086278181150804959397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9480230075149735479891725 3555086278181150804959397)
                  ·
                    refine ⟨666578677158965775929887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3555086278181150804959397 666578677158965775929887)
                    ·
                      rfl

theorem cell22_1947236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1947236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947236 prefixEnd_1947236 := by exact prefixLift 1947236
  have htrace : WordTrace (prefixWord ++ tailWord_1947236) baseStart_1947236 baseEnd_1947236 := by
    simpa [prefixWord, tailWord_1947236, baseEnd_1947236] using wordTrace_append hprefix tailTrace_1947236
  have hstable : (prefixWord ++ tailWord_1947236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947236).length < 2 ^ (prefixWord ++ tailWord_1947236).sum := by decide
  have hdescent : baseEnd_1947236 < baseStart_1947236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947268 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1947268 : Nat := 118140960795 + 1947268 * 2 ^ 59
def prefixEnd_1947268 : Nat := 4983230072969 + 3 ^ 40 * 1947268 * 2
def baseEnd_1947268 : Nat := 222196543804309453043263

theorem tailTrace_1947268 : CollatzResearch.WordTrace tailWord_1947268 prefixEnd_1947268 222196543804309453043263 := by
  unfold tailWord_1947268
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511349354694038871253229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47348465806258718495004305 35511349354694038871253229)
  ·
    refine ⟨13316756008010264576719961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35511349354694038871253229 13316756008010264576719961)
    ·
      refine ⟨9987567006007698432539971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13316756008010264576719961 9987567006007698432539971)
      ·
        refine ⟨14981350509011547648809957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9987567006007698432539971 14981350509011547648809957)
        ·
          refine ⟨2809003220439665184151867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14981350509011547648809957 2809003220439665184151867)
          ·
            refine ⟨4213504830659497776227801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809003220439665184151867 4213504830659497776227801)
            ·
              refine ⟨3160128622994623332170851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213504830659497776227801 3160128622994623332170851)
              ·
                refine ⟨4740192934491934998256277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160128622994623332170851 4740192934491934998256277)
                ·
                  refine ⟨222196543804309453043263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4740192934491934998256277 222196543804309453043263)
                  ·
                    rfl

theorem cell22_1947268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1947268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947268 prefixEnd_1947268 := by exact prefixLift 1947268
  have htrace : WordTrace (prefixWord ++ tailWord_1947268) baseStart_1947268 baseEnd_1947268 := by
    simpa [prefixWord, tailWord_1947268, baseEnd_1947268] using wordTrace_append hprefix tailTrace_1947268
  have hstable : (prefixWord ++ tailWord_1947268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947268).length < 2 ^ (prefixWord ++ tailWord_1947268).sum := by decide
  have hdescent : baseEnd_1947268 < baseStart_1947268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947296 : List Nat := [2, 1, 1, 4, 3, 2, 1, 8]
def baseStart_1947296 : Nat := 118140960795 + 1947296 * 2 ^ 59
def prefixEnd_1947296 : Nat := 4983230072969 + 3 ^ 40 * 1947296 * 2
def baseEnd_1947296 : Nat := 74066579598349513269967

theorem tailTrace_1947296 : CollatzResearch.WordTrace tailWord_1947296 prefixEnd_1947296 74066579598349513269967 := by
  unfold tailWord_1947296
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511859976643319262262871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47349146635524425683017161 35511859976643319262262871)
  ·
    refine ⟨53267789964964978893394307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35511859976643319262262871 53267789964964978893394307)
    ·
      refine ⟨79901684947447468340091461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53267789964964978893394307 79901684947447468340091461)
      ·
        refine ⟨14981565927646400313767149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79901684947447468340091461 14981565927646400313767149)
        ·
          refine ⟨5618087222867400117662681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14981565927646400313767149 5618087222867400117662681)
          ·
            refine ⟨4213565417150550088247011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5618087222867400117662681 4213565417150550088247011)
            ·
              refine ⟨6320348125725825132370517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213565417150550088247011 6320348125725825132370517)
              ·
                refine ⟨74066579598349513269967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6320348125725825132370517 74066579598349513269967)
                ·
                  rfl

theorem cell22_1947296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_1947296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947296 prefixEnd_1947296 := by exact prefixLift 1947296
  have htrace : WordTrace (prefixWord ++ tailWord_1947296) baseStart_1947296 baseEnd_1947296 := by
    simpa [prefixWord, tailWord_1947296, baseEnd_1947296] using wordTrace_append hprefix tailTrace_1947296
  have hstable : (prefixWord ++ tailWord_1947296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947296).length < 2 ^ (prefixWord ++ tailWord_1947296).sum := by decide
  have hdescent : baseEnd_1947296 < baseStart_1947296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947334 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1947334 : Nat := 118140960795 + 1947334 * 2 ^ 59
def prefixEnd_1947334 : Nat := 4983230072969 + 3 ^ 40 * 1947334 * 2
def baseEnd_1947334 : Nat := 666612224561726186979587

theorem tailTrace_1947334 : CollatzResearch.WordTrace tailWord_1947334 prefixEnd_1947334 666612224561726186979587 := by
  unfold tailWord_1947334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219534560223405344200283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47350070618099314009606037 2219534560223405344200283)
  ·
    refine ⟨3329301840335108016300425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2219534560223405344200283 3329301840335108016300425)
    ·
      refine ⟨2496976380251331012225319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3329301840335108016300425 2496976380251331012225319)
      ·
        refine ⟨3745464570376996518337979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496976380251331012225319 3745464570376996518337979)
        ·
          refine ⟨5618196855565494777506969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745464570376996518337979 5618196855565494777506969)
          ·
            refine ⟨4213647641674121083130227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5618196855565494777506969 4213647641674121083130227)
            ·
              refine ⟨6320471462511181624695341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213647641674121083130227 6320471462511181624695341)
              ·
                refine ⟨2370176798441693109260753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6320471462511181624695341 2370176798441693109260753)
                ·
                  refine ⟨1777632598831269831945565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2370176798441693109260753 1777632598831269831945565)
                  ·
                    refine ⟨666612224561726186979587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777632598831269831945565 666612224561726186979587)
                    ·
                      rfl

theorem cell22_1947334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1947334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947334 prefixEnd_1947334 := by exact prefixLift 1947334
  have htrace : WordTrace (prefixWord ++ tailWord_1947334) baseStart_1947334 baseEnd_1947334 := by
    simpa [prefixWord, tailWord_1947334, baseEnd_1947334] using wordTrace_append hprefix tailTrace_1947334
  have hstable : (prefixWord ++ tailWord_1947334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947334).length < 2 ^ (prefixWord ++ tailWord_1947334).sum := by decide
  have hdescent : baseEnd_1947334 < baseStart_1947334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947386 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_1947386 : Nat := 118140960795 + 1947386 * 2 ^ 59
def prefixEnd_1947386 : Nat := 4983230072969 + 3 ^ 40 * 1947386 * 2
def baseEnd_1947386 : Nat := 222210008408138461559809

theorem tailTrace_1947386 : CollatzResearch.WordTrace tailWord_1947386 prefixEnd_1947386 222210008408138461559809 := by
  unfold tailWord_1947386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17756750630740145973825503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47351335015307055930201341 17756750630740145973825503)
  ·
    refine ⟨26635125946110218960738255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17756750630740145973825503 26635125946110218960738255)
    ·
      refine ⟨39952688919165328441107383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26635125946110218960738255 39952688919165328441107383)
      ·
        refine ⟨59929033378747992661661075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39952688919165328441107383 59929033378747992661661075)
        ·
          refine ⟨89893550068121988992491613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59929033378747992661661075 89893550068121988992491613)
          ·
            refine ⟨33710081275545745872184355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89893550068121988992491613 33710081275545745872184355)
            ·
              refine ⟨50565121913318618808276533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33710081275545745872184355 50565121913318618808276533)
              ·
                refine ⟨4740480179373620513275925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50565121913318618808276533 4740480179373620513275925)
                ·
                  refine ⟨222210008408138461559809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4740480179373620513275925 222210008408138461559809)
                  ·
                    rfl

theorem cell22_1947386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_1947386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947386 prefixEnd_1947386 := by exact prefixLift 1947386
  have htrace : WordTrace (prefixWord ++ tailWord_1947386) baseStart_1947386 baseEnd_1947386 := by
    simpa [prefixWord, tailWord_1947386, baseEnd_1947386] using wordTrace_append hprefix tailTrace_1947386
  have hstable : (prefixWord ++ tailWord_1947386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947386).length < 2 ^ (prefixWord ++ tailWord_1947386).sum := by decide
  have hdescent : baseEnd_1947386 < baseStart_1947386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947390 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1947390 : Nat := 118140960795 + 1947390 * 2 ^ 59
def prefixEnd_1947390 : Nat := 4983230072969 + 3 ^ 40 * 1947390 * 2
def baseEnd_1947390 : Nat := 666631394506160707579415

theorem tailTrace_1947390 : CollatzResearch.WordTrace tailWord_1947390 prefixEnd_1947390 666631394506160707579415 := by
  unfold tailWord_1947390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878393551868261572305953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47351432276630728385631749 8878393551868261572305953)
  ·
    refine ⟨6658795163901196179229465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8878393551868261572305953 6658795163901196179229465)
    ·
      refine ⟨4994096372925897134422099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6658795163901196179229465 4994096372925897134422099)
      ·
        refine ⟨7491144559388845701633149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994096372925897134422099 7491144559388845701633149)
        ·
          refine ⟨2809179209770817138112431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7491144559388845701633149 2809179209770817138112431)
          ·
            refine ⟨4213768814656225707168647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809179209770817138112431 4213768814656225707168647)
            ·
              refine ⟨6320653221984338560752971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213768814656225707168647 6320653221984338560752971)
              ·
                refine ⟨9480979832976507841129457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320653221984338560752971 9480979832976507841129457)
                ·
                  refine ⟨7110734874732380880847093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9480979832976507841129457 7110734874732380880847093)
                  ·
                    refine ⟨666631394506160707579415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7110734874732380880847093 666631394506160707579415)
                    ·
                      rfl

theorem cell22_1947390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1947390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947390 prefixEnd_1947390 := by exact prefixLift 1947390
  have htrace : WordTrace (prefixWord ++ tailWord_1947390) baseStart_1947390 baseEnd_1947390 := by
    simpa [prefixWord, tailWord_1947390, baseEnd_1947390] using wordTrace_append hprefix tailTrace_1947390
  have hstable : (prefixWord ++ tailWord_1947390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947390).length < 2 ^ (prefixWord ++ tailWord_1947390).sum := by decide
  have hdescent : baseEnd_1947390 < baseStart_1947390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947418 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_1947418 : Nat := 118140960795 + 1947418 * 2 ^ 59
def prefixEnd_1947418 : Nat := 4983230072969 + 3 ^ 40 * 1947418 * 2
def baseEnd_1947418 : Nat := 666640979478377967879329

theorem tailTrace_1947418 : CollatzResearch.WordTrace tailWord_1947418 prefixEnd_1947418 666640979478377967879329 := by
  unfold tailWord_1947418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17757042414711163340116727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47352113105896435573644605 17757042414711163340116727)
  ·
    refine ⟨26635563622066745010175091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17757042414711163340116727 26635563622066745010175091)
    ·
      refine ⟨39953345433100117515262637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26635563622066745010175091 39953345433100117515262637)
      ·
        refine ⟨14982504537412544068223489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39953345433100117515262637 14982504537412544068223489)
        ·
          refine ⟨11236878403059408051167617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14982504537412544068223489 11236878403059408051167617)
          ·
            refine ⟨8427658802294556038375713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11236878403059408051167617 8427658802294556038375713)
            ·
              refine ⟨6320744101720917028781785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8427658802294556038375713 6320744101720917028781785)
              ·
                refine ⟨4740558076290687771586339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6320744101720917028781785 4740558076290687771586339)
                ·
                  refine ⟨7110837114436031657379509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740558076290687771586339 7110837114436031657379509)
                  ·
                    refine ⟨666640979478377967879329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7110837114436031657379509 666640979478377967879329)
                    ·
                      rfl

theorem cell22_1947418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_1947418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947418 prefixEnd_1947418 := by exact prefixLift 1947418
  have htrace : WordTrace (prefixWord ++ tailWord_1947418) baseStart_1947418 baseEnd_1947418 := by
    simpa [prefixWord, tailWord_1947418, baseEnd_1947418] using wordTrace_append hprefix tailTrace_1947418
  have hstable : (prefixWord ++ tailWord_1947418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947418).length < 2 ^ (prefixWord ++ tailWord_1947418).sum := by decide
  have hdescent : baseEnd_1947418 < baseStart_1947418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947420 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 4]
def baseStart_1947420 : Nat := 118140960795 + 1947420 * 2 ^ 59
def prefixEnd_1947420 : Nat := 4983230072969 + 3 ^ 40 * 1947420 * 2
def baseEnd_1947420 : Nat := 222213888039750209776441

theorem tailTrace_1947420 : CollatzResearch.WordTrace tailWord_1947420 prefixEnd_1947420 222213888039750209776441 := by
  unfold tailWord_1947420
  simp only [CollatzResearch.WordTrace]
  refine ⟨35514121302418703851019857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47352161736558271801359809 35514121302418703851019857)
  ·
    refine ⟨26635590976814027888264893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35514121302418703851019857 26635590976814027888264893)
    ·
      refine ⟨9988346616305260458099335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26635590976814027888264893 9988346616305260458099335)
      ·
        refine ⟨14982519924457890687149003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988346616305260458099335 14982519924457890687149003)
        ·
          refine ⟨22473779886686836030723505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982519924457890687149003 22473779886686836030723505)
          ·
            refine ⟨16855334915015127023042629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22473779886686836030723505 16855334915015127023042629)
            ·
              refine ⟨3160375296565336316820493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16855334915015127023042629 3160375296565336316820493)
              ·
                refine ⟨1185140736212001118807685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3160375296565336316820493 1185140736212001118807685)
                ·
                  refine ⟨222213888039750209776441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185140736212001118807685 222213888039750209776441)
                  ·
                    rfl

theorem cell22_1947420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_1947420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947420 prefixEnd_1947420 := by exact prefixLift 1947420
  have htrace : WordTrace (prefixWord ++ tailWord_1947420) baseStart_1947420 baseEnd_1947420 := by
    simpa [prefixWord, tailWord_1947420, baseEnd_1947420] using wordTrace_append hprefix tailTrace_1947420
  have hstable : (prefixWord ++ tailWord_1947420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947420).length < 2 ^ (prefixWord ++ tailWord_1947420).sum := by decide
  have hdescent : baseEnd_1947420 < baseStart_1947420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947493 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 5]
def baseStart_1947493 : Nat := 118140960795 + 1947493 * 2 ^ 59
def prefixEnd_1947493 : Nat := 4983230072969 + 3 ^ 40 * 1947493 * 2
def baseEnd_1947493 : Nat := 222222217837034257418033

theorem tailTrace_1947493 : CollatzResearch.WordTrace tailWord_1947493 prefixEnd_1947493 222222217837034257418033 := by
  unfold tailWord_1947493
  simp only [CollatzResearch.WordTrace]
  refine ⟨71030905133572941169447133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47353936755715294112964755 71030905133572941169447133)
  ·
    refine ⟨26636589425089852938542675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71030905133572941169447133 26636589425089852938542675)
    ·
      refine ⟨39954884137634779407814013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26636589425089852938542675 39954884137634779407814013)
      ·
        refine ⟨14983081551613042277930255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39954884137634779407814013 14983081551613042277930255)
        ·
          refine ⟨22474622327419563416895383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983081551613042277930255 22474622327419563416895383)
          ·
            refine ⟨33711933491129345125343075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474622327419563416895383 33711933491129345125343075)
            ·
              refine ⟨50567900236694017688014613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33711933491129345125343075 50567900236694017688014613)
              ·
                refine ⟨2370370323595032079125685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50567900236694017688014613 2370370323595032079125685)
                ·
                  refine ⟨222222217837034257418033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2370370323595032079125685 222222217837034257418033)
                  ·
                    rfl

theorem cell22_1947493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_1947493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947493 prefixEnd_1947493 := by exact prefixLift 1947493
  have htrace : WordTrace (prefixWord ++ tailWord_1947493) baseStart_1947493 baseEnd_1947493 := by
    simpa [prefixWord, tailWord_1947493, baseEnd_1947493] using wordTrace_append hprefix tailTrace_1947493
  have hstable : (prefixWord ++ tailWord_1947493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947493).length < 2 ^ (prefixWord ++ tailWord_1947493).sum := by decide
  have hdescent : baseEnd_1947493 < baseStart_1947493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947643 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_1947643 : Nat := 118140960795 + 1947643 * 2 ^ 59
def prefixEnd_1947643 : Nat := 4983230072969 + 3 ^ 40 * 1947643 * 2
def baseEnd_1947643 : Nat := 666718001576552381003639

theorem tailTrace_1947643 : CollatzResearch.WordTrace tailWord_1947643 prefixEnd_1947643 666718001576552381003639 := by
  unfold tailWord_1947643
  simp only [CollatzResearch.WordTrace]
  refine ⟨71036376083029516787407583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47357584055353011191605055 71036376083029516787407583)
  ·
    refine ⟨106554564124544275181111375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71036376083029516787407583 106554564124544275181111375)
    ·
      refine ⟨159831846186816412771667063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106554564124544275181111375 159831846186816412771667063)
      ·
        refine ⟨239747769280224619157500595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159831846186816412771667063 239747769280224619157500595)
        ·
          refine ⟨359621653920336928736250893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239747769280224619157500595 359621653920336928736250893)
          ·
            refine ⟨134858120220126348276094085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359621653920336928736250893 134858120220126348276094085)
            ·
              refine ⟨25285897541273690301767641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134858120220126348276094085 25285897541273690301767641)
              ·
                refine ⟨18964423155955267726325731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25285897541273690301767641 18964423155955267726325731)
                ·
                  refine ⟨28446634733932901589488597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18964423155955267726325731 28446634733932901589488597)
                  ·
                    refine ⟨666718001576552381003639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28446634733932901589488597 666718001576552381003639)
                    ·
                      rfl

theorem cell22_1947643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_1947643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947643 prefixEnd_1947643 := by exact prefixLift 1947643
  have htrace : WordTrace (prefixWord ++ tailWord_1947643) baseStart_1947643 baseEnd_1947643 := by
    simpa [prefixWord, tailWord_1947643, baseEnd_1947643] using wordTrace_append hprefix tailTrace_1947643
  have hstable : (prefixWord ++ tailWord_1947643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947643).length < 2 ^ (prefixWord ++ tailWord_1947643).sum := by decide
  have hdescent : baseEnd_1947643 < baseStart_1947643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947709 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_1947709 : Nat := 118140960795 + 1947709 * 2 ^ 59
def prefixEnd_1947709 : Nat := 4983230072969 + 3 ^ 40 * 1947709 * 2
def baseEnd_1947709 : Nat := 666740594725350208853437

theorem tailTrace_1947709 : CollatzResearch.WordTrace tailWord_1947709 prefixEnd_1947709 666740594725350208853437 := by
  unfold tailWord_1947709
  simp only [CollatzResearch.WordTrace]
  refine ⟨71038783300790410059310181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47359188867193606706206787 71038783300790410059310181)
  ·
    refine ⟨13319771868898201886120659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71038783300790410059310181 13319771868898201886120659)
    ·
      refine ⟨19979657803347302829180989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13319771868898201886120659 19979657803347302829180989)
      ·
        refine ⟨7492371676255238560942871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19979657803347302829180989 7492371676255238560942871)
        ·
          refine ⟨11238557514382857841414307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492371676255238560942871 11238557514382857841414307)
          ·
            refine ⟨16857836271574286762121461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11238557514382857841414307 16857836271574286762121461)
            ·
              refine ⟨1580422150460089383948887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16857836271574286762121461 1580422150460089383948887)
              ·
                refine ⟨2370633225690134075923331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580422150460089383948887 2370633225690134075923331)
                ·
                  refine ⟨3555949838535201113884997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370633225690134075923331 3555949838535201113884997)
                  ·
                    refine ⟨666740594725350208853437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3555949838535201113884997 666740594725350208853437)
                    ·
                      rfl

theorem cell22_1947709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_1947709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947709 prefixEnd_1947709 := by exact prefixLift 1947709
  have htrace : WordTrace (prefixWord ++ tailWord_1947709) baseStart_1947709 baseEnd_1947709 := by
    simpa [prefixWord, tailWord_1947709, baseEnd_1947709] using wordTrace_append hprefix tailTrace_1947709
  have hstable : (prefixWord ++ tailWord_1947709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947709).length < 2 ^ (prefixWord ++ tailWord_1947709).sum := by decide
  have hdescent : baseEnd_1947709 < baseStart_1947709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947720 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_1947720 : Nat := 118140960795 + 1947720 * 2 ^ 59
def prefixEnd_1947720 : Nat := 4983230072969 + 3 ^ 40 * 1947720 * 2
def baseEnd_1947720 : Nat := 666744360250149846828403

theorem tailTrace_1947720 : CollatzResearch.WordTrace tailWord_1947720 prefixEnd_1947720 666744360250149846828403 := by
  unfold tailWord_1947720
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519592251875279468980307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47359456335833705958640409 35519592251875279468980307)
  ·
    refine ⟨53279388377812919203470461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35519592251875279468980307 53279388377812919203470461)
    ·
      refine ⟨19979770641679844701301423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53279388377812919203470461 19979770641679844701301423)
      ·
        refine ⟨29969655962519767051952135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19979770641679844701301423 29969655962519767051952135)
        ·
          refine ⟨44954483943779650577928203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29969655962519767051952135 44954483943779650577928203)
          ·
            refine ⟨67431725915669475866892305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44954483943779650577928203 67431725915669475866892305)
            ·
              refine ⟨50573794436752106900169229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67431725915669475866892305 50573794436752106900169229)
              ·
                refine ⟨18965172913782040087563461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50573794436752106900169229 18965172913782040087563461)
                ·
                  refine ⟨3555969921334132516418149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18965172913782040087563461 3555969921334132516418149)
                  ·
                    refine ⟨666744360250149846828403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3555969921334132516418149 666744360250149846828403)
                    ·
                      rfl

theorem cell22_1947720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_1947720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947720 prefixEnd_1947720 := by exact prefixLift 1947720
  have htrace : WordTrace (prefixWord ++ tailWord_1947720) baseStart_1947720 baseEnd_1947720 := by
    simpa [prefixWord, tailWord_1947720, baseEnd_1947720] using wordTrace_append hprefix tailTrace_1947720
  have hstable : (prefixWord ++ tailWord_1947720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947720).length < 2 ^ (prefixWord ++ tailWord_1947720).sum := by decide
  have hdescent : baseEnd_1947720 < baseStart_1947720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947724 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 4]
def baseStart_1947724 : Nat := 118140960795 + 1947724 * 2 ^ 59
def prefixEnd_1947724 : Nat := 4983230072969 + 3 ^ 40 * 1947724 * 2
def baseEnd_1947724 : Nat := 222248576510631723242797

theorem tailTrace_1947724 : CollatzResearch.WordTrace tailWord_1947724 prefixEnd_1947724 222248576510631723242797 := by
  unfold tailWord_1947724
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519665197868033810553113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47359553597157378414070817 35519665197868033810553113)
  ·
    refine ⟨26639748898401025357914835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35519665197868033810553113 26639748898401025357914835)
    ·
      refine ⟨39959623347601538036872253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26639748898401025357914835 39959623347601538036872253)
      ·
        refine ⟨14984858755350576763827095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39959623347601538036872253 14984858755350576763827095)
        ·
          refine ⟨22477288133025865145740643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14984858755350576763827095 22477288133025865145740643)
          ·
            refine ⟨33715932199538797718610965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22477288133025865145740643 33715932199538797718610965)
            ·
              refine ⟨1580434321853381143059889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33715932199538797718610965 1580434321853381143059889)
              ·
                refine ⟨1185325741390035857294917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580434321853381143059889 1185325741390035857294917)
                ·
                  refine ⟨222248576510631723242797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185325741390035857294917 222248576510631723242797)
                  ·
                    rfl

theorem cell22_1947724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_1947724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947724 prefixEnd_1947724 := by exact prefixLift 1947724
  have htrace : WordTrace (prefixWord ++ tailWord_1947724) baseStart_1947724 baseEnd_1947724 := by
    simpa [prefixWord, tailWord_1947724, baseEnd_1947724] using wordTrace_append hprefix tailTrace_1947724
  have hstable : (prefixWord ++ tailWord_1947724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947724).length < 2 ^ (prefixWord ++ tailWord_1947724).sum := by decide
  have hdescent : baseEnd_1947724 < baseStart_1947724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947735 : List Nat := [1, 1, 3, 2, 2, 1, 5, 7]
def baseStart_1947735 : Nat := 118140960795 + 1947735 * 2 ^ 59
def prefixEnd_1947735 : Nat := 4983230072969 + 3 ^ 40 * 1947735 * 2
def baseEnd_1947735 : Nat := 74083277228521645300373

theorem tailTrace_1947735 : CollatzResearch.WordTrace tailWord_1947735 prefixEnd_1947735 74083277228521645300373 := by
  unfold tailWord_1947735
  simp only [CollatzResearch.WordTrace]
  refine ⟨71039731598696216499756659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47359821065797477666504439 71039731598696216499756659)
  ·
    refine ⟨106559597398044324749634989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71039731598696216499756659 106559597398044324749634989)
    ·
      refine ⟨39959849024266621781113121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106559597398044324749634989 39959849024266621781113121)
      ·
        refine ⟨29969886768199966335834841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39959849024266621781113121 29969886768199966335834841)
        ·
          refine ⟨22477415076149974751876131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29969886768199966335834841 22477415076149974751876131)
          ·
            refine ⟨33716122614224962127814197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22477415076149974751876131 33716122614224962127814197)
            ·
              refine ⟨3160886495083590199482581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33716122614224962127814197 3160886495083590199482581)
              ·
                refine ⟨74083277228521645300373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3160886495083590199482581 74083277228521645300373)
                ·
                  rfl

theorem cell22_1947735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 7].length) (baseStart_1947735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947735 prefixEnd_1947735 := by exact prefixLift 1947735
  have htrace : WordTrace (prefixWord ++ tailWord_1947735) baseStart_1947735 baseEnd_1947735 := by
    simpa [prefixWord, tailWord_1947735, baseEnd_1947735] using wordTrace_append hprefix tailTrace_1947735
  have hstable : (prefixWord ++ tailWord_1947735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947735).length < 2 ^ (prefixWord ++ tailWord_1947735).sum := by decide
  have hdescent : baseEnd_1947735 < baseStart_1947735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947784 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_1947784 : Nat := 118140960795 + 1947784 * 2 ^ 59
def prefixEnd_1947784 : Nat := 4983230072969 + 3 ^ 40 * 1947784 * 2
def baseEnd_1947784 : Nat := 666766268758075013228207

theorem tailTrace_1947784 : CollatzResearch.WordTrace tailWord_1947784 prefixEnd_1947784 666766268758075013228207 := by
  unfold tailWord_1947784
  simp only [CollatzResearch.WordTrace]
  refine ⟨35520759387759348934145203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47361012517012465245526937 35520759387759348934145203)
  ·
    refine ⟨53281139081639023401217805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35520759387759348934145203 53281139081639023401217805)
    ·
      refine ⟨19980427155614633775456677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53281139081639023401217805 19980427155614633775456677)
      ·
        refine ⟨3746330091677743832898127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19980427155614633775456677 3746330091677743832898127)
        ·
          refine ⟨5619495137516615749347191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746330091677743832898127 5619495137516615749347191)
          ·
            refine ⟨8429242706274923624020787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619495137516615749347191 8429242706274923624020787)
            ·
              refine ⟨12643864059412385436031181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429242706274923624020787 12643864059412385436031181)
              ·
                refine ⟨4741449022279644538511693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12643864059412385436031181 4741449022279644538511693)
                ·
                  refine ⟨1778043383354866701941885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4741449022279644538511693 1778043383354866701941885)
                  ·
                    refine ⟨666766268758075013228207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778043383354866701941885 666766268758075013228207)
                    ·
                      rfl

theorem cell22_1947784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_1947784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947784 prefixEnd_1947784 := by exact prefixLift 1947784
  have htrace : WordTrace (prefixWord ++ tailWord_1947784) baseStart_1947784 baseEnd_1947784 := by
    simpa [prefixWord, tailWord_1947784, baseEnd_1947784] using wordTrace_append hprefix tailTrace_1947784
  have hstable : (prefixWord ++ tailWord_1947784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947784).length < 2 ^ (prefixWord ++ tailWord_1947784).sum := by decide
  have hdescent : baseEnd_1947784 < baseStart_1947784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947932 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_1947932 : Nat := 118140960795 + 1947932 * 2 ^ 59
def prefixEnd_1947932 : Nat := 4983230072969 + 3 ^ 40 * 1947932 * 2
def baseEnd_1947932 : Nat := 222272310727550653509251

theorem tailTrace_1947932 : CollatzResearch.WordTrace tailWord_1947932 prefixEnd_1947932 222272310727550653509251 := by
  unfold tailWord_1947932
  simp only [CollatzResearch.WordTrace]
  refine ⟨35523458389491259572339025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47364611185988346096452033 35523458389491259572339025)
  ·
    refine ⟨26642593792118444679254269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35523458389491259572339025 26642593792118444679254269)
    ·
      refine ⟨9990972672044416754720351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26642593792118444679254269 9990972672044416754720351)
      ·
        refine ⟨14986459008066625132080527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990972672044416754720351 14986459008066625132080527)
        ·
          refine ⟨22479688512099937698120791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14986459008066625132080527 22479688512099937698120791)
          ·
            refine ⟨33719532768149906547181187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22479688512099937698120791 33719532768149906547181187)
            ·
              refine ⟨50579299152224859820771781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33719532768149906547181187 50579299152224859820771781)
              ·
                refine ⟨9483618591042161216394709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50579299152224859820771781 9483618591042161216394709)
                ·
                  refine ⟨222272310727550653509251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9483618591042161216394709 222272310727550653509251)
                  ·
                    rfl

theorem cell22_1947932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_1947932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1947932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1947932 prefixEnd_1947932 := by exact prefixLift 1947932
  have htrace : WordTrace (prefixWord ++ tailWord_1947932) baseStart_1947932 baseEnd_1947932 := by
    simpa [prefixWord, tailWord_1947932, baseEnd_1947932] using wordTrace_append hprefix tailTrace_1947932
  have hstable : (prefixWord ++ tailWord_1947932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947932).length < 2 ^ (prefixWord ++ tailWord_1947932).sum := by decide
  have hdescent : baseEnd_1947932 < baseStart_1947932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948009 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_1948009 : Nat := 118140960795 + 1948009 * 2 ^ 59
def prefixEnd_1948009 : Nat := 4983230072969 + 3 ^ 40 * 1948009 * 2
def baseEnd_1948009 : Nat := 666843290856249426352517

theorem tailTrace_1948009 : CollatzResearch.WordTrace tailWord_1948009 prefixEnd_1948009 666843290856249426352517 := by
  unfold tailWord_1948009
  simp only [CollatzResearch.WordTrace]
  refine ⟨71049725199703561295231081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47366483466469040863487387 71049725199703561295231081)
  ·
    refine ⟨53287293899777670971423311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71049725199703561295231081 53287293899777670971423311)
    ·
      refine ⟨79930940849666506457134967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53287293899777670971423311 79930940849666506457134967)
      ·
        refine ⟨119896411274499759685702451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79930940849666506457134967 119896411274499759685702451)
        ·
          refine ⟨179844616911749639528553677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119896411274499759685702451 179844616911749639528553677)
          ·
            refine ⟨67441731341906114823207629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179844616911749639528553677 67441731341906114823207629)
            ·
              refine ⟨25290649253214793058702861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67441731341906114823207629 25290649253214793058702861)
              ·
                refine ⟨9483993469955547397013573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25290649253214793058702861 9483993469955547397013573)
                ·
                  refine ⟨1778248775616665136940045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9483993469955547397013573 1778248775616665136940045)
                  ·
                    refine ⟨666843290856249426352517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778248775616665136940045 666843290856249426352517)
                    ·
                      rfl

theorem cell22_1948009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_1948009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948009 prefixEnd_1948009 := by exact prefixLift 1948009
  have htrace : WordTrace (prefixWord ++ tailWord_1948009) baseStart_1948009 baseEnd_1948009 := by
    simpa [prefixWord, tailWord_1948009, baseEnd_1948009] using wordTrace_append hprefix tailTrace_1948009
  have hstable : (prefixWord ++ tailWord_1948009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948009).length < 2 ^ (prefixWord ++ tailWord_1948009).sum := by decide
  have hdescent : baseEnd_1948009 < baseStart_1948009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948041 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_1948041 : Nat := 118140960795 + 1948041 * 2 ^ 59
def prefixEnd_1948041 : Nat := 4983230072969 + 3 ^ 40 * 1948041 * 2
def baseEnd_1948041 : Nat := 666854245110212009552419

theorem tailTrace_1948041 : CollatzResearch.WordTrace tailWord_1948041 prefixEnd_1948041 666854245110212009552419 := by
  unfold tailWord_1948041
  simp only [CollatzResearch.WordTrace]
  refine ⟨71050892335587630760395977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47367261557058420506930651 71050892335587630760395977)
  ·
    refine ⟨53288169251690723070296983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71050892335587630760395977 53288169251690723070296983)
    ·
      refine ⟨79932253877536084605445475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53288169251690723070296983 79932253877536084605445475)
      ·
        refine ⟨119898380816304126908168213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79932253877536084605445475 119898380816304126908168213)
        ·
          refine ⟨5620236600764255948820385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119898380816304126908168213 5620236600764255948820385)
          ·
            refine ⟨4215177450573191961615289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5620236600764255948820385 4215177450573191961615289)
            ·
              refine ⟨3161383087929893971211467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215177450573191961615289 3161383087929893971211467)
              ·
                refine ⟨4742074631894840956817201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161383087929893971211467 4742074631894840956817201)
                ·
                  refine ⟨3556555973921130717612901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4742074631894840956817201 3556555973921130717612901)
                  ·
                    refine ⟨666854245110212009552419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3556555973921130717612901 666854245110212009552419)
                    ·
                      rfl

theorem cell22_1948041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_1948041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948041 prefixEnd_1948041 := by exact prefixLift 1948041
  have htrace : WordTrace (prefixWord ++ tailWord_1948041) baseStart_1948041 baseEnd_1948041 := by
    simpa [prefixWord, tailWord_1948041, baseEnd_1948041] using wordTrace_append hprefix tailTrace_1948041
  have hstable : (prefixWord ++ tailWord_1948041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948041).length < 2 ^ (prefixWord ++ tailWord_1948041).sum := by decide
  have hdescent : baseEnd_1948041 < baseStart_1948041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948062 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1948062 : Nat := 118140960795 + 1948062 * 2 ^ 59
def prefixEnd_1948062 : Nat := 4983230072969 + 3 ^ 40 * 1948062 * 2
def baseEnd_1948062 : Nat := 222287144613124984925785

theorem tailTrace_1948062 : CollatzResearch.WordTrace tailWord_1948062 prefixEnd_1948062 222287144613124984925785 := by
  unfold tailWord_1948062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881457283563943918363805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47367772179007700897940293 8881457283563943918363805)
  ·
    refine ⟨3330546481336478969386427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8881457283563943918363805 3330546481336478969386427)
    ·
      refine ⟨4995819722004718454079641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3330546481336478969386427 4995819722004718454079641)
      ·
        refine ⟨3746864791503538840559731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4995819722004718454079641 3746864791503538840559731)
        ·
          refine ⟨5620297187255308260839597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746864791503538840559731 5620297187255308260839597)
          ·
            refine ⟨2107611445220740597814849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5620297187255308260839597 2107611445220740597814849)
            ·
              refine ⟨1580708583915555448361137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107611445220740597814849 1580708583915555448361137)
              ·
                refine ⟨1185531437936666586270853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580708583915555448361137 1185531437936666586270853)
                ·
                  refine ⟨222287144613124984925785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185531437936666586270853 222287144613124984925785)
                  ·
                    rfl

theorem cell22_1948062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1948062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948062 prefixEnd_1948062 := by exact prefixLift 1948062
  have htrace : WordTrace (prefixWord ++ tailWord_1948062) baseStart_1948062 baseEnd_1948062 := by
    simpa [prefixWord, tailWord_1948062, baseEnd_1948062] using wordTrace_append hprefix tailTrace_1948062
  have hstable : (prefixWord ++ tailWord_1948062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948062).length < 2 ^ (prefixWord ++ tailWord_1948062).sum := by decide
  have hdescent : baseEnd_1948062 < baseStart_1948062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948116 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1948116 : Nat := 118140960795 + 1948116 * 2 ^ 59
def prefixEnd_1948116 : Nat := 4983230072969 + 3 ^ 40 * 1948116 * 2
def baseEnd_1948116 : Nat := 666879919142936813927189

theorem tailTrace_1948116 : CollatzResearch.WordTrace tailWord_1948116 prefixEnd_1948116 666879919142936813927189 := by
  unfold tailWord_1948116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35526813905157959284688101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47369085206877279046250801 35526813905157959284688101)
  ·
    refine ⟨6661277607217117365879019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35526813905157959284688101 6661277607217117365879019)
    ·
      refine ⟨9991916410825676048818529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661277607217117365879019 9991916410825676048818529)
      ·
        refine ⟨7493937308119257036613897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9991916410825676048818529 7493937308119257036613897)
        ·
          refine ⟨5620452981089442777460423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7493937308119257036613897 5620452981089442777460423)
          ·
            refine ⟨8430679471634164166190635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620452981089442777460423 8430679471634164166190635)
            ·
              refine ⟨12646019207451246249285953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430679471634164166190635 12646019207451246249285953)
              ·
                refine ⟨9484514405588434686964465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12646019207451246249285953 9484514405588434686964465)
                ·
                  refine ⟨7113385804191326015223349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9484514405588434686964465 7113385804191326015223349)
                  ·
                    refine ⟨666879919142936813927189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7113385804191326015223349 666879919142936813927189)
                    ·
                      rfl

theorem cell22_1948116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1948116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948116 prefixEnd_1948116 := by exact prefixLift 1948116
  have htrace : WordTrace (prefixWord ++ tailWord_1948116) baseStart_1948116 baseEnd_1948116 := by
    simpa [prefixWord, tailWord_1948116, baseEnd_1948116] using wordTrace_append hprefix tailTrace_1948116
  have hstable : (prefixWord ++ tailWord_1948116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948116).length < 2 ^ (prefixWord ++ tailWord_1948116).sum := by decide
  have hdescent : baseEnd_1948116 < baseStart_1948116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948159 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_1948159 : Nat := 118140960795 + 1948159 * 2 ^ 59
def prefixEnd_1948159 : Nat := 4983230072969 + 3 ^ 40 * 1948159 * 2
def baseEnd_1948159 : Nat := 666894638921699035102057

theorem tailTrace_1948159 : CollatzResearch.WordTrace tailWord_1948159 prefixEnd_1948159 666894638921699035102057 := by
  unfold tailWord_1948159
  simp only [CollatzResearch.WordTrace]
  refine ⟨71055196149160136913191531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47370130766106757942127687 71055196149160136913191531)
  ·
    refine ⟨106582794223740205369787297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71055196149160136913191531 106582794223740205369787297)
    ·
      refine ⟨79937095667805154027340473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106582794223740205369787297 79937095667805154027340473)
      ·
        refine ⟨59952821750853865520505355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79937095667805154027340473 59952821750853865520505355)
        ·
          refine ⟨89929232626280798280758033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59952821750853865520505355 89929232626280798280758033)
          ·
            refine ⟨67446924469710598710568525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89929232626280798280758033 67446924469710598710568525)
            ·
              refine ⟨25292596676141474516463197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67446924469710598710568525 25292596676141474516463197)
              ·
                refine ⟨9484723753553052943673699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25292596676141474516463197 9484723753553052943673699)
                ·
                  refine ⟨14227085630329579415510549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9484723753553052943673699 14227085630329579415510549)
                  ·
                    refine ⟨666894638921699035102057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14227085630329579415510549 666894638921699035102057)
                    ·
                      rfl

theorem cell22_1948159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_1948159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948159 prefixEnd_1948159 := by exact prefixLift 1948159
  have htrace : WordTrace (prefixWord ++ tailWord_1948159) baseStart_1948159 baseEnd_1948159 := by
    simpa [prefixWord, tailWord_1948159, baseEnd_1948159] using wordTrace_append hprefix tailTrace_1948159
  have hstable : (prefixWord ++ tailWord_1948159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948159).length < 2 ^ (prefixWord ++ tailWord_1948159).sum := by decide
  have hdescent : baseEnd_1948159 < baseStart_1948159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948180 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1948180 : Nat := 118140960795 + 1948180 * 2 ^ 59
def prefixEnd_1948180 : Nat := 4983230072969 + 3 ^ 40 * 1948180 * 2
def baseEnd_1948180 : Nat := 222300609216953993442331

theorem tailTrace_1948180 : CollatzResearch.WordTrace tailWord_1948180 prefixEnd_1948180 222300609216953993442331 := by
  unfold tailWord_1948180
  simp only [CollatzResearch.WordTrace]
  refine ⟨35527981041042028749852997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47370641388056038333137329 35527981041042028749852997)
  ·
    refine ⟨6661496445195380390597437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35527981041042028749852997 6661496445195380390597437)
    ·
      refine ⟨2498061166948267646474039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6661496445195380390597437 2498061166948267646474039)
      ·
        refine ⟨3747091750422401469711059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498061166948267646474039 3747091750422401469711059)
        ·
          refine ⟨5620637625633602204566589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747091750422401469711059 5620637625633602204566589)
          ·
            refine ⟨2107739109612600826712471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5620637625633602204566589 2107739109612600826712471)
            ·
              refine ⟨3161608664418901240068707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107739109612600826712471 3161608664418901240068707)
              ·
                refine ⟨4742412996628351860103061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161608664418901240068707 4742412996628351860103061)
                ·
                  refine ⟨222300609216953993442331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4742412996628351860103061 222300609216953993442331)
                  ·
                    rfl

theorem cell22_1948180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1948180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948180 prefixEnd_1948180 := by exact prefixLift 1948180
  have htrace : WordTrace (prefixWord ++ tailWord_1948180) baseStart_1948180 baseEnd_1948180 := by
    simpa [prefixWord, tailWord_1948180, baseEnd_1948180] using wordTrace_append hprefix tailTrace_1948180
  have hstable : (prefixWord ++ tailWord_1948180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948180).length < 2 ^ (prefixWord ++ tailWord_1948180).sum := by decide
  have hdescent : baseEnd_1948180 < baseStart_1948180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948195 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 2, 3]
def baseStart_1948195 : Nat := 118140960795 + 1948195 * 2 ^ 59
def prefixEnd_1948195 : Nat := 4983230072969 + 3 ^ 40 * 1948195 * 2
def baseEnd_1948195 : Nat := 666906962457406941201947

theorem tailTrace_1948195 : CollatzResearch.WordTrace tailWord_1948195 prefixEnd_1948195 666906962457406941201947 := by
  unfold tailWord_1948195
  simp only [CollatzResearch.WordTrace]
  refine ⟨71056509177029715061502039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47371006118019810041001359 71056509177029715061502039)
  ·
    refine ⟨106584763765544572592253059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71056509177029715061502039 106584763765544572592253059)
    ·
      refine ⟨159877145648316858888379589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106584763765544572592253059 159877145648316858888379589)
      ·
        refine ⟨29976964809059411041571173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159877145648316858888379589 29976964809059411041571173)
        ·
          refine ⟨5620680901698639570294595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29976964809059411041571173 5620680901698639570294595)
          ·
            refine ⟨8431021352547959355441893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620680901698639570294595 8431021352547959355441893)
            ·
              refine ⟨1580816503602742379145355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8431021352547959355441893 1580816503602742379145355)
              ·
                refine ⟨2371224755404113568718033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580816503602742379145355 2371224755404113568718033)
                ·
                  refine ⟨1778418566553085176538525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2371224755404113568718033 1778418566553085176538525)
                  ·
                    refine ⟨666906962457406941201947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778418566553085176538525 666906962457406941201947)
                    ·
                      rfl

theorem cell22_1948195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 3].length) (baseStart_1948195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948195 prefixEnd_1948195 := by exact prefixLift 1948195
  have htrace : WordTrace (prefixWord ++ tailWord_1948195) baseStart_1948195 baseEnd_1948195 := by
    simpa [prefixWord, tailWord_1948195, baseEnd_1948195] using wordTrace_append hprefix tailTrace_1948195
  have hstable : (prefixWord ++ tailWord_1948195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948195).length < 2 ^ (prefixWord ++ tailWord_1948195).sum := by decide
  have hdescent : baseEnd_1948195 < baseStart_1948195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948199 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1948199 : Nat := 118140960795 + 1948199 * 2 ^ 59
def prefixEnd_1948199 : Nat := 4983230072969 + 3 ^ 40 * 1948199 * 2
def baseEnd_1948199 : Nat := 666908331739152264101935

theorem tailTrace_1948199 : CollatzResearch.WordTrace tailWord_1948199 prefixEnd_1948199 666908331739152264101935 := by
  unfold tailWord_1948199
  simp only [CollatzResearch.WordTrace]
  refine ⟨71056655069015223744647651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47371103379343482496431767 71056655069015223744647651)
  ·
    refine ⟨106584982603522835616971477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71056655069015223744647651 106584982603522835616971477)
    ·
      refine ⟨2498085529770066459772769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 106584982603522835616971477 2498085529770066459772769)
      ·
        refine ⟨1873564147327549844829577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2498085529770066459772769 1873564147327549844829577)
        ·
          refine ⟨1405173110495662383622183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873564147327549844829577 1405173110495662383622183)
          ·
            refine ⟨2107759665743493575433275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405173110495662383622183 2107759665743493575433275)
            ·
              refine ⟨3161639498615240363149913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107759665743493575433275 3161639498615240363149913)
              ·
                refine ⟨2371229623961430272362435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161639498615240363149913 2371229623961430272362435)
                ·
                  refine ⟨3556844435942145408543653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371229623961430272362435 3556844435942145408543653)
                  ·
                    refine ⟨666908331739152264101935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3556844435942145408543653 666908331739152264101935)
                    ·
                      rfl

theorem cell22_1948199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1948199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948199 prefixEnd_1948199 := by exact prefixLift 1948199
  have htrace : WordTrace (prefixWord ++ tailWord_1948199) baseStart_1948199 baseEnd_1948199 := by
    simpa [prefixWord, tailWord_1948199, baseEnd_1948199] using wordTrace_append hprefix tailTrace_1948199
  have hstable : (prefixWord ++ tailWord_1948199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948199).length < 2 ^ (prefixWord ++ tailWord_1948199).sum := by decide
  have hdescent : baseEnd_1948199 < baseStart_1948199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948311 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1948311 : Nat := 118140960795 + 1948311 * 2 ^ 59
def prefixEnd_1948311 : Nat := 4983230072969 + 3 ^ 40 * 1948311 * 2
def baseEnd_1948311 : Nat := 666946671628021305301591

theorem tailTrace_1948311 : CollatzResearch.WordTrace tailWord_1948311 prefixEnd_1948311 666946671628021305301591 := by
  unfold tailWord_1948311
  simp only [CollatzResearch.WordTrace]
  refine ⟨71060740044609466872724787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47373826696406311248483191 71060740044609466872724787)
  ·
    refine ⟨106591110066914200309087181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71060740044609466872724787 106591110066914200309087181)
    ·
      refine ⟨39971666275092825115907693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106591110066914200309087181 39971666275092825115907693)
      ·
        refine ⟨14989374853159809418465385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39971666275092825115907693 14989374853159809418465385)
        ·
          refine ⟨11242031139869857063849039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14989374853159809418465385 11242031139869857063849039)
          ·
            refine ⟨16863046709804785595773559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11242031139869857063849039 16863046709804785595773559)
            ·
              refine ⟨25294570064707178393660339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16863046709804785595773559 25294570064707178393660339)
              ·
                refine ⟨37941855097060767590490509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25294570064707178393660339 37941855097060767590490509)
                ·
                  refine ⟨14228195661397787846433941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37941855097060767590490509 14228195661397787846433941)
                  ·
                    refine ⟨666946671628021305301591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14228195661397787846433941 666946671628021305301591)
                    ·
                      rfl

theorem cell22_1948311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1948311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948311 prefixEnd_1948311 := by exact prefixLift 1948311
  have htrace : WordTrace (prefixWord ++ tailWord_1948311) baseStart_1948311 baseEnd_1948311 := by
    simpa [prefixWord, tailWord_1948311, baseEnd_1948311] using wordTrace_append hprefix tailTrace_1948311
  have hstable : (prefixWord ++ tailWord_1948311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948311).length < 2 ^ (prefixWord ++ tailWord_1948311).sum := by decide
  have hdescent : baseEnd_1948311 < baseStart_1948311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948343 : List Nat := [1, 1, 3, 1, 6, 2, 8]
def baseStart_1948343 : Nat := 118140960795 + 1948343 * 2 ^ 59
def prefixEnd_1948343 : Nat := 4983230072969 + 3 ^ 40 * 1948343 * 2
def baseEnd_1948343 : Nat := 24702134291925329203759

theorem tailTrace_1948343 : CollatzResearch.WordTrace tailWord_1948343 prefixEnd_1948343 24702134291925329203759 := by
  unfold tailWord_1948343
  simp only [CollatzResearch.WordTrace]
  refine ⟨71061907180493536337889683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47374604786995690891926455 71061907180493536337889683)
  ·
    refine ⟨106592860770740304506834525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71061907180493536337889683 106592860770740304506834525)
    ·
      refine ⟨39972322789027614190062947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106592860770740304506834525 39972322789027614190062947)
      ·
        refine ⟨59958484183541421285094421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39972322789027614190062947 59958484183541421285094421)
        ·
          refine ⟨2810553946103504122738801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59958484183541421285094421 2810553946103504122738801)
          ·
            refine ⟨2107915459577628092054101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810553946103504122738801 2107915459577628092054101)
            ·
              refine ⟨24702134291925329203759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2107915459577628092054101 24702134291925329203759)
              ·
                rfl

theorem cell22_1948343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 8].length) (baseStart_1948343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948343 prefixEnd_1948343 := by exact prefixLift 1948343
  have htrace : WordTrace (prefixWord ++ tailWord_1948343) baseStart_1948343 baseEnd_1948343 := by
    simpa [prefixWord, tailWord_1948343, baseEnd_1948343] using wordTrace_append hprefix tailTrace_1948343
  have hstable : (prefixWord ++ tailWord_1948343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948343).length < 2 ^ (prefixWord ++ tailWord_1948343).sum := by decide
  have hdescent : baseEnd_1948343 < baseStart_1948343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948364 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_1948364 : Nat := 118140960795 + 1948364 * 2 ^ 59
def prefixEnd_1948364 : Nat := 4983230072969 + 3 ^ 40 * 1948364 * 2
def baseEnd_1948364 : Nat := 666964814611146833726429

theorem tailTrace_1948364 : CollatzResearch.WordTrace tailWord_1948364 prefixEnd_1948364 666964814611146833726429 := by
  unfold tailWord_1948364
  simp only [CollatzResearch.WordTrace]
  refine ⟨35531336556708728462202073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47375115408944971282936097 35531336556708728462202073)
  ·
    refine ⟨26648502417531546346651555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35531336556708728462202073 26648502417531546346651555)
    ·
      refine ⟨39972753626297319519977333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26648502417531546346651555 39972753626297319519977333)
      ·
        refine ⟨3747445652465373704997875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39972753626297319519977333 3747445652465373704997875)
        ·
          refine ⟨5621168478698060557496813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747445652465373704997875 5621168478698060557496813)
          ·
            refine ⟨2107938179511772709061305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5621168478698060557496813 2107938179511772709061305)
            ·
              refine ⟨1580953634633829531795979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107938179511772709061305 1580953634633829531795979)
              ·
                refine ⟨2371430451950744297693969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580953634633829531795979 2371430451950744297693969)
                ·
                  refine ⟨1778572838963058223270477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2371430451950744297693969 1778572838963058223270477)
                  ·
                    refine ⟨666964814611146833726429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778572838963058223270477 666964814611146833726429)
                    ·
                      rfl

theorem cell22_1948364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_1948364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948364 prefixEnd_1948364 := by exact prefixLift 1948364
  have htrace : WordTrace (prefixWord ++ tailWord_1948364) baseStart_1948364 baseEnd_1948364 := by
    simpa [prefixWord, tailWord_1948364, baseEnd_1948364] using wordTrace_append hprefix tailTrace_1948364
  have hstable : (prefixWord ++ tailWord_1948364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948364).length < 2 ^ (prefixWord ++ tailWord_1948364).sum := by decide
  have hdescent : baseEnd_1948364 < baseStart_1948364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948452 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1948452 : Nat := 118140960795 + 1948452 * 2 ^ 59
def prefixEnd_1948452 : Nat := 4983230072969 + 3 ^ 40 * 1948452 * 2
def baseEnd_1948452 : Nat := 666994938809543937526159

theorem tailTrace_1948452 : CollatzResearch.WordTrace tailWord_1948452 prefixEnd_1948452 666994938809543937526159 := by
  unfold tailWord_1948452
  simp only [CollatzResearch.WordTrace]
  refine ⟨35532941368549323976803805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47377255158065765302405073 35532941368549323976803805)
  ·
    refine ⟨13324853013205996491301427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35532941368549323976803805 13324853013205996491301427)
    ·
      refine ⟨19987279519808994736952141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13324853013205996491301427 19987279519808994736952141)
      ·
        refine ⟨7495229819928373026357053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19987279519808994736952141 7495229819928373026357053)
        ·
          refine ⟨2810711182473139884883895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7495229819928373026357053 2810711182473139884883895)
          ·
            refine ⟨4216066773709709827325843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810711182473139884883895 4216066773709709827325843)
            ·
              refine ⟨6324100160564564740988765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216066773709709827325843 6324100160564564740988765)
              ·
                refine ⟨2371537560211711777870787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6324100160564564740988765 2371537560211711777870787)
                ·
                  refine ⟨3557306340317567666806181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371537560211711777870787 3557306340317567666806181)
                  ·
                    refine ⟨666994938809543937526159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3557306340317567666806181 666994938809543937526159)
                    ·
                      rfl

theorem cell22_1948452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1948452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948452 prefixEnd_1948452 := by exact prefixLift 1948452
  have htrace : WordTrace (prefixWord ++ tailWord_1948452) baseStart_1948452 baseEnd_1948452 := by
    simpa [prefixWord, tailWord_1948452, baseEnd_1948452] using wordTrace_append hprefix tailTrace_1948452
  have hstable : (prefixWord ++ tailWord_1948452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948452).length < 2 ^ (prefixWord ++ tailWord_1948452).sum := by decide
  have hdescent : baseEnd_1948452 < baseStart_1948452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948465 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_1948465 : Nat := 118140960795 + 1948465 * 2 ^ 59
def prefixEnd_1948465 : Nat := 4983230072969 + 3 ^ 40 * 1948465 * 2
def baseEnd_1948465 : Nat := 666999388975216236951119

theorem tailTrace_1948465 : CollatzResearch.WordTrace tailWord_1948465 prefixEnd_1948465 666999388975216236951119 := by
  unfold tailWord_1948465
  simp only [CollatzResearch.WordTrace]
  refine ⟨71066356886051551173830849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47377571257367700782553899 71066356886051551173830849)
  ·
    refine ⟨53299767664538663380373137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71066356886051551173830849 53299767664538663380373137)
    ·
      refine ⟨39974825748403997535279853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53299767664538663380373137 39974825748403997535279853)
      ·
        refine ⟨14990559655651499075729945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39974825748403997535279853 14990559655651499075729945)
        ·
          refine ⟨11242919741738624306797459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14990559655651499075729945 11242919741738624306797459)
          ·
            refine ⟨16864379612607936460196189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11242919741738624306797459 16864379612607936460196189)
            ·
              refine ⟨6324142354727976172573571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16864379612607936460196189 6324142354727976172573571)
              ·
                refine ⟨9486213532091964258860357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324142354727976172573571 9486213532091964258860357)
                ·
                  refine ⟨1778665037267243298536317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9486213532091964258860357 1778665037267243298536317)
                  ·
                    refine ⟨666999388975216236951119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778665037267243298536317 666999388975216236951119)
                    ·
                      rfl

theorem cell22_1948465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_1948465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948465 prefixEnd_1948465 := by exact prefixLift 1948465
  have htrace : WordTrace (prefixWord ++ tailWord_1948465) baseStart_1948465 baseEnd_1948465 := by
    simpa [prefixWord, tailWord_1948465, baseEnd_1948465] using wordTrace_append hprefix tailTrace_1948465
  have hstable : (prefixWord ++ tailWord_1948465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948465).length < 2 ^ (prefixWord ++ tailWord_1948465).sum := by decide
  have hdescent : baseEnd_1948465 < baseStart_1948465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948486 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1948486 : Nat := 118140960795 + 1948486 * 2 ^ 59
def prefixEnd_1948486 : Nat := 4983230072969 + 3 ^ 40 * 1948486 * 2
def baseEnd_1948486 : Nat := 667006577704379182176055

theorem tailTrace_1948486 : CollatzResearch.WordTrace tailWord_1948486 prefixEnd_1948486 667006577704379182176055 := by
  unfold tailWord_1948486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220847588092983492510791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47378081879316981173563541 2220847588092983492510791)
  ·
    refine ⟨3331271382139475238766187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2220847588092983492510791 3331271382139475238766187)
    ·
      refine ⟨4996907073209212858149281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331271382139475238766187 4996907073209212858149281)
      ·
        refine ⟨3747680304906909643611961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4996907073209212858149281 3747680304906909643611961)
        ·
          refine ⟨2810760228680182232708971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3747680304906909643611961 2810760228680182232708971)
          ·
            refine ⟨4216140343020273349063457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810760228680182232708971 4216140343020273349063457)
            ·
              refine ⟨3162105257265205011797593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216140343020273349063457 3162105257265205011797593)
              ·
                refine ⟨2371578942948903758848195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162105257265205011797593 2371578942948903758848195)
                ·
                  refine ⟨3557368414423355638272293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371578942948903758848195 3557368414423355638272293)
                  ·
                    refine ⟨667006577704379182176055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3557368414423355638272293 667006577704379182176055)
                    ·
                      rfl

theorem cell22_1948486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1948486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948486 prefixEnd_1948486 := by exact prefixLift 1948486
  have htrace : WordTrace (prefixWord ++ tailWord_1948486) baseStart_1948486 baseEnd_1948486 := by
    simpa [prefixWord, tailWord_1948486, baseEnd_1948486] using wordTrace_append hprefix tailTrace_1948486
  have hstable : (prefixWord ++ tailWord_1948486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948486).length < 2 ^ (prefixWord ++ tailWord_1948486).sum := by decide
  have hdescent : baseEnd_1948486 < baseStart_1948486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948523 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 7]
def baseStart_1948523 : Nat := 118140960795 + 1948523 * 2 ^ 59
def prefixEnd_1948523 : Nat := 4983230072969 + 3 ^ 40 * 1948523 * 2
def baseEnd_1948523 : Nat := 222339747853507806333647

theorem tailTrace_1948523 : CollatzResearch.WordTrace tailWord_1948523 prefixEnd_1948523 222339747853507806333647 := by
  unfold tailWord_1948523
  simp only [CollatzResearch.WordTrace]
  refine ⟨71068472319841427079442223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47378981546560951386294815 71068472319841427079442223)
  ·
    refine ⟨106602708479762140619163335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71068472319841427079442223 106602708479762140619163335)
    ·
      refine ⟨159904062719643210928745003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106602708479762140619163335 159904062719643210928745003)
      ·
        refine ⟨239856094079464816393117505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159904062719643210928745003 239856094079464816393117505)
        ·
          refine ⟨179892070559598612294838129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239856094079464816393117505 179892070559598612294838129)
          ·
            refine ⟨134919052919698959221128597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179892070559598612294838129 134919052919698959221128597)
            ·
              refine ⟨6324330605610888713490403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134919052919698959221128597 6324330605610888713490403)
              ·
                refine ⟨9486495908416333070235605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324330605610888713490403 9486495908416333070235605)
                ·
                  refine ⟨222339747853507806333647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9486495908416333070235605 222339747853507806333647)
                  ·
                    rfl

theorem cell22_1948523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_1948523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948523 prefixEnd_1948523 := by exact prefixLift 1948523
  have htrace : WordTrace (prefixWord ++ tailWord_1948523) baseStart_1948523 baseEnd_1948523 := by
    simpa [prefixWord, tailWord_1948523, baseEnd_1948523] using wordTrace_append hprefix tailTrace_1948523
  have hstable : (prefixWord ++ tailWord_1948523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948523).length < 2 ^ (prefixWord ++ tailWord_1948523).sum := by decide
  have hdescent : baseEnd_1948523 < baseStart_1948523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948527 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 1, 3]
def baseStart_1948527 : Nat := 118140960795 + 1948527 * 2 ^ 59
def prefixEnd_1948527 : Nat := 4983230072969 + 3 ^ 40 * 1948527 * 2
def baseEnd_1948527 : Nat := 667020612842268741900929

theorem tailTrace_1948527 : CollatzResearch.WordTrace tailWord_1948527 prefixEnd_1948527 667020612842268741900929 := by
  unfold tailWord_1948527
  simp only [CollatzResearch.WordTrace]
  refine ⟨71068618211826935762587835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47379078807884623841725223 71068618211826935762587835)
  ·
    refine ⟨106602927317740403643881753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71068618211826935762587835 106602927317740403643881753)
    ·
      refine ⟨79952195488305302732911315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106602927317740403643881753 79952195488305302732911315)
      ·
        refine ⟨119928293232457954099366973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79952195488305302732911315 119928293232457954099366973)
        ·
          refine ⟨44973109962171732787262615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119928293232457954099366973 44973109962171732787262615)
          ·
            refine ⟨67459664943257599180893923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44973109962171732787262615 67459664943257599180893923)
            ·
              refine ⟨101189497414886398771340885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67459664943257599180893923 101189497414886398771340885)
              ·
                refine ⟨1185814422830699985601651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 101189497414886398771340885 1185814422830699985601651)
                ·
                  refine ⟨1778721634246049978402477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185814422830699985601651 1778721634246049978402477)
                  ·
                    refine ⟨667020612842268741900929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778721634246049978402477 667020612842268741900929)
                    ·
                      rfl

theorem cell22_1948527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_1948527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948527 prefixEnd_1948527 := by exact prefixLift 1948527
  have htrace : WordTrace (prefixWord ++ tailWord_1948527) baseStart_1948527 baseEnd_1948527 := by
    simpa [prefixWord, tailWord_1948527, baseEnd_1948527] using wordTrace_append hprefix tailTrace_1948527
  have hstable : (prefixWord ++ tailWord_1948527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948527).length < 2 ^ (prefixWord ++ tailWord_1948527).sum := by decide
  have hdescent : baseEnd_1948527 < baseStart_1948527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948538 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_1948538 : Nat := 118140960795 + 1948538 * 2 ^ 59
def prefixEnd_1948538 : Nat := 4983230072969 + 3 ^ 40 * 1948538 * 2
def baseEnd_1948538 : Nat := 667024378367068379875895

theorem tailTrace_1948538 : CollatzResearch.WordTrace tailWord_1948538 prefixEnd_1948538 667024378367068379875895 := by
  unfold tailWord_1948538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767254853696771160309567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47379346276524723094158845 17767254853696771160309567)
  ·
    refine ⟨26650882280545156740464351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17767254853696771160309567 26650882280545156740464351)
    ·
      refine ⟨39976323420817735110696527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26650882280545156740464351 39976323420817735110696527)
      ·
        refine ⟨59964485131226602666044791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39976323420817735110696527 59964485131226602666044791)
        ·
          refine ⟨89946727696839903999067187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59964485131226602666044791 89946727696839903999067187)
          ·
            refine ⟨134920091545259855998600781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89946727696839903999067187 134920091545259855998600781)
            ·
              refine ⟨50595034329472445999475293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134920091545259855998600781 50595034329472445999475293)
              ·
                refine ⟨18973137873552167249803235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50595034329472445999475293 18973137873552167249803235)
                ·
                  refine ⟨28459706810328250874704853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18973137873552167249803235 28459706810328250874704853)
                  ·
                    refine ⟨667024378367068379875895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28459706810328250874704853 667024378367068379875895)
                    ·
                      rfl

theorem cell22_1948538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_1948538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948538 prefixEnd_1948538 := by exact prefixLift 1948538
  have htrace : WordTrace (prefixWord ++ tailWord_1948538) baseStart_1948538 baseEnd_1948538 := by
    simpa [prefixWord, tailWord_1948538, baseEnd_1948538] using wordTrace_append hprefix tailTrace_1948538
  have hstable : (prefixWord ++ tailWord_1948538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948538).length < 2 ^ (prefixWord ++ tailWord_1948538).sum := by decide
  have hdescent : baseEnd_1948538 < baseStart_1948538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948578 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1948578 : Nat := 118140960795 + 1948578 * 2 ^ 59
def prefixEnd_1948578 : Nat := 4983230072969 + 3 ^ 40 * 1948578 * 2
def baseEnd_1948578 : Nat := 667038071184521608875773

theorem tailTrace_1948578 : CollatzResearch.WordTrace tailWord_1948578 prefixEnd_1948578 667038071184521608875773 := by
  unfold tailWord_1948578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767619583660542868173597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47380318889761447648462925 17767619583660542868173597)
  ·
    refine ⟨6662857343872703575565099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17767619583660542868173597 6662857343872703575565099)
    ·
      refine ⟨9994286015809055363347649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662857343872703575565099 9994286015809055363347649)
      ·
        refine ⟨7495714511856791522510737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9994286015809055363347649 7495714511856791522510737)
        ·
          refine ⟨5621785883892593641883053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7495714511856791522510737 5621785883892593641883053)
          ·
            refine ⟨2108169706459722615706145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5621785883892593641883053 2108169706459722615706145)
            ·
              refine ⟨1581127279844791961779609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108169706459722615706145 1581127279844791961779609)
              ·
                refine ⟨1185845459883593971334707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581127279844791961779609 1185845459883593971334707)
                ·
                  refine ⟨1778768189825390957002061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185845459883593971334707 1778768189825390957002061)
                  ·
                    refine ⟨667038071184521608875773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778768189825390957002061 667038071184521608875773)
                    ·
                      rfl

theorem cell22_1948578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1948578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948578 prefixEnd_1948578 := by exact prefixLift 1948578
  have htrace : WordTrace (prefixWord ++ tailWord_1948578) baseStart_1948578 baseEnd_1948578 := by
    simpa [prefixWord, tailWord_1948578, baseEnd_1948578] using wordTrace_append hprefix tailTrace_1948578
  have hstable : (prefixWord ++ tailWord_1948578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948578).length < 2 ^ (prefixWord ++ tailWord_1948578).sum := by decide
  have hdescent : baseEnd_1948578 < baseStart_1948578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948589 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1948589 : Nat := 118140960795 + 1948589 * 2 ^ 59
def prefixEnd_1948589 : Nat := 4983230072969 + 3 ^ 40 * 1948589 * 2
def baseEnd_1948589 : Nat := 667041836709321246850739

theorem tailTrace_1948589 : CollatzResearch.WordTrace tailWord_1948589 prefixEnd_1948589 667041836709321246850739 := by
  unfold tailWord_1948589
  simp only [CollatzResearch.WordTrace]
  refine ⟨71070879537602320351344821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47380586358401546900896547 71070879537602320351344821)
  ·
    refine ⟨6662894956650217532938577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71070879537602320351344821 6662894956650217532938577)
    ·
      refine ⟨4997171217487663149703933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6662894956650217532938577 4997171217487663149703933)
      ·
        refine ⟨1873939206557873681138975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4997171217487663149703933 1873939206557873681138975)
        ·
          refine ⟨2810908809836810521708463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873939206557873681138975 2810908809836810521708463)
          ·
            refine ⟨4216363214755215782562695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810908809836810521708463 4216363214755215782562695)
            ·
              refine ⟨6324544822132823673844043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216363214755215782562695 6324544822132823673844043)
              ·
                refine ⟨9486817233199235510766065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324544822132823673844043 9486817233199235510766065)
                ·
                  refine ⟨7115112924899426633074549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9486817233199235510766065 7115112924899426633074549)
                  ·
                    refine ⟨667041836709321246850739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7115112924899426633074549 667041836709321246850739)
                    ·
                      rfl

theorem cell22_1948589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1948589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948589 prefixEnd_1948589 := by exact prefixLift 1948589
  have htrace : WordTrace (prefixWord ++ tailWord_1948589) baseStart_1948589 baseEnd_1948589 := by
    simpa [prefixWord, tailWord_1948589, baseEnd_1948589] using wordTrace_append hprefix tailTrace_1948589
  have hstable : (prefixWord ++ tailWord_1948589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948589).length < 2 ^ (prefixWord ++ tailWord_1948589).sum := by decide
  have hdescent : baseEnd_1948589 < baseStart_1948589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948600 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_1948600 : Nat := 118140960795 + 1948600 * 2 ^ 59
def prefixEnd_1948600 : Nat := 4983230072969 + 3 ^ 40 * 1948600 * 2
def baseEnd_1948600 : Nat := 667045602234120884825705

theorem tailTrace_1948600 : CollatzResearch.WordTrace tailWord_1948600 prefixEnd_1948600 667045602234120884825705 := by
  unfold tailWord_1948600
  simp only [CollatzResearch.WordTrace]
  refine ⟨35535640370281234614997627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47380853827041646153330169 35535640370281234614997627)
  ·
    refine ⟨53303460555421851922496441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35535640370281234614997627 53303460555421851922496441)
    ·
      refine ⟨39977595416566388941872331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53303460555421851922496441 39977595416566388941872331)
      ·
        refine ⟨59966393124849583412808497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39977595416566388941872331 59966393124849583412808497)
        ·
          refine ⟨44974794843637187559606373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59966393124849583412808497 44974794843637187559606373)
          ·
            refine ⟨8432774033181972667426195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44974794843637187559606373 8432774033181972667426195)
            ·
              refine ⟨12649161049772959001139293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8432774033181972667426195 12649161049772959001139293)
              ·
                refine ⟨4743435393664859625427235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12649161049772959001139293 4743435393664859625427235)
                ·
                  refine ⟨7115153090497289438140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743435393664859625427235 7115153090497289438140853)
                  ·
                    refine ⟨667045602234120884825705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7115153090497289438140853 667045602234120884825705)
                    ·
                      rfl

theorem cell22_1948600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_1948600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948600 prefixEnd_1948600 := by exact prefixLift 1948600
  have htrace : WordTrace (prefixWord ++ tailWord_1948600) baseStart_1948600 baseEnd_1948600 := by
    simpa [prefixWord, tailWord_1948600, baseEnd_1948600] using wordTrace_append hprefix tailTrace_1948600
  have hstable : (prefixWord ++ tailWord_1948600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948600).length < 2 ^ (prefixWord ++ tailWord_1948600).sum := by decide
  have hdescent : baseEnd_1948600 < baseStart_1948600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948634 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_1948634 : Nat := 118140960795 + 1948634 * 2 ^ 59
def prefixEnd_1948634 : Nat := 4983230072969 + 3 ^ 40 * 1948634 * 2
def baseEnd_1948634 : Nat := 667057241128956129475601

theorem tailTrace_1948634 : CollatzResearch.WordTrace tailWord_1948634 prefixEnd_1948634 667057241128956129475601 := by
  unfold tailWord_1948634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768130205609823259183239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47381680548292862024488637 17768130205609823259183239)
  ·
    refine ⟨26652195308414734888774859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17768130205609823259183239 26652195308414734888774859)
    ·
      refine ⟨39978292962622102333162289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26652195308414734888774859 39978292962622102333162289)
      ·
        refine ⟨29983719721966576749871717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39978292962622102333162289 29983719721966576749871717)
        ·
          refine ⟨5621947447868733140600947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29983719721966576749871717 5621947447868733140600947)
          ·
            refine ⟨8432921171803099710901421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621947447868733140600947 8432921171803099710901421)
            ·
              refine ⟨3162345439426162391588033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8432921171803099710901421 3162345439426162391588033)
              ·
                refine ⟨2371759079569621793691025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162345439426162391588033 2371759079569621793691025)
                ·
                  refine ⟨1778819309677216345268269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2371759079569621793691025 1778819309677216345268269)
                  ·
                    refine ⟨667057241128956129475601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778819309677216345268269 667057241128956129475601)
                    ·
                      rfl

theorem cell22_1948634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_1948634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948634 prefixEnd_1948634 := by exact prefixLift 1948634
  have htrace : WordTrace (prefixWord ++ tailWord_1948634) baseStart_1948634 baseEnd_1948634 := by
    simpa [prefixWord, tailWord_1948634, baseEnd_1948634] using wordTrace_append hprefix tailTrace_1948634
  have hstable : (prefixWord ++ tailWord_1948634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948634).length < 2 ^ (prefixWord ++ tailWord_1948634).sum := by decide
  have hdescent : baseEnd_1948634 < baseStart_1948634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948720 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_1948720 : Nat := 118140960795 + 1948720 * 2 ^ 59
def prefixEnd_1948720 : Nat := 4983230072969 + 3 ^ 40 * 1948720 * 2
def baseEnd_1948720 : Nat := 222362226895493523941779

theorem tailTrace_1948720 : CollatzResearch.WordTrace tailWord_1948720 prefixEnd_1948720 222362226895493523941779 := by
  unfold tailWord_1948720
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537828750063864862181807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47383771666751819816242409 35537828750063864862181807)
  ·
    refine ⟨53306743125095797293272711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35537828750063864862181807 53306743125095797293272711)
    ·
      refine ⟨79960114687643695939909067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53306743125095797293272711 79960114687643695939909067)
      ·
        refine ⟨119940172031465543909863601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79960114687643695939909067 119940172031465543909863601)
        ·
          refine ⟨89955129023599157932397701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119940172031465543909863601 89955129023599157932397701)
          ·
            refine ⟨16866586691924842112324569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89955129023599157932397701 16866586691924842112324569)
            ·
              refine ⟨12649940018943631584243427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16866586691924842112324569 12649940018943631584243427)
              ·
                refine ⟨18974910028415447376365141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12649940018943631584243427 18974910028415447376365141)
                ·
                  refine ⟨222362226895493523941779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18974910028415447376365141 222362226895493523941779)
                  ·
                    rfl

theorem cell22_1948720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_1948720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948720 prefixEnd_1948720 := by exact prefixLift 1948720
  have htrace : WordTrace (prefixWord ++ tailWord_1948720) baseStart_1948720 baseEnd_1948720 := by
    simpa [prefixWord, tailWord_1948720, baseEnd_1948720] using wordTrace_append hprefix tailTrace_1948720
  have hstable : (prefixWord ++ tailWord_1948720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948720).length < 2 ^ (prefixWord ++ tailWord_1948720).sum := by decide
  have hdescent : baseEnd_1948720 < baseStart_1948720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948722 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1948722 : Nat := 118140960795 + 1948722 * 2 ^ 59
def prefixEnd_1948722 : Nat := 4983230072969 + 3 ^ 40 * 1948722 * 2
def baseEnd_1948722 : Nat := 667087365327353233275331

theorem tailTrace_1948722 : CollatzResearch.WordTrace tailWord_1948722 prefixEnd_1948722 667087365327353233275331 := by
  unfold tailWord_1948722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768932611530121016484105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47383820297413656043957613 17768932611530121016484105)
  ·
    refine ⟨13326699458647590762363079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17768932611530121016484105 13326699458647590762363079)
    ·
      refine ⟨19990049187971386143544619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13326699458647590762363079 19990049187971386143544619)
      ·
        refine ⟨29985073781957079215316929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19990049187971386143544619 29985073781957079215316929)
        ·
          refine ⟨22488805336467809411487697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29985073781957079215316929 22488805336467809411487697)
          ·
            refine ⟨16866604002350857058615773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22488805336467809411487697 16866604002350857058615773)
            ·
              refine ⟨6324976500881571396980915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16866604002350857058615773 6324976500881571396980915)
              ·
                refine ⟨9487464751322357095471373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324976500881571396980915 9487464751322357095471373)
                ·
                  refine ⟨3557799281745883910801765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9487464751322357095471373 3557799281745883910801765)
                  ·
                    refine ⟨667087365327353233275331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3557799281745883910801765 667087365327353233275331)
                    ·
                      rfl

theorem cell22_1948722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1948722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948722 prefixEnd_1948722 := by exact prefixLift 1948722
  have htrace : WordTrace (prefixWord ++ tailWord_1948722) baseStart_1948722 baseEnd_1948722 := by
    simpa [prefixWord, tailWord_1948722, baseEnd_1948722] using wordTrace_append hprefix tailTrace_1948722
  have hstable : (prefixWord ++ tailWord_1948722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948722).length < 2 ^ (prefixWord ++ tailWord_1948722).sum := by decide
  have hdescent : baseEnd_1948722 < baseStart_1948722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948739 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 1, 4]
def baseStart_1948739 : Nat := 118140960795 + 1948739 * 2 ^ 59
def prefixEnd_1948739 : Nat := 4983230072969 + 3 ^ 40 * 1948739 * 2
def baseEnd_1948739 : Nat := 667093184774770855600279

theorem tailTrace_1948739 : CollatzResearch.WordTrace tailWord_1948739 prefixEnd_1948739 667093184774770855600279 := by
  unfold tailWord_1948739
  simp only [CollatzResearch.WordTrace]
  refine ⟨71076350487058895969305271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47384233658039263979536847 71076350487058895969305271)
  ·
    refine ⟨106614525730588343953957907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71076350487058895969305271 106614525730588343953957907)
    ·
      refine ⟨159921788595882515930936861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106614525730588343953957907 159921788595882515930936861)
      ·
        refine ⟨59970670723455943474101323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159921788595882515930936861 59970670723455943474101323)
        ·
          refine ⟨89956006085183915211151985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59970670723455943474101323 89956006085183915211151985)
          ·
            refine ⟨67467004563887936408363989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89956006085183915211151985 67467004563887936408363989)
            ·
              refine ⟨1581257919466123509571031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67467004563887936408363989 1581257919466123509571031)
              ·
                refine ⟨2371886879199185264356547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581257919466123509571031 2371886879199185264356547)
                ·
                  refine ⟨3557830318798777896534821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371886879199185264356547 3557830318798777896534821)
                  ·
                    refine ⟨667093184774770855600279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3557830318798777896534821 667093184774770855600279)
                    ·
                      rfl

theorem cell22_1948739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 4].length) (baseStart_1948739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948739 prefixEnd_1948739 := by exact prefixLift 1948739
  have htrace : WordTrace (prefixWord ++ tailWord_1948739) baseStart_1948739 baseEnd_1948739 := by
    simpa [prefixWord, tailWord_1948739, baseEnd_1948739] using wordTrace_append hprefix tailTrace_1948739
  have hstable : (prefixWord ++ tailWord_1948739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948739).length < 2 ^ (prefixWord ++ tailWord_1948739).sum := by decide
  have hdescent : baseEnd_1948739 < baseStart_1948739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948752 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_1948752 : Nat := 118140960795 + 1948752 * 2 ^ 59
def prefixEnd_1948752 : Nat := 4983230072969 + 3 ^ 40 * 1948752 * 2
def baseEnd_1948752 : Nat := 667097634940443155025239

theorem tailTrace_1948752 : CollatzResearch.WordTrace tailWord_1948752 prefixEnd_1948752 667097634940443155025239 := by
  unfold tailWord_1948752
  simp only [CollatzResearch.WordTrace]
  refine ⟨35538412318005899594764255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47384549757341199459685673 35538412318005899594764255)
  ·
    refine ⟨53307618477008849392146383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35538412318005899594764255 53307618477008849392146383)
    ·
      refine ⟨79961427715513274088219575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53307618477008849392146383 79961427715513274088219575)
      ·
        refine ⟨119942141573269911132329363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79961427715513274088219575 119942141573269911132329363)
        ·
          refine ⟨179913212359904866698494045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119942141573269911132329363 179913212359904866698494045)
          ·
            refine ⟨67467454634964325011935267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179913212359904866698494045 67467454634964325011935267)
            ·
              refine ⟨101201181952446487517902901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67467454634964325011935267 101201181952446487517902901)
              ·
                refine ⟨9487610808041858204803397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101201181952446487517902901 9487610808041858204803397)
                ·
                  refine ⟨1778927026507848413400637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9487610808041858204803397 1778927026507848413400637)
                  ·
                    refine ⟨667097634940443155025239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778927026507848413400637 667097634940443155025239)
                    ·
                      rfl

theorem cell22_1948752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_1948752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948752 prefixEnd_1948752 := by exact prefixLift 1948752
  have htrace : WordTrace (prefixWord ++ tailWord_1948752) baseStart_1948752 baseEnd_1948752 := by
    simpa [prefixWord, tailWord_1948752, baseEnd_1948752] using wordTrace_append hprefix tailTrace_1948752
  have hstable : (prefixWord ++ tailWord_1948752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948752).length < 2 ^ (prefixWord ++ tailWord_1948752).sum := by decide
  have hdescent : baseEnd_1948752 < baseStart_1948752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948769 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1948769 : Nat := 118140960795 + 1948769 * 2 ^ 59
def prefixEnd_1948769 : Nat := 4983230072969 + 3 ^ 40 * 1948769 * 2
def baseEnd_1948769 : Nat := 667103454387860777350187

theorem tailTrace_1948769 : CollatzResearch.WordTrace tailWord_1948769 prefixEnd_1948769 667103454387860777350187 := by
  unfold tailWord_1948769
  simp only [CollatzResearch.WordTrace]
  refine ⟨71077444676950211092897361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47384963117966807395264907 71077444676950211092897361)
  ·
    refine ⟨53308083507712658319673021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71077444676950211092897361 53308083507712658319673021)
    ·
      refine ⟨19990531315392246869877383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53308083507712658319673021 19990531315392246869877383)
      ·
        refine ⟨29985796973088370304816075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19990531315392246869877383 29985796973088370304816075)
        ·
          refine ⟨44978695459632555457224113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29985796973088370304816075 44978695459632555457224113)
          ·
            refine ⟨33734021594724416592918085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44978695459632555457224113 33734021594724416592918085)
            ·
              refine ⟨6325129049010828111172141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33734021594724416592918085 6325129049010828111172141)
              ·
                refine ⟨2371923393379060541689553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6325129049010828111172141 2371923393379060541689553)
                ·
                  refine ⟨1778942545034295406267165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2371923393379060541689553 1778942545034295406267165)
                  ·
                    refine ⟨667103454387860777350187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778942545034295406267165 667103454387860777350187)
                    ·
                      rfl

theorem cell22_1948769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1948769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948769 prefixEnd_1948769 := by exact prefixLift 1948769
  have htrace : WordTrace (prefixWord ++ tailWord_1948769) baseStart_1948769 baseEnd_1948769 := by
    simpa [prefixWord, tailWord_1948769, baseEnd_1948769] using wordTrace_append hprefix tailTrace_1948769
  have hstable : (prefixWord ++ tailWord_1948769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948769).length < 2 ^ (prefixWord ++ tailWord_1948769).sum := by decide
  have hdescent : baseEnd_1948769 < baseStart_1948769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948878 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_1948878 : Nat := 118140960795 + 1948878 * 2 ^ 59
def prefixEnd_1948878 : Nat := 4983230072969 + 3 ^ 40 * 1948878 * 2
def baseEnd_1948878 : Nat := 222380255771806942124951

theorem tailTrace_1948878 : CollatzResearch.WordTrace tailWord_1948878 prefixEnd_1948878 222380255771806942124951 := by
  unfold tailWord_1948878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885177529194415338576911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47387613489036881805743525 8885177529194415338576911)
  ·
    refine ⟨13327766293791623007865367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8885177529194415338576911 13327766293791623007865367)
    ·
      refine ⟨19991649440687434511798051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13327766293791623007865367 19991649440687434511798051)
      ·
        refine ⟨29987474161031151767697077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19991649440687434511798051 29987474161031151767697077)
        ·
          refine ⟨2811325702596670478221601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29987474161031151767697077 2811325702596670478221601)
          ·
            refine ⟨2108494276947502858666201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811325702596670478221601 2108494276947502858666201)
            ·
              refine ⟨1581370707710627143999651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108494276947502858666201 1581370707710627143999651)
              ·
                refine ⟨2372056061565940715999477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581370707710627143999651 2372056061565940715999477)
                ·
                  refine ⟨222380255771806942124951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372056061565940715999477 222380255771806942124951)
                  ·
                    rfl

theorem cell22_1948878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_1948878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948878 prefixEnd_1948878 := by exact prefixLift 1948878
  have htrace : WordTrace (prefixWord ++ tailWord_1948878) baseStart_1948878 baseEnd_1948878 := by
    simpa [prefixWord, tailWord_1948878, baseEnd_1948878] using wordTrace_append hprefix tailTrace_1948878
  have hstable : (prefixWord ++ tailWord_1948878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948878).length < 2 ^ (prefixWord ++ tailWord_1948878).sum := by decide
  have hdescent : baseEnd_1948878 < baseStart_1948878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948904 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1948904 : Nat := 118140960795 + 1948904 * 2 ^ 59
def prefixEnd_1948904 : Nat := 4983230072969 + 3 ^ 40 * 1948904 * 2
def baseEnd_1948904 : Nat := 667149667646765425224773

theorem tailTrace_1948904 : CollatzResearch.WordTrace tailWord_1948904 prefixEnd_1948904 667149667646765425224773 := by
  unfold tailWord_1948904
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541184265730564574530883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47388245687640752766041177 35541184265730564574530883)
  ·
    refine ⟨53311776398595846861796325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35541184265730564574530883 53311776398595846861796325)
    ·
      refine ⟨9995958074736721286586811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53311776398595846861796325 9995958074736721286586811)
      ·
        refine ⟨14993937112105081929880217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9995958074736721286586811 14993937112105081929880217)
        ·
          refine ⟨11245452834078811447410163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14993937112105081929880217 11245452834078811447410163)
          ·
            refine ⟨16868179251118217171115245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11245452834078811447410163 16868179251118217171115245)
            ·
              refine ⟨6325567219169331439168217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16868179251118217171115245 6325567219169331439168217)
              ·
                refine ⟨4744175414376998579376163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6325567219169331439168217 4744175414376998579376163)
                ·
                  refine ⟨7116263121565497869064245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744175414376998579376163 7116263121565497869064245)
                  ·
                    refine ⟨667149667646765425224773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7116263121565497869064245 667149667646765425224773)
                    ·
                      rfl

theorem cell22_1948904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1948904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948904 prefixEnd_1948904 := by exact prefixLift 1948904
  have htrace : WordTrace (prefixWord ++ tailWord_1948904) baseStart_1948904 baseEnd_1948904 := by
    simpa [prefixWord, tailWord_1948904, baseEnd_1948904] using wordTrace_append hprefix tailTrace_1948904
  have hstable : (prefixWord ++ tailWord_1948904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948904).length < 2 ^ (prefixWord ++ tailWord_1948904).sum := by decide
  have hdescent : baseEnd_1948904 < baseStart_1948904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948916 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1948916 : Nat := 118140960795 + 1948916 * 2 ^ 59
def prefixEnd_1948916 : Nat := 4983230072969 + 3 ^ 40 * 1948916 * 2
def baseEnd_1948916 : Nat := 667153775492001393924737

theorem tailTrace_1948916 : CollatzResearch.WordTrace tailWord_1948916 prefixEnd_1948916 667153775492001393924737 := by
  unfold tailWord_1948916
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541403103708827599249301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47388537471611770132332401 35541403103708827599249301)
  ·
    refine ⟨1666003270486351293714811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35541403103708827599249301 1666003270486351293714811)
    ·
      refine ⟨2499004905729526940572217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666003270486351293714811 2499004905729526940572217)
      ·
        refine ⟨1874253679297145205429163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2499004905729526940572217 1874253679297145205429163)
        ·
          refine ⟨2811380518945717808143745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874253679297145205429163 2811380518945717808143745)
          ·
            refine ⟨2108535389209288356107809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811380518945717808143745 2108535389209288356107809)
            ·
              refine ⟨1581401541906966267080857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108535389209288356107809 1581401541906966267080857)
              ·
                refine ⟨1186051156430224700310643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581401541906966267080857 1186051156430224700310643)
                ·
                  refine ⟨1779076734645337050465965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186051156430224700310643 1779076734645337050465965)
                  ·
                    refine ⟨667153775492001393924737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779076734645337050465965 667153775492001393924737)
                    ·
                      rfl

theorem cell22_1948916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1948916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948916 prefixEnd_1948916 := by exact prefixLift 1948916
  have htrace : WordTrace (prefixWord ++ tailWord_1948916) baseStart_1948916 baseEnd_1948916 := by
    simpa [prefixWord, tailWord_1948916, baseEnd_1948916] using wordTrace_append hprefix tailTrace_1948916
  have hstable : (prefixWord ++ tailWord_1948916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948916).length < 2 ^ (prefixWord ++ tailWord_1948916).sum := by decide
  have hdescent : baseEnd_1948916 < baseStart_1948916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948921 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_1948921 : Nat := 118140960795 + 1948921 * 2 ^ 59
def prefixEnd_1948921 : Nat := 4983230072969 + 3 ^ 40 * 1948921 * 2
def baseEnd_1948921 : Nat := 667155487094183047549721

theorem tailTrace_1948921 : CollatzResearch.WordTrace tailWord_1948921 prefixEnd_1948921 667155487094183047549721 := by
  unfold tailWord_1948921
  simp only [CollatzResearch.WordTrace]
  refine ⟨71082988572399541052430617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47388659048266360701620411 71082988572399541052430617)
  ·
    refine ⟨53312241429299655789322963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71082988572399541052430617 53312241429299655789322963)
    ·
      refine ⟨79968362143949483683984445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53312241429299655789322963 79968362143949483683984445)
      ·
        refine ⟨29988135803981056381494167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79968362143949483683984445 29988135803981056381494167)
        ·
          refine ⟨44982203705971584572241251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29988135803981056381494167 44982203705971584572241251)
          ·
            refine ⟨67473305558957376858361877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44982203705971584572241251 67473305558957376858361877)
            ·
              refine ⟨3162811198076127040235713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67473305558957376858361877 3162811198076127040235713)
              ·
                refine ⟨2372108398557095280176785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162811198076127040235713 2372108398557095280176785)
                ·
                  refine ⟨1779081298917821460132589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372108398557095280176785 1779081298917821460132589)
                  ·
                    refine ⟨667155487094183047549721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779081298917821460132589 667155487094183047549721)
                    ·
                      rfl

theorem cell22_1948921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_1948921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948921 prefixEnd_1948921 := by exact prefixLift 1948921
  have htrace : WordTrace (prefixWord ++ tailWord_1948921) baseStart_1948921 baseEnd_1948921 := by
    simpa [prefixWord, tailWord_1948921, baseEnd_1948921] using wordTrace_append hprefix tailTrace_1948921
  have hstable : (prefixWord ++ tailWord_1948921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948921).length < 2 ^ (prefixWord ++ tailWord_1948921).sum := by decide
  have hdescent : baseEnd_1948921 < baseStart_1948921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948979 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 7]
def baseStart_1948979 : Nat := 118140960795 + 1948979 * 2 ^ 59
def prefixEnd_1948979 : Nat := 4983230072969 + 3 ^ 40 * 1948979 * 2
def baseEnd_1948979 : Nat := 222391780559830076533181

theorem tailTrace_1948979 : CollatzResearch.WordTrace tailWord_1948979 prefixEnd_1948979 222391780559830076533181 := by
  unfold tailWord_1948979
  simp only [CollatzResearch.WordTrace]
  refine ⟨71085104006189416958041991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47390069337459611305361327 71085104006189416958041991)
  ·
    refine ⟨106627656009284125437062987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71085104006189416958041991 106627656009284125437062987)
    ·
      refine ⟨159941484013926188155594481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106627656009284125437062987 159941484013926188155594481)
      ·
        refine ⟨119956113010444641116695861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159941484013926188155594481 119956113010444641116695861)
        ·
          refine ⟨11245885594729185104690237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119956113010444641116695861 11245885594729185104690237)
          ·
            refine ⟨4217207098023444414258839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11245885594729185104690237 4217207098023444414258839)
            ·
              refine ⟨6325810647035166621388259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217207098023444414258839 6325810647035166621388259)
              ·
                refine ⟨9488715970552749932082389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325810647035166621388259 9488715970552749932082389)
                ·
                  refine ⟨222391780559830076533181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9488715970552749932082389 222391780559830076533181)
                  ·
                    rfl

theorem cell22_1948979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_1948979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1948979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1948979 prefixEnd_1948979 := by exact prefixLift 1948979
  have htrace : WordTrace (prefixWord ++ tailWord_1948979) baseStart_1948979 baseEnd_1948979 := by
    simpa [prefixWord, tailWord_1948979, baseEnd_1948979] using wordTrace_append hprefix tailTrace_1948979
  have hstable : (prefixWord ++ tailWord_1948979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948979).length < 2 ^ (prefixWord ++ tailWord_1948979).sum := by decide
  have hdescent : baseEnd_1948979 < baseStart_1948979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949041 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 4]
def baseStart_1949041 : Nat := 118140960795 + 1949041 * 2 ^ 59
def prefixEnd_1949041 : Nat := 4983230072969 + 3 ^ 40 * 1949041 * 2
def baseEnd_1949041 : Nat := 222398855182180911516451

theorem tailTrace_1949041 : CollatzResearch.WordTrace tailWord_1949041 prefixEnd_1949041 222398855182180911516451 := by
  unfold tailWord_1949041
  simp only [CollatzResearch.WordTrace]
  refine ⟨71087365331964801546798977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47391576887976534364532651 71087365331964801546798977)
  ·
    refine ⟨53315523998973601160099233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71087365331964801546798977 53315523998973601160099233)
    ·
      refine ⟨39986642999230200870074425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53315523998973601160099233 39986642999230200870074425)
      ·
        refine ⟨29989982249422650652555819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39986642999230200870074425 29989982249422650652555819)
        ·
          refine ⟨44984973374133975978833729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29989982249422650652555819 44984973374133975978833729)
          ·
            refine ⟨33738730030600481984125297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44984973374133975978833729 33738730030600481984125297)
            ·
              refine ⟨25304047522950361488093973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33738730030600481984125297 25304047522950361488093973)
              ·
                refine ⟨1186127227638298194754405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25304047522950361488093973 1186127227638298194754405)
                ·
                  refine ⟨222398855182180911516451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186127227638298194754405 222398855182180911516451)
                  ·
                    rfl

theorem cell22_1949041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_1949041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949041 prefixEnd_1949041 := by exact prefixLift 1949041
  have htrace : WordTrace (prefixWord ++ tailWord_1949041) baseStart_1949041 baseEnd_1949041 := by
    simpa [prefixWord, tailWord_1949041, baseEnd_1949041] using wordTrace_append hprefix tailTrace_1949041
  have hstable : (prefixWord ++ tailWord_1949041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949041).length < 2 ^ (prefixWord ++ tailWord_1949041).sum := by decide
  have hdescent : baseEnd_1949041 < baseStart_1949041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949086 : List Nat := [4, 3, 1, 2, 12]
def baseStart_1949086 : Nat := 118140960795 + 1949086 * 2 ^ 59
def prefixEnd_1949086 : Nat := 4983230072969 + 3 ^ 40 * 1949086 * 2
def baseEnd_1949086 : Nat := 2745728271465751511005

theorem tailTrace_1949086 : CollatzResearch.WordTrace tailWord_1949086 prefixEnd_1949086 2745728271465751511005 := by
  unfold tailWord_1949086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8886125827100221779023389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47392671077867849488124741 8886125827100221779023389)
  ·
    refine ⟨3332297185162583167133771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8886125827100221779023389 3332297185162583167133771)
    ·
      refine ⟨4998445777743874750700657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332297185162583167133771 4998445777743874750700657)
      ·
        refine ⟨3748834333307906063025493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4998445777743874750700657 3748834333307906063025493)
        ·
          refine ⟨2745728271465751511005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3748834333307906063025493 2745728271465751511005)
          ·
            rfl

theorem cell22_1949086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 12].length) (baseStart_1949086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949086 prefixEnd_1949086 := by exact prefixLift 1949086
  have htrace : WordTrace (prefixWord ++ tailWord_1949086) baseStart_1949086 baseEnd_1949086 := by
    simpa [prefixWord, tailWord_1949086, baseEnd_1949086] using wordTrace_append hprefix tailTrace_1949086
  have hstable : (prefixWord ++ tailWord_1949086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949086).length < 2 ^ (prefixWord ++ tailWord_1949086).sum := by decide
  have hdescent : baseEnd_1949086 < baseStart_1949086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949090 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1949090 : Nat := 118140960795 + 1949090 * 2 ^ 59
def prefixEnd_1949090 : Nat := 4983230072969 + 3 ^ 40 * 1949090 * 2
def baseEnd_1949090 : Nat := 667213339247922940074203

theorem tailTrace_1949090 : CollatzResearch.WordTrace tailWord_1949090 prefixEnd_1949090 667213339247922940074203 := by
  unfold tailWord_1949090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772288127196820728833181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47392768339191521943555149 17772288127196820728833181)
  ·
    refine ⟨6664608047698807773312443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17772288127196820728833181 6664608047698807773312443)
    ·
      refine ⟨9996912071548211659968665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664608047698807773312443 9996912071548211659968665)
      ·
        refine ⟨7497684053661158744976499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9996912071548211659968665 7497684053661158744976499)
        ·
          refine ⟨11246526080491738117464749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497684053661158744976499 11246526080491738117464749)
          ·
            refine ⟨4217447280184401794049281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11246526080491738117464749 4217447280184401794049281)
            ·
              refine ⟨3163085460138301345536961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217447280184401794049281 3163085460138301345536961)
              ·
                refine ⟨2372314095103726009152721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163085460138301345536961 2372314095103726009152721)
                ·
                  refine ⟨1779235571327794506864541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372314095103726009152721 1779235571327794506864541)
                  ·
                    refine ⟨667213339247922940074203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779235571327794506864541 667213339247922940074203)
                    ·
                      rfl

theorem cell22_1949090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1949090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949090 prefixEnd_1949090 := by exact prefixLift 1949090
  have htrace : WordTrace (prefixWord ++ tailWord_1949090) baseStart_1949090 baseEnd_1949090 := by
    simpa [prefixWord, tailWord_1949090, baseEnd_1949090] using wordTrace_append hprefix tailTrace_1949090
  have hstable : (prefixWord ++ tailWord_1949090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949090).length < 2 ^ (prefixWord ++ tailWord_1949090).sum := by decide
  have hdescent : baseEnd_1949090 < baseStart_1949090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949114 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1949114 : Nat := 118140960795 + 1949114 * 2 ^ 59
def prefixEnd_1949114 : Nat := 4983230072969 + 3 ^ 40 * 1949114 * 2
def baseEnd_1949114 : Nat := 222407184979464959158043

theorem tailTrace_1949114 : CollatzResearch.WordTrace tailWord_1949114 prefixEnd_1949114 222407184979464959158043 := by
  unfold tailWord_1949114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772506965175083753551599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47393351907133556676137597 17772506965175083753551599)
  ·
    refine ⟨26658760447762625630327399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17772506965175083753551599 26658760447762625630327399)
    ·
      refine ⟨39988140671643938445491099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26658760447762625630327399 39988140671643938445491099)
      ·
        refine ⟨59982211007465907668236649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39988140671643938445491099 59982211007465907668236649)
        ·
          refine ⟨44986658255599430751177487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59982211007465907668236649 44986658255599430751177487)
          ·
            refine ⟨67479987383399146126766231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44986658255599430751177487 67479987383399146126766231)
            ·
              refine ⟨101219981075098719190149347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67479987383399146126766231 101219981075098719190149347)
              ·
                refine ⟨151829971612648078785224021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101219981075098719190149347 151829971612648078785224021)
                ·
                  refine ⟨222407184979464959158043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 151829971612648078785224021 222407184979464959158043)
                  ·
                    rfl

theorem cell22_1949114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1949114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949114 prefixEnd_1949114 := by exact prefixLift 1949114
  have htrace : WordTrace (prefixWord ++ tailWord_1949114) baseStart_1949114 baseEnd_1949114 := by
    simpa [prefixWord, tailWord_1949114, baseEnd_1949114] using wordTrace_append hprefix tailTrace_1949114
  have hstable : (prefixWord ++ tailWord_1949114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949114).length < 2 ^ (prefixWord ++ tailWord_1949114).sum := by decide
  have hdescent : baseEnd_1949114 < baseStart_1949114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949129 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_1949129 : Nat := 118140960795 + 1949129 * 2 ^ 59
def prefixEnd_1949129 : Nat := 4983230072969 + 3 ^ 40 * 1949129 * 2
def baseEnd_1949129 : Nat := 667226689744939838349083

theorem tailTrace_1949129 : CollatzResearch.WordTrace tailWord_1949129 prefixEnd_1949129 667226689744939838349083 := by
  unfold tailWord_1949129
  simp only [CollatzResearch.WordTrace]
  refine ⟨71090574955645992576002441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47393716637097328384001627 71090574955645992576002441)
  ·
    refine ⟨53317931216734494432001831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71090574955645992576002441 53317931216734494432001831)
    ·
      refine ⟨79976896825101741648002747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53317931216734494432001831 79976896825101741648002747)
      ·
        refine ⟨119965345237652612472004121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79976896825101741648002747 119965345237652612472004121)
        ·
          refine ⟨89974008928239459354003091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119965345237652612472004121 89974008928239459354003091)
          ·
            refine ⟨134961013392359189031004637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89974008928239459354003091 134961013392359189031004637)
            ·
              refine ⟨50610380022134695886626739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134961013392359189031004637 50610380022134695886626739)
              ·
                refine ⟨75915570033202043829940109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50610380022134695886626739 75915570033202043829940109)
                ·
                  refine ⟨28468338762450766436227541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75915570033202043829940109 28468338762450766436227541)
                  ·
                    refine ⟨667226689744939838349083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28468338762450766436227541 667226689744939838349083)
                    ·
                      rfl

theorem cell22_1949129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_1949129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949129 prefixEnd_1949129 := by exact prefixLift 1949129
  have htrace : WordTrace (prefixWord ++ tailWord_1949129) baseStart_1949129 baseEnd_1949129 := by
    simpa [prefixWord, tailWord_1949129, baseEnd_1949129] using wordTrace_append hprefix tailTrace_1949129
  have hstable : (prefixWord ++ tailWord_1949129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949129).length < 2 ^ (prefixWord ++ tailWord_1949129).sum := by decide
  have hdescent : baseEnd_1949129 < baseStart_1949129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949146 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_1949146 : Nat := 118140960795 + 1949146 * 2 ^ 59
def prefixEnd_1949146 : Nat := 4983230072969 + 3 ^ 40 * 1949146 * 2
def baseEnd_1949146 : Nat := 667232509192357460674031

theorem tailTrace_1949146 : CollatzResearch.WordTrace tailWord_1949146 prefixEnd_1949146 667232509192357460674031 := by
  unfold tailWord_1949146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772798749146101119842823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47394129997722936319580861 17772798749146101119842823)
  ·
    refine ⟨26659198123719151679764235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17772798749146101119842823 26659198123719151679764235)
    ·
      refine ⟨39988797185578727519646353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26659198123719151679764235 39988797185578727519646353)
      ·
        refine ⟨29991597889184045639734765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39988797185578727519646353 29991597889184045639734765)
        ·
          refine ⟨11246849208444017114900537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29991597889184045639734765 11246849208444017114900537)
          ·
            refine ⟨8435136906333012836175403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11246849208444017114900537 8435136906333012836175403)
            ·
              refine ⟨12652705359499519254263105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435136906333012836175403 12652705359499519254263105)
              ·
                refine ⟨9489529019624639440697329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12652705359499519254263105 9489529019624639440697329)
                ·
                  refine ⟨7117146764718479580522997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489529019624639440697329 7117146764718479580522997)
                  ·
                    refine ⟨667232509192357460674031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7117146764718479580522997 667232509192357460674031)
                    ·
                      rfl

theorem cell22_1949146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_1949146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949146 prefixEnd_1949146 := by exact prefixLift 1949146
  have htrace : WordTrace (prefixWord ++ tailWord_1949146) baseStart_1949146 baseEnd_1949146 := by
    simpa [prefixWord, tailWord_1949146, baseEnd_1949146] using wordTrace_append hprefix tailTrace_1949146
  have hstable : (prefixWord ++ tailWord_1949146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949146).length < 2 ^ (prefixWord ++ tailWord_1949146).sum := by decide
  have hdescent : baseEnd_1949146 < baseStart_1949146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949176 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_1949176 : Nat := 118140960795 + 1949176 * 2 ^ 59
def prefixEnd_1949176 : Nat := 4983230072969 + 3 ^ 40 * 1949176 * 2
def baseEnd_1949176 : Nat := 222414259601815794141313

theorem tailTrace_1949176 : CollatzResearch.WordTrace tailWord_1949176 prefixEnd_1949176 222414259601815794141313 := by
  unfold tailWord_1949176
  simp only [CollatzResearch.WordTrace]
  refine ⟨35546144593237859801481691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47394859457650479735308921 35546144593237859801481691)
  ·
    refine ⟨53319216889856789702222537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35546144593237859801481691 53319216889856789702222537)
    ·
      refine ⟨39989412667392592276666903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53319216889856789702222537 39989412667392592276666903)
      ·
        refine ⟨59984119001088888415000355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39989412667392592276666903 59984119001088888415000355)
        ·
          refine ⟨89976178501633332622500533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59984119001088888415000355 89976178501633332622500533)
          ·
            refine ⟨8435266734528124933359425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89976178501633332622500533 8435266734528124933359425)
            ·
              refine ⟨6326450050896093700019569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435266734528124933359425 6326450050896093700019569)
              ·
                refine ⟨4744837538172070275014677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326450050896093700019569 4744837538172070275014677)
                ·
                  refine ⟨222414259601815794141313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4744837538172070275014677 222414259601815794141313)
                  ·
                    rfl

theorem cell22_1949176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_1949176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949176 prefixEnd_1949176 := by exact prefixLift 1949176
  have htrace : WordTrace (prefixWord ++ tailWord_1949176) baseStart_1949176 baseEnd_1949176 := by
    simpa [prefixWord, tailWord_1949176, baseEnd_1949176] using wordTrace_append hprefix tailTrace_1949176
  have hstable : (prefixWord ++ tailWord_1949176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949176).length < 2 ^ (prefixWord ++ tailWord_1949176).sum := by decide
  have hdescent : baseEnd_1949176 < baseStart_1949176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949178 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1949178 : Nat := 118140960795 + 1949178 * 2 ^ 59
def prefixEnd_1949178 : Nat := 4983230072969 + 3 ^ 40 * 1949178 * 2
def baseEnd_1949178 : Nat := 667243463446320043873933

theorem tailTrace_1949178 : CollatzResearch.WordTrace tailWord_1949178 prefixEnd_1949178 667243463446320043873933 := by
  unfold tailWord_1949178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773090533117118486134047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47394908088312315963024125 17773090533117118486134047)
  ·
    refine ⟨26659635799675677729201071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17773090533117118486134047 26659635799675677729201071)
    ·
      refine ⟨39989453699513516593801607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26659635799675677729201071 39989453699513516593801607)
      ·
        refine ⟨59984180549270274890702411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39989453699513516593801607 59984180549270274890702411)
        ·
          refine ⟨89976270823905412336053617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59984180549270274890702411 89976270823905412336053617)
          ·
            refine ⟨67482203117929059252040213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89976270823905412336053617 67482203117929059252040213)
            ·
              refine ⟨3163228271152924652439385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67482203117929059252040213 3163228271152924652439385)
              ·
                refine ⟨2372421203364693489329539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163228271152924652439385 2372421203364693489329539)
                ·
                  refine ⟨3558631805047040233994309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372421203364693489329539 3558631805047040233994309)
                  ·
                    refine ⟨667243463446320043873933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3558631805047040233994309 667243463446320043873933)
                    ·
                      rfl

theorem cell22_1949178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1949178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949178 prefixEnd_1949178 := by exact prefixLift 1949178
  have htrace : WordTrace (prefixWord ++ tailWord_1949178) baseStart_1949178 baseEnd_1949178 := by
    simpa [prefixWord, tailWord_1949178, baseEnd_1949178] using wordTrace_append hprefix tailTrace_1949178
  have hstable : (prefixWord ++ tailWord_1949178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949178).length < 2 ^ (prefixWord ++ tailWord_1949178).sum := by decide
  have hdescent : baseEnd_1949178 < baseStart_1949178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949261 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1949261 : Nat := 118140960795 + 1949261 * 2 ^ 59
def prefixEnd_1949261 : Nat := 4983230072969 + 3 ^ 40 * 1949261 * 2
def baseEnd_1949261 : Nat := 222423958680845164682893

theorem tailTrace_1949261 : CollatzResearch.WordTrace tailWord_1949261 prefixEnd_1949261 222423958680845164682893 := by
  unfold tailWord_1949261
  simp only [CollatzResearch.WordTrace]
  refine ⟨71095389391167779119807637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47396926260778519413205091 71095389391167779119807637)
  ·
    refine ⟨3332596377710989646240983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71095389391167779119807637 3332596377710989646240983)
    ·
      refine ⟨4998894566566484469361475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332596377710989646240983 4998894566566484469361475)
      ·
        refine ⟨7498341849849726704042213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998894566566484469361475 7498341849849726704042213)
        ·
          refine ⟨1405939096846823757007915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7498341849849726704042213 1405939096846823757007915)
          ·
            refine ⟨2108908645270235635511873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405939096846823757007915 2108908645270235635511873)
            ·
              refine ⟨1581681483952676726633905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108908645270235635511873 1581681483952676726633905)
              ·
                refine ⟨1186261112964507544975429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581681483952676726633905 1186261112964507544975429)
                ·
                  refine ⟨222423958680845164682893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186261112964507544975429 222423958680845164682893)
                  ·
                    rfl

theorem cell22_1949261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1949261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949261 prefixEnd_1949261 := by exact prefixLift 1949261
  have htrace : WordTrace (prefixWord ++ tailWord_1949261) baseStart_1949261 baseEnd_1949261 := by
    simpa [prefixWord, tailWord_1949261, baseEnd_1949261] using wordTrace_append hprefix tailTrace_1949261
  have hstable : (prefixWord ++ tailWord_1949261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949261).length < 2 ^ (prefixWord ++ tailWord_1949261).sum := by decide
  have hdescent : baseEnd_1949261 < baseStart_1949261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949283 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 5]
def baseStart_1949283 : Nat := 118140960795 + 1949283 * 2 ^ 59
def prefixEnd_1949283 : Nat := 4983230072969 + 3 ^ 40 * 1949283 * 2
def baseEnd_1949283 : Nat := 222426469030711589999537

theorem tailTrace_1949283 : CollatzResearch.WordTrace tailWord_1949283 prefixEnd_1949283 222426469030711589999537 := by
  unfold tailWord_1949283
  simp only [CollatzResearch.WordTrace]
  refine ⟨71096191797088076877108503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47397461198058717918072335 71096191797088076877108503)
  ·
    refine ⟨106644287695632115315662755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71096191797088076877108503 106644287695632115315662755)
    ·
      refine ⟨159966431543448172973494133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106644287695632115315662755 159966431543448172973494133)
      ·
        refine ⟨14996852957198266216265075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159966431543448172973494133 14996852957198266216265075)
        ·
          refine ⟨22495279435797399324397613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14996852957198266216265075 22495279435797399324397613)
          ·
            refine ⟨8435729788424024746649105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22495279435797399324397613 8435729788424024746649105)
            ·
              refine ⟨6326797341318018559986829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435729788424024746649105 6326797341318018559986829)
              ·
                refine ⟨2372549002994256959995061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6326797341318018559986829 2372549002994256959995061)
                ·
                  refine ⟨222426469030711589999537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372549002994256959995061 222426469030711589999537)
                  ·
                    rfl

theorem cell22_1949283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 5].length) (baseStart_1949283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949283 prefixEnd_1949283 := by exact prefixLift 1949283
  have htrace : WordTrace (prefixWord ++ tailWord_1949283) baseStart_1949283 baseEnd_1949283 := by
    simpa [prefixWord, tailWord_1949283, baseEnd_1949283] using wordTrace_append hprefix tailTrace_1949283
  have hstable : (prefixWord ++ tailWord_1949283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949283).length < 2 ^ (prefixWord ++ tailWord_1949283).sum := by decide
  have hdescent : baseEnd_1949283 < baseStart_1949283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949394 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_1949394 : Nat := 118140960795 + 1949394 * 2 ^ 59
def prefixEnd_1949394 : Nat := 4983230072969 + 3 ^ 40 * 1949394 * 2
def baseEnd_1949394 : Nat := 667317404660567480473271

theorem tailTrace_1949394 : CollatzResearch.WordTrace tailWord_1949394 prefixEnd_1949394 667317404660567480473271 := by
  unfold tailWord_1949394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775060074921485708599809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47400160199790628556266157 17775060074921485708599809)
  ·
    refine ⟨13331295056191114281449857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17775060074921485708599809 13331295056191114281449857)
    ·
      refine ⟨9998471292143335711087393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13331295056191114281449857 9998471292143335711087393)
      ·
        refine ⟨7498853469107501783315545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9998471292143335711087393 7498853469107501783315545)
        ·
          refine ⟨5624140101830626337486659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7498853469107501783315545 5624140101830626337486659)
          ·
            refine ⟨8436210152745939506229989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624140101830626337486659 8436210152745939506229989)
            ·
              refine ⟨1581789403639863657418123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8436210152745939506229989 1581789403639863657418123)
              ·
                refine ⟨2372684105459795486127185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581789403639863657418123 2372684105459795486127185)
                ·
                  refine ⟨1779513079094846614595389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372684105459795486127185 1779513079094846614595389)
                  ·
                    refine ⟨667317404660567480473271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779513079094846614595389 667317404660567480473271)
                    ·
                      rfl

theorem cell22_1949394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_1949394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949394 prefixEnd_1949394 := by exact prefixLift 1949394
  have htrace : WordTrace (prefixWord ++ tailWord_1949394) baseStart_1949394 baseEnd_1949394 := by
    simpa [prefixWord, tailWord_1949394, baseEnd_1949394] using wordTrace_append hprefix tailTrace_1949394
  have hstable : (prefixWord ++ tailWord_1949394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949394).length < 2 ^ (prefixWord ++ tailWord_1949394).sum := by decide
  have hdescent : baseEnd_1949394 < baseStart_1949394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949398 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1949398 : Nat := 118140960795 + 1949398 * 2 ^ 59
def prefixEnd_1949398 : Nat := 4983230072969 + 3 ^ 40 * 1949398 * 2
def baseEnd_1949398 : Nat := 667318773942312803373259

theorem tailTrace_1949398 : CollatzResearch.WordTrace tailWord_1949398 prefixEnd_1949398 667318773942312803373259 := by
  unfold tailWord_1949398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443774136979465719846553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47400257461114301011696565 4443774136979465719846553)
  ·
    refine ⟨3332830602734599289884915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4443774136979465719846553 3332830602734599289884915)
    ·
      refine ⟨4999245904101898934827373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332830602734599289884915 4999245904101898934827373)
      ·
        refine ⟨1874717214038212100560265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4999245904101898934827373 1874717214038212100560265)
        ·
          refine ⟨1406037910528659075420199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1874717214038212100560265 1406037910528659075420199)
          ·
            refine ⟨2109056865792988613130299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406037910528659075420199 2109056865792988613130299)
            ·
              refine ⟨3163585298689482919695449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109056865792988613130299 3163585298689482919695449)
              ·
                refine ⟨2372688974017112189771587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163585298689482919695449 2372688974017112189771587)
                ·
                  refine ⟨3559033461025668284657381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372688974017112189771587 3559033461025668284657381)
                  ·
                    refine ⟨667318773942312803373259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3559033461025668284657381 667318773942312803373259)
                    ·
                      rfl

theorem cell22_1949398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1949398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949398 prefixEnd_1949398 := by exact prefixLift 1949398
  have htrace : WordTrace (prefixWord ++ tailWord_1949398) baseStart_1949398 baseEnd_1949398 := by
    simpa [prefixWord, tailWord_1949398, baseEnd_1949398] using wordTrace_append hprefix tailTrace_1949398
  have hstable : (prefixWord ++ tailWord_1949398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949398).length < 2 ^ (prefixWord ++ tailWord_1949398).sum := by decide
  have hdescent : baseEnd_1949398 < baseStart_1949398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949418 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_1949418 : Nat := 118140960795 + 1949418 * 2 ^ 59
def prefixEnd_1949418 : Nat := 4983230072969 + 3 ^ 40 * 1949418 * 2
def baseEnd_1949418 : Nat := 222441873450346472624399

theorem tailTrace_1949418 : CollatzResearch.WordTrace tailWord_1949418 prefixEnd_1949418 222441873450346472624399 := by
  unfold tailWord_1949418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775278912899748733318227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47400743767732663288848605 17775278912899748733318227)
  ·
    refine ⟨26662918369349623099977341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775278912899748733318227 26662918369349623099977341)
    ·
      refine ⟨9998594388506108662491503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26662918369349623099977341 9998594388506108662491503)
      ·
        refine ⟨14997891582759162993737255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9998594388506108662491503 14997891582759162993737255)
        ·
          refine ⟨22496837374138744490605883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14997891582759162993737255 22496837374138744490605883)
          ·
            refine ⟨33745256061208116735908825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22496837374138744490605883 33745256061208116735908825)
            ·
              refine ⟨25308942045906087551931619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33745256061208116735908825 25308942045906087551931619)
              ·
                refine ⟨37963413068859131327897429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25308942045906087551931619 37963413068859131327897429)
                ·
                  refine ⟨222441873450346472624399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37963413068859131327897429 222441873450346472624399)
                  ·
                    rfl

theorem cell22_1949418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_1949418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949418 prefixEnd_1949418 := by exact prefixLift 1949418
  have htrace : WordTrace (prefixWord ++ tailWord_1949418) baseStart_1949418 baseEnd_1949418 := by
    simpa [prefixWord, tailWord_1949418, baseEnd_1949418] using wordTrace_append hprefix tailTrace_1949418
  have hstable : (prefixWord ++ tailWord_1949418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949418).length < 2 ^ (prefixWord ++ tailWord_1949418).sum := by decide
  have hdescent : baseEnd_1949418 < baseStart_1949418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949439 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 1, 3]
def baseStart_1949439 : Nat := 118140960795 + 1949439 * 2 ^ 59
def prefixEnd_1949439 : Nat := 4983230072969 + 3 ^ 40 * 1949439 * 2
def baseEnd_1949439 : Nat := 667332809080202363098133

theorem tailTrace_1949439 : CollatzResearch.WordTrace tailWord_1949439 prefixEnd_1949439 667332809080202363098133 := by
  unfold tailWord_1949439
  simp only [CollatzResearch.WordTrace]
  refine ⟨71101881584522915519787371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47401254389681943679858247 71101881584522915519787371)
  ·
    refine ⟨106652822376784373279681057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71101881584522915519787371 106652822376784373279681057)
    ·
      refine ⟨79989616782588279959760793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106652822376784373279681057 79989616782588279959760793)
      ·
        refine ⟨59992212586941209969820595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79989616782588279959760793 59992212586941209969820595)
        ·
          refine ⟨89988318880411814954730893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59992212586941209969820595 89988318880411814954730893)
          ·
            refine ⟨33745619580154430608024085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89988318880411814954730893 33745619580154430608024085)
            ·
              refine ⟨1581825917819738934751129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33745619580154430608024085 1581825917819738934751129)
              ·
                refine ⟨1186369438364804201063347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581825917819738934751129 1186369438364804201063347)
                ·
                  refine ⟨1779554157547206301595021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186369438364804201063347 1779554157547206301595021)
                  ·
                    refine ⟨667332809080202363098133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779554157547206301595021 667332809080202363098133)
                    ·
                      rfl

theorem cell22_1949439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_1949439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949439 prefixEnd_1949439 := by exact prefixLift 1949439
  have htrace : WordTrace (prefixWord ++ tailWord_1949439) baseStart_1949439 baseEnd_1949439 := by
    simpa [prefixWord, tailWord_1949439, baseEnd_1949439] using wordTrace_append hprefix tailTrace_1949439
  have hstable : (prefixWord ++ tailWord_1949439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949439).length < 2 ^ (prefixWord ++ tailWord_1949439).sum := by decide
  have hdescent : baseEnd_1949439 < baseStart_1949439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949450 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_1949450 : Nat := 118140960795 + 1949450 * 2 ^ 59
def prefixEnd_1949450 : Nat := 4983230072969 + 3 ^ 40 * 1949450 * 2
def baseEnd_1949450 : Nat := 667336574605002001073099

theorem tailTrace_1949450 : CollatzResearch.WordTrace tailWord_1949450 prefixEnd_1949450 667336574605002001073099 := by
  unfold tailWord_1949450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775570696870766099609451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47401521858322042932291869 17775570696870766099609451)
  ·
    refine ⟨26663356045306149149414177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775570696870766099609451 26663356045306149149414177)
    ·
      refine ⟨19997517033979611862060633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26663356045306149149414177 19997517033979611862060633)
      ·
        refine ⟨14998137775484708896545475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19997517033979611862060633 14998137775484708896545475)
        ·
          refine ⟨22497206663227063344818213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14998137775484708896545475 22497206663227063344818213)
          ·
            refine ⟨4218226249355074377153415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22497206663227063344818213 4218226249355074377153415)
            ·
              refine ⟨6327339374032611565730123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218226249355074377153415 6327339374032611565730123)
              ·
                refine ⟨9491009061048917348595185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327339374032611565730123 9491009061048917348595185)
                ·
                  refine ⟨7118256795786688011446389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491009061048917348595185 7118256795786688011446389)
                  ·
                    refine ⟨667336574605002001073099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7118256795786688011446389 667336574605002001073099)
                    ·
                      rfl

theorem cell22_1949450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_1949450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949450 prefixEnd_1949450 := by exact prefixLift 1949450
  have htrace : WordTrace (prefixWord ++ tailWord_1949450) baseStart_1949450 baseEnd_1949450 := by
    simpa [prefixWord, tailWord_1949450, baseEnd_1949450] using wordTrace_append hprefix tailTrace_1949450
  have hstable : (prefixWord ++ tailWord_1949450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949450).length < 2 ^ (prefixWord ++ tailWord_1949450).sum := by decide
  have hdescent : baseEnd_1949450 < baseStart_1949450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949486 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_1949486 : Nat := 118140960795 + 1949486 * 2 ^ 59
def prefixEnd_1949486 : Nat := 4983230072969 + 3 ^ 40 * 1949486 * 2
def baseEnd_1949486 : Nat := 222449632713569969057663

theorem tailTrace_1949486 : CollatzResearch.WordTrace tailWord_1949486 prefixEnd_1949486 222449632713569969057663 := by
  unfold tailWord_1949486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887949476919080318343539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47402397210235095031165541 8887949476919080318343539)
  ·
    refine ⟨13331924215378620477515309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887949476919080318343539 13331924215378620477515309)
    ·
      refine ⟨4999471580766982679068241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13331924215378620477515309 4999471580766982679068241)
      ·
        refine ⟨3749603685575237009301181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4999471580766982679068241 3749603685575237009301181)
        ·
          refine ⟨1406101382090713878487943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3749603685575237009301181 1406101382090713878487943)
          ·
            refine ⟨2109152073136070817731915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406101382090713878487943 2109152073136070817731915)
            ·
              refine ⟨3163728109704106226597873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109152073136070817731915 3163728109704106226597873)
              ·
                refine ⟨2372796082278079669948405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163728109704106226597873 2372796082278079669948405)
                ·
                  refine ⟨222449632713569969057663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372796082278079669948405 222449632713569969057663)
                  ·
                    rfl

theorem cell22_1949486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_1949486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949486 prefixEnd_1949486 := by exact prefixLift 1949486
  have htrace : WordTrace (prefixWord ++ tailWord_1949486) baseStart_1949486 baseEnd_1949486 := by
    simpa [prefixWord, tailWord_1949486, baseEnd_1949486] using wordTrace_append hprefix tailTrace_1949486
  have hstable : (prefixWord ++ tailWord_1949486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949486).length < 2 ^ (prefixWord ++ tailWord_1949486).sum := by decide
  have hdescent : baseEnd_1949486 < baseStart_1949486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949512 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_1949512 : Nat := 118140960795 + 1949512 * 2 ^ 59
def prefixEnd_1949512 : Nat := 4983230072969 + 3 ^ 40 * 1949512 * 2
def baseEnd_1949512 : Nat := 667357798472054506022909

theorem tailTrace_1949512 : CollatzResearch.WordTrace tailWord_1949512 prefixEnd_1949512 667357798472054506022909 := by
  unfold tailWord_1949512
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552272056629224493597395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47403029408838965991463193 35552272056629224493597395)
  ·
    refine ⟨53328408084943836740396093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35552272056629224493597395 53328408084943836740396093)
    ·
      refine ⟨19998153031853938777648535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53328408084943836740396093 19998153031853938777648535)
      ·
        refine ⟨29997229547780908166472803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19998153031853938777648535 29997229547780908166472803)
        ·
          refine ⟨44995844321671362249709205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29997229547780908166472803 44995844321671362249709205)
          ·
            refine ⟨2109180202578345105455119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44995844321671362249709205 2109180202578345105455119)
            ·
              refine ⟨3163770303867517658182679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109180202578345105455119 3163770303867517658182679)
              ·
                refine ⟨4745655455801276487274019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163770303867517658182679 4745655455801276487274019)
                ·
                  refine ⟨7118483183701914730911029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745655455801276487274019 7118483183701914730911029)
                  ·
                    refine ⟨667357798472054506022909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7118483183701914730911029 667357798472054506022909)
                    ·
                      rfl

theorem cell22_1949512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_1949512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949512 prefixEnd_1949512 := by exact prefixLift 1949512
  have htrace : WordTrace (prefixWord ++ tailWord_1949512) baseStart_1949512 baseEnd_1949512 := by
    simpa [prefixWord, tailWord_1949512, baseEnd_1949512] using wordTrace_append hprefix tailTrace_1949512
  have hstable : (prefixWord ++ tailWord_1949512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949512).length < 2 ^ (prefixWord ++ tailWord_1949512).sum := by decide
  have hdescent : baseEnd_1949512 < baseStart_1949512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949525 : List Nat := [1, 3, 2, 2, 2, 3, 1, 8]
def baseStart_1949525 : Nat := 118140960795 + 1949525 * 2 ^ 59
def prefixEnd_1949525 : Nat := 4983230072969 + 3 ^ 40 * 1949525 * 2
def baseEnd_1949525 : Nat := 74151360959747422827541

theorem tailTrace_1949525 : CollatzResearch.WordTrace tailWord_1949525 prefixEnd_1949525 74151360959747422827541 := by
  unfold tailWord_1949525
  simp only [CollatzResearch.WordTrace]
  refine ⟨71105018262211352207418029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47403345508140901471612019 71105018262211352207418029)
  ·
    refine ⟨26664381848329257077781761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71105018262211352207418029 26664381848329257077781761)
    ·
      refine ⟨19998286386246942808336321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26664381848329257077781761 19998286386246942808336321)
      ·
        refine ⟨14998714789685207106252241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19998286386246942808336321 14998714789685207106252241)
        ·
          refine ⟨11249036092263905329689181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14998714789685207106252241 11249036092263905329689181)
          ·
            refine ⟨4218388534598964498633443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11249036092263905329689181 4218388534598964498633443)
            ·
              refine ⟨6327582801898446747950165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218388534598964498633443 6327582801898446747950165)
              ·
                refine ⟨74151360959747422827541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6327582801898446747950165 74151360959747422827541)
                ·
                  rfl

theorem cell22_1949525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 8].length) (baseStart_1949525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949525 prefixEnd_1949525 := by exact prefixLift 1949525
  have htrace : WordTrace (prefixWord ++ tailWord_1949525) baseStart_1949525 baseEnd_1949525 := by
    simpa [prefixWord, tailWord_1949525, baseEnd_1949525] using wordTrace_append hprefix tailTrace_1949525
  have hstable : (prefixWord ++ tailWord_1949525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949525).length < 2 ^ (prefixWord ++ tailWord_1949525).sum := by decide
  have hdescent : baseEnd_1949525 < baseStart_1949525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949615 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 6]
def baseStart_1949615 : Nat := 118140960795 + 1949615 * 2 ^ 59
def prefixEnd_1949615 : Nat := 4983230072969 + 3 ^ 40 * 1949615 * 2
def baseEnd_1949615 : Nat := 222464352492332190232531

theorem tailTrace_1949615 : CollatzResearch.WordTrace tailWord_1949615 prefixEnd_1949615 222464352492332190232531 := by
  unfold tailWord_1949615
  simp only [CollatzResearch.WordTrace]
  refine ⟨71108300831885297578194299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47405533887923531718796199 71108300831885297578194299)
  ·
    refine ⟨106662451247827946367291449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71108300831885297578194299 106662451247827946367291449)
    ·
      refine ⟨79996838435870959775468587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106662451247827946367291449 79996838435870959775468587)
      ·
        refine ⟨119995257653806439663202881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79996838435870959775468587 119995257653806439663202881)
        ·
          refine ⟨89996443240354829747402161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119995257653806439663202881 89996443240354829747402161)
          ·
            refine ⟨67497332430266122310551621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89996443240354829747402161 67497332430266122310551621)
            ·
              refine ⟨12655749830674897933228429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67497332430266122310551621 12655749830674897933228429)
              ·
                refine ⟨4745906186503086724960661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12655749830674897933228429 4745906186503086724960661)
                ·
                  refine ⟨222464352492332190232531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4745906186503086724960661 222464352492332190232531)
                  ·
                    rfl

theorem cell22_1949615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 6].length) (baseStart_1949615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949615 prefixEnd_1949615 := by exact prefixLift 1949615
  have htrace : WordTrace (prefixWord ++ tailWord_1949615) baseStart_1949615 baseEnd_1949615 := by
    simpa [prefixWord, tailWord_1949615, baseEnd_1949615] using wordTrace_append hprefix tailTrace_1949615
  have hstable : (prefixWord ++ tailWord_1949615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949615).length < 2 ^ (prefixWord ++ tailWord_1949615).sum := by decide
  have hdescent : baseEnd_1949615 < baseStart_1949615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949617 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1949617 : Nat := 118140960795 + 1949617 * 2 ^ 59
def prefixEnd_1949617 : Nat := 4983230072969 + 3 ^ 40 * 1949617 * 2
def baseEnd_1949617 : Nat := 667393742117869232147587

theorem tailTrace_1949617 : CollatzResearch.WordTrace tailWord_1949617 prefixEnd_1949617 667393742117869232147587 := by
  unfold tailWord_1949617
  simp only [CollatzResearch.WordTrace]
  refine ⟨71108373777878051919767105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47405582518585367946511403 71108373777878051919767105)
  ·
    refine ⟨53331280333408538939825329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71108373777878051919767105 53331280333408538939825329)
    ·
      refine ⟨39998460250056404204868997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53331280333408538939825329 39998460250056404204868997)
      ·
        refine ⟨7499711296885575788412937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39998460250056404204868997 7499711296885575788412937)
        ·
          refine ⟨5624783472664181841309703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7499711296885575788412937 5624783472664181841309703)
          ·
            refine ⟨8437175208996272761964555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624783472664181841309703 8437175208996272761964555)
            ·
              refine ⟨12655762813494409142946833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437175208996272761964555 12655762813494409142946833)
              ·
                refine ⟨9491822110120806857210125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12655762813494409142946833 9491822110120806857210125)
                ·
                  refine ⟨3559433291295302571453797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9491822110120806857210125 3559433291295302571453797)
                  ·
                    refine ⟨667393742117869232147587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3559433291295302571453797 667393742117869232147587)
                    ·
                      rfl

theorem cell22_1949617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1949617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949617 prefixEnd_1949617 := by exact prefixLift 1949617
  have htrace : WordTrace (prefixWord ++ tailWord_1949617) baseStart_1949617 baseEnd_1949617 := by
    simpa [prefixWord, tailWord_1949617, baseEnd_1949617] using wordTrace_append hprefix tailTrace_1949617
  have hstable : (prefixWord ++ tailWord_1949617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949617).length < 2 ^ (prefixWord ++ tailWord_1949617).sum := by decide
  have hdescent : baseEnd_1949617 < baseStart_1949617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949647 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 4, 3]
def baseStart_1949647 : Nat := 118140960795 + 1949647 * 2 ^ 59
def prefixEnd_1949647 : Nat := 4983230072969 + 3 ^ 40 * 1949647 * 2
def baseEnd_1949647 : Nat := 667404011730959153897495

theorem tailTrace_1949647 : CollatzResearch.WordTrace tailWord_1949647 prefixEnd_1949647 667404011730959153897495 := by
  unfold tailWord_1949647
  simp only [CollatzResearch.WordTrace]
  refine ⟨71109467967769367043359195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47406311978512911362239463 71109467967769367043359195)
  ·
    refine ⟨106664201951654050565038793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71109467967769367043359195 106664201951654050565038793)
    ·
      refine ⟨79998151463740537923779095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106664201951654050565038793 79998151463740537923779095)
      ·
        refine ⟨119997227195610806885668643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79998151463740537923779095 119997227195610806885668643)
        ·
          refine ⟨179995840793416210328502965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119997227195610806885668643 179995840793416210328502965)
          ·
            refine ⟨16874610074382769718297153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179995840793416210328502965 16874610074382769718297153)
            ·
              refine ⟨12655957555787077288722865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16874610074382769718297153 12655957555787077288722865)
              ·
                refine ⟨9491968166840307966542149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12655957555787077288722865 9491968166840307966542149)
                ·
                  refine ⟨1779744031282557743726653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9491968166840307966542149 1779744031282557743726653)
                  ·
                    refine ⟨667404011730959153897495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779744031282557743726653 667404011730959153897495)
                    ·
                      rfl

theorem cell22_1949647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_1949647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949647 prefixEnd_1949647 := by exact prefixLift 1949647
  have htrace : WordTrace (prefixWord ++ tailWord_1949647) baseStart_1949647 baseEnd_1949647 := by
    simpa [prefixWord, tailWord_1949647, baseEnd_1949647] using wordTrace_append hprefix tailTrace_1949647
  have hstable : (prefixWord ++ tailWord_1949647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949647).length < 2 ^ (prefixWord ++ tailWord_1949647).sum := by decide
  have hdescent : baseEnd_1949647 < baseStart_1949647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949666 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1949666 : Nat := 118140960795 + 1949666 * 2 ^ 59
def prefixEnd_1949666 : Nat := 4983230072969 + 3 ^ 40 * 1949666 * 2
def baseEnd_1949666 : Nat := 222470171939749812557479

theorem tailTrace_1949666 : CollatzResearch.WordTrace tailWord_1949666 prefixEnd_1949666 222470171939749812557479 := by
  unfold tailWord_1949666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17777540238675133322075213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47406773969800355525533901 17777540238675133322075213)
  ·
    refine ⟨6666577589503174995778205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17777540238675133322075213 6666577589503174995778205)
    ·
      refine ⟨2499966596063690623416827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6666577589503174995778205 2499966596063690623416827)
      ·
        refine ⟨3749949894095535935125241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499966596063690623416827 3749949894095535935125241)
        ·
          refine ⟨2812462420571651951343931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749949894095535935125241 2812462420571651951343931)
          ·
            refine ⟨4218693630857477927015897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812462420571651951343931 4218693630857477927015897)
            ·
              refine ⟨3164020223143108445261923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218693630857477927015897 3164020223143108445261923)
              ·
                refine ⟨4746030334714662667892885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164020223143108445261923 4746030334714662667892885)
                ·
                  refine ⟨222470171939749812557479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4746030334714662667892885 222470171939749812557479)
                  ·
                    rfl

theorem cell22_1949666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1949666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949666 prefixEnd_1949666 := by exact prefixLift 1949666
  have htrace : WordTrace (prefixWord ++ tailWord_1949666) baseStart_1949666 baseEnd_1949666 := by
    simpa [prefixWord, tailWord_1949666, baseEnd_1949666] using wordTrace_append hprefix tailTrace_1949666
  have hstable : (prefixWord ++ tailWord_1949666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949666).length < 2 ^ (prefixWord ++ tailWord_1949666).sum := by decide
  have hdescent : baseEnd_1949666 < baseStart_1949666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949681 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 1, 5]
def baseStart_1949681 : Nat := 118140960795 + 1949681 * 2 ^ 59
def prefixEnd_1949681 : Nat := 4983230072969 + 3 ^ 40 * 1949681 * 2
def baseEnd_1949681 : Nat := 667415650625794398547391

theorem tailTrace_1949681 : CollatzResearch.WordTrace tailWord_1949681 prefixEnd_1949681 667415650625794398547391 := by
  unfold tailWord_1949681
  simp only [CollatzResearch.WordTrace]
  refine ⟨71110708049646190850096897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47407138699764127233397931 71110708049646190850096897)
  ·
    refine ⟨53333031037234643137572673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71110708049646190850096897 53333031037234643137572673)
    ·
      refine ⟨39999773277925982353179505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53333031037234643137572673 39999773277925982353179505)
      ·
        refine ⟨29999829958444486764884629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39999773277925982353179505 29999829958444486764884629)
        ·
          refine ⟨1406242029302085317103967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29999829958444486764884629 1406242029302085317103967)
          ·
            refine ⟨2109363043953127975655951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406242029302085317103967 2109363043953127975655951)
            ·
              refine ⟨3164044565929691963483927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109363043953127975655951 3164044565929691963483927)
              ·
                refine ⟨4746066848894537945225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164044565929691963483927 4746066848894537945225891)
                ·
                  refine ⟨7119100273341806917838837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746066848894537945225891 7119100273341806917838837)
                  ·
                    refine ⟨667415650625794398547391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7119100273341806917838837 667415650625794398547391)
                    ·
                      rfl

theorem cell22_1949681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_1949681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949681 prefixEnd_1949681 := by exact prefixLift 1949681
  have htrace : WordTrace (prefixWord ++ tailWord_1949681) baseStart_1949681 baseEnd_1949681 := by
    simpa [prefixWord, tailWord_1949681, baseEnd_1949681] using wordTrace_append hprefix tailTrace_1949681
  have hstable : (prefixWord ++ tailWord_1949681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949681).length < 2 ^ (prefixWord ++ tailWord_1949681).sum := by decide
  have hdescent : baseEnd_1949681 < baseStart_1949681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949694 : List Nat := [4, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1949694 : Nat := 118140960795 + 1949694 * 2 ^ 59
def prefixEnd_1949694 : Nat := 4983230072969 + 3 ^ 40 * 1949694 * 2
def baseEnd_1949694 : Nat := 74157788976829633108039

theorem tailTrace_1949694 : CollatzResearch.WordTrace tailWord_1949694 prefixEnd_1949694 74157788976829633108039 := by
  unfold tailWord_1949694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8888897774824886758790017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47407454799066062713546757 8888897774824886758790017)
  ·
    refine ⟨6666673331118665069092513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8888897774824886758790017 6666673331118665069092513)
    ·
      refine ⟨5000004998338998801819385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6666673331118665069092513 5000004998338998801819385)
      ·
        refine ⟨3750003748754249101364539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000004998338998801819385 3750003748754249101364539)
        ·
          refine ⟨5625005623131373652046809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750003748754249101364539 5625005623131373652046809)
          ·
            refine ⟨4218754217348530239035107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625005623131373652046809 4218754217348530239035107)
            ·
              refine ⟨6328131326022795358552661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218754217348530239035107 6328131326022795358552661)
              ·
                refine ⟨74157788976829633108039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6328131326022795358552661 74157788976829633108039)
                ·
                  rfl

theorem cell22_1949694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1949694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949694 prefixEnd_1949694 := by exact prefixLift 1949694
  have htrace : WordTrace (prefixWord ++ tailWord_1949694) baseStart_1949694 baseEnd_1949694 := by
    simpa [prefixWord, tailWord_1949694, baseEnd_1949694] using wordTrace_append hprefix tailTrace_1949694
  have hstable : (prefixWord ++ tailWord_1949694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949694).length < 2 ^ (prefixWord ++ tailWord_1949694).sum := by decide
  have hdescent : baseEnd_1949694 < baseStart_1949694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949700 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 4]
def baseStart_1949700 : Nat := 118140960795 + 1949700 * 2 ^ 59
def prefixEnd_1949700 : Nat := 4983230072969 + 3 ^ 40 * 1949700 * 2
def baseEnd_1949700 : Nat := 222474051571361560774111

theorem tailTrace_1949700 : CollatzResearch.WordTrace tailWord_1949700 prefixEnd_1949700 222474051571361560774111 := by
  unfold tailWord_1949700
  simp only [CollatzResearch.WordTrace]
  refine ⟨35555700518288678547519277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47407600691051571396692369 35555700518288678547519277)
  ·
    refine ⟨13333387694358254455319729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35555700518288678547519277 13333387694358254455319729)
    ·
      refine ⟨10000040770768690841489797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13333387694358254455319729 10000040770768690841489797)
      ·
        refine ⟨1875007644519129532779337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10000040770768690841489797 1875007644519129532779337)
        ·
          refine ⟨1406255733389347149584503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875007644519129532779337 1406255733389347149584503)
          ·
            refine ⟨2109383600084020724376755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406255733389347149584503 2109383600084020724376755)
            ·
              refine ⟨3164075400126031086565133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109383600084020724376755 3164075400126031086565133)
              ·
                refine ⟨1186528275047261657461925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3164075400126031086565133 1186528275047261657461925)
                ·
                  refine ⟨222474051571361560774111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186528275047261657461925 222474051571361560774111)
                  ·
                    rfl

theorem cell22_1949700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_1949700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949700 prefixEnd_1949700 := by exact prefixLift 1949700
  have htrace : WordTrace (prefixWord ++ tailWord_1949700) baseStart_1949700 baseEnd_1949700 := by
    simpa [prefixWord, tailWord_1949700, baseEnd_1949700] using wordTrace_append hprefix tailTrace_1949700
  have hstable : (prefixWord ++ tailWord_1949700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949700).length < 2 ^ (prefixWord ++ tailWord_1949700).sum := by decide
  have hdescent : baseEnd_1949700 < baseStart_1949700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949722 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_1949722 : Nat := 118140960795 + 1949722 * 2 ^ 59
def prefixEnd_1949722 : Nat := 4983230072969 + 3 ^ 40 * 1949722 * 2
def baseEnd_1949722 : Nat := 222476561921227986090755

theorem tailTrace_1949722 : CollatzResearch.WordTrace tailWord_1949722 prefixEnd_1949722 222476561921227986090755 := by
  unfold tailWord_1949722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778050860624413713084855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47408135628331769901559613 17778050860624413713084855)
  ·
    refine ⟨26667076290936620569627283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17778050860624413713084855 26667076290936620569627283)
    ·
      refine ⟨40000614436404930854440925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26667076290936620569627283 40000614436404930854440925)
      ·
        refine ⟨15000230413651849070415347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40000614436404930854440925 15000230413651849070415347)
        ·
          refine ⟨22500345620477773605623021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15000230413651849070415347 22500345620477773605623021)
          ·
            refine ⟨8437629607679165102108633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22500345620477773605623021 8437629607679165102108633)
            ·
              refine ⟨6328222205759373826581475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8437629607679165102108633 6328222205759373826581475)
              ·
                refine ⟨9492333308639060739872213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328222205759373826581475 9492333308639060739872213)
                ·
                  refine ⟨222476561921227986090755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9492333308639060739872213 222476561921227986090755)
                  ·
                    rfl

theorem cell22_1949722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_1949722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949722 prefixEnd_1949722 := by exact prefixLift 1949722
  have htrace : WordTrace (prefixWord ++ tailWord_1949722) baseStart_1949722 baseEnd_1949722 := by
    simpa [prefixWord, tailWord_1949722, baseEnd_1949722] using wordTrace_append hprefix tailTrace_1949722
  have hstable : (prefixWord ++ tailWord_1949722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949722).length < 2 ^ (prefixWord ++ tailWord_1949722).sum := by decide
  have hdescent : baseEnd_1949722 < baseStart_1949722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949799 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1949799 : Nat := 118140960795 + 1949799 * 2 ^ 59
def prefixEnd_1949799 : Nat := 4983230072969 + 3 ^ 40 * 1949799 * 2
def baseEnd_1949799 : Nat := 667456044437281424097029

theorem tailTrace_1949799 : CollatzResearch.WordTrace tailWord_1949799 prefixEnd_1949799 667456044437281424097029 := by
  unfold tailWord_1949799
  simp only [CollatzResearch.WordTrace]
  refine ⟨71115011863218697002892451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47410007908812464668594967 71115011863218697002892451)
  ·
    refine ⟨106672517794828045504338677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71115011863218697002892451 106672517794828045504338677)
    ·
      refine ⟨10000548543265129266031751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106672517794828045504338677 10000548543265129266031751)
      ·
        refine ⟨15000822814897693899047627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000548543265129266031751 15000822814897693899047627)
        ·
          refine ⟨22501234222346540848571441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15000822814897693899047627 22501234222346540848571441)
          ·
            refine ⟨16875925666759905636428581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22501234222346540848571441 16875925666759905636428581)
            ·
              refine ⟨3164236062517482306830359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16875925666759905636428581 3164236062517482306830359)
              ·
                refine ⟨4746354093776223460245539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164236062517482306830359 4746354093776223460245539)
                ·
                  refine ⟨7119531140664335190368309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746354093776223460245539 7119531140664335190368309)
                  ·
                    refine ⟨667456044437281424097029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7119531140664335190368309 667456044437281424097029)
                    ·
                      rfl

theorem cell22_1949799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1949799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949799 prefixEnd_1949799 := by exact prefixLift 1949799
  have htrace : WordTrace (prefixWord ++ tailWord_1949799) baseStart_1949799 baseEnd_1949799 := by
    simpa [prefixWord, tailWord_1949799, baseEnd_1949799] using wordTrace_append hprefix tailTrace_1949799
  have hstable : (prefixWord ++ tailWord_1949799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949799).length < 2 ^ (prefixWord ++ tailWord_1949799).sum := by decide
  have hdescent : baseEnd_1949799 < baseStart_1949799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949850 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_1949850 : Nat := 118140960795 + 1949850 * 2 ^ 59
def prefixEnd_1949850 : Nat := 4983230072969 + 3 ^ 40 * 1949850 * 2
def baseEnd_1949850 : Nat := 667473502779534291071873

theorem tailTrace_1949850 : CollatzResearch.WordTrace tailWord_1949850 prefixEnd_1949850 667473502779534291071873 := by
  unfold tailWord_1949850
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779217996508483178249751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47411247990689288475332669 17779217996508483178249751)
  ·
    refine ⟨26668826994762724767374627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17779217996508483178249751 26668826994762724767374627)
    ·
      refine ⟨40003240492144087151061941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26668826994762724767374627 40003240492144087151061941)
      ·
        refine ⟨3750303796138508170412057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40003240492144087151061941 3750303796138508170412057)
        ·
          refine ⟨2812727847103881127809043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750303796138508170412057 2812727847103881127809043)
          ·
            refine ⟨4219091770655821691713565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812727847103881127809043 4219091770655821691713565)
            ·
              refine ⟨1582159413995933134392587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219091770655821691713565 1582159413995933134392587)
              ·
                refine ⟨2373239120993899701588881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582159413995933134392587 2373239120993899701588881)
                ·
                  refine ⟨1779929340745424776191661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2373239120993899701588881 1779929340745424776191661)
                  ·
                    refine ⟨667473502779534291071873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779929340745424776191661 667473502779534291071873)
                    ·
                      rfl

theorem cell22_1949850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_1949850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949850 prefixEnd_1949850 := by exact prefixLift 1949850
  have htrace : WordTrace (prefixWord ++ tailWord_1949850) baseStart_1949850 baseEnd_1949850 := by
    simpa [prefixWord, tailWord_1949850, baseEnd_1949850] using wordTrace_append hprefix tailTrace_1949850
  have hstable : (prefixWord ++ tailWord_1949850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949850).length < 2 ^ (prefixWord ++ tailWord_1949850).sum := by decide
  have hdescent : baseEnd_1949850 < baseStart_1949850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949863 : List Nat := [1, 1, 6, 2, 2, 2, 2, 6]
def baseStart_1949863 : Nat := 118140960795 + 1949863 * 2 ^ 59
def prefixEnd_1949863 : Nat := 4983230072969 + 3 ^ 40 * 1949863 * 2
def baseEnd_1949863 : Nat := 74164216993911843388537

theorem tailTrace_1949863 : CollatzResearch.WordTrace tailWord_1949863 prefixEnd_1949863 74164216993911843388537 := by
  unfold tailWord_1949863
  simp only [CollatzResearch.WordTrace]
  refine ⟨71117346134986835933222243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47411564089991223955481495 71117346134986835933222243)
  ·
    refine ⟨106676019202480253899833365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71117346134986835933222243 106676019202480253899833365)
    ·
      refine ⟨5000438400116261901554689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106676019202480253899833365 5000438400116261901554689)
      ·
        refine ⟨3750328800087196426166017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000438400116261901554689 3750328800087196426166017)
        ·
          refine ⟨2812746600065397319624513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750328800087196426166017 2812746600065397319624513)
          ·
            refine ⟨2109559950049047989718385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2812746600065397319624513 2109559950049047989718385)
            ·
              refine ⟨1582169962536785992288789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109559950049047989718385 1582169962536785992288789)
              ·
                refine ⟨74164216993911843388537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1582169962536785992288789 74164216993911843388537)
                ·
                  rfl

theorem cell22_1949863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 6].length) (baseStart_1949863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949863 prefixEnd_1949863 := by exact prefixLift 1949863
  have htrace : WordTrace (prefixWord ++ tailWord_1949863) baseStart_1949863 baseEnd_1949863 := by
    simpa [prefixWord, tailWord_1949863, baseEnd_1949863] using wordTrace_append hprefix tailTrace_1949863
  have hstable : (prefixWord ++ tailWord_1949863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949863).length < 2 ^ (prefixWord ++ tailWord_1949863).sum := by decide
  have hdescent : baseEnd_1949863 < baseStart_1949863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949983 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 2, 4]
def baseStart_1949983 : Nat := 118140960795 + 1949983 * 2 ^ 59
def prefixEnd_1949983 : Nat := 4983230072969 + 3 ^ 40 * 1949983 * 2
def baseEnd_1949983 : Nat := 667519031397566277496465

theorem tailTrace_1949983 : CollatzResearch.WordTrace tailWord_1949983 prefixEnd_1949983 667519031397566277496465 := by
  unfold tailWord_1949983
  simp only [CollatzResearch.WordTrace]
  refine ⟨71121722894552096427590603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47414481929701397618393735 71121722894552096427590603)
  ·
    refine ⟨106682584341828144641385905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71121722894552096427590603 106682584341828144641385905)
    ·
      refine ⟨80011938256371108481039429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106682584341828144641385905 80011938256371108481039429)
      ·
        refine ⟨15002238423069582840194893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80011938256371108481039429 15002238423069582840194893)
        ·
          refine ⟨5625839408651093565073085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15002238423069582840194893 5625839408651093565073085)
          ·
            refine ⟨2109689778244160086902407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5625839408651093565073085 2109689778244160086902407)
            ·
              refine ⟨3164534667366240130353611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109689778244160086902407 3164534667366240130353611)
              ·
                refine ⟨4746802001049360195530417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164534667366240130353611 4746802001049360195530417)
                ·
                  refine ⟨3560101500787020146647813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746802001049360195530417 3560101500787020146647813)
                  ·
                    refine ⟨667519031397566277496465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560101500787020146647813 667519031397566277496465)
                    ·
                      rfl

theorem cell22_1949983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_1949983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949983 prefixEnd_1949983 := by exact prefixLift 1949983
  have htrace : WordTrace (prefixWord ++ tailWord_1949983) baseStart_1949983 baseEnd_1949983 := by
    simpa [prefixWord, tailWord_1949983, baseEnd_1949983] using wordTrace_append hprefix tailTrace_1949983
  have hstable : (prefixWord ++ tailWord_1949983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949983).length < 2 ^ (prefixWord ++ tailWord_1949983).sum := by decide
  have hdescent : baseEnd_1949983 < baseStart_1949983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949998 : List Nat := [4, 1, 3, 3, 1, 1, 9]
def baseStart_1949998 : Nat := 118140960795 + 1949998 * 2 ^ 59
def prefixEnd_1949998 : Nat := 4983230072969 + 3 ^ 40 * 1949998 * 2
def baseEnd_1949998 : Nat := 24723117266818934754497

theorem tailTrace_1949998 : CollatzResearch.WordTrace tailWord_1949998 prefixEnd_1949998 24723117266818934754497 := by
  unfold tailWord_1949998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890283748687219248673331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47414846659665169326257765 8890283748687219248673331)
  ·
    refine ⟨13335425623030828873009997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8890283748687219248673331 13335425623030828873009997)
    ·
      refine ⟨5000784608636560827378749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13335425623030828873009997 5000784608636560827378749)
      ·
        refine ⟨1875294228238710310267031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5000784608636560827378749 1875294228238710310267031)
        ·
          refine ⟨2812941342358065465400547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875294228238710310267031 2812941342358065465400547)
          ·
            refine ⟨4219412013537098198100821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812941342358065465400547 4219412013537098198100821)
            ·
              refine ⟨24723117266818934754497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4219412013537098198100821 24723117266818934754497)
              ·
                rfl

theorem cell22_1949998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 9].length) (baseStart_1949998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1949998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1949998 prefixEnd_1949998 := by exact prefixLift 1949998
  have htrace : WordTrace (prefixWord ++ tailWord_1949998) baseStart_1949998 baseEnd_1949998 := by
    simpa [prefixWord, tailWord_1949998, baseEnd_1949998] using wordTrace_append hprefix tailTrace_1949998
  have hstable : (prefixWord ++ tailWord_1949998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949998).length < 2 ^ (prefixWord ++ tailWord_1949998).sum := by decide
  have hdescent : baseEnd_1949998 < baseStart_1949998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950002 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_1950002 : Nat := 118140960795 + 1950002 * 2 ^ 59
def prefixEnd_1950002 : Nat := 4983230072969 + 3 ^ 40 * 1950002 * 2
def baseEnd_1950002 : Nat := 667525535485856561271407

theorem tailTrace_1950002 : CollatzResearch.WordTrace tailWord_1950002 prefixEnd_1950002 667525535485856561271407 := by
  unfold tailWord_1950002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780603970370815668133065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47414943920988841781688173 17780603970370815668133065)
  ·
    refine ⟨13335452977778111751099799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17780603970370815668133065 13335452977778111751099799)
    ·
      refine ⟨20003179466667167626649699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13335452977778111751099799 20003179466667167626649699)
      ·
        refine ⟨30004769200000751439974549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20003179466667167626649699 30004769200000751439974549)
        ·
          refine ⟨1406473556250035223748807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30004769200000751439974549 1406473556250035223748807)
          ·
            refine ⟨2109710334375052835623211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406473556250035223748807 2109710334375052835623211)
            ·
              refine ⟨3164565501562579253434817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109710334375052835623211 3164565501562579253434817)
              ·
                refine ⟨2373424126171934440076113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164565501562579253434817 2373424126171934440076113)
                ·
                  refine ⟨1780068094628950830057085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2373424126171934440076113 1780068094628950830057085)
                  ·
                    refine ⟨667525535485856561271407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1780068094628950830057085 667525535485856561271407)
                    ·
                      rfl

theorem cell22_1950002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_1950002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950002 prefixEnd_1950002 := by exact prefixLift 1950002
  have htrace : WordTrace (prefixWord ++ tailWord_1950002) baseStart_1950002 baseEnd_1950002 := by
    simpa [prefixWord, tailWord_1950002, baseEnd_1950002] using wordTrace_append hprefix tailTrace_1950002
  have hstable : (prefixWord ++ tailWord_1950002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950002).length < 2 ^ (prefixWord ++ tailWord_1950002).sum := by decide
  have hdescent : baseEnd_1950002 < baseStart_1950002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950090 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1950090 : Nat := 118140960795 + 1950090 * 2 ^ 59
def prefixEnd_1950090 : Nat := 4983230072969 + 3 ^ 40 * 1950090 * 2
def baseEnd_1950090 : Nat := 667555659684253665071137

theorem tailTrace_1950090 : CollatzResearch.WordTrace tailWord_1950090 prefixEnd_1950090 667555659684253665071137 := by
  unfold tailWord_1950090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17781406376291113425433931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47417083670109635801157149 17781406376291113425433931)
  ·
    refine ⟨26672109564436670138150897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17781406376291113425433931 26672109564436670138150897)
    ·
      refine ⟨20004082173327502603613173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26672109564436670138150897 20004082173327502603613173)
      ·
        refine ⟨1875382703749453369088735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20004082173327502603613173 1875382703749453369088735)
        ·
          refine ⟨2813074055624180053633103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875382703749453369088735 2813074055624180053633103)
          ·
            refine ⟨4219611083436270080449655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813074055624180053633103 4219611083436270080449655)
            ·
              refine ⟨6329416625154405120674483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219611083436270080449655 6329416625154405120674483)
              ·
                refine ⟨9494124937731607681011725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329416625154405120674483 9494124937731607681011725)
                ·
                  refine ⟨3560296851649352880379397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9494124937731607681011725 3560296851649352880379397)
                  ·
                    refine ⟨667555659684253665071137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560296851649352880379397 667555659684253665071137)
                    ·
                      rfl

theorem cell22_1950090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1950090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950090 prefixEnd_1950090 := by exact prefixLift 1950090
  have htrace : WordTrace (prefixWord ++ tailWord_1950090) baseStart_1950090 baseEnd_1950090 := by
    simpa [prefixWord, tailWord_1950090, baseEnd_1950090] using wordTrace_append hprefix tailTrace_1950090
  have hstable : (prefixWord ++ tailWord_1950090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950090).length < 2 ^ (prefixWord ++ tailWord_1950090).sum := by decide
  have hdescent : baseEnd_1950090 < baseStart_1950090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950176 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_1950176 : Nat := 118140960795 + 1950176 * 2 ^ 59
def prefixEnd_1950176 : Nat := 4983230072969 + 3 ^ 40 * 1950176 * 2
def baseEnd_1950176 : Nat := 667585099241778107420873

theorem tailTrace_1950176 : CollatzResearch.WordTrace tailWord_1950176 prefixEnd_1950176 667585099241778107420873 := by
  unfold tailWord_1950176
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564381091426445194683191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47419174788568593592910921 35564381091426445194683191)
  ·
    refine ⟨53346571637139667792024787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35564381091426445194683191 53346571637139667792024787)
    ·
      refine ⟨80019857455709501688037181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53346571637139667792024787 80019857455709501688037181)
      ·
        refine ⟨30007446545891063133013943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80019857455709501688037181 30007446545891063133013943)
        ·
          refine ⟨45011169818836594699520915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30007446545891063133013943 45011169818836594699520915)
          ·
            refine ⟨67516754728254892049281373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45011169818836594699520915 67516754728254892049281373)
            ·
              refine ⟨25318783023095584518480515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67516754728254892049281373 25318783023095584518480515)
              ·
                refine ⟨37978174534643376777720773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25318783023095584518480515 37978174534643376777720773)
                ·
                  refine ⟨7120907725245633145822645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37978174534643376777720773 7120907725245633145822645)
                  ·
                    refine ⟨667585099241778107420873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7120907725245633145822645 667585099241778107420873)
                    ·
                      rfl

theorem cell22_1950176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_1950176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950176 prefixEnd_1950176 := by exact prefixLift 1950176
  have htrace : WordTrace (prefixWord ++ tailWord_1950176) baseStart_1950176 baseEnd_1950176 := by
    simpa [prefixWord, tailWord_1950176, baseEnd_1950176] using wordTrace_append hprefix tailTrace_1950176
  have hstable : (prefixWord ++ tailWord_1950176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950176).length < 2 ^ (prefixWord ++ tailWord_1950176).sum := by decide
  have hdescent : baseEnd_1950176 < baseStart_1950176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950268 : List Nat := [2, 2, 2, 2, 3, 1, 2, 8]
def baseStart_1950268 : Nat := 118140960795 + 1950268 * 2 ^ 59
def prefixEnd_1950268 : Nat := 4983230072969 + 3 ^ 40 * 1950268 * 2
def baseEnd_1950268 : Nat := 74179621413546726013399

theorem tailTrace_1950268 : CollatzResearch.WordTrace tailWord_1950268 prefixEnd_1950268 74179621413546726013399 := by
  unfold tailWord_1950268
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566058849259795050857729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47421411799013060067810305 35566058849259795050857729)
  ·
    refine ⟨26674544136944846288143297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35566058849259795050857729 26674544136944846288143297)
    ·
      refine ⟨20005908102708634716107473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26674544136944846288143297 20005908102708634716107473)
      ·
        refine ⟨15004431077031476037080605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20005908102708634716107473 15004431077031476037080605)
        ·
          refine ⟨5626661653886803513905227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15004431077031476037080605 5626661653886803513905227)
          ·
            refine ⟨8439992480830205270857841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626661653886803513905227 8439992480830205270857841)
            ·
              refine ⟨6329994360622653953143381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8439992480830205270857841 6329994360622653953143381)
              ·
                refine ⟨74179621413546726013399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6329994360622653953143381 74179621413546726013399)
                ·
                  rfl

theorem cell22_1950268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_1950268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950268 prefixEnd_1950268 := by exact prefixLift 1950268
  have htrace : WordTrace (prefixWord ++ tailWord_1950268) baseStart_1950268 baseEnd_1950268 := by
    simpa [prefixWord, tailWord_1950268, baseEnd_1950268] using wordTrace_append hprefix tailTrace_1950268
  have hstable : (prefixWord ++ tailWord_1950268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950268).length < 2 ^ (prefixWord ++ tailWord_1950268).sum := by decide
  have hdescent : baseEnd_1950268 < baseStart_1950268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950317 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1950317 : Nat := 118140960795 + 1950317 * 2 ^ 59
def prefixEnd_1950317 : Nat := 4983230072969 + 3 ^ 40 * 1950317 * 2
def baseEnd_1950317 : Nat := 667633366423300739645441

theorem tailTrace_1950317 : CollatzResearch.WordTrace tailWord_1950317 prefixEnd_1950317 667633366423300739645441 := by
  unfold tailWord_1950317
  simp only [CollatzResearch.WordTrace]
  refine ⟨71133904875342071470249205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47422603250228047646832803 71133904875342071470249205)
  ·
    refine ⟨6668803582063319200335863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71133904875342071470249205 6668803582063319200335863)
    ·
      refine ⟨10003205373094978800503795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6668803582063319200335863 10003205373094978800503795)
      ·
        refine ⟨15004808059642468200755693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10003205373094978800503795 15004808059642468200755693)
        ·
          refine ⟨5626803022365925575283385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15004808059642468200755693 5626803022365925575283385)
          ·
            refine ⟨4220102266774444181462539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5626803022365925575283385 4220102266774444181462539)
            ·
              refine ⟨6330153400161666272193809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4220102266774444181462539 6330153400161666272193809)
              ·
                refine ⟨4747615050121249704145357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6330153400161666272193809 4747615050121249704145357)
                ·
                  refine ⟨1780355643795468639054509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4747615050121249704145357 1780355643795468639054509)
                  ·
                    refine ⟨667633366423300739645441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1780355643795468639054509 667633366423300739645441)
                    ·
                      rfl

theorem cell22_1950317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1950317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950317 prefixEnd_1950317 := by exact prefixLift 1950317
  have htrace : WordTrace (prefixWord ++ tailWord_1950317) baseStart_1950317 baseEnd_1950317 := by
    simpa [prefixWord, tailWord_1950317, baseEnd_1950317] using wordTrace_append hprefix tailTrace_1950317
  have hstable : (prefixWord ++ tailWord_1950317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950317).length < 2 ^ (prefixWord ++ tailWord_1950317).sum := by decide
  have hdescent : baseEnd_1950317 < baseStart_1950317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950424 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 2, 3]
def baseStart_1950424 : Nat := 118140960795 + 1950424 * 2 ^ 59
def prefixEnd_1950424 : Nat := 4983230072969 + 3 ^ 40 * 1950424 * 2
def baseEnd_1950424 : Nat := 667669994709988127220113

theorem tailTrace_1950424 : CollatzResearch.WordTrace tailWord_1950424 prefixEnd_1950424 667669994709988127220113 := by
  unfold tailWord_1950424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35568903742977214372197163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47425204990636285829596217 35568903742977214372197163)
  ·
    refine ⟨53353355614465821558295745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35568903742977214372197163 53353355614465821558295745)
    ·
      refine ⟨40015016710849366168721809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53353355614465821558295745 40015016710849366168721809)
      ·
        refine ⟨30011262533137024626541357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40015016710849366168721809 30011262533137024626541357)
        ·
          refine ⟨11254223449926384234953009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30011262533137024626541357 11254223449926384234953009)
          ·
            refine ⟨8440667587444788176214757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11254223449926384234953009 8440667587444788176214757)
            ·
              refine ⟨1582625172645897783040267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8440667587444788176214757 1582625172645897783040267)
              ·
                refine ⟨2373937758968846674560401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582625172645897783040267 2373937758968846674560401)
                ·
                  refine ⟨1780453319226635005920301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2373937758968846674560401 1780453319226635005920301)
                  ·
                    refine ⟨667669994709988127220113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1780453319226635005920301 667669994709988127220113)
                    ·
                      rfl

theorem cell22_1950424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_1950424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950424 prefixEnd_1950424 := by exact prefixLift 1950424
  have htrace : WordTrace (prefixWord ++ tailWord_1950424) baseStart_1950424 baseEnd_1950424 := by
    simpa [prefixWord, tailWord_1950424, baseEnd_1950424] using wordTrace_append hprefix tailTrace_1950424
  have hstable : (prefixWord ++ tailWord_1950424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950424).length < 2 ^ (prefixWord ++ tailWord_1950424).sum := by decide
  have hdescent : baseEnd_1950424 < baseStart_1950424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950516 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1950516 : Nat := 118140960795 + 1950516 * 2 ^ 59
def prefixEnd_1950516 : Nat := 4983230072969 + 3 ^ 40 * 1950516 * 2
def baseEnd_1950516 : Nat := 222567162730043517973277

theorem tailTrace_1950516 : CollatzResearch.WordTrace tailWord_1950516 prefixEnd_1950516 222567162730043517973277 := by
  unfold tailWord_1950516
  simp only [CollatzResearch.WordTrace]
  refine ⟨35570581500810564228371701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47427442001080752304495601 35570581500810564228371701)
  ·
    refine ⟨3334742015700990396409847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35570581500810564228371701 3334742015700990396409847)
    ·
      refine ⟨5002113023551485594614771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334742015700990396409847 5002113023551485594614771)
      ·
        refine ⟨7503169535327228391922157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002113023551485594614771 7503169535327228391922157)
        ·
          refine ⟨2813688575747710646970809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7503169535327228391922157 2813688575747710646970809)
          ·
            refine ⟨2110266431810782985228107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813688575747710646970809 2110266431810782985228107)
            ·
              refine ⟨3165399647716174477842161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110266431810782985228107 3165399647716174477842161)
              ·
                refine ⟨2374049735787130858381621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165399647716174477842161 2374049735787130858381621)
                ·
                  refine ⟨222567162730043517973277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2374049735787130858381621 222567162730043517973277)
                  ·
                    rfl

theorem cell22_1950516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1950516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950516 prefixEnd_1950516 := by exact prefixLift 1950516
  have htrace : WordTrace (prefixWord ++ tailWord_1950516) baseStart_1950516 baseEnd_1950516 := by
    simpa [prefixWord, tailWord_1950516, baseEnd_1950516] using wordTrace_append hprefix tailTrace_1950516
  have hstable : (prefixWord ++ tailWord_1950516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950516).length < 2 ^ (prefixWord ++ tailWord_1950516).sum := by decide
  have hdescent : baseEnd_1950516 < baseStart_1950516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950527 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 6]
def baseStart_1950527 : Nat := 118140960795 + 1950527 * 2 ^ 59
def prefixEnd_1950527 : Nat := 4983230072969 + 3 ^ 40 * 1950527 * 2
def baseEnd_1950527 : Nat := 222568417904976730631599

theorem tailTrace_1950527 : CollatzResearch.WordTrace tailWord_1950527 prefixEnd_1950527 222568417904976730631599 := by
  unfold tailWord_1950527
  simp only [CollatzResearch.WordTrace]
  refine ⟨71141564204581277335393835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47427709469720851556929223 71141564204581277335393835)
  ·
    refine ⟨106712346306871916003090753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71141564204581277335393835 106712346306871916003090753)
    ·
      refine ⟨80034259730153937002318065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106712346306871916003090753 80034259730153937002318065)
      ·
        refine ⟨60025694797615452751738549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80034259730153937002318065 60025694797615452751738549)
        ·
          refine ⟨5627408887276448695475489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60025694797615452751738549 5627408887276448695475489)
          ·
            refine ⟨4220556665457336521606617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5627408887276448695475489 4220556665457336521606617)
            ·
              refine ⟨3165417499093002391204963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220556665457336521606617 3165417499093002391204963)
              ·
                refine ⟨4748126248639503586807445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165417499093002391204963 4748126248639503586807445)
                ·
                  refine ⟨222568417904976730631599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4748126248639503586807445 222568417904976730631599)
                  ·
                    rfl

theorem cell22_1950527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 6].length) (baseStart_1950527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950527 prefixEnd_1950527 := by exact prefixLift 1950527
  have htrace : WordTrace (prefixWord ++ tailWord_1950527) baseStart_1950527 baseEnd_1950527 := by
    simpa [prefixWord, tailWord_1950527, baseEnd_1950527] using wordTrace_append hprefix tailTrace_1950527
  have hstable : (prefixWord ++ tailWord_1950527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950527).length < 2 ^ (prefixWord ++ tailWord_1950527).sum := by decide
  have hdescent : baseEnd_1950527 < baseStart_1950527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950621 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1950621 : Nat := 118140960795 + 1950621 * 2 ^ 59
def prefixEnd_1950621 : Nat := 4983230072969 + 3 ^ 40 * 1950621 * 2
def baseEnd_1950621 : Nat := 667737431835945280044509

theorem tailTrace_1950621 : CollatzResearch.WordTrace tailWord_1950621 prefixEnd_1950621 667737431835945280044509 := by
  unfold tailWord_1950621
  simp only [CollatzResearch.WordTrace]
  refine ⟨71144992666240731389315717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47429995110827154259543811 71144992666240731389315717)
  ·
    refine ⟨13339686124920137135496697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71144992666240731389315717 13339686124920137135496697)
    ·
      refine ⟨10004764593690102851622523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13339686124920137135496697 10004764593690102851622523)
      ·
        refine ⟨15007146890535154277433785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10004764593690102851622523 15007146890535154277433785)
        ·
          refine ⟨11255360167901365708075339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15007146890535154277433785 11255360167901365708075339)
          ·
            refine ⟨16883040251852048562113009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11255360167901365708075339 16883040251852048562113009)
            ·
              refine ⟨12662280188889036421584757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16883040251852048562113009 12662280188889036421584757)
              ·
                refine ⟨1187088767708347164523571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12662280188889036421584757 1187088767708347164523571)
                ·
                  refine ⟨1780633151562520746785357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187088767708347164523571 1780633151562520746785357)
                  ·
                    refine ⟨667737431835945280044509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1780633151562520746785357 667737431835945280044509)
                    ·
                      rfl

theorem cell22_1950621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1950621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950621 prefixEnd_1950621 := by exact prefixLift 1950621
  have htrace : WordTrace (prefixWord ++ tailWord_1950621) baseStart_1950621 baseEnd_1950621 := by
    simpa [prefixWord, tailWord_1950621, baseEnd_1950621] using wordTrace_append hprefix tailTrace_1950621
  have hstable : (prefixWord ++ tailWord_1950621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950621).length < 2 ^ (prefixWord ++ tailWord_1950621).sum := by decide
  have hdescent : baseEnd_1950621 < baseStart_1950621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950647 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1950647 : Nat := 118140960795 + 1950647 * 2 ^ 59
def prefixEnd_1950647 : Nat := 4983230072969 + 3 ^ 40 * 1950647 * 2
def baseEnd_1950647 : Nat := 667746332167289878894429

theorem tailTrace_1950647 : CollatzResearch.WordTrace tailWord_1950647 prefixEnd_1950647 667746332167289878894429 := by
  unfold tailWord_1950647
  simp only [CollatzResearch.WordTrace]
  refine ⟨71145940964146537829762195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47430627309431025219841463 71145940964146537829762195)
  ·
    refine ⟨106718911446219806744643293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71145940964146537829762195 106718911446219806744643293)
    ·
      refine ⟨40019591792332427529241235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106718911446219806744643293 40019591792332427529241235)
      ·
        refine ⟨60029387688498641293861853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40019591792332427529241235 60029387688498641293861853)
        ·
          refine ⟨22511020383186990485198195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60029387688498641293861853 22511020383186990485198195)
          ·
            refine ⟨33766530574780485727797293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22511020383186990485198195 33766530574780485727797293)
            ·
              refine ⟨12662448965542682147923985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33766530574780485727797293 12662448965542682147923985)
              ·
                refine ⟨9496836724157011610942989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12662448965542682147923985 9496836724157011610942989)
                ·
                  refine ⟨3561313771558879354103621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9496836724157011610942989 3561313771558879354103621)
                  ·
                    refine ⟨667746332167289878894429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3561313771558879354103621 667746332167289878894429)
                    ·
                      rfl

theorem cell22_1950647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1950647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950647 prefixEnd_1950647 := by exact prefixLift 1950647
  have htrace : WordTrace (prefixWord ++ tailWord_1950647) baseStart_1950647 baseEnd_1950647 := by
    simpa [prefixWord, tailWord_1950647, baseEnd_1950647] using wordTrace_append hprefix tailTrace_1950647
  have hstable : (prefixWord ++ tailWord_1950647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950647).length < 2 ^ (prefixWord ++ tailWord_1950647).sum := by decide
  have hdescent : baseEnd_1950647 < baseStart_1950647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950681 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 1, 4]
def baseStart_1950681 : Nat := 118140960795 + 1950681 * 2 ^ 59
def prefixEnd_1950681 : Nat := 4983230072969 + 3 ^ 40 * 1950681 * 2
def baseEnd_1950681 : Nat := 667757971062125123544325

theorem tailTrace_1950681 : CollatzResearch.WordTrace tailWord_1950681 prefixEnd_1950681 667757971062125123544325 := by
  unfold tailWord_1950681
  simp only [CollatzResearch.WordTrace]
  refine ⟨71147181046023361636499897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47431454030682241090999931 71147181046023361636499897)
  ·
    refine ⟨53360385784517521227374923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71147181046023361636499897 53360385784517521227374923)
    ·
      refine ⟨80040578676776281841062385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53360385784517521227374923 80040578676776281841062385)
      ·
        refine ⟨60030434007582211380796789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80040578676776281841062385 60030434007582211380796789)
        ·
          refine ⟨5627853188210832316949699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60030434007582211380796789 5627853188210832316949699)
          ·
            refine ⟨8441779782316248475424549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627853188210832316949699 8441779782316248475424549)
            ·
              refine ⟨1582833709184296589142103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8441779782316248475424549 1582833709184296589142103)
              ·
                refine ⟨2374250563776444883713155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582833709184296589142103 2374250563776444883713155)
                ·
                  refine ⟨3561375845664667325569733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374250563776444883713155 3561375845664667325569733)
                  ·
                    refine ⟨667757971062125123544325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3561375845664667325569733 667757971062125123544325)
                    ·
                      rfl

theorem cell22_1950681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_1950681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950681 prefixEnd_1950681 := by exact prefixLift 1950681
  have htrace : WordTrace (prefixWord ++ tailWord_1950681) baseStart_1950681 baseEnd_1950681 := by
    simpa [prefixWord, tailWord_1950681, baseEnd_1950681] using wordTrace_append hprefix tailTrace_1950681
  have hstable : (prefixWord ++ tailWord_1950681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950681).length < 2 ^ (prefixWord ++ tailWord_1950681).sum := by decide
  have hdescent : baseEnd_1950681 < baseStart_1950681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950762 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1950762 : Nat := 118140960795 + 1950762 * 2 ^ 59
def prefixEnd_1950762 : Nat := 4983230072969 + 3 ^ 40 * 1950762 * 2
def baseEnd_1950762 : Nat := 667785699017467912269077

theorem tailTrace_1950762 : CollatzResearch.WordTrace tailWord_1950762 prefixEnd_1950762 667785699017467912269077 := by
  unfold tailWord_1950762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787533839682478117549635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47433423572486608313465693 17787533839682478117549635)
  ·
    refine ⟨26681300759523717176324453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17787533839682478117549635 26681300759523717176324453)
    ·
      refine ⟨5002743892410696970560835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26681300759523717176324453 5002743892410696970560835)
      ·
        refine ⟨7504115838616045455841253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002743892410696970560835 7504115838616045455841253)
        ·
          refine ⟨1407021719740508522970235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7504115838616045455841253 1407021719740508522970235)
          ·
            refine ⟨2110532579610762784455353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407021719740508522970235 2110532579610762784455353)
            ·
              refine ⟨1582899434708072088341515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110532579610762784455353 1582899434708072088341515)
              ·
                refine ⟨2374349152062108132512273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582899434708072088341515 2374349152062108132512273)
                ·
                  refine ⟨1780761864046581099384205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2374349152062108132512273 1780761864046581099384205)
                  ·
                    refine ⟨667785699017467912269077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1780761864046581099384205 667785699017467912269077)
                    ·
                      rfl

theorem cell22_1950762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1950762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950762 prefixEnd_1950762 := by exact prefixLift 1950762
  have htrace : WordTrace (prefixWord ++ tailWord_1950762) baseStart_1950762 baseEnd_1950762 := by
    simpa [prefixWord, tailWord_1950762, baseEnd_1950762] using wordTrace_append hprefix tailTrace_1950762
  have hstable : (prefixWord ++ tailWord_1950762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950762).length < 2 ^ (prefixWord ++ tailWord_1950762).sum := by decide
  have hdescent : baseEnd_1950762 < baseStart_1950762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950767 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_1950767 : Nat := 118140960795 + 1950767 * 2 ^ 59
def prefixEnd_1950767 : Nat := 4983230072969 + 3 ^ 40 * 1950767 * 2
def baseEnd_1950767 : Nat := 667787410619649565894061

theorem tailTrace_1950767 : CollatzResearch.WordTrace tailWord_1950767 prefixEnd_1950767 667787410619649565894061 := by
  unfold tailWord_1950767
  simp only [CollatzResearch.WordTrace]
  refine ⟨71150317723711798324130555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47433545149141198882753703 71150317723711798324130555)
  ·
    refine ⟨106725476585567697486195833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71150317723711798324130555 106725476585567697486195833)
    ·
      refine ⟨80044107439175773114646875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106725476585567697486195833 80044107439175773114646875)
      ·
        refine ⟨120066161158763659671970313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80044107439175773114646875 120066161158763659671970313)
        ·
          refine ⟨90049620869072744753977735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120066161158763659671970313 90049620869072744753977735)
          ·
            refine ⟨135074431303609117130966603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90049620869072744753977735 135074431303609117130966603)
            ·
              refine ⟨202611646955413675696449905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135074431303609117130966603 202611646955413675696449905)
              ·
                refine ⟨151958735216560256772337429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202611646955413675696449905 151958735216560256772337429)
                ·
                  refine ⟨7123065713276262036203317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151958735216560256772337429 7123065713276262036203317)
                  ·
                    refine ⟨667787410619649565894061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7123065713276262036203317 667787410619649565894061)
                    ·
                      rfl

theorem cell22_1950767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_1950767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950767 prefixEnd_1950767 := by exact prefixLift 1950767
  have htrace : WordTrace (prefixWord ++ tailWord_1950767) baseStart_1950767 baseEnd_1950767 := by
    simpa [prefixWord, tailWord_1950767, baseEnd_1950767] using wordTrace_append hprefix tailTrace_1950767
  have hstable : (prefixWord ++ tailWord_1950767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950767).length < 2 ^ (prefixWord ++ tailWord_1950767).sum := by decide
  have hdescent : baseEnd_1950767 < baseStart_1950767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950769 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 5]
def baseStart_1950769 : Nat := 118140960795 + 1950769 * 2 ^ 59
def prefixEnd_1950769 : Nat := 4983230072969 + 3 ^ 40 * 1950769 * 2
def baseEnd_1950769 : Nat := 222596031753507409114685

theorem tailTrace_1950769 : CollatzResearch.WordTrace tailWord_1950769 prefixEnd_1950769 222596031753507409114685 := by
  unfold tailWord_1950769
  simp only [CollatzResearch.WordTrace]
  refine ⟨71150390669704552665703361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47433593779803035110468907 71150390669704552665703361)
  ·
    refine ⟨53362793002278414499277521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71150390669704552665703361 53362793002278414499277521)
    ·
      refine ⟨40022094751708810874458141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53362793002278414499277521 40022094751708810874458141)
      ·
        refine ⟨15008285531890804077921803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40022094751708810874458141 15008285531890804077921803)
        ·
          refine ⟨22512428297836206116882705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15008285531890804077921803 22512428297836206116882705)
          ·
            refine ⟨16884321223377154587662029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22512428297836206116882705 16884321223377154587662029)
            ·
              refine ⟨6331620458766432970373261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16884321223377154587662029 6331620458766432970373261)
              ·
                refine ⟨2374357672037412363889973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6331620458766432970373261 2374357672037412363889973)
                ·
                  refine ⟨222596031753507409114685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2374357672037412363889973 222596031753507409114685)
                  ·
                    rfl

theorem cell22_1950769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_1950769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950769 prefixEnd_1950769 := by exact prefixLift 1950769
  have htrace : WordTrace (prefixWord ++ tailWord_1950769) baseStart_1950769 baseEnd_1950769 := by
    simpa [prefixWord, tailWord_1950769, baseEnd_1950769] using wordTrace_append hprefix tailTrace_1950769
  have hstable : (prefixWord ++ tailWord_1950769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950769).length < 2 ^ (prefixWord ++ tailWord_1950769).sum := by decide
  have hdescent : baseEnd_1950769 < baseStart_1950769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950844 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_1950844 : Nat := 118140960795 + 1950844 * 2 ^ 59
def prefixEnd_1950844 : Nat := 4983230072969 + 3 ^ 40 * 1950844 * 2
def baseEnd_1950844 : Nat := 667813769293247031718825

theorem tailTrace_1950844 : CollatzResearch.WordTrace tailWord_1950844 prefixEnd_1950844 667813769293247031718825 := by
  unfold tailWord_1950844
  simp only [CollatzResearch.WordTrace]
  refine ⟨35576563072216420237341793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47435417429621893649789057 35576563072216420237341793)
  ·
    refine ⟨26682422304162315178006345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35576563072216420237341793 26682422304162315178006345)
    ·
      refine ⟨20011816728121736383504759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26682422304162315178006345 20011816728121736383504759)
      ·
        refine ⟨30017725092182604575257139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20011816728121736383504759 30017725092182604575257139)
        ·
          refine ⟨45026587638273906862885709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30017725092182604575257139 45026587638273906862885709)
          ·
            refine ⟨16884970364352715073582141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45026587638273906862885709 16884970364352715073582141)
            ·
              refine ⟨6331863886632268152593303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16884970364352715073582141 6331863886632268152593303)
              ·
                refine ⟨9497795829948402228889955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331863886632268152593303 9497795829948402228889955)
                ·
                  refine ⟨14246693744922603343334933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9497795829948402228889955 14246693744922603343334933)
                  ·
                    refine ⟨667813769293247031718825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14246693744922603343334933 667813769293247031718825)
                    ·
                      rfl

theorem cell22_1950844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_1950844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950844 prefixEnd_1950844 := by exact prefixLift 1950844
  have htrace : WordTrace (prefixWord ++ tailWord_1950844) baseStart_1950844 baseEnd_1950844 := by
    simpa [prefixWord, tailWord_1950844, baseEnd_1950844] using wordTrace_append hprefix tailTrace_1950844
  have hstable : (prefixWord ++ tailWord_1950844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950844).length < 2 ^ (prefixWord ++ tailWord_1950844).sum := by decide
  have hdescent : baseEnd_1950844 < baseStart_1950844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950919 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1950919 : Nat := 118140960795 + 1950919 * 2 ^ 59
def prefixEnd_1950919 : Nat := 4983230072969 + 3 ^ 40 * 1950919 * 2
def baseEnd_1950919 : Nat := 667839443325971836093595

theorem tailTrace_1950919 : CollatzResearch.WordTrace tailWord_1950919 prefixEnd_1950919 667839443325971836093595 := by
  unfold tailWord_1950919
  simp only [CollatzResearch.WordTrace]
  refine ⟨71155861619161128283663811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47437241079440752189109207 71155861619161128283663811)
  ·
    refine ⟨106733792428741692425495717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71155861619161128283663811 106733792428741692425495717)
    ·
      refine ⟨20012586080389067329780447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106733792428741692425495717 20012586080389067329780447)
      ·
        refine ⟨30018879120583600994670671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012586080389067329780447 30018879120583600994670671)
        ·
          refine ⟨45028318680875401492006007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30018879120583600994670671 45028318680875401492006007)
          ·
            refine ⟨67542478021313102238009011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45028318680875401492006007 67542478021313102238009011)
            ·
              refine ⟨101313717031969653357013517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67542478021313102238009011 101313717031969653357013517)
              ·
                refine ⟨37992643886988620008880069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101313717031969653357013517 37992643886988620008880069)
                ·
                  refine ⟨7123620728810366251665013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37992643886988620008880069 7123620728810366251665013)
                  ·
                    refine ⟨667839443325971836093595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7123620728810366251665013 667839443325971836093595)
                    ·
                      rfl

theorem cell22_1950919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1950919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1950919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1950919 prefixEnd_1950919 := by exact prefixLift 1950919
  have htrace : WordTrace (prefixWord ++ tailWord_1950919) baseStart_1950919 baseEnd_1950919 := by
    simpa [prefixWord, tailWord_1950919, baseEnd_1950919] using wordTrace_append hprefix tailTrace_1950919
  have hstable : (prefixWord ++ tailWord_1950919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950919).length < 2 ^ (prefixWord ++ tailWord_1950919).sum := by decide
  have hdescent : baseEnd_1950919 < baseStart_1950919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951013 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1951013 : Nat := 118140960795 + 1951013 * 2 ^ 59
def prefixEnd_1951013 : Nat := 4983230072969 + 3 ^ 40 * 1951013 * 2
def baseEnd_1951013 : Nat := 667871621446986924243307

theorem tailTrace_1951013 : CollatzResearch.WordTrace tailWord_1951013 prefixEnd_1951013 667871621446986924243307 := by
  unfold tailWord_1951013
  simp only [CollatzResearch.WordTrace]
  refine ⟨71159290080820582337585693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47439526720547054891723795 71159290080820582337585693)
  ·
    refine ⟨26684733780307718376594635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71159290080820582337585693 26684733780307718376594635)
    ·
      refine ⟨40027100670461577564891953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26684733780307718376594635 40027100670461577564891953)
      ·
        refine ⟨30020325502846183173668965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40027100670461577564891953 30020325502846183173668965)
        ·
          refine ⟨5628811031783659345062931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30020325502846183173668965 5628811031783659345062931)
          ·
            refine ⟨8443216547675489017594397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628811031783659345062931 8443216547675489017594397)
            ·
              refine ⟨3166206205378308381597899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8443216547675489017594397 3166206205378308381597899)
              ·
                refine ⟨4749309308067462572396849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166206205378308381597899 4749309308067462572396849)
                ·
                  refine ⟨3561981981050596929297637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749309308067462572396849 3561981981050596929297637)
                  ·
                    refine ⟨667871621446986924243307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3561981981050596929297637 667871621446986924243307)
                    ·
                      rfl

theorem cell22_1951013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1951013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951013 prefixEnd_1951013 := by exact prefixLift 1951013
  have htrace : WordTrace (prefixWord ++ tailWord_1951013) baseStart_1951013 baseEnd_1951013 := by
    simpa [prefixWord, tailWord_1951013, baseEnd_1951013] using wordTrace_append hprefix tailTrace_1951013
  have hstable : (prefixWord ++ tailWord_1951013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951013).length < 2 ^ (prefixWord ++ tailWord_1951013).sum := by decide
  have hdescent : baseEnd_1951013 < baseStart_1951013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951133 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1951133 : Nat := 118140960795 + 1951133 * 2 ^ 59
def prefixEnd_1951133 : Nat := 4983230072969 + 3 ^ 40 * 1951133 * 2
def baseEnd_1951133 : Nat := 667912699899346611242939

theorem tailTrace_1951133 : CollatzResearch.WordTrace tailWord_1951133 prefixEnd_1951133 667912699899346611242939 := by
  unfold tailWord_1951133
  simp only [CollatzResearch.WordTrace]
  refine ⟨71163666840385842831954053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47442444560257228554636035 71163666840385842831954053)
  ·
    refine ⟨13343187532572345530991385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71163666840385842831954053 13343187532572345530991385)
    ·
      refine ⟨10007390649429259148243539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13343187532572345530991385 10007390649429259148243539)
      ·
        refine ⟨15011085974143888722365309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10007390649429259148243539 15011085974143888722365309)
        ·
          refine ⟨5629157240303958270886991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15011085974143888722365309 5629157240303958270886991)
          ·
            refine ⟨8443735860455937406330487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629157240303958270886991 8443735860455937406330487)
            ·
              refine ⟨12665603790683906109495731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443735860455937406330487 12665603790683906109495731)
              ·
                refine ⟨18998405686025859164243597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12665603790683906109495731 18998405686025859164243597)
                ·
                  refine ⟨7124402132259697186591349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18998405686025859164243597 7124402132259697186591349)
                  ·
                    refine ⟨667912699899346611242939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7124402132259697186591349 667912699899346611242939)
                    ·
                      rfl

theorem cell22_1951133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1951133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951133 prefixEnd_1951133 := by exact prefixLift 1951133
  have htrace : WordTrace (prefixWord ++ tailWord_1951133) baseStart_1951133 baseEnd_1951133 := by
    simpa [prefixWord, tailWord_1951133, baseEnd_1951133] using wordTrace_append hprefix tailTrace_1951133
  have hstable : (prefixWord ++ tailWord_1951133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951133).length < 2 ^ (prefixWord ++ tailWord_1951133).sum := by decide
  have hdescent : baseEnd_1951133 < baseStart_1951133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951148 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_1951148 : Nat := 118140960795 + 1951148 * 2 ^ 59
def prefixEnd_1951148 : Nat := 4983230072969 + 3 ^ 40 * 1951148 * 2
def baseEnd_1951148 : Nat := 667917834705891572117893

theorem tailTrace_1951148 : CollatzResearch.WordTrace tailWord_1951148 prefixEnd_1951148 667917834705891572117893 := by
  unfold tailWord_1951148
  simp only [CollatzResearch.WordTrace]
  refine ⟨35582106967665750196875049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47442809290221000262500065 35582106967665750196875049)
  ·
    refine ⟨26686580225749312647656287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35582106967665750196875049 26686580225749312647656287)
    ·
      refine ⟨40029870338623968971484431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26686580225749312647656287 40029870338623968971484431)
      ·
        refine ⟨60044805507935953457226647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40029870338623968971484431 60044805507935953457226647)
        ·
          refine ⟨90067208261903930185839971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60044805507935953457226647 90067208261903930185839971)
          ·
            refine ⟨135100812392855895278759957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90067208261903930185839971 135100812392855895278759957)
            ·
              refine ⟨6332850580915120091191873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135100812392855895278759957 6332850580915120091191873)
              ·
                refine ⟨4749637935686340068393905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332850580915120091191873 4749637935686340068393905)
                ·
                  refine ⟨3562228451764755051295429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749637935686340068393905 3562228451764755051295429)
                  ·
                    refine ⟨667917834705891572117893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3562228451764755051295429 667917834705891572117893)
                    ·
                      rfl

theorem cell22_1951148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_1951148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951148 prefixEnd_1951148 := by exact prefixLift 1951148
  have htrace : WordTrace (prefixWord ++ tailWord_1951148) baseStart_1951148 baseEnd_1951148 := by
    simpa [prefixWord, tailWord_1951148, baseEnd_1951148] using wordTrace_append hprefix tailTrace_1951148
  have hstable : (prefixWord ++ tailWord_1951148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951148).length < 2 ^ (prefixWord ++ tailWord_1951148).sum := by decide
  have hdescent : baseEnd_1951148 < baseStart_1951148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951180 : List Nat := [2, 2, 1, 4, 2, 2, 3, 6]
def baseStart_1951180 : Nat := 118140960795 + 1951180 * 2 ^ 59
def prefixEnd_1951180 : Nat := 4983230072969 + 3 ^ 40 * 1951180 * 2
def baseEnd_1951180 : Nat := 74214309884428239479755

theorem tailTrace_1951180 : CollatzResearch.WordTrace tailWord_1951180 prefixEnd_1951180 74214309884428239479755 := by
  unfold tailWord_1951180
  simp only [CollatzResearch.WordTrace]
  refine ⟨35582690535607784929457497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47443587380810379905943329 35582690535607784929457497)
  ·
    refine ⟨26687017901705838697093123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35582690535607784929457497 26687017901705838697093123)
    ·
      refine ⟨40030526852558758045639685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26687017901705838697093123 40030526852558758045639685)
      ·
        refine ⟨7505723784854767133557441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40030526852558758045639685 7505723784854767133557441)
        ·
          refine ⟨5629292838641075350168081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7505723784854767133557441 5629292838641075350168081)
          ·
            refine ⟨4221969628980806512626061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5629292838641075350168081 4221969628980806512626061)
            ·
              refine ⟨1583238610867802442234773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4221969628980806512626061 1583238610867802442234773)
              ·
                refine ⟨74214309884428239479755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1583238610867802442234773 74214309884428239479755)
                ·
                  rfl

theorem cell22_1951180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 6].length) (baseStart_1951180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951180 prefixEnd_1951180 := by exact prefixLift 1951180
  have htrace : WordTrace (prefixWord ++ tailWord_1951180) baseStart_1951180 baseEnd_1951180 := by
    simpa [prefixWord, tailWord_1951180, baseEnd_1951180] using wordTrace_append hprefix tailTrace_1951180
  have hstable : (prefixWord ++ tailWord_1951180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951180).length < 2 ^ (prefixWord ++ tailWord_1951180).sum := by decide
  have hdescent : baseEnd_1951180 < baseStart_1951180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951208 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_1951208 : Nat := 118140960795 + 1951208 * 2 ^ 59
def prefixEnd_1951208 : Nat := 4983230072969 + 3 ^ 40 * 1951208 * 2
def baseEnd_1951208 : Nat := 222646124644023805205903

theorem tailTrace_1951208 : CollatzResearch.WordTrace tailWord_1951208 prefixEnd_1951208 222646124644023805205903 := by
  unfold tailWord_1951208
  simp only [CollatzResearch.WordTrace]
  refine ⟨35583201157557065320467139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47444268210076087093956185 35583201157557065320467139)
  ·
    refine ⟨53374801736335597980700709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35583201157557065320467139 53374801736335597980700709)
    ·
      refine ⟨10007775325562924621381383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53374801736335597980700709 10007775325562924621381383)
      ·
        refine ⟨15011662988344386932072075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10007775325562924621381383 15011662988344386932072075)
        ·
          refine ⟨22517494482516580398108113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15011662988344386932072075 22517494482516580398108113)
          ·
            refine ⟨16888120861887435298581085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22517494482516580398108113 16888120861887435298581085)
            ·
              refine ⟨6333045323207788236967907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16888120861887435298581085 6333045323207788236967907)
              ·
                refine ⟨9499567984811682355451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333045323207788236967907 9499567984811682355451861)
                ·
                  refine ⟨222646124644023805205903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9499567984811682355451861 222646124644023805205903)
                  ·
                    rfl

theorem cell22_1951208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_1951208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951208 prefixEnd_1951208 := by exact prefixLift 1951208
  have htrace : WordTrace (prefixWord ++ tailWord_1951208) baseStart_1951208 baseEnd_1951208 := by
    simpa [prefixWord, tailWord_1951208, baseEnd_1951208] using wordTrace_append hprefix tailTrace_1951208
  have hstable : (prefixWord ++ tailWord_1951208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951208).length < 2 ^ (prefixWord ++ tailWord_1951208).sum := by decide
  have hdescent : baseEnd_1951208 < baseStart_1951208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951246 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_1951246 : Nat := 118140960795 + 1951246 * 2 ^ 59
def prefixEnd_1951246 : Nat := 4983230072969 + 3 ^ 40 * 1951246 * 2
def baseEnd_1951246 : Nat := 667951382108651983167593

theorem tailTrace_1951246 : CollatzResearch.WordTrace tailWord_1951246 prefixEnd_1951246 667951382108651983167593 := by
  unfold tailWord_1951246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895973536122057891352199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47445192192650975420545061 8895973536122057891352199)
  ·
    refine ⟨13343960304183086837028299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8895973536122057891352199 13343960304183086837028299)
    ·
      refine ⟨20015940456274630255542449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13343960304183086837028299 20015940456274630255542449)
      ·
        refine ⟨15011955342205972691656837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20015940456274630255542449 15011955342205972691656837)
        ·
          refine ⟨2814741626663619879685657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15011955342205972691656837 2814741626663619879685657)
          ·
            refine ⟨2111056219997714909764243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814741626663619879685657 2111056219997714909764243)
            ·
              refine ⟨3166584329996572364646365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111056219997714909764243 3166584329996572364646365)
              ·
                refine ⟨1187469123748714636742387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3166584329996572364646365 1187469123748714636742387)
                ·
                  refine ⟨1781203685623071955113581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187469123748714636742387 1781203685623071955113581)
                  ·
                    refine ⟨667951382108651983167593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781203685623071955113581 667951382108651983167593)
                    ·
                      rfl

theorem cell22_1951246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_1951246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951246 prefixEnd_1951246 := by exact prefixLift 1951246
  have htrace : WordTrace (prefixWord ++ tailWord_1951246) baseStart_1951246 baseEnd_1951246 := by
    simpa [prefixWord, tailWord_1951246, baseEnd_1951246] using wordTrace_append hprefix tailTrace_1951246
  have hstable : (prefixWord ++ tailWord_1951246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951246).length < 2 ^ (prefixWord ++ tailWord_1951246).sum := by decide
  have hdescent : baseEnd_1951246 < baseStart_1951246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951343 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 9]
def baseStart_1951343 : Nat := 118140960795 + 1951343 * 2 ^ 59
def prefixEnd_1951343 : Nat := 4983230072969 + 3 ^ 40 * 1951343 * 2
def baseEnd_1951343 : Nat := 222661529063658687830765

theorem tailTrace_1951343 : CollatzResearch.WordTrace tailWord_1951343 prefixEnd_1951343 222661529063658687830765 := by
  unfold tailWord_1951343
  simp only [CollatzResearch.WordTrace]
  refine ⟨71171326169625048697098683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47447550779750032464732455 71171326169625048697098683)
  ·
    refine ⟨106756989254437573045648025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71171326169625048697098683 106756989254437573045648025)
    ·
      refine ⟨80067741940828179784236019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106756989254437573045648025 80067741940828179784236019)
      ·
        refine ⟨120101612911242269676354029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80067741940828179784236019 120101612911242269676354029)
        ·
          refine ⟨45038104841715851128632761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120101612911242269676354029 45038104841715851128632761)
          ·
            refine ⟨33778578631286888346474571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45038104841715851128632761 33778578631286888346474571)
            ·
              refine ⟨50667867946930332519711857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33778578631286888346474571 50667867946930332519711857)
              ·
                refine ⟨38000900960197749389783893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50667867946930332519711857 38000900960197749389783893)
                ·
                  refine ⟨222661529063658687830765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38000900960197749389783893 222661529063658687830765)
                  ·
                    rfl

theorem cell22_1951343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_1951343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951343 prefixEnd_1951343 := by exact prefixLift 1951343
  have htrace : WordTrace (prefixWord ++ tailWord_1951343) baseStart_1951343 baseEnd_1951343 := by
    simpa [prefixWord, tailWord_1951343, baseEnd_1951343] using wordTrace_append hprefix tailTrace_1951343
  have hstable : (prefixWord ++ tailWord_1951343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951343).length < 2 ^ (prefixWord ++ tailWord_1951343).sum := by decide
  have hdescent : baseEnd_1951343 < baseStart_1951343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951407 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 1, 4]
def baseStart_1951407 : Nat := 118140960795 + 1951407 * 2 ^ 59
def prefixEnd_1951407 : Nat := 4983230072969 + 3 ^ 40 * 1951407 * 2
def baseEnd_1951407 : Nat := 668006495698901229892099

theorem tailTrace_1951407 : CollatzResearch.WordTrace tailWord_1951407 prefixEnd_1951407 668006495698901229892099 := by
  unfold tailWord_1951407
  simp only [CollatzResearch.WordTrace]
  refine ⟨71173660441393187627428475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47449106960928791751618983 71173660441393187627428475)
  ·
    refine ⟨106760490662089781441142713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71173660441393187627428475 106760490662089781441142713)
    ·
      refine ⟨80070367996567336080857035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106760490662089781441142713 80070367996567336080857035)
      ·
        refine ⟨120105551994851004121285553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80070367996567336080857035 120105551994851004121285553)
        ·
          refine ⟨90079163996138253090964165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120105551994851004121285553 90079163996138253090964165)
          ·
            refine ⟨16889843249275922454555781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90079163996138253090964165 16889843249275922454555781)
            ·
              refine ⟨3166845609239235460229209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16889843249275922454555781 3166845609239235460229209)
              ·
                refine ⟨2375134206929426595171907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166845609239235460229209 2375134206929426595171907)
                ·
                  refine ⟨3562701310394139892757861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375134206929426595171907 3562701310394139892757861)
                  ·
                    refine ⟨668006495698901229892099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3562701310394139892757861 668006495698901229892099)
                    ·
                      rfl

theorem cell22_1951407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_1951407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951407 prefixEnd_1951407 := by exact prefixLift 1951407
  have htrace : WordTrace (prefixWord ++ tailWord_1951407) baseStart_1951407 baseEnd_1951407 := by
    simpa [prefixWord, tailWord_1951407, baseEnd_1951407] using wordTrace_append hprefix tailTrace_1951407
  have hstable : (prefixWord ++ tailWord_1951407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951407).length < 2 ^ (prefixWord ++ tailWord_1951407).sum := by decide
  have hdescent : baseEnd_1951407 < baseStart_1951407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951450 : List Nat := [3, 1, 1, 2, 2, 3, 1, 9]
def baseStart_1951450 : Nat := 118140960795 + 1951450 * 2 ^ 59
def prefixEnd_1951450 : Nat := 4983230072969 + 3 ^ 40 * 1951450 * 2
def baseEnd_1951450 : Nat := 74224579497518161229663

theorem tailTrace_1951450 : CollatzResearch.WordTrace tailWord_1951450 prefixEnd_1951450 74224579497518161229663 := by
  unfold tailWord_1951450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793807195059351492810951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47450152520158270647495869 17793807195059351492810951)
  ·
    refine ⟨26690710792589027239216427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17793807195059351492810951 26690710792589027239216427)
    ·
      refine ⟨40036066188883540858824641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26690710792589027239216427 40036066188883540858824641)
      ·
        refine ⟨30027049641662655644118481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40036066188883540858824641 30027049641662655644118481)
        ·
          refine ⟨22520287231246991733088861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30027049641662655644118481 22520287231246991733088861)
          ·
            refine ⟨8445107711717621899908323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22520287231246991733088861 8445107711717621899908323)
            ·
              refine ⟨12667661567576432849862485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8445107711717621899908323 12667661567576432849862485)
              ·
                refine ⟨74224579497518161229663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12667661567576432849862485 74224579497518161229663)
                ·
                  rfl

theorem cell22_1951450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_1951450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951450 prefixEnd_1951450 := by exact prefixLift 1951450
  have htrace : WordTrace (prefixWord ++ tailWord_1951450) baseStart_1951450 baseEnd_1951450 := by
    simpa [prefixWord, tailWord_1951450, baseEnd_1951450] using wordTrace_append hprefix tailTrace_1951450
  have hstable : (prefixWord ++ tailWord_1951450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951450).length < 2 ^ (prefixWord ++ tailWord_1951450).sum := by decide
  have hdescent : baseEnd_1951450 < baseStart_1951450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951469 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1951469 : Nat := 118140960795 + 1951469 * 2 ^ 59
def prefixEnd_1951469 : Nat := 4983230072969 + 3 ^ 40 * 1951469 * 2
def baseEnd_1951469 : Nat := 668027719565953734841909

theorem tailTrace_1951469 : CollatzResearch.WordTrace tailWord_1951469 prefixEnd_1951469 668027719565953734841909 := by
  unfold tailWord_1951469
  simp only [CollatzResearch.WordTrace]
  refine ⟨71175921767168572216185461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47450614511445714810790307 71175921767168572216185461)
  ·
    refine ⟨6672742665672053645267387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71175921767168572216185461 6672742665672053645267387)
    ·
      refine ⟨10009113998508080467901081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6672742665672053645267387 10009113998508080467901081)
      ·
        refine ⟨7506835498881060350925811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10009113998508080467901081 7506835498881060350925811)
        ·
          refine ⟨11260253248321590526388717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506835498881060350925811 11260253248321590526388717)
          ·
            refine ⟨4222594968120596447395769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11260253248321590526388717 4222594968120596447395769)
            ·
              refine ⟨3166946226090447335546827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222594968120596447395769 3166946226090447335546827)
              ·
                refine ⟨4750419339135671003320241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166946226090447335546827 4750419339135671003320241)
                ·
                  refine ⟨3562814504351753252490181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4750419339135671003320241 3562814504351753252490181)
                  ·
                    refine ⟨668027719565953734841909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3562814504351753252490181 668027719565953734841909)
                    ·
                      rfl

theorem cell22_1951469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1951469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951469 prefixEnd_1951469 := by exact prefixLift 1951469
  have htrace : WordTrace (prefixWord ++ tailWord_1951469) baseStart_1951469 baseEnd_1951469 := by
    simpa [prefixWord, tailWord_1951469, baseEnd_1951469] using wordTrace_append hprefix tailTrace_1951469
  have hstable : (prefixWord ++ tailWord_1951469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951469).length < 2 ^ (prefixWord ++ tailWord_1951469).sum := by decide
  have hdescent : baseEnd_1951469 < baseStart_1951469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951512 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_1951512 : Nat := 118140960795 + 1951512 * 2 ^ 59
def prefixEnd_1951512 : Nat := 4983230072969 + 3 ^ 40 * 1951512 * 2
def baseEnd_1951512 : Nat := 222680813114905318672259

theorem tailTrace_1951512 : CollatzResearch.WordTrace tailWord_1951512 prefixEnd_1951512 222680813114905318672259 := by
  unfold tailWord_1951512
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588745053006395280000395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47451660070675193706667193 35588745053006395280000395)
  ·
    refine ⟨53383117579509592920000593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35588745053006395280000395 53383117579509592920000593)
    ·
      refine ⟨40037338184632194690000445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53383117579509592920000593 40037338184632194690000445)
      ·
        refine ⟨15014001819237073008750167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40037338184632194690000445 15014001819237073008750167)
        ·
          refine ⟨22521002728855609513125251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15014001819237073008750167 22521002728855609513125251)
          ·
            refine ⟨33781504093283414269687877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22521002728855609513125251 33781504093283414269687877)
            ·
              refine ⟨6334032017490640175566477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33781504093283414269687877 6334032017490640175566477)
              ·
                refine ⟨2375262006558990065837429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6334032017490640175566477 2375262006558990065837429)
                ·
                  refine ⟨222680813114905318672259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2375262006558990065837429 222680813114905318672259)
                  ·
                    rfl

theorem cell22_1951512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_1951512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951512 prefixEnd_1951512 := by exact prefixLift 1951512
  have htrace : WordTrace (prefixWord ++ tailWord_1951512) baseStart_1951512 baseEnd_1951512 := by
    simpa [prefixWord, tailWord_1951512, baseEnd_1951512] using wordTrace_append hprefix tailTrace_1951512
  have hstable : (prefixWord ++ tailWord_1951512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951512).length < 2 ^ (prefixWord ++ tailWord_1951512).sum := by decide
  have hdescent : baseEnd_1951512 < baseStart_1951512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951518 : List Nat := [4, 3, 2, 2, 1, 1, 3, 6]
def baseStart_1951518 : Nat := 118140960795 + 1951518 * 2 ^ 59
def prefixEnd_1951518 : Nat := 4983230072969 + 3 ^ 40 * 1951518 * 2
def baseEnd_1951518 : Nat := 74227165918592660040751

theorem tailTrace_1951518 : CollatzResearch.WordTrace tailWord_1951518 prefixEnd_1951518 74227165918592660040751 := by
  unfold tailWord_1951518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897213617998881698089901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47451805962660702389812805 8897213617998881698089901)
  ·
    refine ⟨3336455106749580636783713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8897213617998881698089901 3336455106749580636783713)
    ·
      refine ⟨2502341330062185477587785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3336455106749580636783713 2502341330062185477587785)
      ·
        refine ⟨1876755997546639108190839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2502341330062185477587785 1876755997546639108190839)
        ·
          refine ⟨2815133996319958662286259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876755997546639108190839 2815133996319958662286259)
          ·
            refine ⟨4222700994479937993429389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815133996319958662286259 4222700994479937993429389)
            ·
              refine ⟨1583512872929976747536021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4222700994479937993429389 1583512872929976747536021)
              ·
                refine ⟨74227165918592660040751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1583512872929976747536021 74227165918592660040751)
                ·
                  rfl

theorem cell22_1951518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_1951518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951518 prefixEnd_1951518 := by exact prefixLift 1951518
  have htrace : WordTrace (prefixWord ++ tailWord_1951518) baseStart_1951518 baseEnd_1951518 := by
    simpa [prefixWord, tailWord_1951518, baseEnd_1951518] using wordTrace_append hprefix tailTrace_1951518
  have hstable : (prefixWord ++ tailWord_1951518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951518).length < 2 ^ (prefixWord ++ tailWord_1951518).sum := by decide
  have hdescent : baseEnd_1951518 < baseStart_1951518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951557 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 6]
def baseStart_1951557 : Nat := 118140960795 + 1951557 * 2 ^ 59
def prefixEnd_1951557 : Nat := 4983230072969 + 3 ^ 40 * 1951557 * 2
def baseEnd_1951557 : Nat := 222685947921450279547213

theorem tailTrace_1951557 : CollatzResearch.WordTrace tailWord_1951557 prefixEnd_1951557 222685947921450279547213 := by
  unfold tailWord_1951557
  simp only [CollatzResearch.WordTrace]
  refine ⟨71179131390849763245388925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47452754260566508830259283 71179131390849763245388925)
  ·
    refine ⟨26692174271568661217020847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71179131390849763245388925 26692174271568661217020847)
    ·
      refine ⟨40038261407352991825531271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26692174271568661217020847 40038261407352991825531271)
      ·
        refine ⟨60057392111029487738296907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40038261407352991825531271 60057392111029487738296907)
        ·
          refine ⟨90086088166544231607445361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60057392111029487738296907 90086088166544231607445361)
          ·
            refine ⟨67564566124908173705584021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90086088166544231607445361 67564566124908173705584021)
            ·
              refine ⟨3167089037105070642449251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67564566124908173705584021 3167089037105070642449251)
              ·
                refine ⟨4750633555657605963673877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167089037105070642449251 4750633555657605963673877)
                ·
                  refine ⟨222685947921450279547213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4750633555657605963673877 222685947921450279547213)
                  ·
                    rfl

theorem cell22_1951557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_1951557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951557 prefixEnd_1951557 := by exact prefixLift 1951557
  have htrace : WordTrace (prefixWord ++ tailWord_1951557) baseStart_1951557 baseEnd_1951557 := by
    simpa [prefixWord, tailWord_1951557, baseEnd_1951557] using wordTrace_append hprefix tailTrace_1951557
  have hstable : (prefixWord ++ tailWord_1951557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951557).length < 2 ^ (prefixWord ++ tailWord_1951557).sum := by decide
  have hdescent : baseEnd_1951557 < baseStart_1951557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951651 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 1, 3]
def baseStart_1951651 : Nat := 118140960795 + 1951651 * 2 ^ 59
def prefixEnd_1951651 : Nat := 4983230072969 + 3 ^ 40 * 1951651 * 2
def baseEnd_1951651 : Nat := 668090021885365926791351

theorem tailTrace_1951651 : CollatzResearch.WordTrace tailWord_1951651 prefixEnd_1951651 668090021885365926791351 := by
  unfold tailWord_1951651
  simp only [CollatzResearch.WordTrace]
  refine ⟨71182559852509217299310807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47455039901672811532873871 71182559852509217299310807)
  ·
    refine ⟨106773839778763825948966211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71182559852509217299310807 106773839778763825948966211)
    ·
      refine ⟨160160759668145738923449317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106773839778763825948966211 160160759668145738923449317)
      ·
        refine ⟨30030142437777326048146747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160160759668145738923449317 30030142437777326048146747)
        ·
          refine ⟨45045213656665989072220121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30030142437777326048146747 45045213656665989072220121)
          ·
            refine ⟨33783910242499491804165091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45045213656665989072220121 33783910242499491804165091)
            ·
              refine ⟨50675865363749237706247637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33783910242499491804165091 50675865363749237706247637)
              ·
                refine ⟨1187715594462872758740179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50675865363749237706247637 1187715594462872758740179)
                ·
                  refine ⟨1781573391694309138110269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187715594462872758740179 1781573391694309138110269)
                  ·
                    refine ⟨668090021885365926791351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781573391694309138110269 668090021885365926791351)
                    ·
                      rfl

theorem cell22_1951651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 3].length) (baseStart_1951651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951651 prefixEnd_1951651 := by exact prefixLift 1951651
  have htrace : WordTrace (prefixWord ++ tailWord_1951651) baseStart_1951651 baseEnd_1951651 := by
    simpa [prefixWord, tailWord_1951651, baseEnd_1951651] using wordTrace_append hprefix tailTrace_1951651
  have hstable : (prefixWord ++ tailWord_1951651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951651).length < 2 ^ (prefixWord ++ tailWord_1951651).sum := by decide
  have hdescent : baseEnd_1951651 < baseStart_1951651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951694 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1951694 : Nat := 118140960795 + 1951694 * 2 ^ 59
def prefixEnd_1951694 : Nat := 4983230072969 + 3 ^ 40 * 1951694 * 2
def baseEnd_1951694 : Nat := 668104741664128147966219

theorem tailTrace_1951694 : CollatzResearch.WordTrace tailWord_1951694 prefixEnd_1951694 668104741664128147966219 := by
  unfold tailWord_1951694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898016023919179455390767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47456085460902290428750757 8898016023919179455390767)
  ·
    refine ⟨13347024035878769183086151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898016023919179455390767 13347024035878769183086151)
    ·
      refine ⟨20020536053818153774629227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13347024035878769183086151 20020536053818153774629227)
      ·
        refine ⟨30030804080727230661943841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020536053818153774629227 30030804080727230661943841)
        ·
          refine ⟨22523103060545422996457881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30030804080727230661943841 22523103060545422996457881)
          ·
            refine ⟨16892327295409067247343411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22523103060545422996457881 16892327295409067247343411)
            ·
              refine ⟨25338490943113600871015117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16892327295409067247343411 25338490943113600871015117)
              ·
                refine ⟨9501934103667600326630669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25338490943113600871015117 9501934103667600326630669)
                ·
                  refine ⟨3563225288875350122486501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9501934103667600326630669 3563225288875350122486501)
                  ·
                    refine ⟨668104741664128147966219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3563225288875350122486501 668104741664128147966219)
                    ·
                      rfl

theorem cell22_1951694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1951694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951694 prefixEnd_1951694 := by exact prefixLift 1951694
  have htrace : WordTrace (prefixWord ++ tailWord_1951694) baseStart_1951694 baseEnd_1951694 := by
    simpa [prefixWord, tailWord_1951694, baseEnd_1951694] using wordTrace_append hprefix tailTrace_1951694
  have hstable : (prefixWord ++ tailWord_1951694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951694).length < 2 ^ (prefixWord ++ tailWord_1951694).sum := by decide
  have hdescent : baseEnd_1951694 < baseStart_1951694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951702 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1951702 : Nat := 118140960795 + 1951702 * 2 ^ 59
def prefixEnd_1951702 : Nat := 4983230072969 + 3 ^ 40 * 1951702 * 2
def baseEnd_1951702 : Nat := 668107480227618793766195

theorem tailTrace_1951702 : CollatzResearch.WordTrace tailWord_1951702 prefixEnd_1951702 668107480227618793766195 := by
  unfold tailWord_1951702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449026248457778313088585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47456279983549635339611573 4449026248457778313088585)
  ·
    refine ⟨3336769686343333734816439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4449026248457778313088585 3336769686343333734816439)
    ·
      refine ⟨5005154529515000602224659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3336769686343333734816439 5005154529515000602224659)
      ·
        refine ⟨7507731794272500903336989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005154529515000602224659 7507731794272500903336989)
        ·
          refine ⟨2815399422852187838751371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7507731794272500903336989 2815399422852187838751371)
          ·
            refine ⟨4223099134278281758127057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815399422852187838751371 4223099134278281758127057)
            ·
              refine ⟨3167324350708711318595293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223099134278281758127057 3167324350708711318595293)
              ·
                refine ⟨1187746631515766744473235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3167324350708711318595293 1187746631515766744473235)
                ·
                  refine ⟨1781619947273650116709853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187746631515766744473235 1781619947273650116709853)
                  ·
                    refine ⟨668107480227618793766195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781619947273650116709853 668107480227618793766195)
                    ·
                      rfl

theorem cell22_1951702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1951702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951702 prefixEnd_1951702 := by exact prefixLift 1951702
  have htrace : WordTrace (prefixWord ++ tailWord_1951702) baseStart_1951702 baseEnd_1951702 := by
    simpa [prefixWord, tailWord_1951702, baseEnd_1951702] using wordTrace_append hprefix tailTrace_1951702
  have hstable : (prefixWord ++ tailWord_1951702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951702).length < 2 ^ (prefixWord ++ tailWord_1951702).sum := by decide
  have hdescent : baseEnd_1951702 < baseStart_1951702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951711 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 1, 4]
def baseStart_1951711 : Nat := 118140960795 + 1951711 * 2 ^ 59
def prefixEnd_1951711 : Nat := 4983230072969 + 3 ^ 40 * 1951711 * 2
def baseEnd_1951711 : Nat := 668110561111545770291167

theorem tailTrace_1951711 : CollatzResearch.WordTrace tailWord_1951711 prefixEnd_1951711 668110561111545770291167 := by
  unfold tailWord_1951711
  simp only [CollatzResearch.WordTrace]
  refine ⟨71184748232291847546494987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47456498821527898364329991 71184748232291847546494987)
  ·
    refine ⟨106777122348437771319742481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71184748232291847546494987 106777122348437771319742481)
    ·
      refine ⟨80082841761328328489806861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106777122348437771319742481 80082841761328328489806861)
      ·
        refine ⟨30031065660498123183677573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80082841761328328489806861 30031065660498123183677573)
        ·
          refine ⟨5630824811343398096939545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30031065660498123183677573 5630824811343398096939545)
          ·
            refine ⟨4223118608507548572704659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5630824811343398096939545 4223118608507548572704659)
            ·
              refine ⟨6334677912761322859056989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223118608507548572704659 6334677912761322859056989)
              ·
                refine ⟨2375504217285496072146371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6334677912761322859056989 2375504217285496072146371)
                ·
                  refine ⟨3563256325928244108219557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375504217285496072146371 3563256325928244108219557)
                  ·
                    refine ⟨668110561111545770291167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3563256325928244108219557 668110561111545770291167)
                    ·
                      rfl

theorem cell22_1951711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_1951711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951711 prefixEnd_1951711 := by exact prefixLift 1951711
  have htrace : WordTrace (prefixWord ++ tailWord_1951711) baseStart_1951711 baseEnd_1951711 := by
    simpa [prefixWord, tailWord_1951711, baseEnd_1951711] using wordTrace_append hprefix tailTrace_1951711
  have hstable : (prefixWord ++ tailWord_1951711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951711).length < 2 ^ (prefixWord ++ tailWord_1951711).sum := by decide
  have hdescent : baseEnd_1951711 < baseStart_1951711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951726 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1951726 : Nat := 118140960795 + 1951726 * 2 ^ 59
def prefixEnd_1951726 : Nat := 4983230072969 + 3 ^ 40 * 1951726 * 2
def baseEnd_1951726 : Nat := 222705231972696910388707

theorem tailTrace_1951726 : CollatzResearch.WordTrace tailWord_1951726 prefixEnd_1951726 222705231972696910388707 := by
  unfold tailWord_1951726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898161915904688138536379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47456863551491670072194021 8898161915904688138536379)
  ·
    refine ⟨13347242873857032207804569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898161915904688138536379 13347242873857032207804569)
    ·
      refine ⟨10010432155392774155853427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13347242873857032207804569 10010432155392774155853427)
      ·
        refine ⟨15015648233089161233780141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10010432155392774155853427 15015648233089161233780141)
        ·
          refine ⟨5630868087408435462667553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15015648233089161233780141 5630868087408435462667553)
          ·
            refine ⟨4223151065556326597000665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5630868087408435462667553 4223151065556326597000665)
            ·
              refine ⟨3167363299167244947750499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223151065556326597000665 3167363299167244947750499)
              ·
                refine ⟨4751044948750867421625749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167363299167244947750499 4751044948750867421625749)
                ·
                  refine ⟨222705231972696910388707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4751044948750867421625749 222705231972696910388707)
                  ·
                    rfl

theorem cell22_1951726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1951726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951726 prefixEnd_1951726 := by exact prefixLift 1951726
  have htrace : WordTrace (prefixWord ++ tailWord_1951726) baseStart_1951726 baseEnd_1951726 := by
    simpa [prefixWord, tailWord_1951726, baseEnd_1951726] using wordTrace_append hprefix tailTrace_1951726
  have hstable : (prefixWord ++ tailWord_1951726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951726).length < 2 ^ (prefixWord ++ tailWord_1951726).sum := by decide
  have hdescent : baseEnd_1951726 < baseStart_1951726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951741 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_1951741 : Nat := 118140960795 + 1951741 * 2 ^ 59
def prefixEnd_1951741 : Nat := 4983230072969 + 3 ^ 40 * 1951741 * 2
def baseEnd_1951741 : Nat := 668120830724635692041075

theorem tailTrace_1951741 : CollatzResearch.WordTrace tailWord_1951741 prefixEnd_1951741 668120830724635692041075 := by
  unfold tailWord_1951741
  simp only [CollatzResearch.WordTrace]
  refine ⟨71185842422183162670087077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47457228281455441780058051 71185842422183162670087077)
  ·
    refine ⟨13347345454159343000641327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71185842422183162670087077 13347345454159343000641327)
    ·
      refine ⟨20021018181239014500961991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13347345454159343000641327 20021018181239014500961991)
      ·
        refine ⟨30031527271858521751442987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20021018181239014500961991 30031527271858521751442987)
        ·
          refine ⟨45047290907787782627164481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30031527271858521751442987 45047290907787782627164481)
          ·
            refine ⟨33785468180840836970373361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45047290907787782627164481 33785468180840836970373361)
            ·
              refine ⟨25339101135630627727780021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33785468180840836970373361 25339101135630627727780021)
              ·
                refine ⟨2375540731465371349479377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25339101135630627727780021 2375540731465371349479377)
                ·
                  refine ⟨1781655548599028512109533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2375540731465371349479377 1781655548599028512109533)
                  ·
                    refine ⟨668120830724635692041075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781655548599028512109533 668120830724635692041075)
                    ·
                      rfl

theorem cell22_1951741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_1951741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951741 prefixEnd_1951741 := by exact prefixLift 1951741
  have htrace : WordTrace (prefixWord ++ tailWord_1951741) baseStart_1951741 baseEnd_1951741 := by
    simpa [prefixWord, tailWord_1951741, baseEnd_1951741] using wordTrace_append hprefix tailTrace_1951741
  have hstable : (prefixWord ++ tailWord_1951741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951741).length < 2 ^ (prefixWord ++ tailWord_1951741).sum := by decide
  have hdescent : baseEnd_1951741 < baseStart_1951741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951837 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1951837 : Nat := 118140960795 + 1951837 * 2 ^ 59
def prefixEnd_1951837 : Nat := 4983230072969 + 3 ^ 40 * 1951837 * 2
def baseEnd_1951837 : Nat := 668153693486523441640781

theorem tailTrace_1951837 : CollatzResearch.WordTrace tailWord_1951837 prefixEnd_1951837 668153693486523441640781 := by
  unfold tailWord_1951837
  simp only [CollatzResearch.WordTrace]
  refine ⟨71189343829835371065581765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47459562553223580710387843 71189343829835371065581765)
  ·
    refine ⟨13348001968094132074796581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71189343829835371065581765 13348001968094132074796581)
    ·
      refine ⟨2502750369017649764024359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13348001968094132074796581 2502750369017649764024359)
      ·
        refine ⟨3754125553526474646036539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502750369017649764024359 3754125553526474646036539)
        ·
          refine ⟨5631188330289711969054809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754125553526474646036539 5631188330289711969054809)
          ·
            refine ⟨4223391247717283976791107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5631188330289711969054809 4223391247717283976791107)
            ·
              refine ⟨6335086871575925965186661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223391247717283976791107 6335086871575925965186661)
              ·
                refine ⟨1187828788420486118472499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6335086871575925965186661 1187828788420486118472499)
                ·
                  refine ⟨1781743182630729177708749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187828788420486118472499 1781743182630729177708749)
                  ·
                    refine ⟨668153693486523441640781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781743182630729177708749 668153693486523441640781)
                    ·
                      rfl

theorem cell22_1951837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1951837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951837 prefixEnd_1951837 := by exact prefixLift 1951837
  have htrace : WordTrace (prefixWord ++ tailWord_1951837) baseStart_1951837 baseEnd_1951837 := by
    simpa [prefixWord, tailWord_1951837, baseEnd_1951837] using wordTrace_append hprefix tailTrace_1951837
  have hstable : (prefixWord ++ tailWord_1951837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951837).length < 2 ^ (prefixWord ++ tailWord_1951837).sum := by decide
  have hdescent : baseEnd_1951837 < baseStart_1951837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951876 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1951876 : Nat := 118140960795 + 1951876 * 2 ^ 59
def prefixEnd_1951876 : Nat := 4983230072969 + 3 ^ 40 * 1951876 * 2
def baseEnd_1951876 : Nat := 668167043983540339915661

theorem tailTrace_1951876 : CollatzResearch.WordTrace tailWord_1951876 prefixEnd_1951876 668167043983540339915661 := by
  unfold tailWord_1951876
  simp only [CollatzResearch.WordTrace]
  refine ⟨35595383138347040363125741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47460510851129387150834321 35595383138347040363125741)
  ·
    refine ⟨13348268676880140136172153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35595383138347040363125741 13348268676880140136172153)
    ·
      refine ⟨10011201507660105102129115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13348268676880140136172153 10011201507660105102129115)
      ·
        refine ⟨15016802261490157653193673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10011201507660105102129115 15016802261490157653193673)
        ·
          refine ⟨11262601696117618239895255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15016802261490157653193673 11262601696117618239895255)
          ·
            refine ⟨16893902544176427359842883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11262601696117618239895255 16893902544176427359842883)
            ·
              refine ⟨25340853816264641039764325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16893902544176427359842883 25340853816264641039764325)
              ·
                refine ⟨4751410090549620194955811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25340853816264641039764325 4751410090549620194955811)
                ·
                  refine ⟨7127115135824430292433717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751410090549620194955811 7127115135824430292433717)
                  ·
                    refine ⟨668167043983540339915661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7127115135824430292433717 668167043983540339915661)
                    ·
                      rfl

theorem cell22_1951876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1951876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951876 prefixEnd_1951876 := by exact prefixLift 1951876
  have htrace : WordTrace (prefixWord ++ tailWord_1951876) baseStart_1951876 baseEnd_1951876 := by
    simpa [prefixWord, tailWord_1951876, baseEnd_1951876] using wordTrace_append hprefix tailTrace_1951876
  have hstable : (prefixWord ++ tailWord_1951876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951876).length < 2 ^ (prefixWord ++ tailWord_1951876).sum := by decide
  have hdescent : baseEnd_1951876 < baseStart_1951876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951880 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 1, 4]
def baseStart_1951880 : Nat := 118140960795 + 1951880 * 2 ^ 59
def prefixEnd_1951880 : Nat := 4983230072969 + 3 ^ 40 * 1951880 * 2
def baseEnd_1951880 : Nat := 668168413265285662815649

theorem tailTrace_1951880 : CollatzResearch.WordTrace tailWord_1951880 prefixEnd_1951880 668168413265285662815649 := by
  unfold tailWord_1951880
  simp only [CollatzResearch.WordTrace]
  refine ⟨35595456084339794704698547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47460608112453059606264729 35595456084339794704698547)
  ·
    refine ⟨53393184126509692057047821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35595456084339794704698547 53393184126509692057047821)
    ·
      refine ⟨20022444047441134521392933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53393184126509692057047821 20022444047441134521392933)
      ·
        refine ⟨3754208258895212722761175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20022444047441134521392933 3754208258895212722761175)
        ·
          refine ⟨5631312388342819084141763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754208258895212722761175 5631312388342819084141763)
          ·
            refine ⟨8446968582514228626212645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631312388342819084141763 8446968582514228626212645)
            ·
              refine ⟨1583806609221417867414871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8446968582514228626212645 1583806609221417867414871)
              ·
                refine ⟨2375709913832126801122307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583806609221417867414871 2375709913832126801122307)
                ·
                  refine ⟨3563564870748190201683461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375709913832126801122307 3563564870748190201683461)
                  ·
                    refine ⟨668168413265285662815649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3563564870748190201683461 668168413265285662815649)
                    ·
                      rfl

theorem cell22_1951880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_1951880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951880 prefixEnd_1951880 := by exact prefixLift 1951880
  have htrace : WordTrace (prefixWord ++ tailWord_1951880) baseStart_1951880 baseEnd_1951880 := by
    simpa [prefixWord, tailWord_1951880, baseEnd_1951880] using wordTrace_append hprefix tailTrace_1951880
  have hstable : (prefixWord ++ tailWord_1951880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951880).length < 2 ^ (prefixWord ++ tailWord_1951880).sum := by decide
  have hdescent : baseEnd_1951880 < baseStart_1951880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951951 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 5]
def baseStart_1951951 : Nat := 118140960795 + 1951951 * 2 ^ 59
def prefixEnd_1951951 : Nat := 4983230072969 + 3 ^ 40 * 1951951 * 2
def baseEnd_1951951 : Nat := 222730906005421714763477

theorem tailTrace_1951951 : CollatzResearch.WordTrace tailWord_1951951 prefixEnd_1951951 222730906005421714763477 := by
  unfold tailWord_1951951
  simp only [CollatzResearch.WordTrace]
  refine ⟨71193501751422368535231707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47462334500948245690154471 71193501751422368535231707)
  ·
    refine ⟨106790252627133552802847561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71193501751422368535231707 106790252627133552802847561)
    ·
      refine ⟨80092689470350164602135671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106790252627133552802847561 80092689470350164602135671)
      ·
        refine ⟨120139034205525246903203507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80092689470350164602135671 120139034205525246903203507)
        ·
          refine ⟨180208551308287870354805261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120139034205525246903203507 180208551308287870354805261)
          ·
            refine ⟨67578206740607951383051973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180208551308287870354805261 67578206740607951383051973)
            ·
              refine ⟨12670913763863990884322245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67578206740607951383051973 12670913763863990884322245)
              ·
                refine ⟨2375796330724498290810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12670913763863990884322245 2375796330724498290810421)
                ·
                  refine ⟨222730906005421714763477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2375796330724498290810421 222730906005421714763477)
                  ·
                    rfl

theorem cell22_1951951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 5].length) (baseStart_1951951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1951951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1951951 prefixEnd_1951951 := by exact prefixLift 1951951
  have htrace : WordTrace (prefixWord ++ tailWord_1951951) baseStart_1951951 baseEnd_1951951 := by
    simpa [prefixWord, tailWord_1951951, baseEnd_1951951] using wordTrace_append hprefix tailTrace_1951951
  have hstable : (prefixWord ++ tailWord_1951951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951951).length < 2 ^ (prefixWord ++ tailWord_1951951).sum := by decide
  have hdescent : baseEnd_1951951 < baseStart_1951951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952011 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_1952011 : Nat := 118140960795 + 1952011 * 2 ^ 59
def prefixEnd_1952011 : Nat := 4983230072969 + 3 ^ 40 * 1952011 * 2
def baseEnd_1952011 : Nat := 668213257242444987790247

theorem tailTrace_1952011 : CollatzResearch.WordTrace tailWord_1952011 prefixEnd_1952011 668213257242444987790247 := by
  unfold tailWord_1952011
  simp only [CollatzResearch.WordTrace]
  refine ⟨71195690131204998782415887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47463793420803332521610591 71195690131204998782415887)
  ·
    refine ⟨106793535196807498173623831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71195690131204998782415887 106793535196807498173623831)
    ·
      refine ⟨160190302795211247260435747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106793535196807498173623831 160190302795211247260435747)
      ·
        refine ⟨240285454192816870890653621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160190302795211247260435747 240285454192816870890653621)
        ·
          refine ⟨22526761330576581645998777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240285454192816870890653621 22526761330576581645998777)
          ·
            refine ⟨16895070997932436234499083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22526761330576581645998777 16895070997932436234499083)
            ·
              refine ⟨25342606496898654351748625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16895070997932436234499083 25342606496898654351748625)
              ·
                refine ⟨19006954872673990763811469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25342606496898654351748625 19006954872673990763811469)
                ·
                  refine ⟨7127608077252746536429301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19006954872673990763811469 7127608077252746536429301)
                  ·
                    refine ⟨668213257242444987790247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7127608077252746536429301 668213257242444987790247)
                    ·
                      rfl

theorem cell22_1952011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_1952011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952011 prefixEnd_1952011 := by exact prefixLift 1952011
  have htrace : WordTrace (prefixWord ++ tailWord_1952011) baseStart_1952011 baseEnd_1952011 := by
    simpa [prefixWord, tailWord_1952011, baseEnd_1952011] using wordTrace_append hprefix tailTrace_1952011
  have hstable : (prefixWord ++ tailWord_1952011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952011).length < 2 ^ (prefixWord ++ tailWord_1952011).sum := by decide
  have hdescent : baseEnd_1952011 < baseStart_1952011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952028 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1952028 : Nat := 118140960795 + 1952028 * 2 ^ 59
def prefixEnd_1952028 : Nat := 4983230072969 + 3 ^ 40 * 1952028 * 2
def baseEnd_1952028 : Nat := 668219076689862610115195

theorem tailTrace_1952028 : CollatzResearch.WordTrace tailWord_1952028 prefixEnd_1952028 668219076689862610115195 := by
  unfold tailWord_1952028
  simp only [CollatzResearch.WordTrace]
  refine ⟨35598155086071705342892369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47464206781428940457189825 35598155086071705342892369)
  ·
    refine ⟨26698616314553779007169277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35598155086071705342892369 26698616314553779007169277)
    ·
      refine ⟨10011981117957667127688479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26698616314553779007169277 10011981117957667127688479)
      ·
        refine ⟨15017971676936500691532719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10011981117957667127688479 15017971676936500691532719)
        ·
          refine ⟨22526957515404751037299079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15017971676936500691532719 22526957515404751037299079)
          ·
            refine ⟨33790436273107126555948619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22526957515404751037299079 33790436273107126555948619)
            ·
              refine ⟨50685654409660689833922929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33790436273107126555948619 50685654409660689833922929)
              ·
                refine ⟨38014240807245517375442197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50685654409660689833922929 38014240807245517375442197)
                ·
                  refine ⟨1781917537839633626973853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38014240807245517375442197 1781917537839633626973853)
                  ·
                    refine ⟨668219076689862610115195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781917537839633626973853 668219076689862610115195)
                    ·
                      rfl

theorem cell22_1952028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1952028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952028 prefixEnd_1952028 := by exact prefixLift 1952028
  have htrace : WordTrace (prefixWord ++ tailWord_1952028) baseStart_1952028 baseEnd_1952028 := by
    simpa [prefixWord, tailWord_1952028, baseEnd_1952028] using wordTrace_append hprefix tailTrace_1952028
  have hstable : (prefixWord ++ tailWord_1952028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952028).length < 2 ^ (prefixWord ++ tailWord_1952028).sum := by decide
  have hdescent : baseEnd_1952028 < baseStart_1952028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952030 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1952030 : Nat := 118140960795 + 1952030 * 2 ^ 59
def prefixEnd_1952030 : Nat := 4983230072969 + 3 ^ 40 * 1952030 * 2
def baseEnd_1952030 : Nat := 222739920443578423855063

theorem tailTrace_1952030 : CollatzResearch.WordTrace tailWord_1952030 prefixEnd_1952030 222739920443578423855063 := by
  unfold tailWord_1952030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899547889767020628419693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47464255412090776684905029 8899547889767020628419693)
  ·
    refine ⟨3337330458662632735657385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8899547889767020628419693 3337330458662632735657385)
    ·
      refine ⟨2502997843996974551743039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3337330458662632735657385 2502997843996974551743039)
      ·
        refine ⟨3754496765995461827614559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502997843996974551743039 3754496765995461827614559)
        ·
          refine ⟨5631745148993192741421839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754496765995461827614559 5631745148993192741421839)
          ·
            refine ⟨8447617723489789112132759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631745148993192741421839 8447617723489789112132759)
            ·
              refine ⟨12671426585234683668199139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447617723489789112132759 12671426585234683668199139)
              ·
                refine ⟨19007139877852025502298709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12671426585234683668199139 19007139877852025502298709)
                ·
                  refine ⟨222739920443578423855063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19007139877852025502298709 222739920443578423855063)
                  ·
                    rfl

theorem cell22_1952030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1952030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952030 prefixEnd_1952030 := by exact prefixLift 1952030
  have htrace : WordTrace (prefixWord ++ tailWord_1952030) baseStart_1952030 baseEnd_1952030 := by
    simpa [prefixWord, tailWord_1952030, baseEnd_1952030] using wordTrace_append hprefix tailTrace_1952030
  have hstable : (prefixWord ++ tailWord_1952030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952030).length < 2 ^ (prefixWord ++ tailWord_1952030).sum := by decide
  have hdescent : baseEnd_1952030 < baseStart_1952030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952049 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 1, 4]
def baseStart_1952049 : Nat := 118140960795 + 1952049 * 2 ^ 59
def prefixEnd_1952049 : Nat := 4983230072969 + 3 ^ 40 * 1952049 * 2
def baseEnd_1952049 : Nat := 668226265419025555340131

theorem tailTrace_1952049 : CollatzResearch.WordTrace tailWord_1952049 prefixEnd_1952049 668226265419025555340131 := by
  unfold tailWord_1952049
  simp only [CollatzResearch.WordTrace]
  refine ⟨71197076105067331272299201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47464717403378220848199467 71197076105067331272299201)
  ·
    refine ⟨53397807078800498454224401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71197076105067331272299201 53397807078800498454224401)
    ·
      refine ⟨40048355309100373840668301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53397807078800498454224401 40048355309100373840668301)
      ·
        refine ⟨15018133240912640190250613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40048355309100373840668301 15018133240912640190250613)
        ·
          refine ⟨1407949991335560017835995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15018133240912640190250613 1407949991335560017835995)
          ·
            refine ⟨2111924987003340026753993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407949991335560017835995 2111924987003340026753993)
            ·
              refine ⟨1583943740252505020065495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111924987003340026753993 1583943740252505020065495)
              ·
                refine ⟨2375915610378757530098243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583943740252505020065495 2375915610378757530098243)
                ·
                  refine ⟨3563873415568136295147365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375915610378757530098243 3563873415568136295147365)
                  ·
                    refine ⟨668226265419025555340131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3563873415568136295147365 668226265419025555340131)
                    ·
                      rfl

theorem cell22_1952049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_1952049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952049 prefixEnd_1952049 := by exact prefixLift 1952049
  have htrace : WordTrace (prefixWord ++ tailWord_1952049) baseStart_1952049 baseEnd_1952049 := by
    simpa [prefixWord, tailWord_1952049, baseEnd_1952049] using wordTrace_append hprefix tailTrace_1952049
  have hstable : (prefixWord ++ tailWord_1952049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952049).length < 2 ^ (prefixWord ++ tailWord_1952049).sum := by decide
  have hdescent : baseEnd_1952049 < baseStart_1952049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952062 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1952062 : Nat := 118140960795 + 1952062 * 2 ^ 59
def prefixEnd_1952062 : Nat := 4983230072969 + 3 ^ 40 * 1952062 * 2
def baseEnd_1952062 : Nat := 668230715584697854765091

theorem tailTrace_1952062 : CollatzResearch.WordTrace tailWord_1952062 prefixEnd_1952062 668230715584697854765091 := by
  unfold tailWord_1952062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899693781752529311565305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47465033502680156328348293 8899693781752529311565305)
  ·
    refine ⟨6674770336314396983673979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8899693781752529311565305 6674770336314396983673979)
    ·
      refine ⟨10012155504471595475510969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6674770336314396983673979 10012155504471595475510969)
      ·
        refine ⟨7509116628353696606633227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10012155504471595475510969 7509116628353696606633227)
        ·
          refine ⟨11263674942530544909949841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509116628353696606633227 11263674942530544909949841)
          ·
            refine ⟨8447756206897908682462381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11263674942530544909949841 8447756206897908682462381)
            ·
              refine ⟨3167908577586715755923393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8447756206897908682462381 3167908577586715755923393)
              ·
                refine ⟨2375931433190036816942545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167908577586715755923393 2375931433190036816942545)
                ·
                  refine ⟨1781948574892527612706909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2375931433190036816942545 1781948574892527612706909)
                  ·
                    refine ⟨668230715584697854765091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781948574892527612706909 668230715584697854765091)
                    ·
                      rfl

theorem cell22_1952062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1952062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952062 prefixEnd_1952062 := by exact prefixLift 1952062
  have htrace : WordTrace (prefixWord ++ tailWord_1952062) baseStart_1952062 baseEnd_1952062 := by
    simpa [prefixWord, tailWord_1952062, baseEnd_1952062] using wordTrace_append hprefix tailTrace_1952062
  have hstable : (prefixWord ++ tailWord_1952062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952062).length < 2 ^ (prefixWord ++ tailWord_1952062).sum := by decide
  have hdescent : baseEnd_1952062 < baseStart_1952062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952103 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 7]
def baseStart_1952103 : Nat := 118140960795 + 1952103 * 2 ^ 59
def prefixEnd_1952103 : Nat := 4983230072969 + 3 ^ 40 * 1952103 * 2
def baseEnd_1952103 : Nat := 222748250240862471496655

theorem tailTrace_1952103 : CollatzResearch.WordTrace tailWord_1952103 prefixEnd_1952103 222748250240862471496655 := by
  unfold tailWord_1952103
  simp only [CollatzResearch.WordTrace]
  refine ⟨71199045646871698494764963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47466030431247798996509975 71199045646871698494764963)
  ·
    refine ⟨106798568470307547742147445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71199045646871698494764963 106798568470307547742147445)
    ·
      refine ⟨10012365794091332600826323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106798568470307547742147445 10012365794091332600826323)
      ·
        refine ⟨15018548691136998901239485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012365794091332600826323 15018548691136998901239485)
        ·
          refine ⟨5631955759176374587964807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15018548691136998901239485 5631955759176374587964807)
          ·
            refine ⟨8447933638764561881947211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631955759176374587964807 8447933638764561881947211)
            ·
              refine ⟨12671900458146842822920817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447933638764561881947211 12671900458146842822920817)
              ·
                refine ⟨9503925343610132117190613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12671900458146842822920817 9503925343610132117190613)
                ·
                  refine ⟨222748250240862471496655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9503925343610132117190613 222748250240862471496655)
                  ·
                    rfl

theorem cell22_1952103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 7].length) (baseStart_1952103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1952103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1952103 prefixEnd_1952103 := by exact prefixLift 1952103
  have htrace : WordTrace (prefixWord ++ tailWord_1952103) baseStart_1952103 baseEnd_1952103 := by
    simpa [prefixWord, tailWord_1952103, baseEnd_1952103] using wordTrace_append hprefix tailTrace_1952103
  have hstable : (prefixWord ++ tailWord_1952103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952103).length < 2 ^ (prefixWord ++ tailWord_1952103).sum := by decide
  have hdescent : baseEnd_1952103 < baseStart_1952103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
