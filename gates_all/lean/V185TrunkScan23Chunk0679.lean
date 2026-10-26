import V185TrunkScan23Chunk0678

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4014947 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 1, 4, 2]
def baseStart_4014947 : Nat := 118140960795 + 4014947 * 2 ^ 59
def prefixEnd_4014947 : Nat := 4983230072969 + 3 ^ 40 * 4014947 * 2
def baseEnd_4014947 : Nat := 2061597613327208235098101

theorem tailTrace_4014947 : CollatzResearch.WordTrace tailWord_4014947 prefixEnd_4014947 2061597613327208235098101 := by
  unfold tailWord_4014947
  simp only [CollatzResearch.WordTrace]
  refine ⟨146437147385540192201475095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97624764923693461467650063 146437147385540192201475095)
  ·
    refine ⟨219655721078310288302212643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146437147385540192201475095 219655721078310288302212643)
    ·
      refine ⟨329483581617465432453318965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219655721078310288302212643 329483581617465432453318965)
      ·
        refine ⟨30889085776637384292498653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329483581617465432453318965 30889085776637384292498653)
        ·
          refine ⟨11583407166239019109686995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30889085776637384292498653 11583407166239019109686995)
          ·
            refine ⟨17375110749358528664530493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583407166239019109686995 17375110749358528664530493)
            ·
              refine ⟨6515666531009448249198935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17375110749358528664530493 6515666531009448249198935)
              ·
                refine ⟨9773499796514172373798403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515666531009448249198935 9773499796514172373798403)
                ·
                  refine ⟨14660249694771258560697605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9773499796514172373798403 14660249694771258560697605)
                  ·
                    refine ⟨2748796817769610980130801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14660249694771258560697605 2748796817769610980130801)
                    ·
                      refine ⟨2061597613327208235098101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748796817769610980130801 2061597613327208235098101)
                      ·
                        rfl

theorem cell23_4014947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_4014947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014947 prefixEnd_4014947 := by exact prefixLift 4014947
  have htrace : WordTrace (prefixWord ++ tailWord_4014947) baseStart_4014947 baseEnd_4014947 := by
    simpa [prefixWord, tailWord_4014947, baseEnd_4014947] using wordTrace_append hprefix tailTrace_4014947
  have hstable : (prefixWord ++ tailWord_4014947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014947).length < 2 ^ (prefixWord ++ tailWord_4014947).sum := by decide
  have hdescent : baseEnd_4014947 < baseStart_4014947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014963 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 3]
def baseStart_4014963 : Nat := 118140960795 + 4014963 * 2 ^ 59
def prefixEnd_4014963 : Nat := 4983230072969 + 3 ^ 40 * 4014963 * 2
def baseEnd_4014963 : Nat := 2061605829017680172498027

theorem tailTrace_4014963 : CollatzResearch.WordTrace tailWord_4014963 prefixEnd_4014963 2061605829017680172498027 := by
  unfold tailWord_4014963
  simp only [CollatzResearch.WordTrace]
  refine ⟨146437730953482226934057543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97625153968988151289371695 146437730953482226934057543)
  ·
    refine ⟨219656596430223340401086315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146437730953482226934057543 219656596430223340401086315)
    ·
      refine ⟨329484894645335010601629473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219656596430223340401086315 329484894645335010601629473)
      ·
        refine ⟨247113670984001257951222105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329484894645335010601629473 247113670984001257951222105)
        ·
          refine ⟨185335253238000943463416579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247113670984001257951222105 185335253238000943463416579)
          ·
            refine ⟨278002879857001415195124869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185335253238000943463416579 278002879857001415195124869)
            ·
              refine ⟨52125539973187765349085913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278002879857001415195124869 52125539973187765349085913)
              ·
                refine ⟨39094154979890824011814435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52125539973187765349085913 39094154979890824011814435)
                ·
                  refine ⟨58641232469836236017721653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39094154979890824011814435 58641232469836236017721653)
                  ·
                    refine ⟨5497615544047147126661405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58641232469836236017721653 5497615544047147126661405)
                    ·
                      refine ⟨2061605829017680172498027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497615544047147126661405 2061605829017680172498027)
                      ·
                        rfl

theorem cell23_4014963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_4014963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014963 prefixEnd_4014963 := by exact prefixLift 4014963
  have htrace : WordTrace (prefixWord ++ tailWord_4014963) baseStart_4014963 baseEnd_4014963 := by
    simpa [prefixWord, tailWord_4014963, baseEnd_4014963] using wordTrace_append hprefix tailTrace_4014963
  have hstable : (prefixWord ++ tailWord_4014963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014963).length < 2 ^ (prefixWord ++ tailWord_4014963).sum := by decide
  have hdescent : baseEnd_4014963 < baseStart_4014963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015020 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 6, 2]
def baseStart_4015020 : Nat := 118140960795 + 4015020 * 2 ^ 59
def prefixEnd_4015020 : Nat := 4983230072969 + 3 ^ 40 * 4015020 * 2
def baseEnd_4015020 : Nat := 2061635097414986449485265

theorem tailTrace_4015020 : CollatzResearch.WordTrace tailWord_4015020 prefixEnd_4015020 2061635097414986449485265 := by
  unfold tailWord_4015020
  simp only [CollatzResearch.WordTrace]
  refine ⟨73219904957137862834441257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97626539942850483779255009 73219904957137862834441257)
  ·
    refine ⟨54914928717853397125830943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73219904957137862834441257 54914928717853397125830943)
    ·
      refine ⟨82372393076780095688746415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54914928717853397125830943 82372393076780095688746415)
      ·
        refine ⟨123558589615170143533119623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82372393076780095688746415 123558589615170143533119623)
        ·
          refine ⟨185337884422755215299679435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123558589615170143533119623 185337884422755215299679435)
          ·
            refine ⟨278006826634132822949519153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185337884422755215299679435 278006826634132822949519153)
            ·
              refine ⟨208505119975599617212139365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278006826634132822949519153 208505119975599617212139365)
              ·
                refine ⟨39094709995424928227276131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208505119975599617212139365 39094709995424928227276131)
                ·
                  refine ⟨58642064993137392340914197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39094709995424928227276131 58642064993137392340914197)
                  ·
                    refine ⟨2748846796553315265980353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58642064993137392340914197 2748846796553315265980353)
                    ·
                      refine ⟨2061635097414986449485265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748846796553315265980353 2061635097414986449485265)
                      ·
                        rfl

theorem cell23_4015020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_4015020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015020 prefixEnd_4015020 := by exact prefixLift 4015020
  have htrace : WordTrace (prefixWord ++ tailWord_4015020) baseStart_4015020 baseEnd_4015020 := by
    simpa [prefixWord, tailWord_4015020, baseEnd_4015020] using wordTrace_append hprefix tailTrace_4015020
  have hstable : (prefixWord ++ tailWord_4015020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015020).length < 2 ^ (prefixWord ++ tailWord_4015020).sum := by decide
  have hdescent : baseEnd_4015020 < baseStart_4015020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015063 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_4015063 : Nat := 118140960795 + 4015063 * 2 ^ 59
def prefixEnd_4015063 : Nat := 4983230072969 + 3 ^ 40 * 4015063 * 2
def baseEnd_4015063 : Nat := 2061657177083129781247567

theorem tailTrace_4015063 : CollatzResearch.WordTrace tailWord_4015063 prefixEnd_4015063 2061657177083129781247567 := by
  unfold tailWord_4015063
  simp only [CollatzResearch.WordTrace]
  refine ⟨146441378253119944012697843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97627585502079962675131895 146441378253119944012697843)
  ·
    refine ⟨219662067379679916019046765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146441378253119944012697843 219662067379679916019046765)
    ·
      refine ⟨82373275267379968507142537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219662067379679916019046765 82373275267379968507142537)
      ·
        refine ⟨61779956450534976380356903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82373275267379968507142537 61779956450534976380356903)
        ·
          refine ⟨92669934675802464570535355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61779956450534976380356903 92669934675802464570535355)
          ·
            refine ⟨139004902013703696855803033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92669934675802464570535355 139004902013703696855803033)
            ·
              refine ⟨104253676510277772641852275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139004902013703696855803033 104253676510277772641852275)
              ·
                refine ⟨156380514765416658962778413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104253676510277772641852275 156380514765416658962778413)
                ·
                  refine ⟨58642693037031247111041905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156380514765416658962778413 58642693037031247111041905)
                  ·
                    refine ⟨43982019777773435333281429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58642693037031247111041905 43982019777773435333281429)
                    ·
                      refine ⟨2061657177083129781247567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43982019777773435333281429 2061657177083129781247567)
                      ·
                        rfl

theorem cell23_4015063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_4015063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015063 prefixEnd_4015063 := by exact prefixLift 4015063
  have htrace : WordTrace (prefixWord ++ tailWord_4015063) baseStart_4015063 baseEnd_4015063 := by
    simpa [prefixWord, tailWord_4015063, baseEnd_4015063] using wordTrace_append hprefix tailTrace_4015063
  have hstable : (prefixWord ++ tailWord_4015063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015063).length < 2 ^ (prefixWord ++ tailWord_4015063).sum := by decide
  have hdescent : baseEnd_4015063 < baseStart_4015063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015074 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4015074 : Nat := 118140960795 + 4015074 * 2 ^ 59
def prefixEnd_4015074 : Nat := 4983230072969 + 3 ^ 40 * 4015074 * 2
def baseEnd_4015074 : Nat := 2061662825370329238210017

theorem tailTrace_4015074 : CollatzResearch.WordTrace tailWord_4015074 prefixEnd_4015074 2061662825370329238210017 := by
  unfold tailWord_4015074
  simp only [CollatzResearch.WordTrace]
  refine ⟨36610444864020023222837069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97627852970720061927565517 36610444864020023222837069)
  ·
    refine ⟨13728916824007508708563901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36610444864020023222837069 13728916824007508708563901)
    ·
      refine ⟨5148343809002815765711463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13728916824007508708563901 5148343809002815765711463)
      ·
        refine ⟨7722515713504223648567195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148343809002815765711463 7722515713504223648567195)
        ·
          refine ⟨11583773570256335472850793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722515713504223648567195 11583773570256335472850793)
          ·
            refine ⟨8687830177692251604638095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11583773570256335472850793 8687830177692251604638095)
            ·
              refine ⟨13031745266538377406957143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687830177692251604638095 13031745266538377406957143)
              ·
                refine ⟨19547617899807566110435715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13031745266538377406957143 19547617899807566110435715)
                ·
                  refine ⟨29321426849711349165653573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19547617899807566110435715 29321426849711349165653573)
                  ·
                    refine ⟨5497767534320877968560045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29321426849711349165653573 5497767534320877968560045)
                    ·
                      refine ⟨2061662825370329238210017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497767534320877968560045 2061662825370329238210017)
                      ·
                        rfl

theorem cell23_4015074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4015074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015074 prefixEnd_4015074 := by exact prefixLift 4015074
  have htrace : WordTrace (prefixWord ++ tailWord_4015074) baseStart_4015074 baseEnd_4015074 := by
    simpa [prefixWord, tailWord_4015074, baseEnd_4015074] using wordTrace_append hprefix tailTrace_4015074
  have hstable : (prefixWord ++ tailWord_4015074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015074).length < 2 ^ (prefixWord ++ tailWord_4015074).sum := by decide
  have hdescent : baseEnd_4015074 < baseStart_4015074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015083 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_4015083 : Nat := 118140960795 + 4015083 * 2 ^ 59
def prefixEnd_4015083 : Nat := 4983230072969 + 3 ^ 40 * 4015083 * 2
def baseEnd_4015083 : Nat := 2061667446696219702997475

theorem tailTrace_4015083 : CollatzResearch.WordTrace tailWord_4015083 prefixEnd_4015083 2061667446696219702997475 := by
  unfold tailWord_4015083
  simp only [CollatzResearch.WordTrace]
  refine ⟨146442107713047487428425903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97628071808698324952283935 146442107713047487428425903)
  ·
    refine ⟨219663161569571231142638855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146442107713047487428425903 219663161569571231142638855)
    ·
      refine ⟨329494742354356846713958283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219663161569571231142638855 329494742354356846713958283)
      ·
        refine ⟨494242113531535270070937425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329494742354356846713958283 494242113531535270070937425)
        ·
          refine ⟨370681585148651452553203069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494242113531535270070937425 370681585148651452553203069)
          ·
            refine ⟨139005594430744294707451151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370681585148651452553203069 139005594430744294707451151)
            ·
              refine ⟨208508391646116442061176727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139005594430744294707451151 208508391646116442061176727)
              ·
                refine ⟨312762587469174663091765091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208508391646116442061176727 312762587469174663091765091)
                ·
                  refine ⟨469143881203761994637647637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312762587469174663091765091 469143881203761994637647637)
                  ·
                    refine ⟨21991119431426343498639733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 469143881203761994637647637 21991119431426343498639733)
                    ·
                      refine ⟨2061667446696219702997475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21991119431426343498639733 2061667446696219702997475)
                      ·
                        rfl

theorem cell23_4015083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_4015083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015083 prefixEnd_4015083 := by exact prefixLift 4015083
  have htrace : WordTrace (prefixWord ++ tailWord_4015083) baseStart_4015083 baseEnd_4015083 := by
    simpa [prefixWord, tailWord_4015083, baseEnd_4015083] using wordTrace_append hprefix tailTrace_4015083
  have hstable : (prefixWord ++ tailWord_4015083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015083).length < 2 ^ (prefixWord ++ tailWord_4015083).sum := by decide
  have hdescent : baseEnd_4015083 < baseStart_4015083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015094 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_4015094 : Nat := 118140960795 + 4015094 * 2 ^ 59
def prefixEnd_4015094 : Nat := 4983230072969 + 3 ^ 40 * 4015094 * 2
def baseEnd_4015094 : Nat := 229074788331491017773325

theorem tailTrace_4015094 : CollatzResearch.WordTrace tailWord_4015094 prefixEnd_4015094 229074788331491017773325 := by
  unfold tailWord_4015094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152656807250477269192271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97628339277338424204717557 9152656807250477269192271)
  ·
    refine ⟨13728985210875715903788407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9152656807250477269192271 13728985210875715903788407)
    ·
      refine ⟨20593477816313573855682611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13728985210875715903788407 20593477816313573855682611)
      ·
        refine ⟨30890216724470360783523917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20593477816313573855682611 30890216724470360783523917)
        ·
          refine ⟨11583831271676385293821469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30890216724470360783523917 11583831271676385293821469)
          ·
            refine ⟨4343936726878644485183051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11583831271676385293821469 4343936726878644485183051)
            ·
              refine ⟨6515905090317966727774577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343936726878644485183051 6515905090317966727774577)
              ·
                refine ⟨4886928817738475045830933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515905090317966727774577 4886928817738475045830933)
                ·
                  refine ⟨229074788331491017773325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4886928817738475045830933 229074788331491017773325)
                  ·
                    rfl

theorem cell23_4015094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_4015094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015094 prefixEnd_4015094 := by exact prefixLift 4015094
  have htrace : WordTrace (prefixWord ++ tailWord_4015094) baseStart_4015094 baseEnd_4015094 := by
    simpa [prefixWord, tailWord_4015094, baseEnd_4015094] using wordTrace_append hprefix tailTrace_4015094
  have hstable : (prefixWord ++ tailWord_4015094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015094).length < 2 ^ (prefixWord ++ tailWord_4015094).sum := by decide
  have hdescent : baseEnd_4015094 < baseStart_4015094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015097 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 4, 3, 2]
def baseStart_4015097 : Nat := 118140960795 + 4015097 * 2 ^ 59
def prefixEnd_4015097 : Nat := 4983230072969 + 3 ^ 40 * 4015097 * 2
def baseEnd_4015097 : Nat := 2061674635425382648222411

theorem tailTrace_4015097 : CollatzResearch.WordTrace tailWord_4015097 prefixEnd_4015097 2061674635425382648222411 := by
  unfold tailWord_4015097
  simp only [CollatzResearch.WordTrace]
  refine ⟨146442618334996767819435545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97628412223331178546290363 146442618334996767819435545)
  ·
    refine ⟨109831963751247575864576659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146442618334996767819435545 109831963751247575864576659)
    ·
      refine ⟨164747945626871363796864989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109831963751247575864576659 164747945626871363796864989)
      ·
        refine ⟨61780479610076761423824371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164747945626871363796864989 61780479610076761423824371)
        ·
          refine ⟨92670719415115142135736557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61780479610076761423824371 92670719415115142135736557)
          ·
            refine ⟨34751519780668178300901209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92670719415115142135736557 34751519780668178300901209)
            ·
              refine ⟨26063639835501133725675907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34751519780668178300901209 26063639835501133725675907)
              ·
                refine ⟨39095459753251700588513861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26063639835501133725675907 39095459753251700588513861)
                ·
                  refine ⟨7330398703734693860346349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39095459753251700588513861 7330398703734693860346349)
                  ·
                    refine ⟨2748899513900510197629881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7330398703734693860346349 2748899513900510197629881)
                    ·
                      refine ⟨2061674635425382648222411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748899513900510197629881 2061674635425382648222411)
                      ·
                        rfl

theorem cell23_4015097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_4015097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015097 prefixEnd_4015097 := by exact prefixLift 4015097
  have htrace : WordTrace (prefixWord ++ tailWord_4015097) baseStart_4015097 baseEnd_4015097 := by
    simpa [prefixWord, tailWord_4015097, baseEnd_4015097] using wordTrace_append hprefix tailTrace_4015097
  have hstable : (prefixWord ++ tailWord_4015097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015097).length < 2 ^ (prefixWord ++ tailWord_4015097).sum := by decide
  have hdescent : baseEnd_4015097 < baseStart_4015097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015103 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 10]
def baseStart_4015103 : Nat := 118140960795 + 4015103 * 2 ^ 59
def prefixEnd_4015103 : Nat := 4983230072969 + 3 ^ 40 * 4015103 * 2
def baseEnd_4015103 : Nat := 687225905436436541582461

theorem tailTrace_4015103 : CollatzResearch.WordTrace tailWord_4015103 prefixEnd_4015103 687225905436436541582461 := by
  unfold tailWord_4015103
  simp only [CollatzResearch.WordTrace]
  refine ⟨146442837172975030844153963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97628558115316687229435975 146442837172975030844153963)
  ·
    refine ⟨219664255759462546266230945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146442837172975030844153963 219664255759462546266230945)
    ·
      refine ⟨164748191819596909699673209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219664255759462546266230945 164748191819596909699673209)
      ·
        refine ⟨123561143864697682274754907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164748191819596909699673209 123561143864697682274754907)
        ·
          refine ⟨185341715797046523412132361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123561143864697682274754907 185341715797046523412132361)
          ·
            refine ⟨139006286847784892559099271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185341715797046523412132361 139006286847784892559099271)
            ·
              refine ⟨208509430271677338838648907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139006286847784892559099271 208509430271677338838648907)
              ·
                refine ⟨312764145407516008257973361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208509430271677338838648907 312764145407516008257973361)
                ·
                  refine ⟨234573109055637006193480021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312764145407516008257973361 234573109055637006193480021)
                  ·
                    refine ⟨687225905436436541582461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 234573109055637006193480021 687225905436436541582461)
                    ·
                      rfl

theorem cell23_4015103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_4015103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015103 prefixEnd_4015103 := by exact prefixLift 4015103
  have htrace : WordTrace (prefixWord ++ tailWord_4015103) baseStart_4015103 baseEnd_4015103 := by
    simpa [prefixWord, tailWord_4015103, baseEnd_4015103] using wordTrace_append hprefix tailTrace_4015103
  have hstable : (prefixWord ++ tailWord_4015103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015103).length < 2 ^ (prefixWord ++ tailWord_4015103).sum := by decide
  have hdescent : baseEnd_4015103 < baseStart_4015103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015120 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 8, 4]
def baseStart_4015120 : Nat := 118140960795 + 4015120 * 2 ^ 59
def prefixEnd_4015120 : Nat := 4983230072969 + 3 ^ 40 * 4015120 * 2
def baseEnd_4015120 : Nat := 687228815160145352744935

theorem tailTrace_4015120 : CollatzResearch.WordTrace tailWord_4015120 prefixEnd_4015120 687228815160145352744935 := by
  unfold tailWord_4015120
  simp only [CollatzResearch.WordTrace]
  refine ⟨73221728606956721373761407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97628971475942295165015209 73221728606956721373761407)
  ·
    refine ⟨109832592910435082060642111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73221728606956721373761407 109832592910435082060642111)
    ·
      refine ⟨164748889365652623090963167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109832592910435082060642111 164748889365652623090963167)
      ·
        refine ⟨247123334048478934636444751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164748889365652623090963167 247123334048478934636444751)
        ·
          refine ⟨370685001072718401954667127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247123334048478934636444751 370685001072718401954667127)
          ·
            refine ⟨556027501609077602932000691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370685001072718401954667127 556027501609077602932000691)
            ·
              refine ⟨834041252413616404398001037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556027501609077602932000691 834041252413616404398001037)
              ·
                refine ⟨312765469655106151649250389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 834041252413616404398001037 312765469655106151649250389)
                ·
                  refine ⟨3665220347520775214639653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 312765469655106151649250389 3665220347520775214639653)
                  ·
                    refine ⟨687228815160145352744935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665220347520775214639653 687228815160145352744935)
                    ·
                      rfl

theorem cell23_4015120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_4015120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015120 prefixEnd_4015120 := by exact prefixLift 4015120
  have htrace : WordTrace (prefixWord ++ tailWord_4015120) baseStart_4015120 baseEnd_4015120 := by
    simpa [prefixWord, tailWord_4015120, baseEnd_4015120] using wordTrace_append hprefix tailTrace_4015120
  have hstable : (prefixWord ++ tailWord_4015120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015120).length < 2 ^ (prefixWord ++ tailWord_4015120).sum := by decide
  have hdescent : baseEnd_4015120 < baseStart_4015120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015130 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_4015130 : Nat := 118140960795 + 4015130 * 2 ^ 59
def prefixEnd_4015130 : Nat := 4983230072969 + 3 ^ 40 * 4015130 * 2
def baseEnd_4015130 : Nat := 2061691580286981019109759

theorem tailTrace_4015130 : CollatzResearch.WordTrace tailWord_4015130 prefixEnd_4015130 2061691580286981019109759 := by
  unfold tailWord_4015130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36610955485969303613846711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97629214629251476303591229 36610955485969303613846711)
  ·
    refine ⟨54916433228953955420770067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36610955485969303613846711 54916433228953955420770067)
    ·
      refine ⟨82374649843430933131155101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54916433228953955420770067 82374649843430933131155101)
      ·
        refine ⟨30890493691286599924183163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82374649843430933131155101 30890493691286599924183163)
        ·
          refine ⟨46335740536929899886274745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30890493691286599924183163 46335740536929899886274745)
          ·
            refine ⟨34751805402697424914706059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46335740536929899886274745 34751805402697424914706059)
            ·
              refine ⟨52127708104046137372059089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34751805402697424914706059 52127708104046137372059089)
              ·
                refine ⟨39095781078034603029044317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52127708104046137372059089 39095781078034603029044317)
                ·
                  refine ⟨14660917904262976135891619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39095781078034603029044317 14660917904262976135891619)
                  ·
                    refine ⟨21991376856394464203837429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14660917904262976135891619 21991376856394464203837429)
                    ·
                      refine ⟨2061691580286981019109759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21991376856394464203837429 2061691580286981019109759)
                      ·
                        rfl

theorem cell23_4015130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_4015130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015130 prefixEnd_4015130 := by exact prefixLift 4015130
  have htrace : WordTrace (prefixWord ++ tailWord_4015130) baseStart_4015130 baseEnd_4015130 := by
    simpa [prefixWord, tailWord_4015130, baseEnd_4015130] using wordTrace_append hprefix tailTrace_4015130
  have hstable : (prefixWord ++ tailWord_4015130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015130).length < 2 ^ (prefixWord ++ tailWord_4015130).sum := by decide
  have hdescent : baseEnd_4015130 < baseStart_4015130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015137 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 4, 4]
def baseStart_4015137 : Nat := 118140960795 + 4015137 * 2 ^ 59
def prefixEnd_4015137 : Nat := 4983230072969 + 3 ^ 40 * 4015137 * 2
def baseEnd_4015137 : Nat := 687231724883854163907409

theorem tailTrace_4015137 : CollatzResearch.WordTrace tailWord_4015137 prefixEnd_4015137 687231724883854163907409 := by
  unfold tailWord_4015137
  simp only [CollatzResearch.WordTrace]
  refine ⟨146444077254851854650891665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97629384836567903100594443 146444077254851854650891665)
  ·
    refine ⟨109833057941138890988168749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146444077254851854650891665 109833057941138890988168749)
    ·
      refine ⟨41187396727927084120563281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109833057941138890988168749 41187396727927084120563281)
      ·
        refine ⟨30890547545945313090422461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41187396727927084120563281 30890547545945313090422461)
        ·
          refine ⟨11583955329729492408908423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30890547545945313090422461 11583955329729492408908423)
          ·
            refine ⟨17375932994594238613362635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583955329729492408908423 17375932994594238613362635)
            ·
              refine ⟨26063899491891357920043953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17375932994594238613362635 26063899491891357920043953)
              ·
                refine ⟨19547924618918518440032965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26063899491891357920043953 19547924618918518440032965)
                ·
                  refine ⟨3665235866047222207506181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19547924618918518440032965 3665235866047222207506181)
                  ·
                    refine ⟨687231724883854163907409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665235866047222207506181 687231724883854163907409)
                    ·
                      rfl

theorem cell23_4015137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_4015137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015137 prefixEnd_4015137 := by exact prefixLift 4015137
  have htrace : WordTrace (prefixWord ++ tailWord_4015137) baseStart_4015137 baseEnd_4015137 := by
    simpa [prefixWord, tailWord_4015137, baseEnd_4015137] using wordTrace_append hprefix tailTrace_4015137
  have hstable : (prefixWord ++ tailWord_4015137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015137).length < 2 ^ (prefixWord ++ tailWord_4015137).sum := by decide
  have hdescent : baseEnd_4015137 < baseStart_4015137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015138 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_4015138 : Nat := 118140960795 + 4015138 * 2 ^ 59
def prefixEnd_4015138 : Nat := 4983230072969 + 3 ^ 40 * 4015138 * 2
def baseEnd_4015138 : Nat := 2061695688132216987809723

theorem tailTrace_4015138 : CollatzResearch.WordTrace tailWord_4015138 prefixEnd_4015138 2061695688132216987809723 := by
  unfold tailWord_4015138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611028431962057955419517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97629409151898821214452045 36611028431962057955419517)
  ·
    refine ⟨13729135661985771733282319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36611028431962057955419517 13729135661985771733282319)
    ·
      refine ⟨20593703492978657599923479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13729135661985771733282319 20593703492978657599923479)
      ·
        refine ⟨30890555239467986399885219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20593703492978657599923479 30890555239467986399885219)
        ·
          refine ⟨46335832859201979599827829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30890555239467986399885219 46335832859201979599827829)
          ·
            refine ⟨4343984330550185587483859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46335832859201979599827829 4343984330550185587483859)
            ·
              refine ⟨6515976495825278381225789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343984330550185587483859 6515976495825278381225789)
              ·
                refine ⟨2443491185934479392959671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6515976495825278381225789 2443491185934479392959671)
                ·
                  refine ⟨3665236778901719089439507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443491185934479392959671 3665236778901719089439507)
                  ·
                    refine ⟨5497855168352578634159261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3665236778901719089439507 5497855168352578634159261)
                    ·
                      refine ⟨2061695688132216987809723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497855168352578634159261 2061695688132216987809723)
                      ·
                        rfl

theorem cell23_4015138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_4015138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015138 prefixEnd_4015138 := by exact prefixLift 4015138
  have htrace : WordTrace (prefixWord ++ tailWord_4015138) baseStart_4015138 baseEnd_4015138 := by
    simpa [prefixWord, tailWord_4015138, baseEnd_4015138] using wordTrace_append hprefix tailTrace_4015138
  have hstable : (prefixWord ++ tailWord_4015138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015138).length < 2 ^ (prefixWord ++ tailWord_4015138).sum := by decide
  have hdescent : baseEnd_4015138 < baseStart_4015138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015147 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 3]
def baseStart_4015147 : Nat := 118140960795 + 4015147 * 2 ^ 59
def prefixEnd_4015147 : Nat := 4983230072969 + 3 ^ 40 * 4015147 * 2
def baseEnd_4015147 : Nat := 2061700309458107452597181

theorem tailTrace_4015147 : CollatzResearch.WordTrace tailWord_4015147 prefixEnd_4015147 2061700309458107452597181 := by
  unfold tailWord_4015147
  simp only [CollatzResearch.WordTrace]
  refine ⟨146444441984815626358755695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97629627989877084239170463 146444441984815626358755695)
  ·
    refine ⟨219666662977223439538133543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146444441984815626358755695 219666662977223439538133543)
    ·
      refine ⟨329499994465835159307200315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219666662977223439538133543 329499994465835159307200315)
      ·
        refine ⟨494249991698752738960800473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329499994465835159307200315 494249991698752738960800473)
        ·
          refine ⟨370687493774064554220600355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494249991698752738960800473 370687493774064554220600355)
          ·
            refine ⟨556031240661096831330900533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370687493774064554220600355 556031240661096831330900533)
            ·
              refine ⟨52127928811977827937271925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556031240661096831330900533 52127928811977827937271925)
              ·
                refine ⟨4886993326122921369119243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52127928811977827937271925 4886993326122921369119243)
                ·
                  refine ⟨7330489989184382053678865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886993326122921369119243 7330489989184382053678865)
                  ·
                    refine ⟨5497867491888286540259149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330489989184382053678865 5497867491888286540259149)
                    ·
                      refine ⟨2061700309458107452597181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497867491888286540259149 2061700309458107452597181)
                      ·
                        rfl

theorem cell23_4015147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 3].length) (baseStart_4015147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015147 prefixEnd_4015147 := by exact prefixLift 4015147
  have htrace : WordTrace (prefixWord ++ tailWord_4015147) baseStart_4015147 baseEnd_4015147 := by
    simpa [prefixWord, tailWord_4015147, baseEnd_4015147] using wordTrace_append hprefix tailTrace_4015147
  have hstable : (prefixWord ++ tailWord_4015147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015147).length < 2 ^ (prefixWord ++ tailWord_4015147).sum := by decide
  have hdescent : baseEnd_4015147 < baseStart_4015147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015161 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4015161 : Nat := 118140960795 + 4015161 * 2 ^ 59
def prefixEnd_4015161 : Nat := 4983230072969 + 3 ^ 40 * 4015161 * 2
def baseEnd_4015161 : Nat := 2061707498187270397822117

theorem tailTrace_4015161 : CollatzResearch.WordTrace tailWord_4015161 prefixEnd_4015161 2061707498187270397822117 := by
  unfold tailWord_4015161
  simp only [CollatzResearch.WordTrace]
  refine ⟨146444952606764906749765337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97629968404509937833176891 146444952606764906749765337)
  ·
    refine ⟨109833714455073680062324003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146444952606764906749765337 109833714455073680062324003)
    ·
      refine ⟨164750571682610520093486005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109833714455073680062324003 164750571682610520093486005)
      ·
        refine ⟨15445366095244736258764313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164750571682610520093486005 15445366095244736258764313)
        ·
          refine ⟨11584024571433552194073235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15445366095244736258764313 11584024571433552194073235)
          ·
            refine ⟨17376036857150328291109853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584024571433552194073235 17376036857150328291109853)
            ·
              refine ⟨6516013821431373109166195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17376036857150328291109853 6516013821431373109166195)
              ·
                refine ⟨9774020732147059663749293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516013821431373109166195 9774020732147059663749293)
                ·
                  refine ⟨3665257774555147373905985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9774020732147059663749293 3665257774555147373905985)
                  ·
                    refine ⟨2748943330916360530429489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665257774555147373905985 2748943330916360530429489)
                    ·
                      refine ⟨2061707498187270397822117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748943330916360530429489 2061707498187270397822117)
                      ·
                        rfl

theorem cell23_4015161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4015161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015161 prefixEnd_4015161 := by exact prefixLift 4015161
  have htrace : WordTrace (prefixWord ++ tailWord_4015161) baseStart_4015161 baseEnd_4015161 := by
    simpa [prefixWord, tailWord_4015161, baseEnd_4015161] using wordTrace_append hprefix tailTrace_4015161
  have hstable : (prefixWord ++ tailWord_4015161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015161).length < 2 ^ (prefixWord ++ tailWord_4015161).sum := by decide
  have hdescent : baseEnd_4015161 < baseStart_4015161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015174 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4015174 : Nat := 118140960795 + 4015174 * 2 ^ 59
def prefixEnd_4015174 : Nat := 4983230072969 + 3 ^ 40 * 4015174 * 2
def baseEnd_4015174 : Nat := 2061714173435778846959557

theorem tailTrace_4015174 : CollatzResearch.WordTrace tailWord_4015174 prefixEnd_4015174 2061714173435778846959557 := by
  unfold tailWord_4015174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576419586116181561562143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97630284503811873313325717 4576419586116181561562143)
  ·
    refine ⟨6864629379174272342343215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4576419586116181561562143 6864629379174272342343215)
    ·
      refine ⟨10296944068761408513514823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864629379174272342343215 10296944068761408513514823)
      ·
        refine ⟨15445416103142112770272235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10296944068761408513514823 15445416103142112770272235)
        ·
          refine ⟨23168124154713169155408353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15445416103142112770272235 23168124154713169155408353)
          ·
            refine ⟨17376093116034876866556265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23168124154713169155408353 17376093116034876866556265)
            ·
              refine ⟨13032069837026157649917199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17376093116034876866556265 13032069837026157649917199)
              ·
                refine ⟨19548104755539236474875799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13032069837026157649917199 19548104755539236474875799)
                ·
                  refine ⟨29322157133308854712313699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19548104755539236474875799 29322157133308854712313699)
                  ·
                    refine ⟨43983235699963282068470549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29322157133308854712313699 43983235699963282068470549)
                    ·
                      refine ⟨2061714173435778846959557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43983235699963282068470549 2061714173435778846959557)
                      ·
                        rfl

theorem cell23_4015174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4015174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015174 prefixEnd_4015174 := by exact prefixLift 4015174
  have htrace : WordTrace (prefixWord ++ tailWord_4015174) baseStart_4015174 baseEnd_4015174 := by
    simpa [prefixWord, tailWord_4015174, baseEnd_4015174] using wordTrace_append hprefix tailTrace_4015174
  have hstable : (prefixWord ++ tailWord_4015174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015174).length < 2 ^ (prefixWord ++ tailWord_4015174).sum := by decide
  have hdescent : baseEnd_4015174 < baseStart_4015174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015177 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 3]
def baseStart_4015177 : Nat := 118140960795 + 4015177 * 2 ^ 59
def prefixEnd_4015177 : Nat := 4983230072969 + 3 ^ 40 * 4015177 * 2
def baseEnd_4015177 : Nat := 2061715713877742335222043

theorem tailTrace_4015177 : CollatzResearch.WordTrace tailWord_4015177 prefixEnd_4015177 2061715713877742335222043 := by
  unfold tailWord_4015177
  simp only [CollatzResearch.WordTrace]
  refine ⟨146445536174706941482347785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97630357449804627654898523 146445536174706941482347785)
  ·
    refine ⟨109834152131030206111760839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146445536174706941482347785 109834152131030206111760839)
    ·
      refine ⟨164751228196545309167641259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109834152131030206111760839 164751228196545309167641259)
      ·
        refine ⟨247126842294817963751461889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164751228196545309167641259 247126842294817963751461889)
        ·
          refine ⟨185345131721113472813596417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247126842294817963751461889 185345131721113472813596417)
          ·
            refine ⟨139008848790835104610197313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185345131721113472813596417 139008848790835104610197313)
            ·
              refine ⟨104256636593126328457647985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139008848790835104610197313 104256636593126328457647985)
              ·
                refine ⟨78192477444844746343235989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104256636593126328457647985 78192477444844746343235989)
                ·
                  refine ⟨3665272380227097484839187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78192477444844746343235989 3665272380227097484839187)
                  ·
                    refine ⟨5497908570340646227258781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3665272380227097484839187 5497908570340646227258781)
                    ·
                      refine ⟨2061715713877742335222043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497908570340646227258781 2061715713877742335222043)
                      ·
                        rfl

theorem cell23_4015177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_4015177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015177 prefixEnd_4015177 := by exact prefixLift 4015177
  have htrace : WordTrace (prefixWord ++ tailWord_4015177) baseStart_4015177 baseEnd_4015177 := by
    simpa [prefixWord, tailWord_4015177, baseEnd_4015177] using wordTrace_append hprefix tailTrace_4015177
  have hstable : (prefixWord ++ tailWord_4015177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015177).length < 2 ^ (prefixWord ++ tailWord_4015177).sum := by decide
  have hdescent : baseEnd_4015177 < baseStart_4015177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015181 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4015181 : Nat := 118140960795 + 4015181 * 2 ^ 59
def prefixEnd_4015181 : Nat := 4983230072969 + 3 ^ 40 * 4015181 * 2
def baseEnd_4015181 : Nat := 2061717767800360319572025

theorem tailTrace_4015181 : CollatzResearch.WordTrace tailWord_4015181 prefixEnd_4015181 2061717767800360319572025 := by
  unfold tailWord_4015181
  simp only [CollatzResearch.WordTrace]
  refine ⟨146445682066692450165493397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97630454711128300110328931 146445682066692450165493397)
  ·
    refine ⟨6864641346876208601507503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146445682066692450165493397 6864641346876208601507503)
    ·
      refine ⟨10296962020314312902261255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864641346876208601507503 10296962020314312902261255)
      ·
        refine ⟨15445443030471469353391883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10296962020314312902261255 15445443030471469353391883)
        ·
          refine ⟨23168164545707204030087825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15445443030471469353391883 23168164545707204030087825)
          ·
            refine ⟨17376123409280403022565869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23168164545707204030087825 17376123409280403022565869)
            ·
              refine ⟨6516046278480151133462201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17376123409280403022565869 6516046278480151133462201)
              ·
                refine ⟨4887034708860113350096651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516046278480151133462201 4887034708860113350096651)
                ·
                  refine ⟨7330552063290170025144977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887034708860113350096651 7330552063290170025144977)
                  ·
                    refine ⟨5497914047467627518858733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330552063290170025144977 5497914047467627518858733)
                    ·
                      refine ⟨2061717767800360319572025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497914047467627518858733 2061717767800360319572025)
                      ·
                        rfl

theorem cell23_4015181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4015181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015181 prefixEnd_4015181 := by exact prefixLift 4015181
  have htrace : WordTrace (prefixWord ++ tailWord_4015181) baseStart_4015181 baseEnd_4015181 := by
    simpa [prefixWord, tailWord_4015181, baseEnd_4015181] using wordTrace_append hprefix tailTrace_4015181
  have hstable : (prefixWord ++ tailWord_4015181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015181).length < 2 ^ (prefixWord ++ tailWord_4015181).sum := by decide
  have hdescent : baseEnd_4015181 < baseStart_4015181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015198 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4015198 : Nat := 118140960795 + 4015198 * 2 ^ 59
def prefixEnd_4015198 : Nat := 4983230072969 + 3 ^ 40 * 4015198 * 2
def baseEnd_4015198 : Nat := 2061726496971486753059447

theorem tailTrace_4015198 : CollatzResearch.WordTrace tailWord_4015198 prefixEnd_4015198 2061726496971486753059447 := by
  unfold tailWord_4015198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18305787763453857758607781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97630868071753908045908165 18305787763453857758607781)
  ·
    refine ⟨3432335205647598329738959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18305787763453857758607781 3432335205647598329738959)
    ·
      refine ⟨5148502808471397494608439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432335205647598329738959 5148502808471397494608439)
      ·
        refine ⟨7722754212707096241912659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148502808471397494608439 7722754212707096241912659)
        ·
          refine ⟨11584131319060644362868989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722754212707096241912659 11584131319060644362868989)
          ·
            refine ⟨4344049244647741636075871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11584131319060644362868989 4344049244647741636075871)
            ·
              refine ⟨6516073866971612454113807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344049244647741636075871 6516073866971612454113807)
              ·
                refine ⟨9774110800457418681170711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516073866971612454113807 9774110800457418681170711)
                ·
                  refine ⟨14661166200686128021756067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9774110800457418681170711 14661166200686128021756067)
                  ·
                    refine ⟨21991749301029192032634101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14661166200686128021756067 21991749301029192032634101)
                    ·
                      refine ⟨2061726496971486753059447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21991749301029192032634101 2061726496971486753059447)
                      ·
                        rfl

theorem cell23_4015198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4015198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015198 prefixEnd_4015198 := by exact prefixLift 4015198
  have htrace : WordTrace (prefixWord ++ tailWord_4015198) baseStart_4015198 baseEnd_4015198 := by
    simpa [prefixWord, tailWord_4015198, baseEnd_4015198] using wordTrace_append hprefix tailTrace_4015198
  have hstable : (prefixWord ++ tailWord_4015198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015198).length < 2 ^ (prefixWord ++ tailWord_4015198).sum := by decide
  have hdescent : baseEnd_4015198 < baseStart_4015198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015268 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_4015268 : Nat := 118140960795 + 4015268 * 2 ^ 59
def prefixEnd_4015268 : Nat := 4983230072969 + 3 ^ 40 * 4015268 * 2
def baseEnd_4015268 : Nat := 2061762440617301479184125

theorem tailTrace_4015268 : CollatzResearch.WordTrace tailWord_4015268 prefixEnd_4015268 2061762440617301479184125 := by
  unfold tailWord_4015268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73224427608688632011955229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97632570144918176015940305 73224427608688632011955229)
  ·
    refine ⟨27459160353258237004483211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73224427608688632011955229 27459160353258237004483211)
    ·
      refine ⟨41188740529887355506724817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27459160353258237004483211 41188740529887355506724817)
      ·
        refine ⟨30891555397415516630043613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41188740529887355506724817 30891555397415516630043613)
        ·
          refine ⟨11584333274030818736266355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30891555397415516630043613 11584333274030818736266355)
          ·
            refine ⟨17376499911046228104399533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584333274030818736266355 17376499911046228104399533)
            ·
              refine ⟨6516187466642335539149825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17376499911046228104399533 6516187466642335539149825)
              ·
                refine ⟨4887140599981751654362369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516187466642335539149825 4887140599981751654362369)
                ·
                  refine ⟨3665355449986313740771777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4887140599981751654362369 3665355449986313740771777)
                  ·
                    refine ⟨2749016587489735305578833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665355449986313740771777 2749016587489735305578833)
                    ·
                      refine ⟨2061762440617301479184125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749016587489735305578833 2061762440617301479184125)
                      ·
                        rfl

theorem cell23_4015268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_4015268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015268 prefixEnd_4015268 := by exact prefixLift 4015268
  have htrace : WordTrace (prefixWord ++ tailWord_4015268) baseStart_4015268 baseEnd_4015268 := by
    simpa [prefixWord, tailWord_4015268, baseEnd_4015268] using wordTrace_append hprefix tailTrace_4015268
  have hstable : (prefixWord ++ tailWord_4015268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015268).length < 2 ^ (prefixWord ++ tailWord_4015268).sum := by decide
  have hdescent : baseEnd_4015268 < baseStart_4015268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015274 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_4015274 : Nat := 118140960795 + 4015274 * 2 ^ 59
def prefixEnd_4015274 : Nat := 4983230072969 + 3 ^ 40 * 4015274 * 2
def baseEnd_4015274 : Nat := 229085057944580939523233

theorem tailTrace_4015274 : CollatzResearch.WordTrace tailWord_4015274 prefixEnd_4015274 229085057944580939523233 := by
  unfold tailWord_4015274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36612268513838881762157219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97632716036903684699085917 36612268513838881762157219)
  ·
    refine ⟨54918402770758322643235829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36612268513838881762157219 54918402770758322643235829)
    ·
      refine ⟨5148600259758592747803359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54918402770758322643235829 5148600259758592747803359)
      ·
        refine ⟨7722900389637889121705039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148600259758592747803359 7722900389637889121705039)
        ·
          refine ⟨11584350584456833682557559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722900389637889121705039 11584350584456833682557559)
          ·
            refine ⟨17376525876685250523836339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584350584456833682557559 17376525876685250523836339)
            ·
              refine ⟨26064788815027875785754509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17376525876685250523836339 26064788815027875785754509)
              ·
                refine ⟨9774295805635453419657941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26064788815027875785754509 9774295805635453419657941)
                ·
                  refine ⟨229085057944580939523233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9774295805635453419657941 229085057944580939523233)
                  ·
                    rfl

theorem cell23_4015274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_4015274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015274 prefixEnd_4015274 := by exact prefixLift 4015274
  have htrace : WordTrace (prefixWord ++ tailWord_4015274) baseStart_4015274 baseEnd_4015274 := by
    simpa [prefixWord, tailWord_4015274, baseEnd_4015274] using wordTrace_append hprefix tailTrace_4015274
  have hstable : (prefixWord ++ tailWord_4015274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015274).length < 2 ^ (prefixWord ++ tailWord_4015274).sum := by decide
  have hdescent : baseEnd_4015274 < baseStart_4015274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015361 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_4015361 : Nat := 118140960795 + 4015361 * 2 ^ 59
def prefixEnd_4015361 : Nat := 4983230072969 + 3 ^ 40 * 4015361 * 2
def baseEnd_4015361 : Nat := 2061810194318169615321197

theorem tailTrace_4015361 : CollatzResearch.WordTrace tailWord_4015361 prefixEnd_4015361 2061810194318169615321197 := by
  unfold tailWord_4015361
  simp only [CollatzResearch.WordTrace]
  refine ⟨146452247206040340907045937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97634831470693560604697291 146452247206040340907045937)
  ·
    refine ⟨109839185404530255680284453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146452247206040340907045937 109839185404530255680284453)
    ·
      refine ⟨20594847263349422940053335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109839185404530255680284453 20594847263349422940053335)
      ·
        refine ⟨30892270895024134410080003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20594847263349422940053335 30892270895024134410080003)
        ·
          refine ⟨46338406342536201615120005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30892270895024134410080003 46338406342536201615120005)
          ·
            refine ⟨8688451189225537802835001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46338406342536201615120005 8688451189225537802835001)
            ·
              refine ⟨6516338391919153352126251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8688451189225537802835001 6516338391919153352126251)
              ·
                refine ⟨9774507587878730028189377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516338391919153352126251 9774507587878730028189377)
                ·
                  refine ⟨7330880690909047521142033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9774507587878730028189377 7330880690909047521142033)
                  ·
                    refine ⟨5498160518181785640856525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330880690909047521142033 5498160518181785640856525)
                    ·
                      refine ⟨2061810194318169615321197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5498160518181785640856525 2061810194318169615321197)
                      ·
                        rfl

theorem cell23_4015361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_4015361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015361 prefixEnd_4015361 := by exact prefixLift 4015361
  have htrace : WordTrace (prefixWord ++ tailWord_4015361) baseStart_4015361 baseEnd_4015361 := by
    simpa [prefixWord, tailWord_4015361, baseEnd_4015361] using wordTrace_append hprefix tailTrace_4015361
  have hstable : (prefixWord ++ tailWord_4015361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015361).length < 2 ^ (prefixWord ++ tailWord_4015361).sum := by decide
  have hdescent : baseEnd_4015361 < baseStart_4015361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015424 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 4, 4]
def baseStart_4015424 : Nat := 118140960795 + 4015424 * 2 ^ 59
def prefixEnd_4015424 : Nat := 4983230072969 + 3 ^ 40 * 4015424 * 2
def baseEnd_4015424 : Nat := 687280847866467622944469

theorem tailTrace_4015424 : CollatzResearch.WordTrace tailWord_4015424 prefixEnd_4015424 687280847866467622944469 := by
  unfold tailWord_4015424
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227272502406051333294663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97636363336541401777726217 73227272502406051333294663)
  ·
    refine ⟨109840908753609076999941995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73227272502406051333294663 109840908753609076999941995)
    ·
      refine ⟨164761363130413615499912993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109840908753609076999941995 164761363130413615499912993)
      ·
        refine ⟨123571022347810211624934745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164761363130413615499912993 123571022347810211624934745)
        ·
          refine ⟨92678266760857658718701059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123571022347810211624934745 92678266760857658718701059)
          ·
            refine ⟨139017400141286488078051589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92678266760857658718701059 139017400141286488078051589)
            ·
              refine ⟨26065762526491216514634673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139017400141286488078051589 26065762526491216514634673)
              ·
                refine ⟨19549321894868412385976005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26065762526491216514634673 19549321894868412385976005)
                ·
                  refine ⟨3665497855287827322370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19549321894868412385976005 3665497855287827322370501)
                  ·
                    refine ⟨687280847866467622944469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665497855287827322370501 687280847866467622944469)
                    ·
                      rfl

theorem cell23_4015424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_4015424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015424 prefixEnd_4015424 := by exact prefixLift 4015424
  have htrace : WordTrace (prefixWord ++ tailWord_4015424) baseStart_4015424 baseEnd_4015424 := by
    simpa [prefixWord, tailWord_4015424, baseEnd_4015424] using wordTrace_append hprefix tailTrace_4015424
  have hstable : (prefixWord ++ tailWord_4015424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015424).length < 2 ^ (prefixWord ++ tailWord_4015424).sum := by decide
  have hdescent : baseEnd_4015424 < baseStart_4015424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015425 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4015425 : Nat := 118140960795 + 4015425 * 2 ^ 59
def prefixEnd_4015425 : Nat := 4983230072969 + 3 ^ 40 * 4015425 * 2
def baseEnd_4015425 : Nat := 2061843057080057364920903

theorem tailTrace_4015425 : CollatzResearch.WordTrace tailWord_4015425 prefixEnd_4015425 2061843057080057364920903 := by
  unfold tailWord_4015425
  simp only [CollatzResearch.WordTrace]
  refine ⟨146454581477808479837375729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97636387651872319891583819 146454581477808479837375729)
  ·
    refine ⟨109840936108356359878031797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146454581477808479837375729 109840936108356359878031797)
    ·
      refine ⟨10297587760158408738565481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109840936108356359878031797 10297587760158408738565481)
      ·
        refine ⟨7723190820118806553924111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10297587760158408738565481 7723190820118806553924111)
        ·
          refine ⟨11584786230178209830886167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723190820118806553924111 11584786230178209830886167)
          ·
            refine ⟨17377179345267314746329251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584786230178209830886167 17377179345267314746329251)
            ·
              refine ⟨26065769017900972119493877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17377179345267314746329251 26065769017900972119493877)
              ·
                refine ⟨2443665845428216136202551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26065769017900972119493877 2443665845428216136202551)
                ·
                  refine ⟨3665498768142324204303827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443665845428216136202551 3665498768142324204303827)
                  ·
                    refine ⟨5498248152213486306455741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3665498768142324204303827 5498248152213486306455741)
                    ·
                      refine ⟨2061843057080057364920903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5498248152213486306455741 2061843057080057364920903)
                      ·
                        rfl

theorem cell23_4015425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4015425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015425 prefixEnd_4015425 := by exact prefixLift 4015425
  have htrace : WordTrace (prefixWord ++ tailWord_4015425) baseStart_4015425 baseEnd_4015425 := by
    simpa [prefixWord, tailWord_4015425, baseEnd_4015425] using wordTrace_append hprefix tailTrace_4015425
  have hstable : (prefixWord ++ tailWord_4015425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015425).length < 2 ^ (prefixWord ++ tailWord_4015425).sum := by decide
  have hdescent : baseEnd_4015425 < baseStart_4015425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015427 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_4015427 : Nat := 118140960795 + 4015427 * 2 ^ 59
def prefixEnd_4015427 : Nat := 4983230072969 + 3 ^ 40 * 4015427 * 2
def baseEnd_4015427 : Nat := 2061844084041366357095893

theorem tailTrace_4015427 : CollatzResearch.WordTrace tailWord_4015427 prefixEnd_4015427 2061844084041366357095893 := by
  unfold tailWord_4015427
  simp only [CollatzResearch.WordTrace]
  refine ⟨146454654423801234178948535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97636436282534156119299023 146454654423801234178948535)
  ·
    refine ⟨219681981635701851268422803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146454654423801234178948535 219681981635701851268422803)
    ·
      refine ⟨329522972453552776902634205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219681981635701851268422803 329522972453552776902634205)
      ·
        refine ⟨123571114670082291338487827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329522972453552776902634205 123571114670082291338487827)
        ·
          refine ⟨185356672005123437007731741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123571114670082291338487827 185356672005123437007731741)
          ·
            refine ⟨69508752001921288877899403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185356672005123437007731741 69508752001921288877899403)
            ·
              refine ⟨104263128002881933316849105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69508752001921288877899403 104263128002881933316849105)
              ·
                refine ⟨78197346002161449987636829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104263128002881933316849105 78197346002161449987636829)
                ·
                  refine ⟨29324004750810543745363811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78197346002161449987636829 29324004750810543745363811)
                  ·
                    refine ⟨43986007126215815618045717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29324004750810543745363811 43986007126215815618045717)
                    ·
                      refine ⟨2061844084041366357095893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43986007126215815618045717 2061844084041366357095893)
                      ·
                        rfl

theorem cell23_4015427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_4015427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015427 prefixEnd_4015427 := by exact prefixLift 4015427
  have htrace : WordTrace (prefixWord ++ tailWord_4015427) baseStart_4015427 baseEnd_4015427 := by
    simpa [prefixWord, tailWord_4015427, baseEnd_4015427] using wordTrace_append hprefix tailTrace_4015427
  have hstable : (prefixWord ++ tailWord_4015427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015427).length < 2 ^ (prefixWord ++ tailWord_4015427).sum := by decide
  have hdescent : baseEnd_4015427 < baseStart_4015427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015428 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4015428 : Nat := 118140960795 + 4015428 * 2 ^ 59
def prefixEnd_4015428 : Nat := 4983230072969 + 3 ^ 40 * 4015428 * 2
def baseEnd_4015428 : Nat := 687281532507340284394463

theorem tailTrace_4015428 : CollatzResearch.WordTrace tailWord_4015428 prefixEnd_4015428 687281532507340284394463 := by
  unfold tailWord_4015428
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227345448398805674867469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97636460597865074233156625 73227345448398805674867469)
  ·
    refine ⟨27460254543149552128075301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73227345448398805674867469 27460254543149552128075301)
    ·
      refine ⟨5148797726840541024014119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27460254543149552128075301 5148797726840541024014119)
      ·
        refine ⟨7723196590260811536021179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148797726840541024014119 7723196590260811536021179)
        ·
          refine ⟨11584794885391217304031769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723196590260811536021179 11584794885391217304031769)
          ·
            refine ⟨8688596164043412978023827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11584794885391217304031769 8688596164043412978023827)
            ·
              refine ⟨13032894246065119467035741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688596164043412978023827 13032894246065119467035741)
              ·
                refine ⟨4887335342274419800138403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13032894246065119467035741 4887335342274419800138403)
                ·
                  refine ⟨7331003013411629700207605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887335342274419800138403 7331003013411629700207605)
                  ·
                    refine ⟨687281532507340284394463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331003013411629700207605 687281532507340284394463)
                    ·
                      rfl

theorem cell23_4015428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4015428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015428 prefixEnd_4015428 := by exact prefixLift 4015428
  have htrace : WordTrace (prefixWord ++ tailWord_4015428) baseStart_4015428 baseEnd_4015428 := by
    simpa [prefixWord, tailWord_4015428, baseEnd_4015428] using wordTrace_append hprefix tailTrace_4015428
  have hstable : (prefixWord ++ tailWord_4015428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015428).length < 2 ^ (prefixWord ++ tailWord_4015428).sum := by decide
  have hdescent : baseEnd_4015428 < baseStart_4015428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015431 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_4015431 : Nat := 118140960795 + 4015431 * 2 ^ 59
def prefixEnd_4015431 : Nat := 4983230072969 + 3 ^ 40 * 4015431 * 2
def baseEnd_4015431 : Nat := 2061846137963984341445875

theorem tailTrace_4015431 : CollatzResearch.WordTrace tailWord_4015431 prefixEnd_4015431 2061846137963984341445875 := by
  unfold tailWord_4015431
  simp only [CollatzResearch.WordTrace]
  refine ⟨146454800315786742862094147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97636533543857828574729431 146454800315786742862094147)
  ·
    refine ⟨219682200473680114293141221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146454800315786742862094147 219682200473680114293141221)
    ·
      refine ⟨41190412588815021429963979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219682200473680114293141221 41190412588815021429963979)
      ·
        refine ⟨61785618883222532144945969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41190412588815021429963979 61785618883222532144945969)
        ·
          refine ⟨46339214162416899108709477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61785618883222532144945969 46339214162416899108709477)
          ·
            refine ⟨8688602655453168582883027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46339214162416899108709477 8688602655453168582883027)
            ·
              refine ⟨13032903983179752874324541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688602655453168582883027 13032903983179752874324541)
              ·
                refine ⟨4887338993692407327871703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13032903983179752874324541 4887338993692407327871703)
                ·
                  refine ⟨7331008490538610991807555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887338993692407327871703 7331008490538610991807555)
                  ·
                    refine ⟨10996512735807916487711333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331008490538610991807555 10996512735807916487711333)
                    ·
                      refine ⟨2061846137963984341445875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10996512735807916487711333 2061846137963984341445875)
                      ·
                        rfl

theorem cell23_4015431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_4015431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015431 prefixEnd_4015431 := by exact prefixLift 4015431
  have htrace : WordTrace (prefixWord ++ tailWord_4015431) baseStart_4015431 baseEnd_4015431 := by
    simpa [prefixWord, tailWord_4015431, baseEnd_4015431] using wordTrace_append hprefix tailTrace_4015431
  have hstable : (prefixWord ++ tailWord_4015431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015431).length < 2 ^ (prefixWord ++ tailWord_4015431).sum := by decide
  have hdescent : baseEnd_4015431 < baseStart_4015431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015444 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_4015444 : Nat := 118140960795 + 4015444 * 2 ^ 59
def prefixEnd_4015444 : Nat := 4983230072969 + 3 ^ 40 * 4015444 * 2
def baseEnd_4015444 : Nat := 2061852813212492790583315

theorem tailTrace_4015444 : CollatzResearch.WordTrace tailWord_4015444 prefixEnd_4015444 2061852813212492790583315 := by
  unfold tailWord_4015444
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227637232369823041158693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97636849643159764054878257 73227637232369823041158693)
  ·
    refine ⟨13730181981069341820217255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73227637232369823041158693 13730181981069341820217255)
    ·
      refine ⟨20595272971604012730325883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13730181981069341820217255 20595272971604012730325883)
      ·
        refine ⟨30892909457406019095488825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20595272971604012730325883 30892909457406019095488825)
        ·
          refine ⟨23169682093054514321616619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30892909457406019095488825 23169682093054514321616619)
          ·
            refine ⟨34754523139581771482424929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23169682093054514321616619 34754523139581771482424929)
            ·
              refine ⟨26065892354686328611818697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34754523139581771482424929 26065892354686328611818697)
              ·
                refine ⟨19549419266014746458864023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26065892354686328611818697 19549419266014746458864023)
                ·
                  refine ⟨29324128899022119688296035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19549419266014746458864023 29324128899022119688296035)
                  ·
                    refine ⟨43986193348533179532444053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29324128899022119688296035 43986193348533179532444053)
                    ·
                      refine ⟨2061852813212492790583315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43986193348533179532444053 2061852813212492790583315)
                      ·
                        rfl

theorem cell23_4015444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_4015444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015444 prefixEnd_4015444 := by exact prefixLift 4015444
  have htrace : WordTrace (prefixWord ++ tailWord_4015444) baseStart_4015444 baseEnd_4015444 := by
    simpa [prefixWord, tailWord_4015444, baseEnd_4015444] using wordTrace_append hprefix tailTrace_4015444
  have hstable : (prefixWord ++ tailWord_4015444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015444).length < 2 ^ (prefixWord ++ tailWord_4015444).sum := by decide
  have hdescent : baseEnd_4015444 < baseStart_4015444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015448 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 3, 2, 2]
def baseStart_4015448 : Nat := 118140960795 + 4015448 * 2 ^ 59
def prefixEnd_4015448 : Nat := 4983230072969 + 3 ^ 40 * 4015448 * 2
def baseEnd_4015448 : Nat := 2061854867135110774933297

theorem tailTrace_4015448 : CollatzResearch.WordTrace tailWord_4015448 prefixEnd_4015448 2061854867135110774933297 := by
  unfold tailWord_4015448
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227710178362577382731499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97636946904483436510308665 73227710178362577382731499)
  ·
    refine ⟨109841565267543866074097249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73227710178362577382731499 109841565267543866074097249)
    ·
      refine ⟨82381173950657899555572937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109841565267543866074097249 82381173950657899555572937)
      ·
        refine ⟨61785880462993424666679703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82381173950657899555572937 61785880462993424666679703)
        ·
          refine ⟨92678820694490137000019555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61785880462993424666679703 92678820694490137000019555)
          ·
            refine ⟨139018231041735205500029333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92678820694490137000019555 139018231041735205500029333)
            ·
              refine ⟨6516479580081337757813875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139018231041735205500029333 6516479580081337757813875)
              ·
                refine ⟨9774719370122006636720813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516479580081337757813875 9774719370122006636720813)
                ·
                  refine ⟨3665519763795752488770305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9774719370122006636720813 3665519763795752488770305)
                  ·
                    refine ⟨2749139822846814366577729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665519763795752488770305 2749139822846814366577729)
                    ·
                      refine ⟨2061854867135110774933297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749139822846814366577729 2061854867135110774933297)
                      ·
                        rfl

theorem cell23_4015448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_4015448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015448 prefixEnd_4015448 := by exact prefixLift 4015448
  have htrace : WordTrace (prefixWord ++ tailWord_4015448) baseStart_4015448 baseEnd_4015448 := by
    simpa [prefixWord, tailWord_4015448, baseEnd_4015448] using wordTrace_append hprefix tailTrace_4015448
  have hstable : (prefixWord ++ tailWord_4015448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015448).length < 2 ^ (prefixWord ++ tailWord_4015448).sum := by decide
  have hdescent : baseEnd_4015448 < baseStart_4015448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015468 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_4015468 : Nat := 118140960795 + 4015468 * 2 ^ 59
def prefixEnd_4015468 : Nat := 4983230072969 + 3 ^ 40 * 4015468 * 2
def baseEnd_4015468 : Nat := 2061865136748200696683205

theorem tailTrace_4015468 : CollatzResearch.WordTrace tailWord_4015468 prefixEnd_4015468 2061865136748200696683205 := by
  unfold tailWord_4015468
  simp only [CollatzResearch.WordTrace]
  refine ⟨73228074908326349090595529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97637433211101798787460705 73228074908326349090595529)
  ·
    refine ⟨54921056181244761817946647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73228074908326349090595529 54921056181244761817946647)
    ·
      refine ⟨82381584271867142726919971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54921056181244761817946647 82381584271867142726919971)
      ·
        refine ⟨123572376407800714090379957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82381584271867142726919971 123572376407800714090379957)
        ·
          refine ⟨11584910288231316945973121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123572376407800714090379957 11584910288231316945973121)
          ·
            refine ⟨8688682716173487709479841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11584910288231316945973121 8688682716173487709479841)
            ·
              refine ⟨6516512037130115782109881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8688682716173487709479841 6516512037130115782109881)
              ·
                refine ⟨4887384027847586836582411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516512037130115782109881 4887384027847586836582411)
                ·
                  refine ⟨7331076041771380254873617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887384027847586836582411 7331076041771380254873617)
                  ·
                    refine ⟨5498307031328535191155213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331076041771380254873617 5498307031328535191155213)
                    ·
                      refine ⟨2061865136748200696683205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5498307031328535191155213 2061865136748200696683205)
                      ·
                        rfl

theorem cell23_4015468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_4015468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015468 prefixEnd_4015468 := by exact prefixLift 4015468
  have htrace : WordTrace (prefixWord ++ tailWord_4015468) baseStart_4015468 baseEnd_4015468 := by
    simpa [prefixWord, tailWord_4015468, baseEnd_4015468] using wordTrace_append hprefix tailTrace_4015468
  have hstable : (prefixWord ++ tailWord_4015468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015468).length < 2 ^ (prefixWord ++ tailWord_4015468).sum := by decide
  have hdescent : baseEnd_4015468 < baseStart_4015468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015481 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 3]
def baseStart_4015481 : Nat := 118140960795 + 4015481 * 2 ^ 59
def prefixEnd_4015481 : Nat := 4983230072969 + 3 ^ 40 * 4015481 * 2
def baseEnd_4015481 : Nat := 2061871811996709145820645

theorem tailTrace_4015481 : CollatzResearch.WordTrace tailWord_4015481 prefixEnd_4015481 2061871811996709145820645 := by
  unfold tailWord_4015481
  simp only [CollatzResearch.WordTrace]
  refine ⟨146456623965605601401414297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97637749310403734267609531 146456623965605601401414297)
  ·
    refine ⟨109842467974204201051060723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146456623965605601401414297 109842467974204201051060723)
    ·
      refine ⟨164763701961306301576591085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109842467974204201051060723 164763701961306301576591085)
      ·
        refine ⟨61786388235489863091221657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164763701961306301576591085 61786388235489863091221657)
        ·
          refine ⟨46339791176617397318416243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61786388235489863091221657 46339791176617397318416243)
          ·
            refine ⟨69509686764926095977624365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46339791176617397318416243 69509686764926095977624365)
            ·
              refine ⟨26066132536847285991609137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69509686764926095977624365 26066132536847285991609137)
              ·
                refine ⟨19549599402635464493706853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26066132536847285991609137 19549599402635464493706853)
                ·
                  refine ⟨3665549887994149592570035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19549599402635464493706853 3665549887994149592570035)
                  ·
                    refine ⟨5498324831991224388855053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3665549887994149592570035 5498324831991224388855053)
                    ·
                      refine ⟨2061871811996709145820645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5498324831991224388855053 2061871811996709145820645)
                      ·
                        rfl

theorem cell23_4015481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_4015481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015481 prefixEnd_4015481 := by exact prefixLift 4015481
  have htrace : WordTrace (prefixWord ++ tailWord_4015481) baseStart_4015481 baseEnd_4015481 := by
    simpa [prefixWord, tailWord_4015481, baseEnd_4015481] using wordTrace_append hprefix tailTrace_4015481
  have hstable : (prefixWord ++ tailWord_4015481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015481).length < 2 ^ (prefixWord ++ tailWord_4015481).sum := by decide
  have hdescent : baseEnd_4015481 < baseStart_4015481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015514 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_4015514 : Nat := 118140960795 + 4015514 * 2 ^ 59
def prefixEnd_4015514 : Nat := 4983230072969 + 3 ^ 40 * 4015514 * 2
def baseEnd_4015514 : Nat := 687296252286102505569331

theorem tailTrace_4015514 : CollatzResearch.WordTrace tailWord_4015514 prefixEnd_4015514 687296252286102505569331 := by
  unfold tailWord_4015514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36614456893621512009341399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97638551716324032024910397 36614456893621512009341399)
  ·
    refine ⟨54921685340432268014012099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36614456893621512009341399 54921685340432268014012099)
    ·
      refine ⟨82382528010648402021018149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54921685340432268014012099 82382528010648402021018149)
      ·
        refine ⟨15446724001996575378940903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82382528010648402021018149 15446724001996575378940903)
        ·
          refine ⟨23170086002994863068411355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446724001996575378940903 23170086002994863068411355)
          ·
            refine ⟨34755129004492294602617033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23170086002994863068411355 34755129004492294602617033)
            ·
              refine ⟨26066346753369220951962775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34755129004492294602617033 26066346753369220951962775)
              ·
                refine ⟨39099520130053831427944163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26066346753369220951962775 39099520130053831427944163)
                ·
                  refine ⟨58649280195080747141916245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39099520130053831427944163 58649280195080747141916245)
                  ·
                    refine ⟨687296252286102505569331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58649280195080747141916245 687296252286102505569331)
                    ·
                      rfl

theorem cell23_4015514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_4015514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015514 prefixEnd_4015514 := by exact prefixLift 4015514
  have htrace : WordTrace (prefixWord ++ tailWord_4015514) baseStart_4015514 baseEnd_4015514 := by
    simpa [prefixWord, tailWord_4015514, baseEnd_4015514] using wordTrace_append hprefix tailTrace_4015514
  have hstable : (prefixWord ++ tailWord_4015514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015514).length < 2 ^ (prefixWord ++ tailWord_4015514).sum := by decide
  have hdescent : baseEnd_4015514 < baseStart_4015514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015538 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_4015538 : Nat := 118140960795 + 4015538 * 2 ^ 59
def prefixEnd_4015538 : Nat := 4983230072969 + 3 ^ 40 * 4015538 * 2
def baseEnd_4015538 : Nat := 2061901080394015422807883

theorem tailTrace_4015538 : CollatzResearch.WordTrace tailWord_4015538 prefixEnd_4015538 2061901080394015422807883 := by
  unfold tailWord_4015538
  simp only [CollatzResearch.WordTrace]
  refine ⟨36614675731599775034059817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97639135284266066757492845 36614675731599775034059817)
  ·
    refine ⟨27461006798699831275544863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36614675731599775034059817 27461006798699831275544863)
    ·
      refine ⟨41191510198049746913317295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27461006798699831275544863 41191510198049746913317295)
      ·
        refine ⟨61787265297074620369975943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41191510198049746913317295 61787265297074620369975943)
        ·
          refine ⟨92680897945611930554963915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61787265297074620369975943 92680897945611930554963915)
          ·
            refine ⟨139021346918417895832445873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92680897945611930554963915 139021346918417895832445873)
            ·
              refine ⟨104266010188813421874334405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139021346918417895832445873 104266010188813421874334405)
              ·
                refine ⟨19549876910402516601437701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104266010188813421874334405 19549876910402516601437701)
                ·
                  refine ⟨3665601920700471862769569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19549876910402516601437701 3665601920700471862769569)
                  ·
                    refine ⟨2749201440525353897077177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665601920700471862769569 2749201440525353897077177)
                    ·
                      refine ⟨2061901080394015422807883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749201440525353897077177 2061901080394015422807883)
                      ·
                        rfl

theorem cell23_4015538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_4015538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015538 prefixEnd_4015538 := by exact prefixLift 4015538
  have htrace : WordTrace (prefixWord ++ tailWord_4015538) baseStart_4015538 baseEnd_4015538 := by
    simpa [prefixWord, tailWord_4015538, baseEnd_4015538] using wordTrace_append hprefix tailTrace_4015538
  have hstable : (prefixWord ++ tailWord_4015538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015538).length < 2 ^ (prefixWord ++ tailWord_4015538).sum := by decide
  have hdescent : baseEnd_4015538 < baseStart_4015538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015541 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4015541 : Nat := 118140960795 + 4015541 * 2 ^ 59
def prefixEnd_4015541 : Nat := 4983230072969 + 3 ^ 40 * 4015541 * 2
def baseEnd_4015541 : Nat := 2061902620835978911070369

theorem tailTrace_4015541 : CollatzResearch.WordTrace tailWord_4015541 prefixEnd_4015541 2061902620835978911070369 := by
  unfold tailWord_4015541
  simp only [CollatzResearch.WordTrace]
  refine ⟨146458812345388231648598477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97639208230258821099065651 146458812345388231648598477)
  ·
    refine ⟨54922054629520586868224429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146458812345388231648598477 54922054629520586868224429)
    ·
      refine ⟨20595770486070220075584161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54922054629520586868224429 20595770486070220075584161)
      ·
        refine ⟨15446827864552665056688121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20595770486070220075584161 15446827864552665056688121)
        ·
          refine ⟨11585120898414498792516091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15446827864552665056688121 11585120898414498792516091)
          ·
            refine ⟨17377681347621748188774137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11585120898414498792516091 17377681347621748188774137)
            ·
              refine ⟨13033261010716311141580603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17377681347621748188774137 13033261010716311141580603)
              ·
                refine ⟨19549891516074466712370905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13033261010716311141580603 19549891516074466712370905)
                ·
                  refine ⟨14662418637055850034278179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19549891516074466712370905 14662418637055850034278179)
                  ·
                    refine ⟨21993627955583775051417269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14662418637055850034278179 21993627955583775051417269)
                    ·
                      refine ⟨2061902620835978911070369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21993627955583775051417269 2061902620835978911070369)
                      ·
                        rfl

theorem cell23_4015541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4015541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015541 prefixEnd_4015541 := by exact prefixLift 4015541
  have htrace : WordTrace (prefixWord ++ tailWord_4015541) baseStart_4015541 baseEnd_4015541 := by
    simpa [prefixWord, tailWord_4015541, baseEnd_4015541] using wordTrace_append hprefix tailTrace_4015541
  have hstable : (prefixWord ++ tailWord_4015541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015541).length < 2 ^ (prefixWord ++ tailWord_4015541).sum := by decide
  have hdescent : baseEnd_4015541 < baseStart_4015541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015584 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_4015584 : Nat := 118140960795 + 4015584 * 2 ^ 59
def prefixEnd_4015584 : Nat := 4983230072969 + 3 ^ 40 * 4015584 * 2
def baseEnd_4015584 : Nat := 2061924700504122242832671

theorem tailTrace_4015584 : CollatzResearch.WordTrace tailWord_4015584 prefixEnd_4015584 2061924700504122242832671 := by
  unfold tailWord_4015584
  simp only [CollatzResearch.WordTrace]
  refine ⟨73230190342116224996206903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97640253789488299994942537 73230190342116224996206903)
  ·
    refine ⟨109845285513174337494310355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73230190342116224996206903 109845285513174337494310355)
    ·
      refine ⟨164767928269761506241465533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109845285513174337494310355 164767928269761506241465533)
      ·
        refine ⟨61787973101160564840549575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164767928269761506241465533 61787973101160564840549575)
        ·
          refine ⟨92681959651740847260824363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61787973101160564840549575 92681959651740847260824363)
          ·
            refine ⟨139022939477611270891236545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92681959651740847260824363 139022939477611270891236545)
            ·
              refine ⟨104267204608208453168427409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139022939477611270891236545 104267204608208453168427409)
              ·
                refine ⟨78200403456156339876320557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104267204608208453168427409 78200403456156339876320557)
                ·
                  refine ⟨29325151296058627453620209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78200403456156339876320557 29325151296058627453620209)
                  ·
                    refine ⟨21993863472043970590215157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29325151296058627453620209 21993863472043970590215157)
                    ·
                      refine ⟨2061924700504122242832671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21993863472043970590215157 2061924700504122242832671)
                      ·
                        rfl

theorem cell23_4015584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_4015584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015584 prefixEnd_4015584 := by exact prefixLift 4015584
  have htrace : WordTrace (prefixWord ++ tailWord_4015584) baseStart_4015584 baseEnd_4015584 := by
    simpa [prefixWord, tailWord_4015584, baseEnd_4015584] using wordTrace_append hprefix tailTrace_4015584
  have hstable : (prefixWord ++ tailWord_4015584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015584).length < 2 ^ (prefixWord ++ tailWord_4015584).sum := by decide
  have hdescent : baseEnd_4015584 < baseStart_4015584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015591 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 1, 7]
def baseStart_4015591 : Nat := 118140960795 + 4015591 * 2 ^ 59
def prefixEnd_4015591 : Nat := 4983230072969 + 3 ^ 40 * 4015591 * 2
def baseEnd_4015591 : Nat := 687309431622901238481713

theorem tailTrace_4015591 : CollatzResearch.WordTrace tailWord_4015591 prefixEnd_4015591 687309431622901238481713 := by
  unfold tailWord_4015591
  simp only [CollatzResearch.WordTrace]
  refine ⟨146460635995207090187918627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97640423996804726791945751 146460635995207090187918627)
  ·
    refine ⟨219690953992810635281877941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146460635995207090187918627 219690953992810635281877941)
    ·
      refine ⟨20596026936825997057676057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219690953992810635281877941 20596026936825997057676057)
      ·
        refine ⟨15447020202619497793257043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20596026936825997057676057 15447020202619497793257043)
        ·
          refine ⟨23170530303929246689885565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447020202619497793257043 23170530303929246689885565)
          ·
            refine ⟨8688948863973467508707087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23170530303929246689885565 8688948863973467508707087)
            ·
              refine ⟨13033423295960201263060631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688948863973467508707087 13033423295960201263060631)
              ·
                refine ⟨19550134943940301894590947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13033423295960201263060631 19550134943940301894590947)
                ·
                  refine ⟨29325202415910452841886421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19550134943940301894590947 29325202415910452841886421)
                  ·
                    refine ⟨687309431622901238481713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29325202415910452841886421 687309431622901238481713)
                    ·
                      rfl

theorem cell23_4015591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_4015591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015591 prefixEnd_4015591 := by exact prefixLift 4015591
  have htrace : WordTrace (prefixWord ++ tailWord_4015591) baseStart_4015591 baseEnd_4015591 := by
    simpa [prefixWord, tailWord_4015591, baseEnd_4015591] using wordTrace_append hprefix tailTrace_4015591
  have hstable : (prefixWord ++ tailWord_4015591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015591).length < 2 ^ (prefixWord ++ tailWord_4015591).sum := by decide
  have hdescent : baseEnd_4015591 < baseStart_4015591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015611 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 6, 2]
def baseStart_4015611 : Nat := 118140960795 + 4015611 * 2 ^ 59
def prefixEnd_4015611 : Nat := 4983230072969 + 3 ^ 40 * 4015611 * 2
def baseEnd_4015611 : Nat := 2061938564481793637195047

theorem tailTrace_4015611 : CollatzResearch.WordTrace tailWord_4015611 prefixEnd_4015611 2061938564481793637195047 := by
  unfold tailWord_4015611
  simp only [CollatzResearch.WordTrace]
  refine ⟨146461365455134633603646687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97640910303423089069097791 146461365455134633603646687)
  ·
    refine ⟨219692048182701950405470031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146461365455134633603646687 219692048182701950405470031)
    ·
      refine ⟨329538072274052925608205047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219692048182701950405470031 329538072274052925608205047)
      ·
        refine ⟨494307108411079388412307571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329538072274052925608205047 494307108411079388412307571)
        ·
          refine ⟨741460662616619082618461357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494307108411079388412307571 741460662616619082618461357)
          ·
            refine ⟨278047748481232155981923009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741460662616619082618461357 278047748481232155981923009)
            ·
              refine ⟨208535811360924116986442257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278047748481232155981923009 208535811360924116986442257)
              ·
                refine ⟨156401858520693087739831693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208535811360924116986442257 156401858520693087739831693)
                ·
                  refine ⟨58650696945259907902436885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156401858520693087739831693 58650696945259907902436885)
                  ·
                    refine ⟨2749251419309058182926729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58650696945259907902436885 2749251419309058182926729)
                    ·
                      refine ⟨2061938564481793637195047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749251419309058182926729 2061938564481793637195047)
                      ·
                        rfl

theorem cell23_4015611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6, 2].length) (baseStart_4015611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015611 prefixEnd_4015611 := by exact prefixLift 4015611
  have htrace : WordTrace (prefixWord ++ tailWord_4015611) baseStart_4015611 baseEnd_4015611 := by
    simpa [prefixWord, tailWord_4015611, baseEnd_4015611] using wordTrace_append hprefix tailTrace_4015611
  have hstable : (prefixWord ++ tailWord_4015611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015611).length < 2 ^ (prefixWord ++ tailWord_4015611).sum := by decide
  have hdescent : baseEnd_4015611 < baseStart_4015611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015646 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_4015646 : Nat := 118140960795 + 4015646 * 2 ^ 59
def prefixEnd_4015646 : Nat := 4983230072969 + 3 ^ 40 * 4015646 * 2
def baseEnd_4015646 : Nat := 229106281811633444473043

theorem tailTrace_4015646 : CollatzResearch.WordTrace tailWord_4015646 prefixEnd_4015646 229106281811633444473043 := by
  unfold tailWord_4015646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18307830251250979322646349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97641761340005223054113861 18307830251250979322646349)
  ·
    refine ⟨6865436344219117245992381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18307830251250979322646349 6865436344219117245992381)
    ·
      refine ⟨2574538629082168967247143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6865436344219117245992381 2574538629082168967247143)
      ·
        refine ⟨3861807943623253450870715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574538629082168967247143 3861807943623253450870715)
        ·
          refine ⟨5792711915434880176306073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861807943623253450870715 5792711915434880176306073)
          ·
            refine ⟨4344533936576160132229555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792711915434880176306073 4344533936576160132229555)
            ·
              refine ⟨6516800904864240198344333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344533936576160132229555 6516800904864240198344333)
              ·
                refine ⟨2443800339324090074379125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6516800904864240198344333 2443800339324090074379125)
                ·
                  refine ⟨229106281811633444473043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2443800339324090074379125 229106281811633444473043)
                  ·
                    rfl

theorem cell23_4015646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_4015646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015646 prefixEnd_4015646 := by exact prefixLift 4015646
  have htrace : WordTrace (prefixWord ++ tailWord_4015646) baseStart_4015646 baseEnd_4015646 := by
    simpa [prefixWord, tailWord_4015646, baseEnd_4015646] using wordTrace_append hprefix tailTrace_4015646
  have hstable : (prefixWord ++ tailWord_4015646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015646).length < 2 ^ (prefixWord ++ tailWord_4015646).sum := by decide
  have hdescent : baseEnd_4015646 < baseStart_4015646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015648 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4015648 : Nat := 118140960795 + 4015648 * 2 ^ 59
def prefixEnd_4015648 : Nat := 4983230072969 + 3 ^ 40 * 4015648 * 2
def baseEnd_4015648 : Nat := 2061957563266009992432377

theorem tailTrace_4015648 : CollatzResearch.WordTrace tailWord_4015648 prefixEnd_4015648 2061957563266009992432377 := by
  unfold tailWord_4015648
  simp only [CollatzResearch.WordTrace]
  refine ⟨73231357478000294461371799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97641809970667059281829065 73231357478000294461371799)
  ·
    refine ⟨109847036217000441692057699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73231357478000294461371799 109847036217000441692057699)
    ·
      refine ⟨164770554325500662538086549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109847036217000441692057699 164770554325500662538086549)
      ·
        refine ⟨7723619734007843556472807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164770554325500662538086549 7723619734007843556472807)
        ·
          refine ⟨11585429601011765334709211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723619734007843556472807 11585429601011765334709211)
          ·
            refine ⟨17378144401517648002063817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11585429601011765334709211 17378144401517648002063817)
            ·
              refine ⟨13033608301138236001547863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17378144401517648002063817 13033608301138236001547863)
              ·
                refine ⟨19550412451707354002321795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13033608301138236001547863 19550412451707354002321795)
                ·
                  refine ⟨29325618677561031003482693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19550412451707354002321795 29325618677561031003482693)
                  ·
                    refine ⟨5498553502042693313153005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29325618677561031003482693 5498553502042693313153005)
                    ·
                      refine ⟨2061957563266009992432377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5498553502042693313153005 2061957563266009992432377)
                      ·
                        rfl

theorem cell23_4015648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4015648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015648 prefixEnd_4015648 := by exact prefixLift 4015648
  have htrace : WordTrace (prefixWord ++ tailWord_4015648) baseStart_4015648 baseEnd_4015648 := by
    simpa [prefixWord, tailWord_4015648, baseEnd_4015648] using wordTrace_append hprefix tailTrace_4015648
  have hstable : (prefixWord ++ tailWord_4015648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015648).length < 2 ^ (prefixWord ++ tailWord_4015648).sum := by decide
  have hdescent : baseEnd_4015648 < baseStart_4015648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015672 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 1, 4]
def baseStart_4015672 : Nat := 118140960795 + 4015672 * 2 ^ 59
def prefixEnd_4015672 : Nat := 4983230072969 + 3 ^ 40 * 4015672 * 2
def baseEnd_4015672 : Nat := 687323295600572632844089

theorem tailTrace_4015672 : CollatzResearch.WordTrace tailWord_4015672 prefixEnd_4015672 687323295600572632844089 := by
  unfold tailWord_4015672
  simp only [CollatzResearch.WordTrace]
  refine ⟨73231795153956820510808635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97642393538609094014411513 73231795153956820510808635)
  ·
    refine ⟨109847692730935230766212953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73231795153956820510808635 109847692730935230766212953)
    ·
      refine ⟨82385769548201423074659715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109847692730935230766212953 82385769548201423074659715)
      ·
        refine ⟨123578654322302134611989573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82385769548201423074659715 123578654322302134611989573)
        ·
          refine ⟨23170997685431650239748045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123578654322302134611989573 23170997685431650239748045)
          ·
            refine ⟨8689124132036868839905517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23170997685431650239748045 8689124132036868839905517)
            ·
              refine ⟨3258421549513825814964569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8689124132036868839905517 3258421549513825814964569)
              ·
                refine ⟨2443816162135369361223427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258421549513825814964569 2443816162135369361223427)
                ·
                  refine ⟨3665724243203054041835141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443816162135369361223427 3665724243203054041835141)
                  ·
                    refine ⟨687323295600572632844089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665724243203054041835141 687323295600572632844089)
                    ·
                      rfl

theorem cell23_4015672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_4015672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015672 prefixEnd_4015672 := by exact prefixLift 4015672
  have htrace : WordTrace (prefixWord ++ tailWord_4015672) baseStart_4015672 baseEnd_4015672 := by
    simpa [prefixWord, tailWord_4015672, baseEnd_4015672] using wordTrace_append hprefix tailTrace_4015672
  have hstable : (prefixWord ++ tailWord_4015672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015672).length < 2 ^ (prefixWord ++ tailWord_4015672).sum := by decide
  have hdescent : baseEnd_4015672 < baseStart_4015672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015698 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4015698 : Nat := 118140960795 + 4015698 * 2 ^ 59
def prefixEnd_4015698 : Nat := 4983230072969 + 3 ^ 40 * 4015698 * 2
def baseEnd_4015698 : Nat := 687327745766244932269049

theorem tailTrace_4015698 : CollatzResearch.WordTrace tailWord_4015698 prefixEnd_4015698 687327745766244932269049 := by
  unfold tailWord_4015698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36616134651454861865515937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97643025737212964974709165 36616134651454861865515937)
  ·
    refine ⟨27462100988591146399136953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36616134651454861865515937 27462100988591146399136953)
    ·
      refine ⟨20596575741443359799352715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27462100988591146399136953 20596575741443359799352715)
      ·
        refine ⟨30894863612165039699029073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20596575741443359799352715 30894863612165039699029073)
        ·
          refine ⟨23171147709123779774271805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30894863612165039699029073 23171147709123779774271805)
          ·
            refine ⟨8689180390921417415351927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23171147709123779774271805 8689180390921417415351927)
            ·
              refine ⟨13033770586382126123027891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689180390921417415351927 13033770586382126123027891)
              ·
                refine ⟨19550655879573189184541837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13033770586382126123027891 19550655879573189184541837)
                ·
                  refine ⟨7331495954839945944203189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19550655879573189184541837 7331495954839945944203189)
                  ·
                    refine ⟨687327745766244932269049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331495954839945944203189 687327745766244932269049)
                    ·
                      rfl

theorem cell23_4015698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4015698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015698 prefixEnd_4015698 := by exact prefixLift 4015698
  have htrace : WordTrace (prefixWord ++ tailWord_4015698) baseStart_4015698 baseEnd_4015698 := by
    simpa [prefixWord, tailWord_4015698, baseEnd_4015698] using wordTrace_append hprefix tailTrace_4015698
  have hstable : (prefixWord ++ tailWord_4015698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015698).length < 2 ^ (prefixWord ++ tailWord_4015698).sum := by decide
  have hdescent : baseEnd_4015698 < baseStart_4015698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015715 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 1, 5]
def baseStart_4015715 : Nat := 118140960795 + 4015715 * 2 ^ 59
def prefixEnd_4015715 : Nat := 4983230072969 + 3 ^ 40 * 4015715 * 2
def baseEnd_4015715 : Nat := 687330655489953743431523

theorem tailTrace_4015715 : CollatzResearch.WordTrace tailWord_4015715 prefixEnd_4015715 687330655489953743431523 := by
  unfold tailWord_4015715
  simp only [CollatzResearch.WordTrace]
  refine ⟨146465158646757859365432599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97643439097838572910288399 146465158646757859365432599)
  ·
    refine ⟨219697737970136789048148899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146465158646757859365432599 219697737970136789048148899)
    ·
      refine ⟨329546606955205183572223349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219697737970136789048148899 329546606955205183572223349)
      ·
        refine ⟨30894994402050485959895939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329546606955205183572223349 30894994402050485959895939)
        ·
          refine ⟨46342491603075728939843909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30894994402050485959895939 46342491603075728939843909)
          ·
            refine ⟨8689217175576699176220733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46342491603075728939843909 8689217175576699176220733)
            ·
              refine ⟨3258456440841262191082775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8689217175576699176220733 3258456440841262191082775)
              ·
                refine ⟨4887684661261893286624163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258456440841262191082775 4887684661261893286624163)
                ·
                  refine ⟨7331526991892839929936245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887684661261893286624163 7331526991892839929936245)
                  ·
                    refine ⟨687330655489953743431523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331526991892839929936245 687330655489953743431523)
                    ·
                      rfl

theorem cell23_4015715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 5].length) (baseStart_4015715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015715 prefixEnd_4015715 := by exact prefixLift 4015715
  have htrace : WordTrace (prefixWord ++ tailWord_4015715) baseStart_4015715 baseEnd_4015715 := by
    simpa [prefixWord, tailWord_4015715, baseEnd_4015715] using wordTrace_append hprefix tailTrace_4015715
  have hstable : (prefixWord ++ tailWord_4015715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015715).length < 2 ^ (prefixWord ++ tailWord_4015715).sum := by decide
  have hdescent : baseEnd_4015715 < baseStart_4015715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015735 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 3, 2, 2]
def baseStart_4015735 : Nat := 118140960795 + 4015735 * 2 ^ 59
def prefixEnd_4015735 : Nat := 4983230072969 + 3 ^ 40 * 4015735 * 2
def baseEnd_4015735 : Nat := 2062002236082951152044477

theorem tailTrace_4015735 : CollatzResearch.WordTrace tailWord_4015735 prefixEnd_4015735 2062002236082951152044477 := by
  unfold tailWord_4015735
  simp only [CollatzResearch.WordTrace]
  refine ⟨146465888106685402781160659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97643925404456935187440439 146465888106685402781160659)
  ·
    refine ⟨219698832160028104171740989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146465888106685402781160659 219698832160028104171740989)
    ·
      refine ⟨82387062060010539064402871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219698832160028104171740989 82387062060010539064402871)
      ·
        refine ⟨123580593090015808596604307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82387062060010539064402871 123580593090015808596604307)
        ·
          refine ⟨185370889635023712894906461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123580593090015808596604307 185370889635023712894906461)
          ·
            refine ⟨69514083613133892335589923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185370889635023712894906461 69514083613133892335589923)
            ·
              refine ⟨104271125419700838503384885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69514083613133892335589923 104271125419700838503384885)
              ·
                refine ⟨9775418008096953609692333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104271125419700838503384885 9775418008096953609692333)
                ·
                  refine ⟨3665781753036357603634625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9775418008096953609692333 3665781753036357603634625)
                  ·
                    refine ⟨2749336314777268202725969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665781753036357603634625 2749336314777268202725969)
                    ·
                      refine ⟨2062002236082951152044477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749336314777268202725969 2062002236082951152044477)
                      ·
                        rfl

theorem cell23_4015735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_4015735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015735 prefixEnd_4015735 := by exact prefixLift 4015735
  have htrace : WordTrace (prefixWord ++ tailWord_4015735) baseStart_4015735 baseEnd_4015735 := by
    simpa [prefixWord, tailWord_4015735, baseEnd_4015735] using wordTrace_append hprefix tailTrace_4015735
  have hstable : (prefixWord ++ tailWord_4015735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015735).length < 2 ^ (prefixWord ++ tailWord_4015735).sum := by decide
  have hdescent : baseEnd_4015735 < baseStart_4015735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015745 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4015745 : Nat := 118140960795 + 4015745 * 2 ^ 59
def prefixEnd_4015745 : Nat := 4983230072969 + 3 ^ 40 * 4015745 * 2
def baseEnd_4015745 : Nat := 687335790296498704306477

theorem tailTrace_4015745 : CollatzResearch.WordTrace tailWord_4015745 prefixEnd_4015745 687335790296498704306477 := by
  unfold tailWord_4015745
  simp only [CollatzResearch.WordTrace]
  refine ⟨146466252836649174489024689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97644168557766116326016459 146466252836649174489024689)
  ·
    refine ⟨109849689627486880866768517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146466252836649174489024689 109849689627486880866768517)
    ·
      refine ⟨20596816805153790162519097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109849689627486880866768517 20596816805153790162519097)
      ·
        refine ⟨15447612603865342621889323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20596816805153790162519097 15447612603865342621889323)
        ·
          refine ⟨23171418905798013932833985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447612603865342621889323 23171418905798013932833985)
          ·
            refine ⟨17378564179348510449625489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23171418905798013932833985 17378564179348510449625489)
            ·
              refine ⟨13033923134511382837219117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17378564179348510449625489 13033923134511382837219117)
              ·
                refine ⟨4887721175441768563957169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13033923134511382837219117 4887721175441768563957169)
                ·
                  refine ⟨3665790881581326422967877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4887721175441768563957169 3665790881581326422967877)
                  ·
                    refine ⟨687335790296498704306477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665790881581326422967877 687335790296498704306477)
                    ·
                      rfl

theorem cell23_4015745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4015745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015745 prefixEnd_4015745 := by exact prefixLift 4015745
  have htrace : WordTrace (prefixWord ++ tailWord_4015745) baseStart_4015745 baseEnd_4015745 := by
    simpa [prefixWord, tailWord_4015745, baseEnd_4015745] using wordTrace_append hprefix tailTrace_4015745
  have hstable : (prefixWord ++ tailWord_4015745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015745).length < 2 ^ (prefixWord ++ tailWord_4015745).sum := by decide
  have hdescent : baseEnd_4015745 < baseStart_4015745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015772 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_4015772 : Nat := 118140960795 + 4015772 * 2 ^ 59
def prefixEnd_4015772 : Nat := 4983230072969 + 3 ^ 40 * 4015772 * 2
def baseEnd_4015772 : Nat := 2062021234867167507281807

theorem tailTrace_4015772 : CollatzResearch.WordTrace tailWord_4015772 prefixEnd_4015772 2062021234867167507281807 := by
  unfold tailWord_4015772
  simp only [CollatzResearch.WordTrace]
  refine ⟨73233618803775679050128785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97644825071700905400171713 73233618803775679050128785)
  ·
    refine ⟨54925214102831759287596589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73233618803775679050128785 54925214102831759287596589)
    ·
      refine ⟨20596955288561909732848721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54925214102831759287596589 20596955288561909732848721)
      ·
        refine ⟨15447716466421432299636541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20596955288561909732848721 15447716466421432299636541)
        ·
          refine ⟨5792893674908037112363703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15447716466421432299636541 5792893674908037112363703)
          ·
            refine ⟨8689340512362055668545555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792893674908037112363703 8689340512362055668545555)
            ·
              refine ⟨13034010768543083502818333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689340512362055668545555 13034010768543083502818333)
              ·
                refine ⟨4887754038203656313556875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13034010768543083502818333 4887754038203656313556875)
                ·
                  refine ⟨7331631057305484470335313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887754038203656313556875 7331631057305484470335313)
                  ·
                    refine ⟨5498723292979113352751485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331631057305484470335313 5498723292979113352751485)
                    ·
                      refine ⟨2062021234867167507281807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5498723292979113352751485 2062021234867167507281807)
                      ·
                        rfl

theorem cell23_4015772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_4015772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015772 prefixEnd_4015772 := by exact prefixLift 4015772
  have htrace : WordTrace (prefixWord ++ tailWord_4015772) baseStart_4015772 baseEnd_4015772 := by
    simpa [prefixWord, tailWord_4015772, baseEnd_4015772] using wordTrace_append hprefix tailTrace_4015772
  have hstable : (prefixWord ++ tailWord_4015772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015772).length < 2 ^ (prefixWord ++ tailWord_4015772).sum := by decide
  have hdescent : baseEnd_4015772 < baseStart_4015772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015811 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_4015811 : Nat := 118140960795 + 4015811 * 2 ^ 59
def prefixEnd_4015811 : Nat := 4983230072969 + 3 ^ 40 * 4015811 * 2
def baseEnd_4015811 : Nat := 2062041260612692854694127

theorem tailTrace_4015811 : CollatzResearch.WordTrace tailWord_4015811 prefixEnd_4015811 2062041260612692854694127 := by
  unfold tailWord_4015811
  simp only [CollatzResearch.WordTrace]
  refine ⟨146468660054410067760927287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97645773369606711840618191 146468660054410067760927287)
  ·
    refine ⟨219702990081615101641390931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146468660054410067760927287 219702990081615101641390931)
    ·
      refine ⟨329554485122422652462086397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219702990081615101641390931 329554485122422652462086397)
      ·
        refine ⟨123582931920908494673282399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329554485122422652462086397 123582931920908494673282399)
        ·
          refine ⟨185374397881362742009923599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123582931920908494673282399 185374397881362742009923599)
          ·
            refine ⟨278061596822044113014885399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185374397881362742009923599 278061596822044113014885399)
            ·
              refine ⟨417092395233066169522328099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278061596822044113014885399 417092395233066169522328099)
              ·
                refine ⟨625638592849599254283492149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417092395233066169522328099 625638592849599254283492149)
                ·
                  refine ⟨58653618079649930089077389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 625638592849599254283492149 58653618079649930089077389)
                  ·
                    refine ⟨21995106779868723783404021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58653618079649930089077389 21995106779868723783404021)
                    ·
                      refine ⟨2062041260612692854694127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21995106779868723783404021 2062041260612692854694127)
                      ·
                        rfl

theorem cell23_4015811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_4015811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015811 prefixEnd_4015811 := by exact prefixLift 4015811
  have htrace : WordTrace (prefixWord ++ tailWord_4015811) baseStart_4015811 baseEnd_4015811 := by
    simpa [prefixWord, tailWord_4015811, baseEnd_4015811] using wordTrace_append hprefix tailTrace_4015811
  have hstable : (prefixWord ++ tailWord_4015811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015811).length < 2 ^ (prefixWord ++ tailWord_4015811).sum := by decide
  have hdescent : baseEnd_4015811 < baseStart_4015811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015859 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 2, 2, 2]
def baseStart_4015859 : Nat := 118140960795 + 4015859 * 2 ^ 59
def prefixEnd_4015859 : Nat := 4983230072969 + 3 ^ 40 * 4015859 * 2
def baseEnd_4015859 : Nat := 2062065907684108666893907

theorem tailTrace_4015859 : CollatzResearch.WordTrace tailWord_4015859 prefixEnd_4015859 2062065907684108666893907 := by
  unfold tailWord_4015859
  simp only [CollatzResearch.WordTrace]
  refine ⟨146470410758236171958674631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97646940505490781305783087 146470410758236171958674631)
  ·
    refine ⟨219705616137354257938011947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146470410758236171958674631 219705616137354257938011947)
    ·
      refine ⟨329558424206031386907017921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219705616137354257938011947 329558424206031386907017921)
      ·
        refine ⟨247168818154523540180263441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329558424206031386907017921 247168818154523540180263441)
        ·
          refine ⟨185376613615892655135197581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247168818154523540180263441 185376613615892655135197581)
          ·
            refine ⟨69516230105959745675699093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185376613615892655135197581 69516230105959745675699093)
            ·
              refine ⟨3258573286216863078548395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69516230105959745675699093 3258573286216863078548395)
              ·
                refine ⟨4887859929325294617822593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258573286216863078548395 4887859929325294617822593)
                ·
                  refine ⟨3665894946993970963366945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4887859929325294617822593 3665894946993970963366945)
                  ·
                    refine ⟨2749421210245478222525209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665894946993970963366945 2749421210245478222525209)
                    ·
                      refine ⟨2062065907684108666893907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749421210245478222525209 2062065907684108666893907)
                      ·
                        rfl

theorem cell23_4015859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 2, 2].length) (baseStart_4015859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015859 prefixEnd_4015859 := by exact prefixLift 4015859
  have htrace : WordTrace (prefixWord ++ tailWord_4015859) baseStart_4015859 baseEnd_4015859 := by
    simpa [prefixWord, tailWord_4015859, baseEnd_4015859] using wordTrace_append hprefix tailTrace_4015859
  have hstable : (prefixWord ++ tailWord_4015859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015859).length < 2 ^ (prefixWord ++ tailWord_4015859).sum := by decide
  have hdescent : baseEnd_4015859 < baseStart_4015859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015895 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 2, 5]
def baseStart_4015895 : Nat := 118140960795 + 4015895 * 2 ^ 59
def prefixEnd_4015895 : Nat := 4983230072969 + 3 ^ 40 * 4015895 * 2
def baseEnd_4015895 : Nat := 687361464329223508681247

theorem tailTrace_4015895 : CollatzResearch.WordTrace tailWord_4015895 prefixEnd_4015895 687361464329223508681247 := by
  unfold tailWord_4015895
  simp only [CollatzResearch.WordTrace]
  refine ⟨146471723786105750106985139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97647815857403833404656759 146471723786105750106985139)
  ·
    refine ⟨219707585679158625160477709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146471723786105750106985139 219707585679158625160477709)
    ·
      refine ⟨82390344629684484435179141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219707585679158625160477709 82390344629684484435179141)
      ·
        refine ⟨15448189618065840831596089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82390344629684484435179141 15448189618065840831596089)
        ·
          refine ⟨11586142213549380623697067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15448189618065840831596089 11586142213549380623697067)
          ·
            refine ⟨17379213320324070935545601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586142213549380623697067 17379213320324070935545601)
            ·
              refine ⟨13034409990243053201659201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17379213320324070935545601 13034409990243053201659201)
              ·
                refine ⟨9775807492682289901244401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13034409990243053201659201 9775807492682289901244401)
                ·
                  refine ⟨7331855619511717425933301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775807492682289901244401 7331855619511717425933301)
                  ·
                    refine ⟨687361464329223508681247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331855619511717425933301 687361464329223508681247)
                    ·
                      rfl

theorem cell23_4015895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_4015895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015895 prefixEnd_4015895 := by exact prefixLift 4015895
  have htrace : WordTrace (prefixWord ++ tailWord_4015895) baseStart_4015895 baseEnd_4015895 := by
    simpa [prefixWord, tailWord_4015895, baseEnd_4015895] using wordTrace_append hprefix tailTrace_4015895
  have hstable : (prefixWord ++ tailWord_4015895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015895).length < 2 ^ (prefixWord ++ tailWord_4015895).sum := by decide
  have hdescent : baseEnd_4015895 < baseStart_4015895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015929 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 2, 5]
def baseStart_4015929 : Nat := 118140960795 + 4015929 * 2 ^ 59
def prefixEnd_4015929 : Nat := 4983230072969 + 3 ^ 40 * 4015929 * 2
def baseEnd_4015929 : Nat := 687367283776641131006195

theorem tailTrace_4015929 : CollatzResearch.WordTrace tailWord_4015929 prefixEnd_4015929 687367283776641131006195 := by
  unfold tailWord_4015929
  simp only [CollatzResearch.WordTrace]
  refine ⟨146472963867982573913722841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97648642578655049275815227 146472963867982573913722841)
  ·
    refine ⟨109854722900986930435292131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146472963867982573913722841 109854722900986930435292131)
    ·
      refine ⟨164782084351480395652938197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109854722900986930435292131 164782084351480395652938197)
      ·
        refine ⟨3862080101987821773115739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 164782084351480395652938197 3862080101987821773115739)
        ·
          refine ⟨5793120152981732659673609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862080101987821773115739 5793120152981732659673609)
          ·
            refine ⟨4344840114736299494755207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5793120152981732659673609 4344840114736299494755207)
            ·
              refine ⟨6517260172104449242132811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344840114736299494755207 6517260172104449242132811)
              ·
                refine ⟨9775890258156673863199217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517260172104449242132811 9775890258156673863199217)
                ·
                  refine ⟨7331917693617505397399413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775890258156673863199217 7331917693617505397399413)
                  ·
                    refine ⟨687367283776641131006195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331917693617505397399413 687367283776641131006195)
                    ·
                      rfl

theorem cell23_4015929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_4015929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015929 prefixEnd_4015929 := by exact prefixLift 4015929
  have htrace : WordTrace (prefixWord ++ tailWord_4015929) baseStart_4015929 baseEnd_4015929 := by
    simpa [prefixWord, tailWord_4015929, baseEnd_4015929] using wordTrace_append hprefix tailTrace_4015929
  have hstable : (prefixWord ++ tailWord_4015929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015929).length < 2 ^ (prefixWord ++ tailWord_4015929).sum := by decide
  have hdescent : baseEnd_4015929 < baseStart_4015929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015949 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4015949 : Nat := 118140960795 + 4015949 * 2 ^ 59
def prefixEnd_4015949 : Nat := 4983230072969 + 3 ^ 40 * 4015949 * 2
def baseEnd_4015949 : Nat := 2062112120943013314768493

theorem tailTrace_4015949 : CollatzResearch.WordTrace tailWord_4015949 prefixEnd_4015949 2062112120943013314768493 := by
  unfold tailWord_4015949
  simp only [CollatzResearch.WordTrace]
  refine ⟨146473693327910117329450901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97649128885273411552967267 146473693327910117329450901)
  ·
    refine ⟨6865954374745786749818011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146473693327910117329450901 6865954374745786749818011)
    ·
      refine ⟨10298931562118680124727017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865954374745786749818011 10298931562118680124727017)
      ·
        refine ⟨7724198671589010093545263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10298931562118680124727017 7724198671589010093545263)
        ·
          refine ⟨11586298007383515140317895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724198671589010093545263 11586298007383515140317895)
          ·
            refine ⟨17379447011075272710476843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586298007383515140317895 17379447011075272710476843)
            ·
              refine ⟨26069170516612909065715265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17379447011075272710476843 26069170516612909065715265)
              ·
                refine ⟨19551877887459681799286449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26069170516612909065715265 19551877887459681799286449)
                ·
                  refine ⟨14663908415594761349464837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19551877887459681799286449 14663908415594761349464837)
                  ·
                    refine ⟨2749482827924017753024657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14663908415594761349464837 2749482827924017753024657)
                    ·
                      refine ⟨2062112120943013314768493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749482827924017753024657 2062112120943013314768493)
                      ·
                        rfl

theorem cell23_4015949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4015949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4015949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4015949 prefixEnd_4015949 := by exact prefixLift 4015949
  have htrace : WordTrace (prefixWord ++ tailWord_4015949) baseStart_4015949 baseEnd_4015949 := by
    simpa [prefixWord, tailWord_4015949, baseEnd_4015949] using wordTrace_append hprefix tailTrace_4015949
  have hstable : (prefixWord ++ tailWord_4015949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015949).length < 2 ^ (prefixWord ++ tailWord_4015949).sum := by decide
  have hdescent : baseEnd_4015949 < baseStart_4015949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016025 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_4016025 : Nat := 118140960795 + 4016025 * 2 ^ 59
def prefixEnd_4016025 : Nat := 4983230072969 + 3 ^ 40 * 4016025 * 2
def baseEnd_4016025 : Nat := 2062151145472755017418143

theorem tailTrace_4016025 : CollatzResearch.WordTrace tailWord_4016025 prefixEnd_4016025 2062151145472755017418143 := by
  unfold tailWord_4016025
  simp only [CollatzResearch.WordTrace]
  refine ⟨146476465275634782309217529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97650976850423188206145019 146476465275634782309217529)
  ·
    refine ⟨109857348956726086731913147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146476465275634782309217529 109857348956726086731913147)
    ·
      refine ⟨164786023435089130097869721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109857348956726086731913147 164786023435089130097869721)
      ·
        refine ⟨123589517576316847573402291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164786023435089130097869721 123589517576316847573402291)
        ·
          refine ⟨185384276364475271360103437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123589517576316847573402291 185384276364475271360103437)
          ·
            refine ⟨69519103636678226760038789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185384276364475271360103437 69519103636678226760038789)
            ·
              refine ⟨13034831931877167517507273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69519103636678226760038789 13034831931877167517507273)
              ·
                refine ⟨9776123948907875638130455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13034831931877167517507273 9776123948907875638130455)
                ·
                  refine ⟨14664185923361813457195683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776123948907875638130455 14664185923361813457195683)
                  ·
                    refine ⟨21996278885042720185793525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14664185923361813457195683 21996278885042720185793525)
                    ·
                      refine ⟨2062151145472755017418143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21996278885042720185793525 2062151145472755017418143)
                      ·
                        rfl

theorem cell23_4016025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_4016025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016025 prefixEnd_4016025 := by exact prefixLift 4016025
  have htrace : WordTrace (prefixWord ++ tailWord_4016025) baseStart_4016025 baseEnd_4016025 := by
    simpa [prefixWord, tailWord_4016025, baseEnd_4016025] using wordTrace_append hprefix tailTrace_4016025
  have hstable : (prefixWord ++ tailWord_4016025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016025).length < 2 ^ (prefixWord ++ tailWord_4016025).sum := by decide
  have hdescent : baseEnd_4016025 < baseStart_4016025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016035 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4]
def baseStart_4016035 : Nat := 118140960795 + 4016035 * 2 ^ 59
def prefixEnd_4016035 : Nat := 4983230072969 + 3 ^ 40 * 4016035 * 2
def baseEnd_4016035 : Nat := 2062156280279299978293097

theorem tailTrace_4016035 : CollatzResearch.WordTrace tailWord_4016035 prefixEnd_4016035 2062156280279299978293097 := by
  unfold tailWord_4016035
  simp only [CollatzResearch.WordTrace]
  refine ⟨146476830005598554017081559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97651220003732369344721039 146476830005598554017081559)
  ·
    refine ⟨219715245008397831025622339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146476830005598554017081559 219715245008397831025622339)
    ·
      refine ⟨329572867512596746538433509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219715245008397831025622339 329572867512596746538433509)
      ·
        refine ⟨61794912658611889975956283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329572867512596746538433509 61794912658611889975956283)
        ·
          refine ⟨92692368987917834963934425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61794912658611889975956283 92692368987917834963934425)
          ·
            refine ⟨69519276740938376222950819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92692368987917834963934425 69519276740938376222950819)
            ·
              refine ⟨104278915111407564334426229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69519276740938376222950819 104278915111407564334426229)
              ·
                refine ⟨9776148291694459156352459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104278915111407564334426229 9776148291694459156352459)
                ·
                  refine ⟨14664222437541688734528689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776148291694459156352459 14664222437541688734528689)
                  ·
                    refine ⟨10998166828156266550896517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14664222437541688734528689 10998166828156266550896517)
                    ·
                      refine ⟨2062156280279299978293097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10998166828156266550896517 2062156280279299978293097)
                      ·
                        rfl

theorem cell23_4016035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_4016035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016035 prefixEnd_4016035 := by exact prefixLift 4016035
  have htrace : WordTrace (prefixWord ++ tailWord_4016035) baseStart_4016035 baseEnd_4016035 := by
    simpa [prefixWord, tailWord_4016035, baseEnd_4016035] using wordTrace_append hprefix tailTrace_4016035
  have hstable : (prefixWord ++ tailWord_4016035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016035).length < 2 ^ (prefixWord ++ tailWord_4016035).sum := by decide
  have hdescent : baseEnd_4016035 < baseStart_4016035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016039 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_4016039 : Nat := 118140960795 + 4016039 * 2 ^ 59
def prefixEnd_4016039 : Nat := 4983230072969 + 3 ^ 40 * 4016039 * 2
def baseEnd_4016039 : Nat := 2062158334201917962643079

theorem tailTrace_4016039 : CollatzResearch.WordTrace tailWord_4016039 prefixEnd_4016039 2062158334201917962643079 := by
  unfold tailWord_4016039
  simp only [CollatzResearch.WordTrace]
  refine ⟨146476975897584062700227171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97651317265056041800151447 146476975897584062700227171)
  ·
    refine ⟨219715463846376094050340757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146476975897584062700227171 219715463846376094050340757)
    ·
      refine ⟨10299162367798879408609723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219715463846376094050340757 10299162367798879408609723)
      ·
        refine ⟨15448743551698319112914585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299162367798879408609723 15448743551698319112914585)
        ·
          refine ⟨11586557663773739334685939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15448743551698319112914585 11586557663773739334685939)
          ·
            refine ⟨17379836495660609002028909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586557663773739334685939 17379836495660609002028909)
            ·
              refine ⟨6517438685872728375760841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17379836495660609002028909 6517438685872728375760841)
              ·
                refine ⟨4888079014404546281820631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517438685872728375760841 4888079014404546281820631)
                ·
                  refine ⟨7332118521606819422730947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888079014404546281820631 7332118521606819422730947)
                  ·
                    refine ⟨10998177782410229134096421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7332118521606819422730947 10998177782410229134096421)
                    ·
                      refine ⟨2062158334201917962643079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10998177782410229134096421 2062158334201917962643079)
                      ·
                        rfl

theorem cell23_4016039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_4016039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016039 prefixEnd_4016039 := by exact prefixLift 4016039
  have htrace : WordTrace (prefixWord ++ tailWord_4016039) baseStart_4016039 baseEnd_4016039 := by
    simpa [prefixWord, tailWord_4016039, baseEnd_4016039] using wordTrace_append hprefix tailTrace_4016039
  have hstable : (prefixWord ++ tailWord_4016039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016039).length < 2 ^ (prefixWord ++ tailWord_4016039).sum := by decide
  have hdescent : baseEnd_4016039 < baseStart_4016039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016056 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 1, 2, 2]
def baseStart_4016056 : Nat := 118140960795 + 4016056 * 2 ^ 59
def prefixEnd_4016056 : Nat := 4983230072969 + 3 ^ 40 * 4016056 * 2
def baseEnd_4016056 : Nat := 2062167063373044396130501

theorem tailTrace_4016056 : CollatzResearch.WordTrace tailWord_4016056 prefixEnd_4016056 2062167063373044396130501 := by
  unfold tailWord_4016056
  simp only [CollatzResearch.WordTrace]
  refine ⟨73238797969261237301798011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97651730625681649735730681 73238797969261237301798011)
  ·
    refine ⟨109858196953891855952697017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73238797969261237301798011 109858196953891855952697017)
    ·
      refine ⟨82393647715418891964522763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109858196953891855952697017 82393647715418891964522763)
      ·
        refine ⟨123590471573128337946784145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82393647715418891964522763 123590471573128337946784145)
        ·
          refine ⟨92692853679846253460088109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123590471573128337946784145 92692853679846253460088109)
          ·
            refine ⟨34759820129942345047533041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92692853679846253460088109 34759820129942345047533041)
            ·
              refine ⟨26069865097456758785649781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34759820129942345047533041 26069865097456758785649781)
              ·
                refine ⟨2444049852886571136154667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26069865097456758785649781 2444049852886571136154667)
                ·
                  refine ⟨3666074779329856704232001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444049852886571136154667 3666074779329856704232001)
                  ·
                    refine ⟨2749556084497392528174001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666074779329856704232001 2749556084497392528174001)
                    ·
                      refine ⟨2062167063373044396130501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749556084497392528174001 2062167063373044396130501)
                      ·
                        rfl

theorem cell23_4016056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_4016056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016056 prefixEnd_4016056 := by exact prefixLift 4016056
  have htrace : WordTrace (prefixWord ++ tailWord_4016056) baseStart_4016056 baseEnd_4016056 := by
    simpa [prefixWord, tailWord_4016056, baseEnd_4016056] using wordTrace_append hprefix tailTrace_4016056
  have hstable : (prefixWord ++ tailWord_4016056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016056).length < 2 ^ (prefixWord ++ tailWord_4016056).sum := by decide
  have hdescent : baseEnd_4016056 < baseStart_4016056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016086 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4016086 : Nat := 118140960795 + 4016086 * 2 ^ 59
def prefixEnd_4016086 : Nat := 4983230072969 + 3 ^ 40 * 4016086 * 2
def baseEnd_4016086 : Nat := 2062182467792679278755363

theorem tailTrace_4016086 : CollatzResearch.WordTrace tailWord_4016086 prefixEnd_4016086 2062182467792679278755363 := by
  unfold tailWord_4016086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154918133025861857949257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97652460085609193151458741 9154918133025861857949257)
  ·
    refine ⟨6866188599769396393461943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9154918133025861857949257 6866188599769396393461943)
    ·
      refine ⟨10299282899654094590192915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6866188599769396393461943 10299282899654094590192915)
      ·
        refine ⟨15448924349481141885289373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299282899654094590192915 15448924349481141885289373)
        ·
          refine ⟨5793346631055428206983515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15448924349481141885289373 5793346631055428206983515)
          ·
            refine ⟨8690019946583142310475273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793346631055428206983515 8690019946583142310475273)
            ·
              refine ⟨6517514959937356732856455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690019946583142310475273 6517514959937356732856455)
              ·
                refine ⟨9776272439906035099284683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517514959937356732856455 9776272439906035099284683)
                ·
                  refine ⟨14664408659859052648927025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776272439906035099284683 14664408659859052648927025)
                  ·
                    refine ⟨10998306494894289486695269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14664408659859052648927025 10998306494894289486695269)
                    ·
                      refine ⟨2062182467792679278755363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10998306494894289486695269 2062182467792679278755363)
                      ·
                        rfl

theorem cell23_4016086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4016086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016086 prefixEnd_4016086 := by exact prefixLift 4016086
  have htrace : WordTrace (prefixWord ++ tailWord_4016086) baseStart_4016086 baseEnd_4016086 := by
    simpa [prefixWord, tailWord_4016086, baseEnd_4016086] using wordTrace_append hprefix tailTrace_4016086
  have hstable : (prefixWord ++ tailWord_4016086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016086).length < 2 ^ (prefixWord ++ tailWord_4016086).sum := by decide
  have hdescent : baseEnd_4016086 < baseStart_4016086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016089 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_4016089 : Nat := 118140960795 + 4016089 * 2 ^ 59
def prefixEnd_4016089 : Nat := 4983230072969 + 3 ^ 40 * 4016089 * 2
def baseEnd_4016089 : Nat := 2062184008234642767017849

theorem tailTrace_4016089 : CollatzResearch.WordTrace tailWord_4016089 prefixEnd_4016089 2062184008234642767017849 := by
  unfold tailWord_4016089
  simp only [CollatzResearch.WordTrace]
  refine ⟨146478799547402921239547321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97652533031601947493031547 146478799547402921239547321)
  ·
    refine ⟨109859099660552190929660491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146478799547402921239547321 109859099660552190929660491)
    ·
      refine ⟨164788649490828286394490737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109859099660552190929660491 164788649490828286394490737)
      ·
        refine ⟨123591487118121214795868053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164788649490828286394490737 123591487118121214795868053)
        ·
          refine ⟨5793350958661931943556315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123591487118121214795868053 5793350958661931943556315)
          ·
            refine ⟨8690026437992897915334473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793350958661931943556315 8690026437992897915334473)
            ·
              refine ⟨6517519828494673436500855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690026437992897915334473 6517519828494673436500855)
              ·
                refine ⟨9776279742742010154751283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517519828494673436500855 9776279742742010154751283)
                ·
                  refine ⟨14664419614113015232126925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776279742742010154751283 14664419614113015232126925)
                  ·
                    refine ⟨5499157355292380712047597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14664419614113015232126925 5499157355292380712047597)
                    ·
                      refine ⟨2062184008234642767017849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499157355292380712047597 2062184008234642767017849)
                      ·
                        rfl

theorem cell23_4016089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_4016089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016089 prefixEnd_4016089 := by exact prefixLift 4016089
  have htrace : WordTrace (prefixWord ++ tailWord_4016089) baseStart_4016089 baseEnd_4016089 := by
    simpa [prefixWord, tailWord_4016089, baseEnd_4016089] using wordTrace_append hprefix tailTrace_4016089
  have hstable : (prefixWord ++ tailWord_4016089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016089).length < 2 ^ (prefixWord ++ tailWord_4016089).sum := by decide
  have hdescent : baseEnd_4016089 < baseStart_4016089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016099 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 3, 3, 2]
def baseStart_4016099 : Nat := 118140960795 + 4016099 * 2 ^ 59
def prefixEnd_4016099 : Nat := 4983230072969 + 3 ^ 40 * 4016099 * 2
def baseEnd_4016099 : Nat := 2062189143041187727892803

theorem tailTrace_4016099 : CollatzResearch.WordTrace tailWord_4016099 prefixEnd_4016099 2062189143041187727892803 := by
  unfold tailWord_4016099
  simp only [CollatzResearch.WordTrace]
  refine ⟨146479164277366692947411351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97652776184911128631607567 146479164277366692947411351)
  ·
    refine ⟨219718746416050039421117027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146479164277366692947411351 219718746416050039421117027)
    ·
      refine ⟨329578119624075059131675541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219718746416050039421117027 329578119624075059131675541)
      ·
        refine ⟨15448974357378518396797291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 329578119624075059131675541 15448974357378518396797291)
        ·
          refine ⟨23173461536067777595195937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15448974357378518396797291 23173461536067777595195937)
          ·
            refine ⟨17380096152050833196396953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23173461536067777595195937 17380096152050833196396953)
            ·
              refine ⟨13035072114038124897297715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17380096152050833196396953 13035072114038124897297715)
              ·
                refine ⟨19552608171057187345946573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13035072114038124897297715 19552608171057187345946573)
                ·
                  refine ⟨7332228064146445254729965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19552608171057187345946573 7332228064146445254729965)
                  ·
                    refine ⟨2749585524054916970523737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7332228064146445254729965 2749585524054916970523737)
                    ·
                      refine ⟨2062189143041187727892803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749585524054916970523737 2062189143041187727892803)
                      ·
                        rfl

theorem cell23_4016099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_4016099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016099 prefixEnd_4016099 := by exact prefixLift 4016099
  have htrace : WordTrace (prefixWord ++ tailWord_4016099) baseStart_4016099 baseEnd_4016099 := by
    simpa [prefixWord, tailWord_4016099, baseEnd_4016099] using wordTrace_append hprefix tailTrace_4016099
  have hstable : (prefixWord ++ tailWord_4016099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016099).length < 2 ^ (prefixWord ++ tailWord_4016099).sum := by decide
  have hdescent : baseEnd_4016099 < baseStart_4016099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016115 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5]
def baseStart_4016115 : Nat := 118140960795 + 4016115 * 2 ^ 59
def prefixEnd_4016115 : Nat := 4983230072969 + 3 ^ 40 * 4016115 * 2
def baseEnd_4016115 : Nat := 2062197358731659665292729

theorem tailTrace_4016115 : CollatzResearch.WordTrace tailWord_4016115 prefixEnd_4016115 2062197358731659665292729 := by
  unfold tailWord_4016115
  simp only [CollatzResearch.WordTrace]
  refine ⟨146479747845308727679993799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97653165230205818453329199 146479747845308727679993799)
  ·
    refine ⟨219719621767963091519990699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146479747845308727679993799 219719621767963091519990699)
    ·
      refine ⟨329579432651944637279986049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219719621767963091519990699 329579432651944637279986049)
      ·
        refine ⟨247184574488958477959989537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329579432651944637279986049 247184574488958477959989537)
        ·
          refine ⟨185388430866718858469992153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247184574488958477959989537 185388430866718858469992153)
          ·
            refine ⟨139041323150039143852494115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185388430866718858469992153 139041323150039143852494115)
            ·
              refine ⟨208561984725058715778741173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139041323150039143852494115 208561984725058715778741173)
              ·
                refine ⟨19552686067974254604256985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208561984725058715778741173 19552686067974254604256985)
                ·
                  refine ⟨14664514550980690953192739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19552686067974254604256985 14664514550980690953192739)
                  ·
                    refine ⟨21996771826471036429789109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14664514550980690953192739 21996771826471036429789109)
                    ·
                      refine ⟨2062197358731659665292729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21996771826471036429789109 2062197358731659665292729)
                      ·
                        rfl

theorem cell23_4016115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_4016115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016115 prefixEnd_4016115 := by exact prefixLift 4016115
  have htrace : WordTrace (prefixWord ++ tailWord_4016115) baseStart_4016115 baseEnd_4016115 := by
    simpa [prefixWord, tailWord_4016115, baseEnd_4016115] using wordTrace_append hprefix tailTrace_4016115
  have hstable : (prefixWord ++ tailWord_4016115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016115).length < 2 ^ (prefixWord ++ tailWord_4016115).sum := by decide
  have hdescent : baseEnd_4016115 < baseStart_4016115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016142 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4016142 : Nat := 118140960795 + 4016142 * 2 ^ 59
def prefixEnd_4016142 : Nat := 4983230072969 + 3 ^ 40 * 4016142 * 2
def baseEnd_4016142 : Nat := 2062211222709331059655105

theorem tailTrace_4016142 : CollatzResearch.WordTrace tailWord_4016142 prefixEnd_4016142 2062211222709331059655105 := by
  unfold tailWord_4016142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18310091577026363911403335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97653821744140607527484453 18310091577026363911403335)
  ·
    refine ⟨27465137365539545867105003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18310091577026363911403335 27465137365539545867105003)
    ·
      refine ⟨41197706048309318800657505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27465137365539545867105003 41197706048309318800657505)
      ·
        refine ⟨30898279536231989100493129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41197706048309318800657505 30898279536231989100493129)
        ·
          refine ⟨23173709652173991825369847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30898279536231989100493129 23173709652173991825369847)
          ·
            refine ⟨34760564478260987738054771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23173709652173991825369847 34760564478260987738054771)
            ·
              refine ⟨52140846717391481607082157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34760564478260987738054771 52140846717391481607082157)
              ·
                refine ⟨19552817519021805602655809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52140846717391481607082157 19552817519021805602655809)
                ·
                  refine ⟨14664613139266354201991857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19552817519021805602655809 14664613139266354201991857)
                  ·
                    refine ⟨10998459854449765651493893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14664613139266354201991857 10998459854449765651493893)
                    ·
                      refine ⟨2062211222709331059655105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10998459854449765651493893 2062211222709331059655105)
                      ·
                        rfl

theorem cell23_4016142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4016142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016142 prefixEnd_4016142 := by exact prefixLift 4016142
  have htrace : WordTrace (prefixWord ++ tailWord_4016142) baseStart_4016142 baseEnd_4016142 := by
    simpa [prefixWord, tailWord_4016142, baseEnd_4016142] using wordTrace_append hprefix tailTrace_4016142
  have hstable : (prefixWord ++ tailWord_4016142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016142).length < 2 ^ (prefixWord ++ tailWord_4016142).sum := by decide
  have hdescent : baseEnd_4016142 < baseStart_4016142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016189 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_4016189 : Nat := 118140960795 + 4016189 * 2 ^ 59
def prefixEnd_4016189 : Nat := 4983230072969 + 3 ^ 40 * 4016189 * 2
def baseEnd_4016189 : Nat := 2062235356300092375767389

theorem tailTrace_4016189 : CollatzResearch.WordTrace tailWord_4016189 prefixEnd_4016189 2062235356300092375767389 := by
  unfold tailWord_4016189
  simp only [CollatzResearch.WordTrace]
  refine ⟨146482446847040638318187621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97654964564693758878791747 146482446847040638318187621)
  ·
    refine ⟨27465458783820119684660179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146482446847040638318187621 27465458783820119684660179)
    ·
      refine ⟨41198188175730179526990269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27465458783820119684660179 41198188175730179526990269)
      ·
        refine ⟨15449320565898817322621351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41198188175730179526990269 15449320565898817322621351)
        ·
          refine ⟨23173980848848225983932027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15449320565898817322621351 23173980848848225983932027)
          ·
            refine ⟨34760971273272338975898041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23173980848848225983932027 34760971273272338975898041)
            ·
              refine ⟨26070728454954254231923531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34760971273272338975898041 26070728454954254231923531)
              ·
                refine ⟨39106092682431381347885297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26070728454954254231923531 39106092682431381347885297)
                ·
                  refine ⟨29329569511823536010913973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39106092682431381347885297 29329569511823536010913973)
                  ·
                    refine ⟨2749647141733456501023185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29329569511823536010913973 2749647141733456501023185)
                    ·
                      refine ⟨2062235356300092375767389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749647141733456501023185 2062235356300092375767389)
                      ·
                        rfl

theorem cell23_4016189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_4016189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016189 prefixEnd_4016189 := by exact prefixLift 4016189
  have htrace : WordTrace (prefixWord ++ tailWord_4016189) baseStart_4016189 baseEnd_4016189 := by
    simpa [prefixWord, tailWord_4016189, baseEnd_4016189] using wordTrace_append hprefix tailTrace_4016189
  have hstable : (prefixWord ++ tailWord_4016189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016189).length < 2 ^ (prefixWord ++ tailWord_4016189).sum := by decide
  have hdescent : baseEnd_4016189 < baseStart_4016189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016192 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_4016192 : Nat := 118140960795 + 4016192 * 2 ^ 59
def prefixEnd_4016192 : Nat := 4983230072969 + 3 ^ 40 * 4016192 * 2
def baseEnd_4016192 : Nat := 2062236896742055864029875

theorem tailTrace_4016192 : CollatzResearch.WordTrace tailWord_4016192 prefixEnd_4016192 2062236896742055864029875 := by
  unfold tailWord_4016192
  simp only [CollatzResearch.WordTrace]
  refine ⟨73241278133014884915273415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97655037510686513220364553 73241278133014884915273415)
  ·
    refine ⟨109861917199522327372910123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73241278133014884915273415 109861917199522327372910123)
    ·
      refine ⟨164792875799283491059365185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109861917199522327372910123 164792875799283491059365185)
      ·
        refine ⟨123594656849462618294523889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164792875799283491059365185 123594656849462618294523889)
        ·
          refine ⟨92695992637096963720892917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123594656849462618294523889 92695992637096963720892917)
          ·
            refine ⟨8690249309727840348833711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92695992637096963720892917 8690249309727840348833711)
            ·
              refine ⟨13035373964591760523250567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690249309727840348833711 13035373964591760523250567)
              ·
                refine ⟨19553060946887640784875851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13035373964591760523250567 19553060946887640784875851)
                ·
                  refine ⟨29329591420331461177313777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19553060946887640784875851 29329591420331461177313777)
                  ·
                    refine ⟨21997193565248595882985333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29329591420331461177313777 21997193565248595882985333)
                    ·
                      refine ⟨2062236896742055864029875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21997193565248595882985333 2062236896742055864029875)
                      ·
                        rfl

theorem cell23_4016192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_4016192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016192 prefixEnd_4016192 := by exact prefixLift 4016192
  have htrace : WordTrace (prefixWord ++ tailWord_4016192) baseStart_4016192 baseEnd_4016192 := by
    simpa [prefixWord, tailWord_4016192, baseEnd_4016192] using wordTrace_append hprefix tailTrace_4016192
  have hstable : (prefixWord ++ tailWord_4016192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016192).length < 2 ^ (prefixWord ++ tailWord_4016192).sum := by decide
  have hdescent : baseEnd_4016192 < baseStart_4016192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016195 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 8]
def baseStart_4016195 : Nat := 118140960795 + 4016195 * 2 ^ 59
def prefixEnd_4016195 : Nat := 4983230072969 + 3 ^ 40 * 4016195 * 2
def baseEnd_4016195 : Nat := 687412812394673117430787

theorem tailTrace_4016195 : CollatzResearch.WordTrace tailWord_4016195 prefixEnd_4016195 687412812394673117430787 := by
  unfold tailWord_4016195
  simp only [CollatzResearch.WordTrace]
  refine ⟨146482665685018901342906039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97655110456679267561937359 146482665685018901342906039)
  ·
    refine ⟨219723998527528352014359059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146482665685018901342906039 219723998527528352014359059)
    ·
      refine ⟨329585997791292528021538589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219723998527528352014359059 329585997791292528021538589)
      ·
        refine ⟨123594749171734698008076971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329585997791292528021538589 123594749171734698008076971)
        ·
          refine ⟨185392123757602047012115457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123594749171734698008076971 185392123757602047012115457)
          ·
            refine ⟨139044092818201535259086593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185392123757602047012115457 139044092818201535259086593)
            ·
              refine ⟨104283069613651151444314945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139044092818201535259086593 104283069613651151444314945)
              ·
                refine ⟨78212302210238363583236209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104283069613651151444314945 78212302210238363583236209)
                ·
                  refine ⟨58659226657678772687427157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78212302210238363583236209 58659226657678772687427157)
                  ·
                    refine ⟨687412812394673117430787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58659226657678772687427157 687412812394673117430787)
                    ·
                      rfl

theorem cell23_4016195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_4016195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016195 prefixEnd_4016195 := by exact prefixLift 4016195
  have htrace : WordTrace (prefixWord ++ tailWord_4016195) baseStart_4016195 baseEnd_4016195 := by
    simpa [prefixWord, tailWord_4016195, baseEnd_4016195] using wordTrace_append hprefix tailTrace_4016195
  have hstable : (prefixWord ++ tailWord_4016195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016195).length < 2 ^ (prefixWord ++ tailWord_4016195).sum := by decide
  have hdescent : baseEnd_4016195 < baseStart_4016195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016202 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4016202 : Nat := 118140960795 + 4016202 * 2 ^ 59
def prefixEnd_4016202 : Nat := 4983230072969 + 3 ^ 40 * 4016202 * 2
def baseEnd_4016202 : Nat := 2062242031548600824904829

theorem tailTrace_4016202 : CollatzResearch.WordTrace tailWord_4016202 prefixEnd_4016202 2062242031548600824904829 := by
  unfold tailWord_4016202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36620730248998385384602715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97655280663995694358940573 36620730248998385384602715)
  ·
    refine ⟨54931095373497578076904073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36620730248998385384602715 54931095373497578076904073)
    ·
      refine ⟨41198321530123183557678055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54931095373497578076904073 41198321530123183557678055)
      ·
        refine ⟨61797482295184775336517083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41198321530123183557678055 61797482295184775336517083)
        ·
          refine ⟨92696223442777163004775625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61797482295184775336517083 92696223442777163004775625)
          ·
            refine ⟨69522167582082872253581719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92696223442777163004775625 69522167582082872253581719)
            ·
              refine ⟨104283251373124308380372579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69522167582082872253581719 104283251373124308380372579)
              ·
                refine ⟨156424877059686462570558869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104283251373124308380372579 156424877059686462570558869)
                ·
                  refine ⟨7332416112172802932994947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156424877059686462570558869 7332416112172802932994947)
                  ·
                    refine ⟨10998624168259204399492421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7332416112172802932994947 10998624168259204399492421)
                    ·
                      refine ⟨2062242031548600824904829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10998624168259204399492421 2062242031548600824904829)
                      ·
                        rfl

theorem cell23_4016202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4016202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016202 prefixEnd_4016202 := by exact prefixLift 4016202
  have htrace : WordTrace (prefixWord ++ tailWord_4016202) baseStart_4016202 baseEnd_4016202 := by
    simpa [prefixWord, tailWord_4016202, baseEnd_4016202] using wordTrace_append hprefix tailTrace_4016202
  have hstable : (prefixWord ++ tailWord_4016202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016202).length < 2 ^ (prefixWord ++ tailWord_4016202).sum := by decide
  have hdescent : baseEnd_4016202 < baseStart_4016202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016239 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_4016239 : Nat := 118140960795 + 4016239 * 2 ^ 59
def prefixEnd_4016239 : Nat := 4983230072969 + 3 ^ 40 * 4016239 * 2
def baseEnd_4016239 : Nat := 2062261030332817180142159

theorem tailTrace_4016239 : CollatzResearch.WordTrace tailWord_4016239 prefixEnd_4016239 2062261030332817180142159 := by
  unfold tailWord_4016239
  simp only [CollatzResearch.WordTrace]
  refine ⟨146484270496859496857507771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97656180331239664571671847 146484270496859496857507771)
  ·
    refine ⟨219726405745289245286261657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146484270496859496857507771 219726405745289245286261657)
    ·
      refine ⟨164794804308966933964696243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219726405745289245286261657 164794804308966933964696243)
      ·
        refine ⟨247192206463450400947044365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164794804308966933964696243 247192206463450400947044365)
        ·
          refine ⟨92697077423793900355141637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247192206463450400947044365 92697077423793900355141637)
          ·
            refine ⟨17380702016961356316589057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92697077423793900355141637 17380702016961356316589057)
            ·
              refine ⟨13035526512721017237441793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17380702016961356316589057 13035526512721017237441793)
              ·
                refine ⟨9776644884540762928081345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13035526512721017237441793 9776644884540762928081345)
                ·
                  refine ⟨7332483663405572196061009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9776644884540762928081345 7332483663405572196061009)
                  ·
                    refine ⟨5499362747554179147045757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332483663405572196061009 5499362747554179147045757)
                    ·
                      refine ⟨2062261030332817180142159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499362747554179147045757 2062261030332817180142159)
                      ·
                        rfl

theorem cell23_4016239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_4016239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016239 prefixEnd_4016239 := by exact prefixLift 4016239
  have htrace : WordTrace (prefixWord ++ tailWord_4016239) baseStart_4016239 baseEnd_4016239 := by
    simpa [prefixWord, tailWord_4016239, baseEnd_4016239] using wordTrace_append hprefix tailTrace_4016239
  have hstable : (prefixWord ++ tailWord_4016239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016239).length < 2 ^ (prefixWord ++ tailWord_4016239).sum := by decide
  have hdescent : baseEnd_4016239 < baseStart_4016239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016272 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_4016272 : Nat := 118140960795 + 4016272 * 2 ^ 59
def prefixEnd_4016272 : Nat := 4983230072969 + 3 ^ 40 * 4016272 * 2
def baseEnd_4016272 : Nat := 687425991731471850343169

theorem tailTrace_4016272 : CollatzResearch.WordTrace tailWord_4016272 prefixEnd_4016272 687425991731471850343169 := by
  unfold tailWord_4016272
  simp only [CollatzResearch.WordTrace]
  refine ⟨73242737052869971746729535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97656982737159962328972713 73242737052869971746729535)
  ·
    refine ⟨109864105579304957620094303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73242737052869971746729535 109864105579304957620094303)
    ·
      refine ⟨164796158368957436430141455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109864105579304957620094303 164796158368957436430141455)
      ·
        refine ⟨247194237553436154645212183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164796158368957436430141455 247194237553436154645212183)
        ·
          refine ⟨370791356330154231967818275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247194237553436154645212183 370791356330154231967818275)
          ·
            refine ⟨556187034495231347951727413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370791356330154231967818275 556187034495231347951727413)
            ·
              refine ⟨52142534483927938870474445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556187034495231347951727413 52142534483927938870474445)
              ·
                refine ⟨19553450431472977076427917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52142534483927938870474445 19553450431472977076427917)
                ·
                  refine ⟨7332543911802366403660469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19553450431472977076427917 7332543911802366403660469)
                  ·
                    refine ⟨687425991731471850343169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7332543911802366403660469 687425991731471850343169)
                    ·
                      rfl

theorem cell23_4016272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_4016272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016272 prefixEnd_4016272 := by exact prefixLift 4016272
  have htrace : WordTrace (prefixWord ++ tailWord_4016272) baseStart_4016272 baseEnd_4016272 := by
    simpa [prefixWord, tailWord_4016272, baseEnd_4016272] using wordTrace_append hprefix tailTrace_4016272
  have hstable : (prefixWord ++ tailWord_4016272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016272).length < 2 ^ (prefixWord ++ tailWord_4016272).sum := by decide
  have hdescent : baseEnd_4016272 < baseStart_4016272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016346 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_4016346 : Nat := 118140960795 + 4016346 * 2 ^ 59
def prefixEnd_4016346 : Nat := 4983230072969 + 3 ^ 40 * 4016346 * 2
def baseEnd_4016346 : Nat := 2062315972762848261504167

theorem tailTrace_4016346 : CollatzResearch.WordTrace tailWord_4016346 prefixEnd_4016346 2062315972762848261504167 := by
  unfold tailWord_4016346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36622043276867963532913223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97658782071647902754435261 36622043276867963532913223)
  ·
    refine ⟨54933064915301945299369835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36622043276867963532913223 54933064915301945299369835)
    ·
      refine ⟨82399597372952917949054753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54933064915301945299369835 82399597372952917949054753)
      ·
        refine ⟨61799698029714688461791065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82399597372952917949054753 61799698029714688461791065)
        ·
          refine ⟨46349773522286016346343299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61799698029714688461791065 46349773522286016346343299)
          ·
            refine ⟨69524660283429024519514949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46349773522286016346343299 69524660283429024519514949)
            ·
              refine ⟨13035873803142942097409053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69524660283429024519514949 13035873803142942097409053)
              ·
                refine ⟨4888452676178603286528395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13035873803142942097409053 4888452676178603286528395)
                ·
                  refine ⟨7332679014267904929792593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888452676178603286528395 7332679014267904929792593)
                  ·
                    refine ⟨5499509260700928697344445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332679014267904929792593 5499509260700928697344445)
                    ·
                      refine ⟨2062315972762848261504167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499509260700928697344445 2062315972762848261504167)
                      ·
                        rfl

theorem cell23_4016346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_4016346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016346 prefixEnd_4016346 := by exact prefixLift 4016346
  have htrace : WordTrace (prefixWord ++ tailWord_4016346) baseStart_4016346 baseEnd_4016346 := by
    simpa [prefixWord, tailWord_4016346, baseEnd_4016346] using wordTrace_append hprefix tailTrace_4016346
  have hstable : (prefixWord ++ tailWord_4016346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016346).length < 2 ^ (prefixWord ++ tailWord_4016346).sum := by decide
  have hdescent : baseEnd_4016346 < baseStart_4016346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016349 : List Nat := [1, 4, 3, 2, 1, 1, 11]
def baseStart_4016349 : Nat := 118140960795 + 4016349 * 2 ^ 59
def prefixEnd_4016349 : Nat := 4983230072969 + 3 ^ 40 * 4016349 * 2
def baseEnd_4016349 : Nat := 25460710039565577157613

theorem tailTrace_4016349 : CollatzResearch.WordTrace tailWord_4016349 prefixEnd_4016349 25460710039565577157613 := by
  unfold tailWord_4016349
  simp only [CollatzResearch.WordTrace]
  refine ⟨146488282526460985644012101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97658855017640657096008067 146488282526460985644012101)
  ·
    refine ⟨27466552973711434808252269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146488282526460985644012101 27466552973711434808252269)
    ·
      refine ⟨10299957365141788053094601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27466552973711434808252269 10299957365141788053094601)
      ·
        refine ⟨7724968023856341039820951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10299957365141788053094601 7724968023856341039820951)
        ·
          refine ⟨11587452035784511559731427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724968023856341039820951 11587452035784511559731427)
          ·
            refine ⟨17381178053676767339597141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11587452035784511559731427 17381178053676767339597141)
            ·
              refine ⟨25460710039565577157613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17381178053676767339597141 25460710039565577157613)
              ·
                rfl

theorem cell23_4016349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 11].length) (baseStart_4016349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016349 prefixEnd_4016349 := by exact prefixLift 4016349
  have htrace : WordTrace (prefixWord ++ tailWord_4016349) baseStart_4016349 baseEnd_4016349 := by
    simpa [prefixWord, tailWord_4016349, baseEnd_4016349] using wordTrace_append hprefix tailTrace_4016349
  have hstable : (prefixWord ++ tailWord_4016349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016349).length < 2 ^ (prefixWord ++ tailWord_4016349).sum := by decide
  have hdescent : baseEnd_4016349 < baseStart_4016349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016354 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4016354 : Nat := 118140960795 + 4016354 * 2 ^ 59
def prefixEnd_4016354 : Nat := 4983230072969 + 3 ^ 40 * 4016354 * 2
def baseEnd_4016354 : Nat := 2062320080608084230204131

theorem tailTrace_4016354 : CollatzResearch.WordTrace tailWord_4016354 prefixEnd_4016354 2062320080608084230204131 := by
  unfold tailWord_4016354
  simp only [CollatzResearch.WordTrace]
  refine ⟨36622116222860717874486029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97658976594295247665296077 36622116222860717874486029)
  ·
    refine ⟨13733293583572769202932261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36622116222860717874486029 13733293583572769202932261)
    ·
      refine ⟨2574992546919894225549799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13733293583572769202932261 2574992546919894225549799)
      ·
        refine ⟨3862488820379841338324699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574992546919894225549799 3862488820379841338324699)
        ·
          refine ⟨5793733230569762007487049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862488820379841338324699 5793733230569762007487049)
          ·
            refine ⟨4345299922927321505615287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5793733230569762007487049 4345299922927321505615287)
            ·
              refine ⟨6517949884390982258422931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345299922927321505615287 6517949884390982258422931)
              ·
                refine ⟨9776924826586473387634397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517949884390982258422931 9776924826586473387634397)
                ·
                  refine ⟨3666346809969927520362899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9776924826586473387634397 3666346809969927520362899)
                  ·
                    refine ⟨5499520214954891280544349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666346809969927520362899 5499520214954891280544349)
                    ·
                      refine ⟨2062320080608084230204131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499520214954891280544349 2062320080608084230204131)
                      ·
                        rfl

theorem cell23_4016354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4016354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016354 prefixEnd_4016354 := by exact prefixLift 4016354
  have htrace : WordTrace (prefixWord ++ tailWord_4016354) baseStart_4016354 baseEnd_4016354 := by
    simpa [prefixWord, tailWord_4016354, baseEnd_4016354] using wordTrace_append hprefix tailTrace_4016354
  have hstable : (prefixWord ++ tailWord_4016354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016354).length < 2 ^ (prefixWord ++ tailWord_4016354).sum := by decide
  have hdescent : baseEnd_4016354 < baseStart_4016354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016360 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_4016360 : Nat := 118140960795 + 4016360 * 2 ^ 59
def prefixEnd_4016360 : Nat := 4983230072969 + 3 ^ 40 * 4016360 * 2
def baseEnd_4016360 : Nat := 2062323161492011206729103

theorem tailTrace_4016360 : CollatzResearch.WordTrace tailWord_4016360 prefixEnd_4016360 2062323161492011206729103 := by
  unfold tailWord_4016360
  simp only [CollatzResearch.WordTrace]
  refine ⟨73244341864710567261331267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97659122486280756348441689 73244341864710567261331267)
  ·
    refine ⟨109866512797065850891996901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73244341864710567261331267 109866512797065850891996901)
    ·
      refine ⟨20599971149449847042249419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109866512797065850891996901 20599971149449847042249419)
      ·
        refine ⟨30899956724174770563374129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20599971149449847042249419 30899956724174770563374129)
        ·
          refine ⟨23174967543131077922530597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30899956724174770563374129 23174967543131077922530597)
          ·
            refine ⟨4345306414337077110474487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23174967543131077922530597 4345306414337077110474487)
            ·
              refine ⟨6517959621505615665711731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345306414337077110474487 6517959621505615665711731)
              ·
                refine ⟨9776939432258423498567597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517959621505615665711731 9776939432258423498567597)
                ·
                  refine ⟨3666352287096908811962849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9776939432258423498567597 3666352287096908811962849)
                  ·
                    refine ⟨2749764215322681608972137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666352287096908811962849 2749764215322681608972137)
                    ·
                      refine ⟨2062323161492011206729103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2749764215322681608972137 2062323161492011206729103)
                      ·
                        rfl

theorem cell23_4016360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_4016360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016360 prefixEnd_4016360 := by exact prefixLift 4016360
  have htrace : WordTrace (prefixWord ++ tailWord_4016360) baseStart_4016360 baseEnd_4016360 := by
    simpa [prefixWord, tailWord_4016360, baseEnd_4016360] using wordTrace_append hprefix tailTrace_4016360
  have hstable : (prefixWord ++ tailWord_4016360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016360).length < 2 ^ (prefixWord ++ tailWord_4016360).sum := by decide
  have hdescent : baseEnd_4016360 < baseStart_4016360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016370 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_4016370 : Nat := 118140960795 + 4016370 * 2 ^ 59
def prefixEnd_4016370 : Nat := 4983230072969 + 3 ^ 40 * 4016370 * 2
def baseEnd_4016370 : Nat := 687442765432852055868019

theorem tailTrace_4016370 : CollatzResearch.WordTrace tailWord_4016370 prefixEnd_4016370 687442765432852055868019 := by
  unfold tailWord_4016370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36622262114846226557631641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97659365639589937487017709 36622262114846226557631641)
  ·
    refine ⟨27466696586134669918223731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36622262114846226557631641 27466696586134669918223731)
    ·
      refine ⟨41200044879202004877335597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27466696586134669918223731 41200044879202004877335597)
      ·
        refine ⟨15450016829700751829000849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41200044879202004877335597 15450016829700751829000849)
        ·
          refine ⟨11587512622275563871750637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15450016829700751829000849 11587512622275563871750637)
          ·
            refine ⟨4345317233353336451906489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11587512622275563871750637 4345317233353336451906489)
            ·
              refine ⟨3258987925015002338929867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345317233353336451906489 3258987925015002338929867)
              ·
                refine ⟨4888481887522503508394801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258987925015002338929867 4888481887522503508394801)
                ·
                  refine ⟨3666361415641877631296101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888481887522503508394801 3666361415641877631296101)
                  ·
                    refine ⟨687442765432852055868019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3666361415641877631296101 687442765432852055868019)
                    ·
                      rfl

theorem cell23_4016370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_4016370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016370 prefixEnd_4016370 := by exact prefixLift 4016370
  have htrace : WordTrace (prefixWord ++ tailWord_4016370) baseStart_4016370 baseEnd_4016370 := by
    simpa [prefixWord, tailWord_4016370, baseEnd_4016370] using wordTrace_append hprefix tailTrace_4016370
  have hstable : (prefixWord ++ tailWord_4016370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016370).length < 2 ^ (prefixWord ++ tailWord_4016370).sum := by decide
  have hdescent : baseEnd_4016370 < baseStart_4016370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016410 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_4016410 : Nat := 118140960795 + 4016410 * 2 ^ 59
def prefixEnd_4016410 : Nat := 4983230072969 + 3 ^ 40 * 4016410 * 2
def baseEnd_4016410 : Nat := 2062348835524736011103873

theorem tailTrace_4016410 : CollatzResearch.WordTrace tailWord_4016410 prefixEnd_4016410 2062348835524736011103873 := by
  unfold tailWord_4016410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36622626844809998265495671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97660338252826662041321789 36622626844809998265495671)
  ·
    refine ⟨54933940267214997398243507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36622626844809998265495671 54933940267214997398243507)
    ·
      refine ⟨82400910400822496097365261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54933940267214997398243507 82400910400822496097365261)
      ·
        refine ⟨30900341400308436036511973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82400910400822496097365261 30900341400308436036511973)
        ·
          refine ⟨5793814012557831756845995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30900341400308436036511973 5793814012557831756845995)
          ·
            refine ⟨8690721018836747635268993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793814012557831756845995 8690721018836747635268993)
            ·
              refine ⟨6518040764127560726451745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690721018836747635268993 6518040764127560726451745)
              ·
                refine ⟨4888530573095670544838809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518040764127560726451745 4888530573095670544838809)
                ·
                  refine ⟨3666397929821752908629107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888530573095670544838809 3666397929821752908629107)
                  ·
                    refine ⟨5499596894732629362943661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666397929821752908629107 5499596894732629362943661)
                    ·
                      refine ⟨2062348835524736011103873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499596894732629362943661 2062348835524736011103873)
                      ·
                        rfl

theorem cell23_4016410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_4016410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016410 prefixEnd_4016410 := by exact prefixLift 4016410
  have htrace : WordTrace (prefixWord ++ tailWord_4016410) baseStart_4016410 baseEnd_4016410 := by
    simpa [prefixWord, tailWord_4016410, baseEnd_4016410] using wordTrace_append hprefix tailTrace_4016410
  have hstable : (prefixWord ++ tailWord_4016410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016410).length < 2 ^ (prefixWord ++ tailWord_4016410).sum := by decide
  have hdescent : baseEnd_4016410 < baseStart_4016410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016419 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 3]
def baseStart_4016419 : Nat := 118140960795 + 4016419 * 2 ^ 59
def prefixEnd_4016419 : Nat := 4983230072969 + 3 ^ 40 * 4016419 * 2
def baseEnd_4016419 : Nat := 2062353456850626475891331

theorem tailTrace_4016419 : CollatzResearch.WordTrace tailWord_4016419 prefixEnd_4016419 2062353456850626475891331 := by
  unfold tailWord_4016419
  simp only [CollatzResearch.WordTrace]
  refine ⟨146490835636207387599060311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97660557090804925066040207 146490835636207387599060311)
  ·
    refine ⟨219736253454311081398590467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146490835636207387599060311 219736253454311081398590467)
    ·
      refine ⟨329604380181466622097885701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219736253454311081398590467 329604380181466622097885701)
      ·
        refine ⟨61800821284024991643353569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329604380181466622097885701 61800821284024991643353569)
        ·
          refine ⟨46350615963018743732515177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61800821284024991643353569 46350615963018743732515177)
          ·
            refine ⟨34762961972264057799386383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46350615963018743732515177 34762961972264057799386383)
            ·
              refine ⟨52144442958396086699079575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34762961972264057799386383 52144442958396086699079575)
              ·
                refine ⟨78216664437594130048619363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52144442958396086699079575 78216664437594130048619363)
                ·
                  refine ⟨117324996656391195072929045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78216664437594130048619363 117324996656391195072929045)
                  ·
                    refine ⟨5499609218268337269043549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117324996656391195072929045 5499609218268337269043549)
                    ·
                      refine ⟨2062353456850626475891331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499609218268337269043549 2062353456850626475891331)
                      ·
                        rfl

theorem cell23_4016419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_4016419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016419 prefixEnd_4016419 := by exact prefixLift 4016419
  have htrace : WordTrace (prefixWord ++ tailWord_4016419) baseStart_4016419 baseEnd_4016419 := by
    simpa [prefixWord, tailWord_4016419, baseEnd_4016419] using wordTrace_append hprefix tailTrace_4016419
  have hstable : (prefixWord ++ tailWord_4016419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016419).length < 2 ^ (prefixWord ++ tailWord_4016419).sum := by decide
  have hdescent : baseEnd_4016419 < baseStart_4016419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016456 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 5]
def baseStart_4016456 : Nat := 118140960795 + 4016456 * 2 ^ 59
def prefixEnd_4016456 : Nat := 4983230072969 + 3 ^ 40 * 4016456 * 2
def baseEnd_4016456 : Nat := 229152495070538092347629

theorem tailTrace_4016456 : CollatzResearch.WordTrace tailWord_4016456 prefixEnd_4016456 229152495070538092347629 := by
  unfold tailWord_4016456
  simp only [CollatzResearch.WordTrace]
  refine ⟨73246092568536671459078611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97661456758048895278771481 73246092568536671459078611)
  ·
    refine ⟨109869138852805007188617917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73246092568536671459078611 109869138852805007188617917)
    ·
      refine ⟨41200927069801877695731719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109869138852805007188617917 41200927069801877695731719)
      ·
        refine ⟨61801390604702816543597579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41200927069801877695731719 61801390604702816543597579)
        ·
          refine ⟨92702085907054224815396369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61801390604702816543597579 92702085907054224815396369)
          ·
            refine ⟨69526564430290668611547277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92702085907054224815396369 69526564430290668611547277)
            ·
              refine ⟨26072461661359000729330229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69526564430290668611547277 26072461661359000729330229)
              ·
                refine ⟨2444293280752406318374709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26072461661359000729330229 2444293280752406318374709)
                ·
                  refine ⟨229152495070538092347629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2444293280752406318374709 229152495070538092347629)
                  ·
                    rfl

theorem cell23_4016456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 5].length) (baseStart_4016456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016456 prefixEnd_4016456 := by exact prefixLift 4016456
  have htrace : WordTrace (prefixWord ++ tailWord_4016456) baseStart_4016456 baseEnd_4016456 := by
    simpa [prefixWord, tailWord_4016456, baseEnd_4016456] using wordTrace_append hprefix tailTrace_4016456
  have hstable : (prefixWord ++ tailWord_4016456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016456).length < 2 ^ (prefixWord ++ tailWord_4016456).sum := by decide
  have hdescent : baseEnd_4016456 < baseStart_4016456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016466 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_4016466 : Nat := 118140960795 + 4016466 * 2 ^ 59
def prefixEnd_4016466 : Nat := 4983230072969 + 3 ^ 40 * 4016466 * 2
def baseEnd_4016466 : Nat := 2062377590441387792003615

theorem tailTrace_4016466 : CollatzResearch.WordTrace tailWord_4016466 prefixEnd_4016466 2062377590441387792003615 := by
  unfold tailWord_4016466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36623137466759278656505313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97661699911358076417347501 36623137466759278656505313)
  ·
    refine ⟨27467353100069458992378985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36623137466759278656505313 27467353100069458992378985)
    ·
      refine ⟨20600514825052094244284239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27467353100069458992378985 20600514825052094244284239)
      ·
        refine ⟨30900772237578141366426359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20600514825052094244284239 30900772237578141366426359)
        ·
          refine ⟨46351158356367212049639539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30900772237578141366426359 46351158356367212049639539)
          ·
            refine ⟨69526737534550818074459309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46351158356367212049639539 69526737534550818074459309)
            ·
              refine ⟨26072526575456556777922241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69526737534550818074459309 26072526575456556777922241)
              ·
                refine ⟨19554394931592417583441681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26072526575456556777922241 19554394931592417583441681)
                ·
                  refine ⟨14665796198694313187581261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19554394931592417583441681 14665796198694313187581261)
                  ·
                    refine ⟨5499673574510367445342973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14665796198694313187581261 5499673574510367445342973)
                    ·
                      refine ⟨2062377590441387792003615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499673574510367445342973 2062377590441387792003615)
                      ·
                        rfl

theorem cell23_4016466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_4016466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016466 prefixEnd_4016466 := by exact prefixLift 4016466
  have htrace : WordTrace (prefixWord ++ tailWord_4016466) baseStart_4016466 baseEnd_4016466 := by
    simpa [prefixWord, tailWord_4016466, baseEnd_4016466] using wordTrace_append hprefix tailTrace_4016466
  have hstable : (prefixWord ++ tailWord_4016466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016466).length < 2 ^ (prefixWord ++ tailWord_4016466).sum := by decide
  have hdescent : baseEnd_4016466 < baseStart_4016466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016478 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4016478 : Nat := 118140960795 + 4016478 * 2 ^ 59
def prefixEnd_4016478 : Nat := 4983230072969 + 3 ^ 40 * 4016478 * 2
def baseEnd_4016478 : Nat := 2062383752209241745053561

theorem tailTrace_4016478 : CollatzResearch.WordTrace tailWord_4016478 prefixEnd_4016478 2062383752209241745053561 := by
  unfold tailWord_4016478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18311623442874205084432261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97661991695329093783638725 18311623442874205084432261)
  ·
    refine ⟨3433429395538913453331049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18311623442874205084432261 3433429395538913453331049)
    ·
      refine ⟨2575072046654185089998287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3433429395538913453331049 2575072046654185089998287)
      ·
        refine ⟨3862608069981277634997431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575072046654185089998287 3862608069981277634997431)
        ·
          refine ⟨5793912104971916452496147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862608069981277634997431 5793912104971916452496147)
          ·
            refine ⟨8690868157457874678744221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793912104971916452496147 8690868157457874678744221)
            ·
              refine ⟨3259075559046703004529083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8690868157457874678744221 3259075559046703004529083)
              ·
                refine ⟨4888613338570054506793625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259075559046703004529083 4888613338570054506793625)
                ·
                  refine ⟨3666460003927540880095219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888613338570054506793625 3666460003927540880095219)
                  ·
                    refine ⟨5499690005891311320142829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666460003927540880095219 5499690005891311320142829)
                    ·
                      refine ⟨2062383752209241745053561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5499690005891311320142829 2062383752209241745053561)
                      ·
                        rfl

theorem cell23_4016478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4016478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016478 prefixEnd_4016478 := by exact prefixLift 4016478
  have htrace : WordTrace (prefixWord ++ tailWord_4016478) baseStart_4016478 baseEnd_4016478 := by
    simpa [prefixWord, tailWord_4016478, baseEnd_4016478] using wordTrace_append hprefix tailTrace_4016478
  have hstable : (prefixWord ++ tailWord_4016478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016478).length < 2 ^ (prefixWord ++ tailWord_4016478).sum := by decide
  have hdescent : baseEnd_4016478 < baseStart_4016478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016479 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_4016479 : Nat := 118140960795 + 4016479 * 2 ^ 59
def prefixEnd_4016479 : Nat := 4983230072969 + 3 ^ 40 * 4016479 * 2
def baseEnd_4016479 : Nat := 2062384265689896241141055

theorem tailTrace_4016479 : CollatzResearch.WordTrace tailWord_4016479 prefixEnd_4016479 2062384265689896241141055 := by
  unfold tailWord_4016479
  simp only [CollatzResearch.WordTrace]
  refine ⟨146493024015990017846244491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97662016010660011897496327 146493024015990017846244491)
  ·
    refine ⟨219739536023985026769366737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146493024015990017846244491 219739536023985026769366737)
    ·
      refine ⟨164804652017988770077025053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219739536023985026769366737 164804652017988770077025053)
      ·
        refine ⟨61801744506745788778884395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164804652017988770077025053 61801744506745788778884395)
        ·
          refine ⟨92702616760118683168326593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61801744506745788778884395 92702616760118683168326593)
          ·
            refine ⟨69526962570089012376244945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92702616760118683168326593 69526962570089012376244945)
            ·
              refine ⟨52145221927566759282183709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69526962570089012376244945 52145221927566759282183709)
              ·
                refine ⟨19554458222837534730818891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52145221927566759282183709 19554458222837534730818891)
                ·
                  refine ⟨29331687334256302096228337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19554458222837534730818891 29331687334256302096228337)
                  ·
                    refine ⟨21998765500692226572171253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29331687334256302096228337 21998765500692226572171253)
                    ·
                      refine ⟨2062384265689896241141055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21998765500692226572171253 2062384265689896241141055)
                      ·
                        rfl

theorem cell23_4016479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_4016479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016479 prefixEnd_4016479 := by exact prefixLift 4016479
  have htrace : WordTrace (prefixWord ++ tailWord_4016479) baseStart_4016479 baseEnd_4016479 := by
    simpa [prefixWord, tailWord_4016479, baseEnd_4016479] using wordTrace_append hprefix tailTrace_4016479
  have hstable : (prefixWord ++ tailWord_4016479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016479).length < 2 ^ (prefixWord ++ tailWord_4016479).sum := by decide
  have hdescent : baseEnd_4016479 < baseStart_4016479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016489 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_4016489 : Nat := 118140960795 + 4016489 * 2 ^ 59
def prefixEnd_4016489 : Nat := 4983230072969 + 3 ^ 40 * 4016489 * 2
def baseEnd_4016489 : Nat := 2062389400496441202016009

theorem tailTrace_4016489 : CollatzResearch.WordTrace tailWord_4016489 prefixEnd_4016489 2062389400496441202016009 := by
  unfold tailWord_4016489
  simp only [CollatzResearch.WordTrace]
  refine ⟨146493388745953789554108521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97662259163969193036072347 146493388745953789554108521)
  ·
    refine ⟨109870041559465342165581391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146493388745953789554108521 109870041559465342165581391)
    ·
      refine ⟨164805062339198013248372087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109870041559465342165581391 164805062339198013248372087)
      ·
        refine ⟨247207593508797019872558131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164805062339198013248372087 247207593508797019872558131)
        ·
          refine ⟨370811390263195529808837197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247207593508797019872558131 370811390263195529808837197)
          ·
            refine ⟨139054271348698323678313949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370811390263195529808837197 139054271348698323678313949)
            ·
              refine ⟨52145351755761871379367731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139054271348698323678313949 52145351755761871379367731)
              ·
                refine ⟨78218027633642807069051597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52145351755761871379367731 78218027633642807069051597)
                ·
                  refine ⟨29331760362616052650894349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78218027633642807069051597 29331760362616052650894349)
                  ·
                    refine ⟨10999410135981019744085381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29331760362616052650894349 10999410135981019744085381)
                    ·
                      refine ⟨2062389400496441202016009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10999410135981019744085381 2062389400496441202016009)
                      ·
                        rfl

theorem cell23_4016489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_4016489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016489 prefixEnd_4016489 := by exact prefixLift 4016489
  have htrace : WordTrace (prefixWord ++ tailWord_4016489) baseStart_4016489 baseEnd_4016489 := by
    simpa [prefixWord, tailWord_4016489, baseEnd_4016489] using wordTrace_append hprefix tailTrace_4016489
  have hstable : (prefixWord ++ tailWord_4016489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016489).length < 2 ^ (prefixWord ++ tailWord_4016489).sum := by decide
  have hdescent : baseEnd_4016489 < baseStart_4016489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016580 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 6]
def baseStart_4016580 : Nat := 118140960795 + 4016580 * 2 ^ 59
def prefixEnd_4016580 : Nat := 4983230072969 + 3 ^ 40 * 4016580 * 2
def baseEnd_4016580 : Nat := 229159569692888927330899

theorem tailTrace_4016580 : CollatzResearch.WordTrace tailWord_4016580 prefixEnd_4016580 229159569692888927330899 := by
  unfold tailWord_4016580
  simp only [CollatzResearch.WordTrace]
  refine ⟨73248353894312056047835597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97664471859082741397114129 73248353894312056047835597)
  ·
    refine ⟨27468132710367021017938349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73248353894312056047835597 27468132710367021017938349)
    ·
      refine ⟨10300549766387632881726881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27468132710367021017938349 10300549766387632881726881)
      ·
        refine ⟨7725412324790724661295161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10300549766387632881726881 7725412324790724661295161)
        ·
          refine ⟨5794059243593043495971371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7725412324790724661295161 5794059243593043495971371)
          ·
            refine ⟨8691088865389565243957057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794059243593043495971371 8691088865389565243957057)
            ·
              refine ⟨6518316649042173932967793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691088865389565243957057 6518316649042173932967793)
              ·
                refine ⟨4888737486781630449725845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518316649042173932967793 4888737486781630449725845)
                ·
                  refine ⟨229159569692888927330899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4888737486781630449725845 229159569692888927330899)
                  ·
                    rfl

theorem cell23_4016580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_4016580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016580 prefixEnd_4016580 := by exact prefixLift 4016580
  have htrace : WordTrace (prefixWord ++ tailWord_4016580) baseStart_4016580 baseEnd_4016580 := by
    simpa [prefixWord, tailWord_4016580, baseEnd_4016580] using wordTrace_append hprefix tailTrace_4016580
  have hstable : (prefixWord ++ tailWord_4016580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016580).length < 2 ^ (prefixWord ++ tailWord_4016580).sum := by decide
  have hdescent : baseEnd_4016580 < baseStart_4016580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016630 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4016630 : Nat := 118140960795 + 4016630 * 2 ^ 59
def prefixEnd_4016630 : Nat := 4983230072969 + 3 ^ 40 * 4016630 * 2
def baseEnd_4016630 : Nat := 2062461801268725150352861

theorem tailTrace_4016630 : CollatzResearch.WordTrace tailWord_4016630 prefixEnd_4016630 2062461801268725150352861 := by
  unfold tailWord_4016630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156158214902685664686959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97665687625628647089994229 9156158214902685664686959)
  ·
    refine ⟨13734237322354028497030439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156158214902685664686959 13734237322354028497030439)
    ·
      refine ⟨20601355983531042745545659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734237322354028497030439 20601355983531042745545659)
      ·
        refine ⟨30902033975296564118318489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20601355983531042745545659 30902033975296564118318489)
        ·
          refine ⟨23176525481472423088738867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30902033975296564118318489 23176525481472423088738867)
          ·
            refine ⟨34764788222208634633108301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23176525481472423088738867 34764788222208634633108301)
            ·
              refine ⟨13036795583328237987415613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34764788222208634633108301 13036795583328237987415613)
              ·
                refine ⟨4888798343748089245280855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13036795583328237987415613 4888798343748089245280855)
                ·
                  refine ⟨7333197515622133867921283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888798343748089245280855 7333197515622133867921283)
                  ·
                    refine ⟨10999796273433200801881925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7333197515622133867921283 10999796273433200801881925)
                    ·
                      refine ⟨2062461801268725150352861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10999796273433200801881925 2062461801268725150352861)
                      ·
                        rfl

theorem cell23_4016630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4016630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016630 prefixEnd_4016630 := by exact prefixLift 4016630
  have htrace : WordTrace (prefixWord ++ tailWord_4016630) baseStart_4016630 baseEnd_4016630 := by
    simpa [prefixWord, tailWord_4016630, baseEnd_4016630] using wordTrace_append hprefix tailTrace_4016630
  have hstable : (prefixWord ++ tailWord_4016630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016630).length < 2 ^ (prefixWord ++ tailWord_4016630).sum := by decide
  have hdescent : baseEnd_4016630 < baseStart_4016630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016660 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4016660 : Nat := 118140960795 + 4016660 * 2 ^ 59
def prefixEnd_4016660 : Nat := 4983230072969 + 3 ^ 40 * 4016660 * 2
def baseEnd_4016660 : Nat := 2062477205688360032977723

theorem tailTrace_4016660 : CollatzResearch.WordTrace tailWord_4016660 prefixEnd_4016660 2062477205688360032977723 := by
  unfold tailWord_4016660
  simp only [CollatzResearch.WordTrace]
  refine ⟨73249812814167142879291717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97666417085556190505722289 73249812814167142879291717)
  ·
    refine ⟨13734339902656339289867197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73249812814167142879291717 13734339902656339289867197)
    ·
      refine ⟨5150377463496127233700199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13734339902656339289867197 5150377463496127233700199)
      ·
        refine ⟨7725566195244190850550299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150377463496127233700199 7725566195244190850550299)
        ·
          refine ⟨11588349292866286275825449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7725566195244190850550299 11588349292866286275825449)
          ·
            refine ⟨8691261969649714706869087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11588349292866286275825449 8691261969649714706869087)
            ·
              refine ⟨13036892954474572060303631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691261969649714706869087 13036892954474572060303631)
              ·
                refine ⟨19555339431711858090455447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13036892954474572060303631 19555339431711858090455447)
                ·
                  refine ⟨29333009147567787135683171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19555339431711858090455447 29333009147567787135683171)
                  ·
                    refine ⟨43999513721351680703524757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29333009147567787135683171 43999513721351680703524757)
                    ·
                      refine ⟨2062477205688360032977723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43999513721351680703524757 2062477205688360032977723)
                      ·
                        rfl

theorem cell23_4016660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4016660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016660 prefixEnd_4016660 := by exact prefixLift 4016660
  have htrace : WordTrace (prefixWord ++ tailWord_4016660) baseStart_4016660 baseEnd_4016660 := by
    simpa [prefixWord, tailWord_4016660, baseEnd_4016660] using wordTrace_append hprefix tailTrace_4016660
  have hstable : (prefixWord ++ tailWord_4016660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016660).length < 2 ^ (prefixWord ++ tailWord_4016660).sum := by decide
  have hdescent : baseEnd_4016660 < baseStart_4016660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016666 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_4016666 : Nat := 118140960795 + 4016666 * 2 ^ 59
def prefixEnd_4016666 : Nat := 4983230072969 + 3 ^ 40 * 4016666 * 2
def baseEnd_4016666 : Nat := 687493428857429003167565

theorem tailTrace_4016666 : CollatzResearch.WordTrace tailWord_4016666 prefixEnd_4016666 687493428857429003167565 := by
  unfold tailWord_4016666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36624961116578137195825463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97666562977541699188867901 36624961116578137195825463)
  ·
    refine ⟨54937441674867205793738195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36624961116578137195825463 54937441674867205793738195)
    ·
      refine ⟨82406162512300808690607293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54937441674867205793738195 82406162512300808690607293)
      ·
        refine ⟨30902310942112803258977735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82406162512300808690607293 30902310942112803258977735)
        ·
          refine ⟨46353466413169204888466603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30902310942112803258977735 46353466413169204888466603)
          ·
            refine ⟨69530199619753807332699905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46353466413169204888466603 69530199619753807332699905)
            ·
              refine ⟨52147649714815355499524929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69530199619753807332699905 52147649714815355499524929)
              ·
                refine ⟨39110737286111516624643697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52147649714815355499524929 39110737286111516624643697)
                ·
                  refine ⟨29333052964583637468482773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39110737286111516624643697 29333052964583637468482773)
                  ·
                    refine ⟨687493428857429003167565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29333052964583637468482773 687493428857429003167565)
                    ·
                      rfl

theorem cell23_4016666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_4016666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016666 prefixEnd_4016666 := by exact prefixLift 4016666
  have htrace : WordTrace (prefixWord ++ tailWord_4016666) baseStart_4016666 baseEnd_4016666 := by
    simpa [prefixWord, tailWord_4016666, baseEnd_4016666] using wordTrace_append hprefix tailTrace_4016666
  have hstable : (prefixWord ++ tailWord_4016666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016666).length < 2 ^ (prefixWord ++ tailWord_4016666).sum := by decide
  have hdescent : baseEnd_4016666 < baseStart_4016666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016708 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4016708 : Nat := 118140960795 + 4016708 * 2 ^ 59
def prefixEnd_4016708 : Nat := 4983230072969 + 3 ^ 40 * 4016708 * 2
def baseEnd_4016708 : Nat := 687500617586591948392501

theorem tailTrace_4016708 : CollatzResearch.WordTrace tailWord_4016708 prefixEnd_4016708 687500617586591948392501 := by
  unfold tailWord_4016708
  simp only [CollatzResearch.WordTrace]
  refine ⟨73250688166080194978165389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97667584221440259970887185 73250688166080194978165389)
  ·
    refine ⟨27469008062280073116812021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73250688166080194978165389 27469008062280073116812021)
    ·
      refine ⟨2575219505838756854701127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27469008062280073116812021 2575219505838756854701127)
      ·
        refine ⟨3862829258758135282051691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575219505838756854701127 3862829258758135282051691)
        ·
          refine ⟨5794243888137202923077537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862829258758135282051691 5794243888137202923077537)
          ·
            refine ⟨4345682916102902192308153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5794243888137202923077537 4345682916102902192308153)
            ·
              refine ⟨3259262187077176644231115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345682916102902192308153 3259262187077176644231115)
              ·
                refine ⟨4888893280615764966346673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259262187077176644231115 4888893280615764966346673)
                ·
                  refine ⟨3666669960461823724760005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888893280615764966346673 3666669960461823724760005)
                  ·
                    refine ⟨687500617586591948392501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3666669960461823724760005 687500617586591948392501)
                    ·
                      rfl

theorem cell23_4016708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4016708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016708 prefixEnd_4016708 := by exact prefixLift 4016708
  have htrace : WordTrace (prefixWord ++ tailWord_4016708) baseStart_4016708 baseEnd_4016708 := by
    simpa [prefixWord, tailWord_4016708, baseEnd_4016708] using wordTrace_append hprefix tailTrace_4016708
  have hstable : (prefixWord ++ tailWord_4016708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016708).length < 2 ^ (prefixWord ++ tailWord_4016708).sum := by decide
  have hdescent : baseEnd_4016708 < baseStart_4016708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016714 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_4016714 : Nat := 118140960795 + 4016714 * 2 ^ 59
def prefixEnd_4016714 : Nat := 4983230072969 + 3 ^ 40 * 4016714 * 2
def baseEnd_4016714 : Nat := 2062504933643702821702475

theorem tailTrace_4016714 : CollatzResearch.WordTrace tailWord_4016714 prefixEnd_4016714 2062504933643702821702475 := by
  unfold tailWord_4016714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36625398792534663245262299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97667730113425768654032797 36625398792534663245262299)
  ·
    refine ⟨54938098188801994867893449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36625398792534663245262299 54938098188801994867893449)
    ·
      refine ⟨41203573641601496150920087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54938098188801994867893449 41203573641601496150920087)
      ·
        refine ⟨61805360462402244226380131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41203573641601496150920087 61805360462402244226380131)
        ·
          refine ⟨92708040693603366339570197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61805360462402244226380131 92708040693603366339570197)
          ·
            refine ⟨4345689407512657797167353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92708040693603366339570197 4345689407512657797167353)
            ·
              refine ⟨3259267055634493347875515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345689407512657797167353 3259267055634493347875515)
              ·
                refine ⟨4888900583451740021813273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259267055634493347875515 4888900583451740021813273)
                ·
                  refine ⟨3666675437588805016359955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888900583451740021813273 3666675437588805016359955)
                  ·
                    refine ⟨5500013156383207524539933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666675437588805016359955 5500013156383207524539933)
                    ·
                      refine ⟨2062504933643702821702475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5500013156383207524539933 2062504933643702821702475)
                      ·
                        rfl

theorem cell23_4016714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_4016714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016714 prefixEnd_4016714 := by exact prefixLift 4016714
  have htrace : WordTrace (prefixWord ++ tailWord_4016714) baseStart_4016714 baseEnd_4016714 := by
    simpa [prefixWord, tailWord_4016714, baseEnd_4016714] using wordTrace_append hprefix tailTrace_4016714
  have hstable : (prefixWord ++ tailWord_4016714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016714).length < 2 ^ (prefixWord ++ tailWord_4016714).sum := by decide
  have hdescent : baseEnd_4016714 < baseStart_4016714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016720 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 6, 2, 2]
def baseStart_4016720 : Nat := 118140960795 + 4016720 * 2 ^ 59
def prefixEnd_4016720 : Nat := 4983230072969 + 3 ^ 40 * 4016720 * 2
def baseEnd_4016720 : Nat := 2062508014527629798227447

theorem tailTrace_4016720 : CollatzResearch.WordTrace tailWord_4016720 prefixEnd_4016720 2062508014527629798227447 := by
  unfold tailWord_4016720
  simp only [CollatzResearch.WordTrace]
  refine ⟨73250907004058458002883807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97667876005411277337178409 73250907004058458002883807)
  ·
    refine ⟨109876360506087687004325711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73250907004058458002883807 109876360506087687004325711)
    ·
      refine ⟨164814540759131530506488567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109876360506087687004325711 164814540759131530506488567)
      ·
        refine ⟨247221811138697295759732851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164814540759131530506488567 247221811138697295759732851)
        ·
          refine ⟨370832716708045943639599277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247221811138697295759732851 370832716708045943639599277)
          ·
            refine ⟨139062268765517228864849729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370832716708045943639599277 139062268765517228864849729)
            ·
              refine ⟨104296701574137921648637297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139062268765517228864849729 104296701574137921648637297)
              ·
                refine ⟨78222526180603441236477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104296701574137921648637297 78222526180603441236477973)
                ·
                  refine ⟨3666680914715786307959905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78222526180603441236477973 3666680914715786307959905)
                  ·
                    refine ⟨2750010686036839730969929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666680914715786307959905 2750010686036839730969929)
                    ·
                      refine ⟨2062508014527629798227447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750010686036839730969929 2062508014527629798227447)
                      ·
                        rfl

theorem cell23_4016720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 2, 2].length) (baseStart_4016720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016720 prefixEnd_4016720 := by exact prefixLift 4016720
  have htrace : WordTrace (prefixWord ++ tailWord_4016720) baseStart_4016720 baseEnd_4016720 := by
    simpa [prefixWord, tailWord_4016720, baseEnd_4016720] using wordTrace_append hprefix tailTrace_4016720
  have hstable : (prefixWord ++ tailWord_4016720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016720).length < 2 ^ (prefixWord ++ tailWord_4016720).sum := by decide
  have hdescent : baseEnd_4016720 < baseStart_4016720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016724 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_4016724 : Nat := 118140960795 + 4016724 * 2 ^ 59
def prefixEnd_4016724 : Nat := 4983230072969 + 3 ^ 40 * 4016724 * 2
def baseEnd_4016724 : Nat := 2062510068450247782577429

theorem tailTrace_4016724 : CollatzResearch.WordTrace tailWord_4016724 prefixEnd_4016724 2062510068450247782577429 := by
  unfold tailWord_4016724
  simp only [CollatzResearch.WordTrace]
  refine ⟨73250979950051212344456613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97667973266734949792608817 73250979950051212344456613)
  ·
    refine ⟨13734558740634602314585615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73250979950051212344456613 13734558740634602314585615)
    ·
      refine ⟨20601838110951903471878423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734558740634602314585615 20601838110951903471878423)
      ·
        refine ⟨30902757166427855207817635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20601838110951903471878423 30902757166427855207817635)
        ·
          refine ⟨46354135749641782811726453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30902757166427855207817635 46354135749641782811726453)
          ·
            refine ⟨4345700226528917138599355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46354135749641782811726453 4345700226528917138599355)
            ·
              refine ⟨6518550339793375707899033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345700226528917138599355 6518550339793375707899033)
              ·
                refine ⟨4888912754845031780924275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518550339793375707899033 4888912754845031780924275)
                ·
                  refine ⟨7333369132267547671386413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888912754845031780924275 7333369132267547671386413)
                  ·
                    refine ⟨2750013424600330376769905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7333369132267547671386413 2750013424600330376769905)
                    ·
                      refine ⟨2062510068450247782577429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750013424600330376769905 2062510068450247782577429)
                      ·
                        rfl

theorem cell23_4016724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_4016724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016724 prefixEnd_4016724 := by exact prefixLift 4016724
  have htrace : WordTrace (prefixWord ++ tailWord_4016724) baseStart_4016724 baseEnd_4016724 := by
    simpa [prefixWord, tailWord_4016724, baseEnd_4016724] using wordTrace_append hprefix tailTrace_4016724
  have hstable : (prefixWord ++ tailWord_4016724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016724).length < 2 ^ (prefixWord ++ tailWord_4016724).sum := by decide
  have hdescent : baseEnd_4016724 < baseStart_4016724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016793 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_4016793 : Nat := 118140960795 + 4016793 * 2 ^ 59
def prefixEnd_4016793 : Nat := 4983230072969 + 3 ^ 40 * 4016793 * 2
def baseEnd_4016793 : Nat := 2062545498615408012614611

theorem tailTrace_4016793 : CollatzResearch.WordTrace tailWord_4016793 prefixEnd_4016793 2062545498615408012614611 := by
  unfold tailWord_4016793
  simp only [CollatzResearch.WordTrace]
  refine ⟨146504476536852449473175033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97669651024568299648783355 146504476536852449473175033)
  ·
    refine ⟨109878357402639337104881275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146504476536852449473175033 109878357402639337104881275)
    ·
      refine ⟨164817536103959005657321913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109878357402639337104881275 164817536103959005657321913)
      ·
        refine ⟨123613152077969254242991435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164817536103959005657321913 123613152077969254242991435)
        ·
          refine ⟨185419728116953881364487153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123613152077969254242991435 185419728116953881364487153)
          ·
            refine ⟨139064796087715411023365365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185419728116953881364487153 139064796087715411023365365)
            ·
              refine ⟨13037324633223319783440503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139064796087715411023365365 13037324633223319783440503)
              ·
                refine ⟨19555986949834979675160755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13037324633223319783440503 19555986949834979675160755)
                ·
                  refine ⟨29333980424752469512741133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19555986949834979675160755 29333980424752469512741133)
                  ·
                    refine ⟨11000242659282176067277925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29333980424752469512741133 11000242659282176067277925)
                    ·
                      refine ⟨2062545498615408012614611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11000242659282176067277925 2062545498615408012614611)
                      ·
                        rfl

theorem cell23_4016793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_4016793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016793 prefixEnd_4016793 := by exact prefixLift 4016793
  have htrace : WordTrace (prefixWord ++ tailWord_4016793) baseStart_4016793 baseEnd_4016793 := by
    simpa [prefixWord, tailWord_4016793, baseEnd_4016793] using wordTrace_append hprefix tailTrace_4016793
  have hstable : (prefixWord ++ tailWord_4016793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016793).length < 2 ^ (prefixWord ++ tailWord_4016793).sum := by decide
  have hdescent : baseEnd_4016793 < baseStart_4016793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016794 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_4016794 : Nat := 118140960795 + 4016794 * 2 ^ 59
def prefixEnd_4016794 : Nat := 4983230072969 + 3 ^ 40 * 4016794 * 2
def baseEnd_4016794 : Nat := 229171779121784723189123

theorem tailTrace_4016794 : CollatzResearch.WordTrace tailWord_4016794 prefixEnd_4016794 229171779121784723189123 := by
  unfold tailWord_4016794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36626128252462206660990359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97669675339899217762640957 36626128252462206660990359)
  ·
    refine ⟨54939192378693309991485539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36626128252462206660990359 54939192378693309991485539)
    ·
      refine ⟨82408788568039964987228309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54939192378693309991485539 82408788568039964987228309)
      ·
        refine ⟨3862911964126873358776327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82408788568039964987228309 3862911964126873358776327)
        ·
          refine ⟨5794367946190310038164491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862911964126873358776327 5794367946190310038164491)
          ·
            refine ⟨8691551919285465057246737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794367946190310038164491 8691551919285465057246737)
            ·
              refine ⟨6518663939464098792935053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691551919285465057246737 6518663939464098792935053)
              ·
                refine ⟨2444498977299037047350645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6518663939464098792935053 2444498977299037047350645)
                ·
                  refine ⟨229171779121784723189123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2444498977299037047350645 229171779121784723189123)
                  ·
                    rfl

theorem cell23_4016794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_4016794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016794 prefixEnd_4016794 := by exact prefixLift 4016794
  have htrace : WordTrace (prefixWord ++ tailWord_4016794) baseStart_4016794 baseEnd_4016794 := by
    simpa [prefixWord, tailWord_4016794, baseEnd_4016794] using wordTrace_append hprefix tailTrace_4016794
  have hstable : (prefixWord ++ tailWord_4016794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016794).length < 2 ^ (prefixWord ++ tailWord_4016794).sum := by decide
  have hdescent : baseEnd_4016794 < baseStart_4016794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016830 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_4016830 : Nat := 118140960795 + 4016830 * 2 ^ 59
def prefixEnd_4016830 : Nat := 4983230072969 + 3 ^ 40 * 4016830 * 2
def baseEnd_4016830 : Nat := 2062564497399624367851941

theorem tailTrace_4016830 : CollatzResearch.WordTrace tailWord_4016830 prefixEnd_4016830 2062564497399624367851941 := by
  unfold tailWord_4016830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313228254714800599033993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97670550691812269861514629 18313228254714800599033993)
  ·
    refine ⟨13734921191036100449275495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18313228254714800599033993 13734921191036100449275495)
    ·
      refine ⟨20602381786554150673913243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734921191036100449275495 20602381786554150673913243)
      ·
        refine ⟨30903572679831226010869865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20602381786554150673913243 30903572679831226010869865)
        ·
          refine ⟨23177679509873419508152399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30903572679831226010869865 23177679509873419508152399)
          ·
            refine ⟨34766519264810129262228599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23177679509873419508152399 34766519264810129262228599)
            ·
              refine ⟨52149778897215193893342899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34766519264810129262228599 52149778897215193893342899)
              ·
                refine ⟨78224668345822790840014349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52149778897215193893342899 78224668345822790840014349)
                ·
                  refine ⟨29334250629683546565005381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78224668345822790840014349 29334250629683546565005381)
                  ·
                    refine ⟨5500171993065664980938509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29334250629683546565005381 5500171993065664980938509)
                    ·
                      refine ⟨2062564497399624367851941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5500171993065664980938509 2062564497399624367851941)
                      ·
                        rfl

theorem cell23_4016830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_4016830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016830 prefixEnd_4016830 := by exact prefixLift 4016830
  have htrace : WordTrace (prefixWord ++ tailWord_4016830) baseStart_4016830 baseEnd_4016830 := by
    simpa [prefixWord, tailWord_4016830, baseEnd_4016830] using wordTrace_append hprefix tailTrace_4016830
  have hstable : (prefixWord ++ tailWord_4016830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016830).length < 2 ^ (prefixWord ++ tailWord_4016830).sum := by decide
  have hdescent : baseEnd_4016830 < baseStart_4016830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016883 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4]
def baseStart_4016883 : Nat := 118140960795 + 4016883 * 2 ^ 59
def prefixEnd_4016883 : Nat := 4983230072969 + 3 ^ 40 * 4016883 * 2
def baseEnd_4016883 : Nat := 2062591711874312660489197

theorem tailTrace_4016883 : CollatzResearch.WordTrace tailWord_4016883 prefixEnd_4016883 2062591711874312660489197 := by
  unfold tailWord_4016883
  simp only [CollatzResearch.WordTrace]
  refine ⟨146507759106526394843951303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97671839404350929895967535 146507759106526394843951303)
  ·
    refine ⟨219761638659789592265926955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146507759106526394843951303 219761638659789592265926955)
    ·
      refine ⟨329642457989684388398890433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219761638659789592265926955 329642457989684388398890433)
      ·
        refine ⟨247231843492263291299167825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329642457989684388398890433 247231843492263291299167825)
        ·
          refine ⟨185423882619197468474375869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247231843492263291299167825 185423882619197468474375869)
          ·
            refine ⟨69533955982199050677890951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185423882619197468474375869 69533955982199050677890951)
            ·
              refine ⟨104300933973298576016836427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69533955982199050677890951 104300933973298576016836427)
              ·
                refine ⟨156451400959947864025254641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104300933973298576016836427 156451400959947864025254641)
                ·
                  refine ⟨117338550719960898018940981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156451400959947864025254641 117338550719960898018940981)
                  ·
                    refine ⟨11000489129996334189275717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117338550719960898018940981 11000489129996334189275717)
                    ·
                      refine ⟨2062591711874312660489197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11000489129996334189275717 2062591711874312660489197)
                      ·
                        rfl

theorem cell23_4016883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_4016883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016883 prefixEnd_4016883 := by exact prefixLift 4016883
  have htrace : WordTrace (prefixWord ++ tailWord_4016883) baseStart_4016883 baseEnd_4016883 := by
    simpa [prefixWord, tailWord_4016883, baseEnd_4016883] using wordTrace_append hprefix tailTrace_4016883
  have hstable : (prefixWord ++ tailWord_4016883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016883).length < 2 ^ (prefixWord ++ tailWord_4016883).sum := by decide
  have hdescent : baseEnd_4016883 < baseStart_4016883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016904 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_4016904 : Nat := 118140960795 + 4016904 * 2 ^ 59
def prefixEnd_4016904 : Nat := 4983230072969 + 3 ^ 40 * 4016904 * 2
def baseEnd_4016904 : Nat := 2062602494968057078326601

theorem tailTrace_4016904 : CollatzResearch.WordTrace tailWord_4016904 prefixEnd_4016904 2062602494968057078326601 := by
  unfold tailWord_4016904
  simp only [CollatzResearch.WordTrace]
  refine ⟨73254262519725157715232883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97672350026300210286977177 73254262519725157715232883)
  ·
    refine ⟨109881393779587736572849325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73254262519725157715232883 109881393779587736572849325)
    ·
      refine ⟨41205522667345401214818497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109881393779587736572849325 41205522667345401214818497)
      ·
        refine ⟨30904142000509050911113873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41205522667345401214818497 30904142000509050911113873)
        ·
          refine ⟨23178106500381788183335405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30904142000509050911113873 23178106500381788183335405)
          ·
            refine ⟨8691789937643170568750777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23178106500381788183335405 8691789937643170568750777)
            ·
              refine ⟨6518842453232377926563083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691789937643170568750777 6518842453232377926563083)
              ·
                refine ⟨9778263679848566889844625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518842453232377926563083 9778263679848566889844625)
                ·
                  refine ⟨7333697759886425167383469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9778263679848566889844625 7333697759886425167383469)
                  ·
                    refine ⟨2750136659957409437768801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7333697759886425167383469 2750136659957409437768801)
                    ·
                      refine ⟨2062602494968057078326601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750136659957409437768801 2062602494968057078326601)
                      ·
                        rfl

theorem cell23_4016904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_4016904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016904 prefixEnd_4016904 := by exact prefixLift 4016904
  have htrace : WordTrace (prefixWord ++ tailWord_4016904) baseStart_4016904 baseEnd_4016904 := by
    simpa [prefixWord, tailWord_4016904, baseEnd_4016904] using wordTrace_append hprefix tailTrace_4016904
  have hstable : (prefixWord ++ tailWord_4016904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016904).length < 2 ^ (prefixWord ++ tailWord_4016904).sum := by decide
  have hdescent : baseEnd_4016904 < baseStart_4016904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016927 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 2, 4]
def baseStart_4016927 : Nat := 118140960795 + 4016927 * 2 ^ 59
def prefixEnd_4016927 : Nat := 4983230072969 + 3 ^ 40 * 4016927 * 2
def baseEnd_4016927 : Nat := 687538101674370162779665

theorem tailTrace_4016927 : CollatzResearch.WordTrace tailWord_4016927 prefixEnd_4016927 687538101674370162779665 := by
  unfold tailWord_4016927
  simp only [CollatzResearch.WordTrace]
  refine ⟨146509363918366990358553035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97672909278911326905702023 146509363918366990358553035)
  ·
    refine ⟨219764045877550485537829553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146509363918366990358553035 219764045877550485537829553)
    ·
      refine ⟨164823034408162864153372165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219764045877550485537829553 164823034408162864153372165)
      ·
        refine ⟨30904318951530537028757281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164823034408162864153372165 30904318951530537028757281)
        ·
          refine ⟨23178239213647902771567961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30904318951530537028757281 23178239213647902771567961)
          ·
            refine ⟨17383679410235927078675971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23178239213647902771567961 17383679410235927078675971)
            ·
              refine ⟨26075519115353890618013957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17383679410235927078675971 26075519115353890618013957)
              ·
                refine ⟨4889159834128854490877617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26075519115353890618013957 4889159834128854490877617)
                ·
                  refine ⟨3666869875596640868158213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4889159834128854490877617 3666869875596640868158213)
                  ·
                    refine ⟨687538101674370162779665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3666869875596640868158213 687538101674370162779665)
                    ·
                      rfl

theorem cell23_4016927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_4016927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016927 prefixEnd_4016927 := by exact prefixLift 4016927
  have htrace : WordTrace (prefixWord ++ tailWord_4016927) baseStart_4016927 baseEnd_4016927 := by
    simpa [prefixWord, tailWord_4016927, baseEnd_4016927] using wordTrace_append hprefix tailTrace_4016927
  have hstable : (prefixWord ++ tailWord_4016927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016927).length < 2 ^ (prefixWord ++ tailWord_4016927).sum := by decide
  have hdescent : baseEnd_4016927 < baseStart_4016927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016928 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 1, 1, 3]
def baseStart_4016928 : Nat := 118140960795 + 4016928 * 2 ^ 59
def prefixEnd_4016928 : Nat := 4983230072969 + 3 ^ 40 * 4016928 * 2
def baseEnd_4016928 : Nat := 2062614818503764984426491

theorem tailTrace_4016928 : CollatzResearch.WordTrace tailWord_4016928 prefixEnd_4016928 2062614818503764984426491 := by
  unfold tailWord_4016928
  simp only [CollatzResearch.WordTrace]
  refine ⟨73254700195681683764669719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97672933594242245019559625 73254700195681683764669719)
  ·
    refine ⟨109882050293522525647004579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73254700195681683764669719 109882050293522525647004579)
    ·
      refine ⟨164823075440283788470506869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109882050293522525647004579 164823075440283788470506869)
      ·
        refine ⟨15452163322526605169110019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164823075440283788470506869 15452163322526605169110019)
        ·
          refine ⟨23178244983789907753665029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15452163322526605169110019 23178244983789907753665029)
          ·
            refine ⟨4345920934460607703812193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23178244983789907753665029 4345920934460607703812193)
            ·
              refine ⟨3259440700845455777859145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345920934460607703812193 3259440700845455777859145)
              ·
                refine ⟨2444580525634091833394359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3259440700845455777859145 2444580525634091833394359)
                ·
                  refine ⟨3666870788451137750091539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444580525634091833394359 3666870788451137750091539)
                  ·
                    refine ⟨5500306182676706625137309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666870788451137750091539 5500306182676706625137309)
                    ·
                      refine ⟨2062614818503764984426491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5500306182676706625137309 2062614818503764984426491)
                      ·
                        rfl

theorem cell23_4016928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_4016928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016928 prefixEnd_4016928 := by exact prefixLift 4016928
  have htrace : WordTrace (prefixWord ++ tailWord_4016928) baseStart_4016928 baseEnd_4016928 := by
    simpa [prefixWord, tailWord_4016928, baseEnd_4016928] using wordTrace_append hprefix tailTrace_4016928
  have hstable : (prefixWord ++ tailWord_4016928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016928).length < 2 ^ (prefixWord ++ tailWord_4016928).sum := by decide
  have hdescent : baseEnd_4016928 < baseStart_4016928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016947 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 4]
def baseStart_4016947 : Nat := 118140960795 + 4016947 * 2 ^ 59
def prefixEnd_4016947 : Nat := 4983230072969 + 3 ^ 40 * 4016947 * 2
def baseEnd_4016947 : Nat := 2062624574636200410088903

theorem tailTrace_4016947 : CollatzResearch.WordTrace tailWord_4016947 prefixEnd_4016947 2062624574636200410088903 := by
  unfold tailWord_4016947
  simp only [CollatzResearch.WordTrace]
  refine ⟨146510093378294533774281095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97673395585529689182854063 146510093378294533774281095)
  ·
    refine ⟨219765140067441800661421643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146510093378294533774281095 219765140067441800661421643)
    ·
      refine ⟨329647710101162700992132465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219765140067441800661421643 329647710101162700992132465)
      ·
        refine ⟨247235782575872025744099349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329647710101162700992132465 247235782575872025744099349)
        ·
          refine ⟨11589177308244001206754657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247235782575872025744099349 11589177308244001206754657)
          ·
            refine ⟨8691882981183000905065993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11589177308244001206754657 8691882981183000905065993)
            ·
              refine ⟨6518912235887250678799495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691882981183000905065993 6518912235887250678799495)
              ·
                refine ⟨9778368353830876018199243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518912235887250678799495 9778368353830876018199243)
                ·
                  refine ⟨14667552530746314027298865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9778368353830876018199243 14667552530746314027298865)
                  ·
                    refine ⟨11000664398059735520474149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14667552530746314027298865 11000664398059735520474149)
                    ·
                      refine ⟨2062624574636200410088903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11000664398059735520474149 2062624574636200410088903)
                      ·
                        rfl

theorem cell23_4016947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_4016947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016947 prefixEnd_4016947 := by exact prefixLift 4016947
  have htrace : WordTrace (prefixWord ++ tailWord_4016947) baseStart_4016947 baseEnd_4016947 := by
    simpa [prefixWord, tailWord_4016947, baseEnd_4016947] using wordTrace_append hprefix tailTrace_4016947
  have hstable : (prefixWord ++ tailWord_4016947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016947).length < 2 ^ (prefixWord ++ tailWord_4016947).sum := by decide
  have hdescent : baseEnd_4016947 < baseStart_4016947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016967 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_4016967 : Nat := 118140960795 + 4016967 * 2 ^ 59
def prefixEnd_4016967 : Nat := 4983230072969 + 3 ^ 40 * 4016967 * 2
def baseEnd_4016967 : Nat := 2062634844249290331838811

theorem tailTrace_4016967 : CollatzResearch.WordTrace tailWord_4016967 prefixEnd_4016967 2062634844249290331838811 := by
  unfold tailWord_4016967
  simp only [CollatzResearch.WordTrace]
  refine ⟨146510822838222077190009155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97673881892148051460006103 146510822838222077190009155)
  ·
    refine ⟨219766234257333115785013733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146510822838222077190009155 219766234257333115785013733)
    ·
      refine ⟨41206168923249959209690075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219766234257333115785013733 41206168923249959209690075)
      ·
        refine ⟨61809253384874938814535113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41206168923249959209690075 61809253384874938814535113)
        ·
          refine ⟨46356940038656204110901335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61809253384874938814535113 46356940038656204110901335)
          ·
            refine ⟨69535410057984306166352003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46356940038656204110901335 69535410057984306166352003)
            ·
              refine ⟨104303115086976459249528005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69535410057984306166352003 104303115086976459249528005)
              ·
                refine ⟨19556834078808086109286501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104303115086976459249528005 19556834078808086109286501)
                ·
                  refine ⟨3666906389776516145491219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19556834078808086109286501 3666906389776516145491219)
                  ·
                    refine ⟨5500359584664774218236829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666906389776516145491219 5500359584664774218236829)
                    ·
                      refine ⟨2062634844249290331838811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5500359584664774218236829 2062634844249290331838811)
                      ·
                        rfl

theorem cell23_4016967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_4016967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4016967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4016967 prefixEnd_4016967 := by exact prefixLift 4016967
  have htrace : WordTrace (prefixWord ++ tailWord_4016967) baseStart_4016967 baseEnd_4016967 := by
    simpa [prefixWord, tailWord_4016967, baseEnd_4016967] using wordTrace_append hprefix tailTrace_4016967
  have hstable : (prefixWord ++ tailWord_4016967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016967).length < 2 ^ (prefixWord ++ tailWord_4016967).sum := by decide
  have hdescent : baseEnd_4016967 < baseStart_4016967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017020 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_4017020 : Nat := 118140960795 + 4017020 * 2 ^ 59
def prefixEnd_4017020 : Nat := 4983230072969 + 3 ^ 40 * 4017020 * 2
def baseEnd_4017020 : Nat := 2062662058723978624476067

theorem tailTrace_4017020 : CollatzResearch.WordTrace tailWord_4017020 prefixEnd_4017020 2062662058723978624476067 := by
  unfold tailWord_4017020
  simp only [CollatzResearch.WordTrace]
  refine ⟨73256377953515033620844257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97675170604686711494459009 73256377953515033620844257)
  ·
    refine ⟨54942283465136275215633193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73256377953515033620844257 54942283465136275215633193)
    ·
      refine ⟨41206712598852206411724895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54942283465136275215633193 41206712598852206411724895)
      ·
        refine ⟨61810068898278309617587343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41206712598852206411724895 61810068898278309617587343)
        ·
          refine ⟨92715103347417464426381015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61810068898278309617587343 92715103347417464426381015)
          ·
            refine ⟨139072655021126196639571523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92715103347417464426381015 139072655021126196639571523)
            ·
              refine ⟨208608982531689294959357285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139072655021126196639571523 208608982531689294959357285)
              ·
                refine ⟨39114184224691742804879491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208608982531689294959357285 39114184224691742804879491)
                ·
                  refine ⟨58671276337037614207319237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39114184224691742804879491 58671276337037614207319237)
                  ·
                    refine ⟨11000864313194552663872357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58671276337037614207319237 11000864313194552663872357)
                    ·
                      refine ⟨2062662058723978624476067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11000864313194552663872357 2062662058723978624476067)
                      ·
                        rfl

theorem cell23_4017020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_4017020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017020 prefixEnd_4017020 := by exact prefixLift 4017020
  have htrace : WordTrace (prefixWord ++ tailWord_4017020) baseStart_4017020 baseEnd_4017020 := by
    simpa [prefixWord, tailWord_4017020, baseEnd_4017020] using wordTrace_append hprefix tailTrace_4017020
  have hstable : (prefixWord ++ tailWord_4017020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017020).length < 2 ^ (prefixWord ++ tailWord_4017020).sum := by decide
  have hdescent : baseEnd_4017020 < baseStart_4017020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017058 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_4017058 : Nat := 118140960795 + 4017058 * 2 ^ 59
def prefixEnd_4017058 : Nat := 4983230072969 + 3 ^ 40 * 4017058 * 2
def baseEnd_4017058 : Nat := 2062681570988849475800893

theorem tailTrace_4017058 : CollatzResearch.WordTrace tailWord_4017058 prefixEnd_4017058 2062681570988849475800893 := by
  unfold tailWord_4017058
  simp only [CollatzResearch.WordTrace]
  refine ⟨36628535470223099932892957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97676094587261599821047885 36628535470223099932892957)
  ·
    refine ⟨13735700801333662474834859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36628535470223099932892957 13735700801333662474834859)
    ·
      refine ⟨20603551202000493712252289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735700801333662474834859 20603551202000493712252289)
      ·
        refine ⟨15452663401500370284189217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20603551202000493712252289 15452663401500370284189217)
        ·
          refine ⟨11589497551125277713141913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15452663401500370284189217 11589497551125277713141913)
          ·
            refine ⟨8692123163343958284856435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11589497551125277713141913 8692123163343958284856435)
            ·
              refine ⟨13038184745015937427284653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692123163343958284856435 13038184745015937427284653)
              ·
                refine ⟨4889319279380976535231745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13038184745015937427284653 4889319279380976535231745)
                ·
                  refine ⟨3666989459535732401423809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4889319279380976535231745 3666989459535732401423809)
                  ·
                    refine ⟨2750242094651799301067857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666989459535732401423809 2750242094651799301067857)
                    ·
                      refine ⟨2062681570988849475800893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750242094651799301067857 2062681570988849475800893)
                      ·
                        rfl

theorem cell23_4017058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_4017058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017058 prefixEnd_4017058 := by exact prefixLift 4017058
  have htrace : WordTrace (prefixWord ++ tailWord_4017058) baseStart_4017058 baseEnd_4017058 := by
    simpa [prefixWord, tailWord_4017058, baseEnd_4017058] using wordTrace_append hprefix tailTrace_4017058
  have hstable : (prefixWord ++ tailWord_4017058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017058).length < 2 ^ (prefixWord ++ tailWord_4017058).sum := by decide
  have hdescent : baseEnd_4017058 < baseStart_4017058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017067 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 2, 5, 2]
def baseStart_4017067 : Nat := 118140960795 + 4017067 * 2 ^ 59
def prefixEnd_4017067 : Nat := 4983230072969 + 3 ^ 40 * 4017067 * 2
def baseEnd_4017067 : Nat := 2062686192314739940588351

theorem tailTrace_4017067 : CollatzResearch.WordTrace tailWord_4017067 prefixEnd_4017067 2062686192314739940588351 := by
  unfold tailWord_4017067
  simp only [CollatzResearch.WordTrace]
  refine ⟨146514470137859794268649455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97676313425239862845766303 146514470137859794268649455)
  ·
    refine ⟨219771705206789691402974183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146514470137859794268649455 219771705206789691402974183)
    ·
      refine ⟨329657557810184537104461275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219771705206789691402974183 329657557810184537104461275)
      ·
        refine ⟨494486336715276805656691913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329657557810184537104461275 494486336715276805656691913)
        ·
          refine ⟨370864752536457604242518935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494486336715276805656691913 370864752536457604242518935)
          ·
            refine ⟨556297128804686406363778403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370864752536457604242518935 556297128804686406363778403)
            ·
              refine ⟨834445693207029609545667605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556297128804686406363778403 834445693207029609545667605)
              ·
                refine ⟨39114641869079512947453169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 834445693207029609545667605 39114641869079512947453169)
                ·
                  refine ⟨29335981401809634710589877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39114641869079512947453169 29335981401809634710589877)
                  ·
                    refine ⟨2750248256419653254117801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29335981401809634710589877 2750248256419653254117801)
                    ·
                      refine ⟨2062686192314739940588351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750248256419653254117801 2062686192314739940588351)
                      ·
                        rfl

theorem cell23_4017067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5, 2].length) (baseStart_4017067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017067 prefixEnd_4017067 := by exact prefixLift 4017067
  have htrace : WordTrace (prefixWord ++ tailWord_4017067) baseStart_4017067 baseEnd_4017067 := by
    simpa [prefixWord, tailWord_4017067, baseEnd_4017067] using wordTrace_append hprefix tailTrace_4017067
  have hstable : (prefixWord ++ tailWord_4017067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017067).length < 2 ^ (prefixWord ++ tailWord_4017067).sum := by decide
  have hdescent : baseEnd_4017067 < baseStart_4017067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017114 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2]
def baseStart_4017114 : Nat := 118140960795 + 4017114 * 2 ^ 59
def prefixEnd_4017114 : Nat := 4983230072969 + 3 ^ 40 * 4017114 * 2
def baseEnd_4017114 : Nat := 2062710325905501256700635

theorem tailTrace_4017114 : CollatzResearch.WordTrace tailWord_4017114 prefixEnd_4017114 2062710325905501256700635 := by
  unfold tailWord_4017114
  simp only [CollatzResearch.WordTrace]
  refine ⟨36629046092172380323902599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97677456245793014197073597 36629046092172380323902599)
  ·
    refine ⟨54943569138258570485853899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36629046092172380323902599 54943569138258570485853899)
    ·
      refine ⟨82415353707387855728780849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54943569138258570485853899 82415353707387855728780849)
      ·
        refine ⟨61811515280540891796585637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82415353707387855728780849 61811515280540891796585637)
        ·
          refine ⟨11589659115101417211859807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61811515280540891796585637 11589659115101417211859807)
          ·
            refine ⟨17384488672652125817789711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11589659115101417211859807 17384488672652125817789711)
            ·
              refine ⟨26076733008978188726684567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17384488672652125817789711 26076733008978188726684567)
              ·
                refine ⟨39115099513467283090026851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26076733008978188726684567 39115099513467283090026851)
                ·
                  refine ⟨58672649270200924635040277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39115099513467283090026851 58672649270200924635040277)
                  ·
                    refine ⟨2750280434540668342267513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58672649270200924635040277 2750280434540668342267513)
                    ·
                      refine ⟨2062710325905501256700635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750280434540668342267513 2062710325905501256700635)
                      ·
                        rfl

theorem cell23_4017114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_4017114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017114 prefixEnd_4017114 := by exact prefixLift 4017114
  have htrace : WordTrace (prefixWord ++ tailWord_4017114) baseStart_4017114 baseEnd_4017114 := by
    simpa [prefixWord, tailWord_4017114, baseEnd_4017114] using wordTrace_append hprefix tailTrace_4017114
  have hstable : (prefixWord ++ tailWord_4017114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017114).length < 2 ^ (prefixWord ++ tailWord_4017114).sum := by decide
  have hdescent : baseEnd_4017114 < baseStart_4017114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017120 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 12]
def baseStart_4017120 : Nat := 118140960795 + 4017120 * 2 ^ 59
def prefixEnd_4017120 : Nat := 4983230072969 + 3 ^ 40 * 4017120 * 2
def baseEnd_4017120 : Nat := 229190378532158692580623

theorem tailTrace_4017120 : CollatzResearch.WordTrace tailWord_4017120 prefixEnd_4017120 229190378532158692580623 := by
  unfold tailWord_4017120
  simp only [CollatzResearch.WordTrace]
  refine ⟨73258201603333892160164407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97677602137778522880219209 73258201603333892160164407)
  ·
    refine ⟨109887302405000838240246611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73258201603333892160164407 109887302405000838240246611)
    ·
      refine ⟨164830953607501257360369917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109887302405000838240246611 164830953607501257360369917)
      ·
        refine ⟨61811607602812971510138719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164830953607501257360369917 61811607602812971510138719)
        ·
          refine ⟨92717411404219457265208079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61811607602812971510138719 92717411404219457265208079)
          ·
            refine ⟨139076117106329185897812119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92717411404219457265208079 139076117106329185897812119)
            ·
              refine ⟨208614175659493778846718179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139076117106329185897812119 208614175659493778846718179)
              ·
                refine ⟨312921263489240668270077269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208614175659493778846718179 312921263489240668270077269)
                ·
                  refine ⟨229190378532158692580623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 312921263489240668270077269 229190378532158692580623)
                  ·
                    rfl

theorem cell23_4017120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_4017120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017120 prefixEnd_4017120 := by exact prefixLift 4017120
  have htrace : WordTrace (prefixWord ++ tailWord_4017120) baseStart_4017120 baseEnd_4017120 := by
    simpa [prefixWord, tailWord_4017120, baseEnd_4017120] using wordTrace_append hprefix tailTrace_4017120
  have hstable : (prefixWord ++ tailWord_4017120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017120).length < 2 ^ (prefixWord ++ tailWord_4017120).sum := by decide
  have hdescent : baseEnd_4017120 < baseStart_4017120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017224 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_4017224 : Nat := 118140960795 + 4017224 * 2 ^ 59
def prefixEnd_4017224 : Nat := 4983230072969 + 3 ^ 40 * 4017224 * 2
def baseEnd_4017224 : Nat := 2062766808777495826325129

theorem tailTrace_4017224 : CollatzResearch.WordTrace tailWord_4017224 prefixEnd_4017224 2062766808777495826325129 := by
  unfold tailWord_4017224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73260098199145505041057363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97680130932194006721409817 73260098199145505041057363)
  ·
    refine ⟨109890147298718257561586045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73260098199145505041057363 109890147298718257561586045)
    ·
      refine ⟨41208805237019346585594767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109890147298718257561586045 41208805237019346585594767)
      ·
        refine ⟨61813207855529019878392151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41208805237019346585594767 61813207855529019878392151)
        ·
          refine ⟨92719811783293529817588227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61813207855529019878392151 92719811783293529817588227)
          ·
            refine ⟨139079717674940294726382341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92719811783293529817588227 139079717674940294726382341)
            ·
              refine ⟨26077447064051305261196689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139079717674940294726382341 26077447064051305261196689)
              ·
                refine ⟨19558085298038478945897517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26077447064051305261196689 19558085298038478945897517)
                ·
                  refine ⟨7334281986764429604711569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19558085298038478945897517 7334281986764429604711569)
                  ·
                    refine ⟨5500711490073322203533677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7334281986764429604711569 5500711490073322203533677)
                    ·
                      refine ⟨2062766808777495826325129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5500711490073322203533677 2062766808777495826325129)
                      ·
                        rfl

theorem cell23_4017224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_4017224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017224 prefixEnd_4017224 := by exact prefixLift 4017224
  have htrace : WordTrace (prefixWord ++ tailWord_4017224) baseStart_4017224 baseEnd_4017224 := by
    simpa [prefixWord, tailWord_4017224, baseEnd_4017224] using wordTrace_append hprefix tailTrace_4017224
  have hstable : (prefixWord ++ tailWord_4017224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017224).length < 2 ^ (prefixWord ++ tailWord_4017224).sum := by decide
  have hdescent : baseEnd_4017224 < baseStart_4017224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017234 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4017234 : Nat := 118140960795 + 4017234 * 2 ^ 59
def prefixEnd_4017234 : Nat := 4983230072969 + 3 ^ 40 * 4017234 * 2
def baseEnd_4017234 : Nat := 2062771943584040787200083

theorem tailTrace_4017234 : CollatzResearch.WordTrace tailWord_4017234 prefixEnd_4017234 2062771943584040787200083 := by
  unfold tailWord_4017234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36630140282063695447494689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97680374085503187859985837 36630140282063695447494689)
  ·
    refine ⟨27472605211547771585621017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36630140282063695447494689 27472605211547771585621017)
    ·
      refine ⟨20604453908660828689215763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27472605211547771585621017 20604453908660828689215763)
      ·
        refine ⟨30906680862991243033823645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20604453908660828689215763 30906680862991243033823645)
        ·
          refine ⟨11590005323621716137683867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30906680862991243033823645 11590005323621716137683867)
          ·
            refine ⟨17385007985432574206525801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11590005323621716137683867 17385007985432574206525801)
            ·
              refine ⟨13038755989074430654894351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17385007985432574206525801 13038755989074430654894351)
              ·
                refine ⟨19558133983611645982341527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038755989074430654894351 19558133983611645982341527)
                ·
                  refine ⟨29337200975417468973512291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19558133983611645982341527 29337200975417468973512291)
                  ·
                    refine ⟨44005801463126203460268437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29337200975417468973512291 44005801463126203460268437)
                    ·
                      refine ⟨2062771943584040787200083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44005801463126203460268437 2062771943584040787200083)
                      ·
                        rfl

theorem cell23_4017234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4017234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017234 prefixEnd_4017234 := by exact prefixLift 4017234
  have htrace : WordTrace (prefixWord ++ tailWord_4017234) baseStart_4017234 baseEnd_4017234 := by
    simpa [prefixWord, tailWord_4017234, baseEnd_4017234] using wordTrace_append hprefix tailTrace_4017234
  have hstable : (prefixWord ++ tailWord_4017234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017234).length < 2 ^ (prefixWord ++ tailWord_4017234).sum := by decide
  have hdescent : baseEnd_4017234 < baseStart_4017234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017288 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4017288 : Nat := 118140960795 + 4017288 * 2 ^ 59
def prefixEnd_4017288 : Nat := 4983230072969 + 3 ^ 40 * 4017288 * 2
def baseEnd_4017288 : Nat := 2062799671539383575924835

theorem tailTrace_4017288 : CollatzResearch.WordTrace tailWord_4017288 prefixEnd_4017288 2062799671539383575924835 := by
  unfold tailWord_4017288
  simp only [CollatzResearch.WordTrace]
  refine ⟨73261265335029574506222259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97681687113372766008296345 73261265335029574506222259)
  ·
    refine ⟨109891898002544361759333389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73261265335029574506222259 109891898002544361759333389)
    ·
      refine ⟨41209461750954135659750021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109891898002544361759333389 41209461750954135659750021)
      ·
        refine ⟨7726774078303900436203129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41209461750954135659750021 7726774078303900436203129)
        ·
          refine ⟨5795080558727925327152347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7726774078303900436203129 5795080558727925327152347)
          ·
            refine ⟨8692620838091887990728521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795080558727925327152347 8692620838091887990728521)
            ·
              refine ⟨6519465628568915993046391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8692620838091887990728521 6519465628568915993046391)
              ·
                refine ⟨9779198442853373989569587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519465628568915993046391 9779198442853373989569587)
                ·
                  refine ⟨14668797664280060984354381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779198442853373989569587 14668797664280060984354381)
                  ·
                    refine ⟨5500799124105022869132893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14668797664280060984354381 5500799124105022869132893)
                    ·
                      refine ⟨2062799671539383575924835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5500799124105022869132893 2062799671539383575924835)
                      ·
                        rfl

theorem cell23_4017288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4017288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017288 prefixEnd_4017288 := by exact prefixLift 4017288
  have htrace : WordTrace (prefixWord ++ tailWord_4017288) baseStart_4017288 baseEnd_4017288 := by
    simpa [prefixWord, tailWord_4017288, baseEnd_4017288] using wordTrace_append hprefix tailTrace_4017288
  have hstable : (prefixWord ++ tailWord_4017288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017288).length < 2 ^ (prefixWord ++ tailWord_4017288).sum := by decide
  have hdescent : baseEnd_4017288 < baseStart_4017288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017298 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_4017298 : Nat := 118140960795 + 4017298 * 2 ^ 59
def prefixEnd_4017298 : Nat := 4983230072969 + 3 ^ 40 * 4017298 * 2
def baseEnd_4017298 : Nat := 2062804806345928536799789

theorem tailTrace_4017298 : CollatzResearch.WordTrace tailWord_4017298 prefixEnd_4017298 2062804806345928536799789 := by
  unfold tailWord_4017298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36630723850005730180077137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97681930266681947146872365 36630723850005730180077137)
  ·
    refine ⟨27473042887504297635057853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36630723850005730180077137 27473042887504297635057853)
    ·
      refine ⟨10302391082814111613146695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27473042887504297635057853 10302391082814111613146695)
      ·
        refine ⟨15453586624221167419720043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10302391082814111613146695 15453586624221167419720043)
        ·
          refine ⟨23180379936331751129580065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15453586624221167419720043 23180379936331751129580065)
          ·
            refine ⟨17385284952248813347185049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23180379936331751129580065 17385284952248813347185049)
            ·
              refine ⟨13038963714186610010388787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17385284952248813347185049 13038963714186610010388787)
              ·
                refine ⟨19558445571279915015583181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038963714186610010388787 19558445571279915015583181)
                ·
                  refine ⟨7334417089229968130843693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19558445571279915015583181 7334417089229968130843693)
                  ·
                    refine ⟨2750406408461238049066385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7334417089229968130843693 2750406408461238049066385)
                    ·
                      refine ⟨2062804806345928536799789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750406408461238049066385 2062804806345928536799789)
                      ·
                        rfl

theorem cell23_4017298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_4017298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017298 prefixEnd_4017298 := by exact prefixLift 4017298
  have htrace : WordTrace (prefixWord ++ tailWord_4017298) baseStart_4017298 baseEnd_4017298 := by
    simpa [prefixWord, tailWord_4017298, baseEnd_4017298] using wordTrace_append hprefix tailTrace_4017298
  have hstable : (prefixWord ++ tailWord_4017298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017298).length < 2 ^ (prefixWord ++ tailWord_4017298).sum := by decide
  have hdescent : baseEnd_4017298 < baseStart_4017298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017322 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4017322 : Nat := 118140960795 + 4017322 * 2 ^ 59
def prefixEnd_4017322 : Nat := 4983230072969 + 3 ^ 40 * 4017322 * 2
def baseEnd_4017322 : Nat := 2062817129881636442899679

theorem tailTrace_4017322 : CollatzResearch.WordTrace tailWord_4017322 prefixEnd_4017322 2062817129881636442899679 := by
  unfold tailWord_4017322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36630942687983993204795555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97682513834623981879454813 36630942687983993204795555)
  ·
    refine ⟨54946414031975989807193333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36630942687983993204795555 54946414031975989807193333)
    ·
      refine ⟨5151226315497749044424375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54946414031975989807193333 5151226315497749044424375)
      ·
        refine ⟨7726839473246623566636563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151226315497749044424375 7726839473246623566636563)
        ·
          refine ⟨11590259209869935349954845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726839473246623566636563 11590259209869935349954845)
          ·
            refine ⟨4346347203701225756233067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11590259209869935349954845 4346347203701225756233067)
            ·
              refine ⟨6519520805551838634349601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4346347203701225756233067 6519520805551838634349601)
              ·
                refine ⟨4889640604163878975762201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6519520805551838634349601 4889640604163878975762201)
                ·
                  refine ⟨3667230453122909231821651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4889640604163878975762201 3667230453122909231821651)
                  ·
                    refine ⟨5500845679684363847732477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3667230453122909231821651 5500845679684363847732477)
                    ·
                      refine ⟨2062817129881636442899679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5500845679684363847732477 2062817129881636442899679)
                      ·
                        rfl

theorem cell23_4017322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4017322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017322 prefixEnd_4017322 := by exact prefixLift 4017322
  have htrace : WordTrace (prefixWord ++ tailWord_4017322) baseStart_4017322 baseEnd_4017322 := by
    simpa [prefixWord, tailWord_4017322, baseEnd_4017322] using wordTrace_append hprefix tailTrace_4017322
  have hstable : (prefixWord ++ tailWord_4017322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017322).length < 2 ^ (prefixWord ++ tailWord_4017322).sum := by decide
  have hdescent : baseEnd_4017322 < baseStart_4017322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017345 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4017345 : Nat := 118140960795 + 4017345 * 2 ^ 59
def prefixEnd_4017345 : Nat := 4983230072969 + 3 ^ 40 * 4017345 * 2
def baseEnd_4017345 : Nat := 2062828939936689852912073

theorem tailTrace_4017345 : CollatzResearch.WordTrace tailWord_4017345 prefixEnd_4017345 2062828939936689852912073 := by
  unfold tailWord_4017345
  simp only [CollatzResearch.WordTrace]
  refine ⟨146524609630852647747269489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97683073087235098498179659 146524609630852647747269489)
  ·
    refine ⟨109893457223139485810452117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146524609630852647747269489 109893457223139485810452117)
    ·
      refine ⟨5151255807334663397364943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109893457223139485810452117 5151255807334663397364943)
      ·
        refine ⟨7726883711001995096047415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151255807334663397364943 7726883711001995096047415)
        ·
          refine ⟨11590325566502992644071123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726883711001995096047415 11590325566502992644071123)
          ·
            refine ⟨17385488349754488966106685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11590325566502992644071123 17385488349754488966106685)
            ·
              refine ⟨6519558131157933362290007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17385488349754488966106685 6519558131157933362290007)
              ·
                refine ⟨9779337196736900043435011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519558131157933362290007 9779337196736900043435011)
                ·
                  refine ⟨14669005795105350065152517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779337196736900043435011 14669005795105350065152517)
                  ·
                    refine ⟨2750438586582253137216097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14669005795105350065152517 2750438586582253137216097)
                    ·
                      refine ⟨2062828939936689852912073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750438586582253137216097 2062828939936689852912073)
                      ·
                        rfl

theorem cell23_4017345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4017345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017345 prefixEnd_4017345 := by exact prefixLift 4017345
  have htrace : WordTrace (prefixWord ++ tailWord_4017345) baseStart_4017345 baseEnd_4017345 := by
    simpa [prefixWord, tailWord_4017345, baseEnd_4017345] using wordTrace_append hprefix tailTrace_4017345
  have hstable : (prefixWord ++ tailWord_4017345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017345).length < 2 ^ (prefixWord ++ tailWord_4017345).sum := by decide
  have hdescent : baseEnd_4017345 < baseStart_4017345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017391 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_4017391 : Nat := 118140960795 + 4017391 * 2 ^ 59
def prefixEnd_4017391 : Nat := 4983230072969 + 3 ^ 40 * 4017391 * 2
def baseEnd_4017391 : Nat := 2062852560046796672936861

theorem tailTrace_4017391 : CollatzResearch.WordTrace tailWord_4017391 prefixEnd_4017391 2062852560046796672936861 := by
  unfold tailWord_4017391
  simp only [CollatzResearch.WordTrace]
  refine ⟨146526287388685997603444027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97684191592457331735629351 146526287388685997603444027)
  ·
    refine ⟨219789431083028996405166041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146526287388685997603444027 219789431083028996405166041)
    ·
      refine ⟨164842073312271747303874531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219789431083028996405166041 164842073312271747303874531)
      ·
        refine ⟨247263109968407620955811797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164842073312271747303874531 247263109968407620955811797)
        ·
          refine ⟨5795229139884553616151839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 247263109968407620955811797 5795229139884553616151839)
          ·
            refine ⟨8692843709826830424227759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795229139884553616151839 8692843709826830424227759)
            ·
              refine ⟨13039265564740245636341639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692843709826830424227759 13039265564740245636341639)
              ·
                refine ⟨19558898347110368454512459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039265564740245636341639 19558898347110368454512459)
                ·
                  refine ⟨29338347520665552681768689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19558898347110368454512459 29338347520665552681768689)
                  ·
                    refine ⟨22003760640499164511326517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29338347520665552681768689 22003760640499164511326517)
                    ·
                      refine ⟨2062852560046796672936861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22003760640499164511326517 2062852560046796672936861)
                      ·
                        rfl

theorem cell23_4017391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_4017391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017391 prefixEnd_4017391 := by exact prefixLift 4017391
  have htrace : WordTrace (prefixWord ++ tailWord_4017391) baseStart_4017391 baseEnd_4017391 := by
    simpa [prefixWord, tailWord_4017391, baseEnd_4017391] using wordTrace_append hprefix tailTrace_4017391
  have hstable : (prefixWord ++ tailWord_4017391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017391).length < 2 ^ (prefixWord ++ tailWord_4017391).sum := by decide
  have hdescent : baseEnd_4017391 < baseStart_4017391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017396 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4017396 : Nat := 118140960795 + 4017396 * 2 ^ 59
def prefixEnd_4017396 : Nat := 4983230072969 + 3 ^ 40 * 4017396 * 2
def baseEnd_4017396 : Nat := 2062855127450069153374339

theorem tailTrace_4017396 : CollatzResearch.WordTrace tailWord_4017396 prefixEnd_4017396 2062855127450069153374339 := by
  unfold tailWord_4017396
  simp only [CollatzResearch.WordTrace]
  refine ⟨73263234876833941728688021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97684313169111922304917361 73263234876833941728688021)
  ·
    refine ⟨3434214134851591018532251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73263234876833941728688021 3434214134851591018532251)
    ·
      refine ⟨5151321202277386527798377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434214134851591018532251 5151321202277386527798377)
      ·
        refine ⟨3863490901708039895848783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5151321202277386527798377 3863490901708039895848783)
        ·
          refine ⟨5795236352562059843773175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863490901708039895848783 5795236352562059843773175)
          ·
            refine ⟨8692854528843089765659763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795236352562059843773175 8692854528843089765659763)
            ·
              refine ⟨13039281793264634648489645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692854528843089765659763 13039281793264634648489645)
              ·
                refine ⟨4889730672474237993183617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13039281793264634648489645 4889730672474237993183617)
                ·
                  refine ⟨3667298004355678494887713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4889730672474237993183617 3667298004355678494887713)
                  ·
                    refine ⟨2750473503266758871165785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3667298004355678494887713 2750473503266758871165785)
                    ·
                      refine ⟨2062855127450069153374339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750473503266758871165785 2062855127450069153374339)
                      ·
                        rfl

theorem cell23_4017396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4017396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017396 prefixEnd_4017396 := by exact prefixLift 4017396
  have htrace : WordTrace (prefixWord ++ tailWord_4017396) baseStart_4017396 baseEnd_4017396 := by
    simpa [prefixWord, tailWord_4017396, baseEnd_4017396] using wordTrace_append hprefix tailTrace_4017396
  have hstable : (prefixWord ++ tailWord_4017396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017396).length < 2 ^ (prefixWord ++ tailWord_4017396).sum := by decide
  have hdescent : baseEnd_4017396 < baseStart_4017396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017401 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 6, 2]
def baseStart_4017401 : Nat := 118140960795 + 4017401 * 2 ^ 59
def prefixEnd_4017401 : Nat := 4983230072969 + 3 ^ 40 * 4017401 * 2
def baseEnd_4017401 : Nat := 2062857694853341633811815

theorem tailTrace_4017401 : CollatzResearch.WordTrace tailWord_4017401 prefixEnd_4017401 2062857694853341633811815 := by
  unfold tailWord_4017401
  simp only [CollatzResearch.WordTrace]
  refine ⟨146526652118649769311308057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97684434745766512874205371 146526652118649769311308057)
  ·
    refine ⟨109894989088987326983481043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146526652118649769311308057 109894989088987326983481043)
    ·
      refine ⟨164842483633480990475221565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109894989088987326983481043 164842483633480990475221565)
      ·
        refine ⟨61815931362555371428208087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164842483633480990475221565 61815931362555371428208087)
        ·
          refine ⟨92723897043833057142312131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61815931362555371428208087 92723897043833057142312131)
          ·
            refine ⟨139085845565749585713468197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92723897043833057142312131 139085845565749585713468197)
            ·
              refine ⟨26078596043578047321275287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139085845565749585713468197 26078596043578047321275287)
              ·
                refine ⟨39117894065367070981912931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26078596043578047321275287 39117894065367070981912931)
                ·
                  refine ⟨58676841098050606472869397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39117894065367070981912931 58676841098050606472869397)
                  ·
                    refine ⟨2750476926471122178415753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58676841098050606472869397 2750476926471122178415753)
                    ·
                      refine ⟨2062857694853341633811815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750476926471122178415753 2062857694853341633811815)
                      ·
                        rfl

theorem cell23_4017401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_4017401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017401 prefixEnd_4017401 := by exact prefixLift 4017401
  have htrace : WordTrace (prefixWord ++ tailWord_4017401) baseStart_4017401 baseEnd_4017401 := by
    simpa [prefixWord, tailWord_4017401, baseEnd_4017401] using wordTrace_append hprefix tailTrace_4017401
  have hstable : (prefixWord ++ tailWord_4017401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017401).length < 2 ^ (prefixWord ++ tailWord_4017401).sum := by decide
  have hdescent : baseEnd_4017401 < baseStart_4017401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017445 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_4017445 : Nat := 118140960795 + 4017445 * 2 ^ 59
def prefixEnd_4017445 : Nat := 4983230072969 + 3 ^ 40 * 4017445 * 2
def baseEnd_4017445 : Nat := 687626762667379820553871

theorem tailTrace_4017445 : CollatzResearch.WordTrace tailWord_4017445 prefixEnd_4017445 687626762667379820553871 := by
  unfold tailWord_4017445
  simp only [CollatzResearch.WordTrace]
  refine ⟨146528256930490364825909789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97685504620326909883939859 146528256930490364825909789)
  ·
    refine ⟨54948096348933886809716171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146528256930490364825909789 54948096348933886809716171)
    ·
      refine ⟨82422144523400830214574257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54948096348933886809716171 82422144523400830214574257)
      ·
        refine ⟨61816608392550622660930693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82422144523400830214574257 61816608392550622660930693)
        ·
          refine ⟨11590614073603241748924505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61816608392550622660930693 11590614073603241748924505)
          ·
            refine ⟨8692960555202431311693379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11590614073603241748924505 8692960555202431311693379)
            ·
              refine ⟨13039440832803646967540069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692960555202431311693379 13039440832803646967540069)
              ·
                refine ⟨2444895156150683806413763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13039440832803646967540069 2444895156150683806413763)
                ·
                  refine ⟨3667342734226025709620645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444895156150683806413763 3667342734226025709620645)
                  ·
                    refine ⟨687626762667379820553871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3667342734226025709620645 687626762667379820553871)
                    ·
                      rfl

theorem cell23_4017445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_4017445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017445 prefixEnd_4017445 := by exact prefixLift 4017445
  have htrace : WordTrace (prefixWord ++ tailWord_4017445) baseStart_4017445 baseEnd_4017445 := by
    simpa [prefixWord, tailWord_4017445, baseEnd_4017445] using wordTrace_append hprefix tailTrace_4017445
  have hstable : (prefixWord ++ tailWord_4017445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017445).length < 2 ^ (prefixWord ++ tailWord_4017445).sum := by decide
  have hdescent : baseEnd_4017445 < baseStart_4017445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017462 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4017462 : Nat := 118140960795 + 4017462 * 2 ^ 59
def prefixEnd_4017462 : Nat := 4983230072969 + 3 ^ 40 * 4017462 * 2
def baseEnd_4017462 : Nat := 687629672391088631716345

theorem tailTrace_4017462 : CollatzResearch.WordTrace tailWord_4017462 prefixEnd_4017462 687629672391088631716345 := by
  unfold tailWord_4017462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9158054810714298545579915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97685917980952517819519093 9158054810714298545579915)
  ·
    refine ⟨13737082216071447818369873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9158054810714298545579915 13737082216071447818369873)
    ·
      refine ⟨10302811662053585863777405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13737082216071447818369873 10302811662053585863777405)
      ·
        refine ⟨3863554373270094698916527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10302811662053585863777405 3863554373270094698916527)
        ·
          refine ⟨5795331559905142048374791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863554373270094698916527 5795331559905142048374791)
          ·
            refine ⟨8692997339857713072562187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795331559905142048374791 8692997339857713072562187)
            ·
              refine ⟨13039496009786569608843281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692997339857713072562187 13039496009786569608843281)
              ·
                refine ⟨9779622007339927206632461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13039496009786569608843281 9779622007339927206632461)
                ·
                  refine ⟨3667358252752472702487173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9779622007339927206632461 3667358252752472702487173)
                  ·
                    refine ⟨687629672391088631716345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3667358252752472702487173 687629672391088631716345)
                    ·
                      rfl

theorem cell23_4017462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4017462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017462 prefixEnd_4017462 := by exact prefixLift 4017462
  have htrace : WordTrace (prefixWord ++ tailWord_4017462) baseStart_4017462 baseEnd_4017462 := by
    simpa [prefixWord, tailWord_4017462, baseEnd_4017462] using wordTrace_append hprefix tailTrace_4017462
  have hstable : (prefixWord ++ tailWord_4017462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017462).length < 2 ^ (prefixWord ++ tailWord_4017462).sum := by decide
  have hdescent : baseEnd_4017462 < baseStart_4017462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017464 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_4017464 : Nat := 118140960795 + 4017464 * 2 ^ 59
def prefixEnd_4017464 : Nat := 4983230072969 + 3 ^ 40 * 4017464 * 2
def baseEnd_4017464 : Nat := 2062890044134574887324025

theorem tailTrace_4017464 : CollatzResearch.WordTrace tailWord_4017464 prefixEnd_4017464 2062890044134574887324025 := by
  unfold tailWord_4017464
  simp only [CollatzResearch.WordTrace]
  refine ⟨73264474958710765535425723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97685966611614354047234297 73264474958710765535425723)
  ·
    refine ⟨109896712438066148303138585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73264474958710765535425723 109896712438066148303138585)
    ·
      refine ⟨82422534328549611227353939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109896712438066148303138585 82422534328549611227353939)
      ·
        refine ⟨123633801492824416841030909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82422534328549611227353939 123633801492824416841030909)
        ·
          refine ⟨46362675559809156315386591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123633801492824416841030909 46362675559809156315386591)
          ·
            refine ⟨69544013339713734473079887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46362675559809156315386591 69544013339713734473079887)
            ·
              refine ⟨104316020009570601709619831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69544013339713734473079887 104316020009570601709619831)
              ·
                refine ⟨156474030014355902564429747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104316020009570601709619831 156474030014355902564429747)
                ·
                  refine ⟨234711045021533853846644621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156474030014355902564429747 234711045021533853846644621)
                  ·
                    refine ⟨88016641883075195192491733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234711045021533853846644621 88016641883075195192491733)
                    ·
                      refine ⟨2062890044134574887324025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88016641883075195192491733 2062890044134574887324025)
                      ·
                        rfl

theorem cell23_4017464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_4017464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017464 prefixEnd_4017464 := by exact prefixLift 4017464
  have htrace : WordTrace (prefixWord ++ tailWord_4017464) baseStart_4017464 baseEnd_4017464 := by
    simpa [prefixWord, tailWord_4017464, baseEnd_4017464] using wordTrace_append hprefix tailTrace_4017464
  have hstable : (prefixWord ++ tailWord_4017464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017464).length < 2 ^ (prefixWord ++ tailWord_4017464).sum := by decide
  have hdescent : baseEnd_4017464 < baseStart_4017464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017468 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_4017468 : Nat := 118140960795 + 4017468 * 2 ^ 59
def prefixEnd_4017468 : Nat := 4983230072969 + 3 ^ 40 * 4017468 * 2
def baseEnd_4017468 : Nat := 2062892098057192871674007

theorem tailTrace_4017468 : CollatzResearch.WordTrace tailWord_4017468 prefixEnd_4017468 2062892098057192871674007 := by
  unfold tailWord_4017468
  simp only [CollatzResearch.WordTrace]
  refine ⟨73264547904703519876998529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97686063872938026502664705 73264547904703519876998529)
  ·
    refine ⟨54948410928527639907748897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73264547904703519876998529 54948410928527639907748897)
    ·
      refine ⟨41211308196395729930811673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54948410928527639907748897 41211308196395729930811673)
      ·
        refine ⟨30908481147296797448108755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41211308196395729930811673 30908481147296797448108755)
        ·
          refine ⟨46362721720945196172163133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30908481147296797448108755 46362721720945196172163133)
          ·
            refine ⟨17386020645354448564561175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46362721720945196172163133 17386020645354448564561175)
            ·
              refine ⟨26079030968031672846841763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17386020645354448564561175 26079030968031672846841763)
              ·
                refine ⟨39118546452047509270262645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26079030968031672846841763 39118546452047509270262645)
                ·
                  refine ⟨3667363729879453994087123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39118546452047509270262645 3667363729879453994087123)
                  ·
                    refine ⟨5501045594819180991130685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3667363729879453994087123 5501045594819180991130685)
                    ·
                      refine ⟨2062892098057192871674007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5501045594819180991130685 2062892098057192871674007)
                      ·
                        rfl

theorem cell23_4017468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_4017468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017468 prefixEnd_4017468 := by exact prefixLift 4017468
  have htrace : WordTrace (prefixWord ++ tailWord_4017468) baseStart_4017468 baseEnd_4017468 := by
    simpa [prefixWord, tailWord_4017468, baseEnd_4017468] using wordTrace_append hprefix tailTrace_4017468
  have hstable : (prefixWord ++ tailWord_4017468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017468).length < 2 ^ (prefixWord ++ tailWord_4017468).sum := by decide
  have hdescent : baseEnd_4017468 < baseStart_4017468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017471 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 3, 5]
def baseStart_4017471 : Nat := 118140960795 + 4017471 * 2 ^ 59
def prefixEnd_4017471 : Nat := 4983230072969 + 3 ^ 40 * 4017471 * 2
def baseEnd_4017471 : Nat := 687631212833052119978831

theorem tailTrace_4017471 : CollatzResearch.WordTrace tailWord_4017471 prefixEnd_4017471 687631212833052119978831 := by
  unfold tailWord_4017471
  simp only [CollatzResearch.WordTrace]
  refine ⟨146529205228396171266356267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97686136818930780844237511 146529205228396171266356267)
  ·
    refine ⟨219793807842594256899534401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146529205228396171266356267 219793807842594256899534401)
    ·
      refine ⟨164845355881945692674650801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219793807842594256899534401 164845355881945692674650801)
      ·
        refine ⟨123634016911459269505988101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164845355881945692674650801 123634016911459269505988101)
        ·
          refine ⟨23181378170898613032372769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123634016911459269505988101 23181378170898613032372769)
          ·
            refine ⟨17386033628173959774279577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23181378170898613032372769 17386033628173959774279577)
            ·
              refine ⟨13039525221130469830709683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17386033628173959774279577 13039525221130469830709683)
              ·
                refine ⟨19559287831695704746064525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039525221130469830709683 19559287831695704746064525)
                ·
                  refine ⟨7334732936885889279774197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19559287831695704746064525 7334732936885889279774197)
                  ·
                    refine ⟨687631212833052119978831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7334732936885889279774197 687631212833052119978831)
                    ·
                      rfl

theorem cell23_4017471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_4017471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017471 prefixEnd_4017471 := by exact prefixLift 4017471
  have htrace : WordTrace (prefixWord ++ tailWord_4017471) baseStart_4017471 baseEnd_4017471 := by
    simpa [prefixWord, tailWord_4017471, baseEnd_4017471] using wordTrace_append hprefix tailTrace_4017471
  have hstable : (prefixWord ++ tailWord_4017471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017471).length < 2 ^ (prefixWord ++ tailWord_4017471).sum := by decide
  have hdescent : baseEnd_4017471 < baseStart_4017471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017585 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4017585 : Nat := 118140960795 + 4017585 * 2 ^ 59
def prefixEnd_4017585 : Nat := 4983230072969 + 3 ^ 40 * 4017585 * 2
def baseEnd_4017585 : Nat := 2062952175293768913910969

theorem tailTrace_4017585 : CollatzResearch.WordTrace tailWord_4017585 prefixEnd_4017585 2062952175293768913910969 := by
  unfold tailWord_4017585
  simp only [CollatzResearch.WordTrace]
  refine ⟨146533363149983168736006209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97688908766655445824004139 146533363149983168736006209)
  ·
    refine ⟨109900022362487376552004657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146533363149983168736006209 109900022362487376552004657)
    ·
      refine ⟨82425016771865532414003493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109900022362487376552004657 82425016771865532414003493)
      ·
        refine ⟨15454690644724787327625655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82425016771865532414003493 15454690644724787327625655)
        ·
          refine ⟨23182035967087180991438483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454690644724787327625655 23182035967087180991438483)
          ·
            refine ⟨34773053950630771487157725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23182035967087180991438483 34773053950630771487157725)
            ·
              refine ⟨13039895231486539307684147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34773053950630771487157725 13039895231486539307684147)
              ·
                refine ⟨19559842847229808961526221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039895231486539307684147 19559842847229808961526221)
                ·
                  refine ⟨7334941067711178360572333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19559842847229808961526221 7334941067711178360572333)
                  ·
                    refine ⟨2750602900391691885214625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7334941067711178360572333 2750602900391691885214625)
                    ·
                      refine ⟨2062952175293768913910969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750602900391691885214625 2062952175293768913910969)
                      ·
                        rfl

theorem cell23_4017585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4017585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017585 prefixEnd_4017585 := by exact prefixLift 4017585
  have htrace : WordTrace (prefixWord ++ tailWord_4017585) baseStart_4017585 baseEnd_4017585 := by
    simpa [prefixWord, tailWord_4017585, baseEnd_4017585] using wordTrace_append hprefix tailTrace_4017585
  have hstable : (prefixWord ++ tailWord_4017585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017585).length < 2 ^ (prefixWord ++ tailWord_4017585).sum := by decide
  have hdescent : baseEnd_4017585 < baseStart_4017585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017615 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 4, 2, 2]
def baseStart_4017615 : Nat := 118140960795 + 4017615 * 2 ^ 59
def prefixEnd_4017615 : Nat := 4983230072969 + 3 ^ 40 * 4017615 * 2
def baseEnd_4017615 : Nat := 2062967579713403796535831

theorem tailTrace_4017615 : CollatzResearch.WordTrace tailWord_4017615 prefixEnd_4017615 2062967579713403796535831 := by
  unfold tailWord_4017615
  simp only [CollatzResearch.WordTrace]
  refine ⟨146534457339874483859598299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97689638226582989239732199 146534457339874483859598299)
  ·
    refine ⟨219801686009811725789397449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146534457339874483859598299 219801686009811725789397449)
    ·
      refine ⟨164851264507358794342048087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219801686009811725789397449 164851264507358794342048087)
      ·
        refine ⟨247276896761038191513072131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164851264507358794342048087 247276896761038191513072131)
        ·
          refine ⟨370915345141557287269608197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247276896761038191513072131 370915345141557287269608197)
          ·
            refine ⟨69546627214041991363051537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370915345141557287269608197 69546627214041991363051537)
            ·
              refine ⟨52159970410531493522288653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69546627214041991363051537 52159970410531493522288653)
              ·
                refine ⟨19559988903949310070858245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52159970410531493522288653 19559988903949310070858245)
                ·
                  refine ⟨3667497919490495638285921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19559988903949310070858245 3667497919490495638285921)
                  ·
                    refine ⟨2750623439617871728714441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3667497919490495638285921 2750623439617871728714441)
                    ·
                      refine ⟨2062967579713403796535831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750623439617871728714441 2062967579713403796535831)
                      ·
                        rfl

theorem cell23_4017615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 2, 2].length) (baseStart_4017615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017615 prefixEnd_4017615 := by exact prefixLift 4017615
  have htrace : WordTrace (prefixWord ++ tailWord_4017615) baseStart_4017615 baseEnd_4017615 := by
    simpa [prefixWord, tailWord_4017615, baseEnd_4017615] using wordTrace_append hprefix tailTrace_4017615
  have hstable : (prefixWord ++ tailWord_4017615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017615).length < 2 ^ (prefixWord ++ tailWord_4017615).sum := by decide
  have hdescent : baseEnd_4017615 < baseStart_4017615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017666 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4017666 : Nat := 118140960795 + 4017666 * 2 ^ 59
def prefixEnd_4017666 : Nat := 4983230072969 + 3 ^ 40 * 4017666 * 2
def baseEnd_4017666 : Nat := 2062993767226783096998097

theorem tailTrace_4017666 : CollatzResearch.WordTrace tailWord_4017666 prefixEnd_4017666 2062993767226783096998097 := by
  unfold tailWord_4017666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36634079365672429892426213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97690878308459813046469901 36634079365672429892426213)
  ·
    refine ⟨6868889881063580604829915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36634079365672429892426213 6868889881063580604829915)
    ·
      refine ⟨10303334821595370907244873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6868889881063580604829915 10303334821595370907244873)
      ·
        refine ⟨7727501116196528180433655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10303334821595370907244873 7727501116196528180433655)
        ·
          refine ⟨11591251674294792270650483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727501116196528180433655 11591251674294792270650483)
          ·
            refine ⟨17386877511442188405975725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591251674294792270650483 17386877511442188405975725)
            ·
              refine ⟨6520079066790820652240897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17386877511442188405975725 6520079066790820652240897)
              ·
                refine ⟨4890059300093115489180673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6520079066790820652240897 4890059300093115489180673)
                ·
                  refine ⟨3667544475069836616885505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4890059300093115489180673 3667544475069836616885505)
                  ·
                    refine ⟨2750658356302377462664129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3667544475069836616885505 2750658356302377462664129)
                    ·
                      refine ⟨2062993767226783096998097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750658356302377462664129 2062993767226783096998097)
                      ·
                        rfl

theorem cell23_4017666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4017666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017666 prefixEnd_4017666 := by exact prefixLift 4017666
  have htrace : WordTrace (prefixWord ++ tailWord_4017666) baseStart_4017666 baseEnd_4017666 := by
    simpa [prefixWord, tailWord_4017666, baseEnd_4017666] using wordTrace_append hprefix tailTrace_4017666
  have hstable : (prefixWord ++ tailWord_4017666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017666).length < 2 ^ (prefixWord ++ tailWord_4017666).sum := by decide
  have hdescent : baseEnd_4017666 < baseStart_4017666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017728 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 6]
def baseStart_4017728 : Nat := 118140960795 + 4017728 * 2 ^ 59
def prefixEnd_4017728 : Nat := 4983230072969 + 3 ^ 40 * 4017728 * 2
def baseEnd_4017728 : Nat := 229225067003040206046979

theorem tailTrace_4017728 : CollatzResearch.WordTrace tailWord_4017728 prefixEnd_4017728 229225067003040206046979 := by
  unfold tailWord_4017728
  simp only [CollatzResearch.WordTrace]
  refine ⟨73269289394232552079230919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97692385858976736105641225 73269289394232552079230919)
  ·
    refine ⟨109903934091348828118846379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73269289394232552079230919 109903934091348828118846379)
    ·
      refine ⟨164855901137023242178269569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109903934091348828118846379 164855901137023242178269569)
      ·
        refine ⟨123641925852767431633702177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164855901137023242178269569 123641925852767431633702177)
        ·
          refine ⟨92731444389575573725276633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123641925852767431633702177 92731444389575573725276633)
          ·
            refine ⟨69548583292181680293957475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92731444389575573725276633 69548583292181680293957475)
            ·
              refine ⟨104322874938272520440936213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69548583292181680293957475 104322874938272520440936213)
              ·
                refine ⟨4890134762731524395668885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104322874938272520440936213 4890134762731524395668885)
                ·
                  refine ⟨229225067003040206046979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4890134762731524395668885 229225067003040206046979)
                  ·
                    rfl

theorem cell23_4017728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_4017728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017728 prefixEnd_4017728 := by exact prefixLift 4017728
  have htrace : WordTrace (prefixWord ++ tailWord_4017728) baseStart_4017728 baseEnd_4017728 := by
    simpa [prefixWord, tailWord_4017728, baseEnd_4017728] using wordTrace_append hprefix tailTrace_4017728
  have hstable : (prefixWord ++ tailWord_4017728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017728).length < 2 ^ (prefixWord ++ tailWord_4017728).sum := by decide
  have hdescent : baseEnd_4017728 < baseStart_4017728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017788 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_4017788 : Nat := 118140960795 + 4017788 * 2 ^ 59
def prefixEnd_4017788 : Nat := 4983230072969 + 3 ^ 40 * 4017788 * 2
def baseEnd_4017788 : Nat := 687685470622210539890845

theorem tailTrace_4017788 : CollatzResearch.WordTrace tailWord_4017788 prefixEnd_4017788 687685470622210539890845 := by
  unfold tailWord_4017788
  simp only [CollatzResearch.WordTrace]
  refine ⟨73270383584123867202823009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97693844778831822937097345 73270383584123867202823009)
  ·
    refine ⟨54952787688092900402117257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73270383584123867202823009 54952787688092900402117257)
    ·
      refine ⟨41214590766069675301587943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54952787688092900402117257 41214590766069675301587943)
      ·
        refine ⟨61821886149104512952381915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41214590766069675301587943 61821886149104512952381915)
        ·
          refine ⟨92732829223656769428572873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61821886149104512952381915 92732829223656769428572873)
          ·
            refine ⟨69549621917742577071429655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92732829223656769428572873 69549621917742577071429655)
            ·
              refine ⟨104324432876613865607144483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69549621917742577071429655 104324432876613865607144483)
              ·
                refine ⟨156486649314920798410716725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104324432876613865607144483 156486649314920798410716725)
                ·
                  refine ⟨14670623373273824851004693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156486649314920798410716725 14670623373273824851004693)
                  ·
                    refine ⟨687685470622210539890845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14670623373273824851004693 687685470622210539890845)
                    ·
                      rfl

theorem cell23_4017788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_4017788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017788 prefixEnd_4017788 := by exact prefixLift 4017788
  have htrace : WordTrace (prefixWord ++ tailWord_4017788) baseStart_4017788 baseEnd_4017788 := by
    simpa [prefixWord, tailWord_4017788, baseEnd_4017788] using wordTrace_append hprefix tailTrace_4017788
  have hstable : (prefixWord ++ tailWord_4017788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017788).length < 2 ^ (prefixWord ++ tailWord_4017788).sum := by decide
  have hdescent : baseEnd_4017788 < baseStart_4017788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017795 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 6, 2]
def baseStart_4017795 : Nat := 118140960795 + 4017795 * 2 ^ 59
def prefixEnd_4017795 : Nat := 4983230072969 + 3 ^ 40 * 4017795 * 2
def baseEnd_4017795 : Nat := 2063060006231213092285003

theorem tailTrace_4017795 : CollatzResearch.WordTrace tailWord_4017795 prefixEnd_4017795 2063060006231213092285003 := by
  unfold tailWord_4017795
  simp only [CollatzResearch.WordTrace]
  refine ⟨146541022479222374601150839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97694014986148249734100559 146541022479222374601150839)
  ·
    refine ⟨219811533718833561901726259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146541022479222374601150839 219811533718833561901726259)
    ·
      refine ⟨329717300578250342852589389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219811533718833561901726259 329717300578250342852589389)
      ·
        refine ⟨123643987716843878569721021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329717300578250342852589389 123643987716843878569721021)
        ·
          refine ⟨46366495393816454463645383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123643987716843878569721021 46366495393816454463645383)
          ·
            refine ⟨69549743090724681695468075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46366495393816454463645383 69549743090724681695468075)
            ·
              refine ⟨104324614636087022543202113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69549743090724681695468075 104324614636087022543202113)
              ·
                refine ⟨78243460977065266907401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104324614636087022543202113 78243460977065266907401585)
                ·
                  refine ⟨58682595732798950180551189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78243460977065266907401585 58682595732798950180551189)
                  ·
                    refine ⟨2750746674974950789713337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58682595732798950180551189 2750746674974950789713337)
                    ·
                      refine ⟨2063060006231213092285003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2750746674974950789713337 2063060006231213092285003)
                      ·
                        rfl

theorem cell23_4017795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_4017795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017795 prefixEnd_4017795 := by exact prefixLift 4017795
  have htrace : WordTrace (prefixWord ++ tailWord_4017795) baseStart_4017795 baseEnd_4017795 := by
    simpa [prefixWord, tailWord_4017795, baseEnd_4017795] using wordTrace_append hprefix tailTrace_4017795
  have hstable : (prefixWord ++ tailWord_4017795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017795).length < 2 ^ (prefixWord ++ tailWord_4017795).sum := by decide
  have hdescent : baseEnd_4017795 < baseStart_4017795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017808 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_4017808 : Nat := 118140960795 + 4017808 * 2 ^ 59
def prefixEnd_4017808 : Nat := 4983230072969 + 3 ^ 40 * 4017808 * 2
def baseEnd_4017808 : Nat := 2063066681479721541422443

theorem tailTrace_4017808 : CollatzResearch.WordTrace tailWord_4017808 prefixEnd_4017808 2063066681479721541422443 := by
  unfold tailWord_4017808
  simp only [CollatzResearch.WordTrace]
  refine ⟨73270748314087638910687039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97694331085450185214249385 73270748314087638910687039)
  ·
    refine ⟨109906122471131458366030559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73270748314087638910687039 109906122471131458366030559)
    ·
      refine ⟨164859183706697187549045839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109906122471131458366030559 164859183706697187549045839)
      ·
        refine ⟨247288775560045781323568759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164859183706697187549045839 247288775560045781323568759)
        ·
          refine ⟨370933163340068671985353139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247288775560045781323568759 370933163340068671985353139)
          ·
            refine ⟨556399745010103007978029709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370933163340068671985353139 556399745010103007978029709)
            ·
              refine ⟨208649904378788627991761141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556399745010103007978029709 208649904378788627991761141)
              ·
                refine ⟨19560928535511433874227607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208649904378788627991761141 19560928535511433874227607)
                ·
                  refine ⟨29341392803267150811341411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19560928535511433874227607 29341392803267150811341411)
                  ·
                    refine ⟨44012089204900726217012117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29341392803267150811341411 44012089204900726217012117)
                    ·
                      refine ⟨2063066681479721541422443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44012089204900726217012117 2063066681479721541422443)
                      ·
                        rfl

theorem cell23_4017808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_4017808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017808 prefixEnd_4017808 := by exact prefixLift 4017808
  have htrace : WordTrace (prefixWord ++ tailWord_4017808) baseStart_4017808 baseEnd_4017808 := by
    simpa [prefixWord, tailWord_4017808, baseEnd_4017808] using wordTrace_append hprefix tailTrace_4017808
  have hstable : (prefixWord ++ tailWord_4017808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017808).length < 2 ^ (prefixWord ++ tailWord_4017808).sum := by decide
  have hdescent : baseEnd_4017808 < baseStart_4017808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017822 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4017822 : Nat := 118140960795 + 4017822 * 2 ^ 59
def prefixEnd_4017822 : Nat := 4983230072969 + 3 ^ 40 * 4017822 * 2
def baseEnd_4017822 : Nat := 687691290069628162215793

theorem tailTrace_4017822 : CollatzResearch.WordTrace tailWord_4017822 prefixEnd_4017822 687691290069628162215793 := by
  unfold tailWord_4017822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317750906265569776547965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97694671500083038808255813 18317750906265569776547965)
  ·
    refine ⟨6869156589849588666205487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18317750906265569776547965 6869156589849588666205487)
    ·
      refine ⟨10303734884774382999308231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869156589849588666205487 10303734884774382999308231)
      ·
        refine ⟨15455602327161574498962347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303734884774382999308231 15455602327161574498962347)
        ·
          refine ⟨23183403490742361748443521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15455602327161574498962347 23183403490742361748443521)
          ·
            refine ⟨17387552618056771311332641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23183403490742361748443521 17387552618056771311332641)
            ·
              refine ⟨13040664463542578483499481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17387552618056771311332641 13040664463542578483499481)
              ·
                refine ⟨9780498347656933862624611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13040664463542578483499481 9780498347656933862624611)
                ·
                  refine ⟨14670747521485400793936917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9780498347656933862624611 14670747521485400793936917)
                  ·
                    refine ⟨687691290069628162215793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14670747521485400793936917 687691290069628162215793)
                    ·
                      rfl

theorem cell23_4017822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4017822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017822 prefixEnd_4017822 := by exact prefixLift 4017822
  have htrace : WordTrace (prefixWord ++ tailWord_4017822) baseStart_4017822 baseEnd_4017822 := by
    simpa [prefixWord, tailWord_4017822, baseEnd_4017822] using wordTrace_append hprefix tailTrace_4017822
  have hstable : (prefixWord ++ tailWord_4017822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017822).length < 2 ^ (prefixWord ++ tailWord_4017822).sum := by decide
  have hdescent : baseEnd_4017822 < baseStart_4017822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017823 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4017823 : Nat := 118140960795 + 4017823 * 2 ^ 59
def prefixEnd_4017823 : Nat := 4983230072969 + 3 ^ 40 * 4017823 * 2
def baseEnd_4017823 : Nat := 2063074383689538982734875

theorem tailTrace_4017823 : CollatzResearch.WordTrace tailWord_4017823 prefixEnd_4017823 2063074383689538982734875 := by
  unfold tailWord_4017823
  simp only [CollatzResearch.WordTrace]
  refine ⟨146542043723120935383170123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97694695815413956922113415 146542043723120935383170123)
  ·
    refine ⟨219813065584681403074755185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146542043723120935383170123 219813065584681403074755185)
    ·
      refine ⟨164859799188511052306066389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219813065584681403074755185 164859799188511052306066389)
      ·
        refine ⟨3863901543480727788423431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 164859799188511052306066389 3863901543480727788423431)
        ·
          refine ⟨5795852315221091682635147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863901543480727788423431 5795852315221091682635147)
          ·
            refine ⟨8693778472831637523952721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795852315221091682635147 8693778472831637523952721)
            ·
              refine ⟨6520333854623728142964541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8693778472831637523952721 6520333854623728142964541)
              ·
                refine ⟨2445125195483898053611703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6520333854623728142964541 2445125195483898053611703)
                ·
                  refine ⟨3667687793225847080417555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445125195483898053611703 3667687793225847080417555)
                  ·
                    refine ⟨5501531689838770620626333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3667687793225847080417555 5501531689838770620626333)
                    ·
                      refine ⟨2063074383689538982734875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5501531689838770620626333 2063074383689538982734875)
                      ·
                        rfl

theorem cell23_4017823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4017823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017823 prefixEnd_4017823 := by exact prefixLift 4017823
  have htrace : WordTrace (prefixWord ++ tailWord_4017823) baseStart_4017823 baseEnd_4017823 := by
    simpa [prefixWord, tailWord_4017823, baseEnd_4017823] using wordTrace_append hprefix tailTrace_4017823
  have hstable : (prefixWord ++ tailWord_4017823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017823).length < 2 ^ (prefixWord ++ tailWord_4017823).sum := by decide
  have hdescent : baseEnd_4017823 < baseStart_4017823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017848 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_4017848 : Nat := 118140960795 + 4017848 * 2 ^ 59
def prefixEnd_4017848 : Nat := 4983230072969 + 3 ^ 40 * 4017848 * 2
def baseEnd_4017848 : Nat := 687695740235300461640753

theorem tailTrace_4017848 : CollatzResearch.WordTrace tailWord_4017848 prefixEnd_4017848 687695740235300461640753 := by
  unfold tailWord_4017848
  simp only [CollatzResearch.WordTrace]
  refine ⟨73271477774015182326415099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97695303698686909768553465 73271477774015182326415099)
  ·
    refine ⟨109907216661022773489622649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73271477774015182326415099 109907216661022773489622649)
    ·
      refine ⟨82430412495767080117216987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109907216661022773489622649 82430412495767080117216987)
      ·
        refine ⟨123645618743650620175825481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82430412495767080117216987 123645618743650620175825481)
        ·
          refine ⟨92734214057737965131869111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123645618743650620175825481 92734214057737965131869111)
          ·
            refine ⟨139101321086606947697803667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92734214057737965131869111 139101321086606947697803667)
            ·
              refine ⟨208651981629910421546705501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139101321086606947697803667 208651981629910421546705501)
              ·
                refine ⟨78244493111216408080014563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208651981629910421546705501 78244493111216408080014563)
                ·
                  refine ⟨117366739666824612120021845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78244493111216408080014563 117366739666824612120021845)
                  ·
                    refine ⟨687695740235300461640753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117366739666824612120021845 687695740235300461640753)
                    ·
                      rfl

theorem cell23_4017848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_4017848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017848 prefixEnd_4017848 := by exact prefixLift 4017848
  have htrace : WordTrace (prefixWord ++ tailWord_4017848) baseStart_4017848 baseEnd_4017848 := by
    simpa [prefixWord, tailWord_4017848, baseEnd_4017848] using wordTrace_append hprefix tailTrace_4017848
  have hstable : (prefixWord ++ tailWord_4017848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017848).length < 2 ^ (prefixWord ++ tailWord_4017848).sum := by decide
  have hdescent : baseEnd_4017848 < baseStart_4017848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017869 : List Nat := [1, 6, 2, 1, 1, 1, 4, 7]
def baseStart_4017869 : Nat := 118140960795 + 4017869 * 2 ^ 59
def prefixEnd_4017869 : Nat := 4983230072969 + 3 ^ 40 * 4017869 * 2
def baseEnd_4017869 : Nat := 76411037177764659361469

theorem tailTrace_4017869 : CollatzResearch.WordTrace tailWord_4017869 prefixEnd_4017869 76411037177764659361469 := by
  unfold tailWord_4017869
  simp only [CollatzResearch.WordTrace]
  refine ⟨146543721480954285239344661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97695814320636190159563107 146543721480954285239344661)
  ·
    refine ⟨6869236944419732120594281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146543721480954285239344661 6869236944419732120594281)
    ·
      refine ⟨5151927708314799090445711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6869236944419732120594281 5151927708314799090445711)
      ·
        refine ⟨7727891562472198635668567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151927708314799090445711 7727891562472198635668567)
        ·
          refine ⟨11591837343708297953502851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727891562472198635668567 11591837343708297953502851)
          ·
            refine ⟨17387756015562446930254277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591837343708297953502851 17387756015562446930254277)
            ·
              refine ⟨3260204252917958799422677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17387756015562446930254277 3260204252917958799422677)
              ·
                refine ⟨76411037177764659361469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3260204252917958799422677 76411037177764659361469)
                ·
                  rfl

theorem cell23_4017869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 7].length) (baseStart_4017869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017869 prefixEnd_4017869 := by exact prefixLift 4017869
  have htrace : WordTrace (prefixWord ++ tailWord_4017869) baseStart_4017869 baseEnd_4017869 := by
    simpa [prefixWord, tailWord_4017869, baseEnd_4017869] using wordTrace_append hprefix tailTrace_4017869
  have hstable : (prefixWord ++ tailWord_4017869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017869).length < 2 ^ (prefixWord ++ tailWord_4017869).sum := by decide
  have hdescent : baseEnd_4017869 < baseStart_4017869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017922 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4017922 : Nat := 118140960795 + 4017922 * 2 ^ 59
def prefixEnd_4017922 : Nat := 4983230072969 + 3 ^ 40 * 4017922 * 2
def baseEnd_4017922 : Nat := 2063125218274334095396919

theorem tailTrace_4017922 : CollatzResearch.WordTrace tailWord_4017922 prefixEnd_4017922 2063125218274334095396919 := by
  unfold tailWord_4017922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36636413637440568822756005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97697103033174850194016013 36636413637440568822756005)
  ·
    refine ⟨6869327557020106654266751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36636413637440568822756005 6869327557020106654266751)
    ·
      refine ⟨10303991335530159981400127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869327557020106654266751 10303991335530159981400127)
      ·
        refine ⟨15455987003295239972100191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303991335530159981400127 15455987003295239972100191)
        ·
          refine ⟨23183980504942859958150287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15455987003295239972100191 23183980504942859958150287)
          ·
            refine ⟨34775970757414289937225431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23183980504942859958150287 34775970757414289937225431)
            ·
              refine ⟨52163956136121434905838147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34775970757414289937225431 52163956136121434905838147)
              ·
                refine ⟨78245934204182152358757221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52163956136121434905838147 78245934204182152358757221)
                ·
                  refine ⟨14671112663284153567266979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78245934204182152358757221 14671112663284153567266979)
                  ·
                    refine ⟨22006668994926230350900469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14671112663284153567266979 22006668994926230350900469)
                    ·
                      refine ⟨2063125218274334095396919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22006668994926230350900469 2063125218274334095396919)
                      ·
                        rfl

theorem cell23_4017922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4017922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017922 prefixEnd_4017922 := by exact prefixLift 4017922
  have htrace : WordTrace (prefixWord ++ tailWord_4017922) baseStart_4017922 baseEnd_4017922 := by
    simpa [prefixWord, tailWord_4017922, baseEnd_4017922] using wordTrace_append hprefix tailTrace_4017922
  have hstable : (prefixWord ++ tailWord_4017922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017922).length < 2 ^ (prefixWord ++ tailWord_4017922).sum := by decide
  have hdescent : baseEnd_4017922 < baseStart_4017922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017935 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_4017935 : Nat := 118140960795 + 4017935 * 2 ^ 59
def prefixEnd_4017935 : Nat := 4983230072969 + 3 ^ 40 * 4017935 * 2
def baseEnd_4017935 : Nat := 2063131893522842544534359

theorem tailTrace_4017935 : CollatzResearch.WordTrace tailWord_4017935 prefixEnd_4017935 2063131893522842544534359 := by
  unfold tailWord_4017935
  simp only [CollatzResearch.WordTrace]
  refine ⟨146546128698715178511247259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97697419132476785674164839 146546128698715178511247259)
  ·
    refine ⟨219819193048072767766870889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146546128698715178511247259 219819193048072767766870889)
    ·
      refine ⟨164864394786054575825153167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219819193048072767766870889 164864394786054575825153167)
      ·
        refine ⟨247296592179081863737729751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164864394786054575825153167 247296592179081863737729751)
        ·
          refine ⟨370944888268622795606594627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247296592179081863737729751 370944888268622795606594627)
          ·
            refine ⟨556417332402934193409891941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370944888268622795606594627 556417332402934193409891941)
            ·
              refine ⟨104328249825550161264354739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556417332402934193409891941 104328249825550161264354739)
              ·
                refine ⟨156492374738325241896532109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104328249825550161264354739 156492374738325241896532109)
                ·
                  refine ⟨58684640526871965711199541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156492374738325241896532109 58684640526871965711199541)
                  ·
                    refine ⟨5501685049394246785424957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58684640526871965711199541 5501685049394246785424957)
                    ·
                      refine ⟨2063131893522842544534359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5501685049394246785424957 2063131893522842544534359)
                      ·
                        rfl

theorem cell23_4017935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_4017935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017935 prefixEnd_4017935 := by exact prefixLift 4017935
  have htrace : WordTrace (prefixWord ++ tailWord_4017935) baseStart_4017935 baseEnd_4017935 := by
    simpa [prefixWord, tailWord_4017935, baseEnd_4017935] using wordTrace_append hprefix tailTrace_4017935
  have hstable : (prefixWord ++ tailWord_4017935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017935).length < 2 ^ (prefixWord ++ tailWord_4017935).sum := by decide
  have hdescent : baseEnd_4017935 < baseStart_4017935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017952 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_4017952 : Nat := 118140960795 + 4017952 * 2 ^ 59
def prefixEnd_4017952 : Nat := 4983230072969 + 3 ^ 40 * 4017952 * 2
def baseEnd_4017952 : Nat := 2063140622693968978021781

theorem tailTrace_4017952 : CollatzResearch.WordTrace tailWord_4017952 prefixEnd_4017952 2063140622693968978021781 := by
  unfold tailWord_4017952
  simp only [CollatzResearch.WordTrace]
  refine ⟨73273374369826795207308055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97697832493102393609744073 73273374369826795207308055)
  ·
    refine ⟨109910061554740192810962083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73273374369826795207308055 109910061554740192810962083)
    ·
      refine ⟨164865092332110289216443125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109910061554740192810962083 164865092332110289216443125)
      ·
        refine ⟨15456102406135339614041543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164865092332110289216443125 15456102406135339614041543)
        ·
          refine ⟨23184153609203009421062315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15456102406135339614041543 23184153609203009421062315)
          ·
            refine ⟨34776230413804514131593473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23184153609203009421062315 34776230413804514131593473)
            ·
              refine ⟨26082172810353385598695105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34776230413804514131593473 26082172810353385598695105)
              ·
                refine ⟨19561629607765039199021329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26082172810353385598695105 19561629607765039199021329)
                ·
                  refine ⟨14671222205823779399265997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19561629607765039199021329 14671222205823779399265997)
                  ·
                    refine ⟨5501708327183917274724749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14671222205823779399265997 5501708327183917274724749)
                    ·
                      refine ⟨2063140622693968978021781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5501708327183917274724749 2063140622693968978021781)
                      ·
                        rfl

theorem cell23_4017952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_4017952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017952 prefixEnd_4017952 := by exact prefixLift 4017952
  have htrace : WordTrace (prefixWord ++ tailWord_4017952) baseStart_4017952 baseEnd_4017952 := by
    simpa [prefixWord, tailWord_4017952, baseEnd_4017952] using wordTrace_append hprefix tailTrace_4017952
  have hstable : (prefixWord ++ tailWord_4017952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017952).length < 2 ^ (prefixWord ++ tailWord_4017952).sum := by decide
  have hdescent : baseEnd_4017952 < baseStart_4017952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017992 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_4017992 : Nat := 118140960795 + 4017992 * 2 ^ 59
def prefixEnd_4017992 : Nat := 4983230072969 + 3 ^ 40 * 4017992 * 2
def baseEnd_4017992 : Nat := 2063161161920148821521597

theorem tailTrace_4017992 : CollatzResearch.WordTrace tailWord_4017992 prefixEnd_4017992 2063161161920148821521597 := by
  unfold tailWord_4017992
  simp only [CollatzResearch.WordTrace]
  refine ⟨73274103829754338623036115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97698805106339118164048153 73274103829754338623036115)
  ·
    refine ⟨109911155744631507934554173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73274103829754338623036115 109911155744631507934554173)
    ·
      refine ⟨41216683404236815475457815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109911155744631507934554173 41216683404236815475457815)
      ·
        refine ⟨61825025106355223213186723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41216683404236815475457815 61825025106355223213186723)
        ·
          refine ⟨92737537659532834819780085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61825025106355223213186723 92737537659532834819780085)
          ·
            refine ⟨8694144155581203264354383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92737537659532834819780085 8694144155581203264354383)
            ·
              refine ⟨13041216233371804896531575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694144155581203264354383 13041216233371804896531575)
              ·
                refine ⟨19561824350057707344797363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041216233371804896531575 19561824350057707344797363)
                ·
                  refine ⟨29342736525086561017196045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19561824350057707344797363 29342736525086561017196045)
                  ·
                    refine ⟨11003526196907460381448517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29342736525086561017196045 11003526196907460381448517)
                    ·
                      refine ⟨2063161161920148821521597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11003526196907460381448517 2063161161920148821521597)
                      ·
                        rfl

theorem cell23_4017992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_4017992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4017992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4017992 prefixEnd_4017992 := by exact prefixLift 4017992
  have htrace : WordTrace (prefixWord ++ tailWord_4017992) baseStart_4017992 baseEnd_4017992 := by
    simpa [prefixWord, tailWord_4017992, baseEnd_4017992] using wordTrace_append hprefix tailTrace_4017992
  have hstable : (prefixWord ++ tailWord_4017992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017992).length < 2 ^ (prefixWord ++ tailWord_4017992).sum := by decide
  have hdescent : baseEnd_4017992 < baseStart_4017992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018035 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_4018035 : Nat := 118140960795 + 4018035 * 2 ^ 59
def prefixEnd_4018035 : Nat := 4983230072969 + 3 ^ 40 * 4018035 * 2
def baseEnd_4018035 : Nat := 2063183241588292153283899

theorem tailTrace_4018035 : CollatzResearch.WordTrace tailWord_4018035 prefixEnd_4018035 2063183241588292153283899 := by
  unfold tailWord_4018035
  simp only [CollatzResearch.WordTrace]
  refine ⟨146549775998352895589887559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97699850665568597059925039 146549775998352895589887559)
  ·
    refine ⟨219824663997529343384831339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146549775998352895589887559 219824663997529343384831339)
    ·
      refine ⟨329736995996294015077247009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219824663997529343384831339 329736995996294015077247009)
      ·
        refine ⟨247302746997220511307935257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329736995996294015077247009 247302746997220511307935257)
        ·
          refine ⟨185477060247915383480951443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247302746997220511307935257 185477060247915383480951443)
          ·
            refine ⟨278215590371873075221427165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185477060247915383480951443 278215590371873075221427165)
            ·
              refine ⟨104330846389452403208035187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278215590371873075221427165 104330846389452403208035187)
              ·
                refine ⟨156496269584178604812052781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104330846389452403208035187 156496269584178604812052781)
                ·
                  refine ⟨58686101094066976804519793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156496269584178604812052781 58686101094066976804519793)
                  ·
                    refine ⟨44014575820550232603389845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58686101094066976804519793 44014575820550232603389845)
                    ·
                      refine ⟨2063183241588292153283899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44014575820550232603389845 2063183241588292153283899)
                      ·
                        rfl

theorem cell23_4018035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_4018035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018035 prefixEnd_4018035 := by exact prefixLift 4018035
  have htrace : WordTrace (prefixWord ++ tailWord_4018035) baseStart_4018035 baseEnd_4018035 := by
    simpa [prefixWord, tailWord_4018035, baseEnd_4018035] using wordTrace_append hprefix tailTrace_4018035
  have hstable : (prefixWord ++ tailWord_4018035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018035).length < 2 ^ (prefixWord ++ tailWord_4018035).sum := by decide
  have hdescent : baseEnd_4018035 < baseStart_4018035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018046 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4018046 : Nat := 118140960795 + 4018046 * 2 ^ 59
def prefixEnd_4018046 : Nat := 4983230072969 + 3 ^ 40 * 4018046 * 2
def baseEnd_4018046 : Nat := 2063188889875491610246349

theorem tailTrace_4018046 : CollatzResearch.WordTrace tailWord_4018046 prefixEnd_4018046 2063188889875491610246349 := by
  unfold tailWord_4018046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318772150164130558567249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97700118134208696312358661 18318772150164130558567249)
  ·
    refine ⟨13739079112623097918925437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18318772150164130558567249 13739079112623097918925437)
    ·
      refine ⟨5152154667233661719597039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13739079112623097918925437 5152154667233661719597039)
      ·
        refine ⟨7728232000850492579395559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152154667233661719597039 7728232000850492579395559)
        ·
          refine ⟨11592348001275738869093339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728232000850492579395559 11592348001275738869093339)
          ·
            refine ⟨17388522001913608303640009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11592348001275738869093339 17388522001913608303640009)
            ·
              refine ⟨13041391501435206227730007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17388522001913608303640009 13041391501435206227730007)
              ·
                refine ⟨19562087252152809341595011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041391501435206227730007 19562087252152809341595011)
                ·
                  refine ⟨29343130878229214012392517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19562087252152809341595011 29343130878229214012392517)
                  ·
                    refine ⟨5501837039667977627323597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29343130878229214012392517 5501837039667977627323597)
                    ·
                      refine ⟨2063188889875491610246349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5501837039667977627323597 2063188889875491610246349)
                      ·
                        rfl

theorem cell23_4018046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4018046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018046 prefixEnd_4018046 := by exact prefixLift 4018046
  have htrace : WordTrace (prefixWord ++ tailWord_4018046) baseStart_4018046 baseEnd_4018046 := by
    simpa [prefixWord, tailWord_4018046, baseEnd_4018046] using wordTrace_append hprefix tailTrace_4018046
  have hstable : (prefixWord ++ tailWord_4018046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018046).length < 2 ^ (prefixWord ++ tailWord_4018046).sum := by decide
  have hdescent : baseEnd_4018046 < baseStart_4018046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018109 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_4018109 : Nat := 118140960795 + 4018109 * 2 ^ 59
def prefixEnd_4018109 : Nat := 4983230072969 + 3 ^ 40 * 4018109 * 2
def baseEnd_4018109 : Nat := 687740413052241621252853

theorem tailTrace_4018109 : CollatzResearch.WordTrace tailWord_4018109 prefixEnd_4018109 687740413052241621252853 := by
  unfold tailWord_4018109
  simp only [CollatzResearch.WordTrace]
  refine ⟨146552475000084806228081381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97701650000056537485387587 146552475000084806228081381)
  ·
    refine ⟨27478589062515901167765259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146552475000084806228081381 27478589062515901167765259)
    ·
      refine ⟨41217883593773851751647889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27478589062515901167765259 41217883593773851751647889)
      ·
        refine ⟨30913412695330388813735917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41217883593773851751647889 30913412695330388813735917)
        ·
          refine ⟨11592529760748895805150969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30913412695330388813735917 11592529760748895805150969)
          ·
            refine ⟨8694397320561671853863227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11592529760748895805150969 8694397320561671853863227)
            ·
              refine ⟨13041595980842507780794841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694397320561671853863227 13041595980842507780794841)
              ·
                refine ⟨9781196985631880835596131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13041595980842507780794841 9781196985631880835596131)
                ·
                  refine ⟨14671795478447821253394197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781196985631880835596131 14671795478447821253394197)
                  ·
                    refine ⟨687740413052241621252853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14671795478447821253394197 687740413052241621252853)
                    ·
                      rfl

theorem cell23_4018109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_4018109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018109 prefixEnd_4018109 := by exact prefixLift 4018109
  have htrace : WordTrace (prefixWord ++ tailWord_4018109) baseStart_4018109 baseEnd_4018109 := by
    simpa [prefixWord, tailWord_4018109, baseEnd_4018109] using wordTrace_append hprefix tailTrace_4018109
  have hstable : (prefixWord ++ tailWord_4018109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018109).length < 2 ^ (prefixWord ++ tailWord_4018109).sum := by decide
  have hdescent : baseEnd_4018109 < baseStart_4018109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018126 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_4018126 : Nat := 118140960795 + 4018126 * 2 ^ 59
def prefixEnd_4018126 : Nat := 4983230072969 + 3 ^ 40 * 4018126 * 2
def baseEnd_4018126 : Nat := 687743322775950432415327

theorem tailTrace_4018126 : CollatzResearch.WordTrace tailWord_4018126 prefixEnd_4018126 687743322775950432415327 := by
  unfold tailWord_4018126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18319136880127902266431279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97702063360682145420966821 18319136880127902266431279)
  ·
    refine ⟨27478705320191853399646919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18319136880127902266431279 27478705320191853399646919)
    ·
      refine ⟨41218057980287780099470379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27478705320191853399646919 41218057980287780099470379)
      ·
        refine ⟨61827086970431670149205569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41218057980287780099470379 61827086970431670149205569)
        ·
          refine ⟨46370315227823752611904177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61827086970431670149205569 46370315227823752611904177)
          ·
            refine ⟨34777736420867814458928133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46370315227823752611904177 34777736420867814458928133)
            ·
              refine ⟨6520825578912715211049025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34777736420867814458928133 6520825578912715211049025)
              ·
                refine ⟨4890619184184536408286769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6520825578912715211049025 4890619184184536408286769)
                ·
                  refine ⟨3667964388138402306215077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4890619184184536408286769 3667964388138402306215077)
                  ·
                    refine ⟨687743322775950432415327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3667964388138402306215077 687743322775950432415327)
                    ·
                      rfl

theorem cell23_4018126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_4018126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018126 prefixEnd_4018126 := by exact prefixLift 4018126
  have htrace : WordTrace (prefixWord ++ tailWord_4018126) baseStart_4018126 baseEnd_4018126 := by
    simpa [prefixWord, tailWord_4018126, baseEnd_4018126] using wordTrace_append hprefix tailTrace_4018126
  have hstable : (prefixWord ++ tailWord_4018126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018126).length < 2 ^ (prefixWord ++ tailWord_4018126).sum := by decide
  have hdescent : baseEnd_4018126 < baseStart_4018126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018152 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_4018152 : Nat := 118140960795 + 4018152 * 2 ^ 59
def prefixEnd_4018152 : Nat := 4983230072969 + 3 ^ 40 * 4018152 * 2
def baseEnd_4018152 : Nat := 687747772941622731840287

theorem tailTrace_4018152 : CollatzResearch.WordTrace tailWord_4018152 prefixEnd_4018152 687747772941622731840287 := by
  unfold tailWord_4018152
  simp only [CollatzResearch.WordTrace]
  refine ⟨73277021669464512285948355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97702695559286016381264473 73277021669464512285948355)
  ·
    refine ⟨109915532504196768428922533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73277021669464512285948355 109915532504196768428922533)
    ·
      refine ⟨20609162344536894080422975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109915532504196768428922533 20609162344536894080422975)
      ·
        refine ⟨30913743516805341120634463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20609162344536894080422975 30913743516805341120634463)
        ·
          refine ⟨46370615275208011680951695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30913743516805341120634463 46370615275208011680951695)
          ·
            refine ⟨69555922912812017521427543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46370615275208011680951695 69555922912812017521427543)
            ·
              refine ⟨104333884369218026282141315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69555922912812017521427543 104333884369218026282141315)
              ·
                refine ⟨156500826553827039423211973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104333884369218026282141315 156500826553827039423211973)
                ·
                  refine ⟨29343904978842569891852245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156500826553827039423211973 29343904978842569891852245)
                  ·
                    refine ⟨687747772941622731840287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29343904978842569891852245 687747772941622731840287)
                    ·
                      rfl

theorem cell23_4018152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_4018152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018152 prefixEnd_4018152 := by exact prefixLift 4018152
  have htrace : WordTrace (prefixWord ++ tailWord_4018152) baseStart_4018152 baseEnd_4018152 := by
    simpa [prefixWord, tailWord_4018152, baseEnd_4018152] using wordTrace_append hprefix tailTrace_4018152
  have hstable : (prefixWord ++ tailWord_4018152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018152).length < 2 ^ (prefixWord ++ tailWord_4018152).sum := by decide
  have hdescent : baseEnd_4018152 < baseStart_4018152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018183 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_4018183 : Nat := 118140960795 + 4018183 * 2 ^ 59
def prefixEnd_4018183 : Nat := 4983230072969 + 3 ^ 40 * 4018183 * 2
def baseEnd_4018183 : Nat := 2063259236725157574233219

theorem tailTrace_4018183 : CollatzResearch.WordTrace tailWord_4018183 prefixEnd_4018183 2063259236725157574233219 := by
  unfold tailWord_4018183
  simp only [CollatzResearch.WordTrace]
  refine ⟨146555174001816716866275203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97703449334544477910850135 146555174001816716866275203)
  ·
    refine ⟨219832761002725075299412805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146555174001816716866275203 219832761002725075299412805)
    ·
      refine ⟨41218642688010951618639901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219832761002725075299412805 41218642688010951618639901)
      ·
        refine ⟨15456991008004106856989963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41218642688010951618639901 15456991008004106856989963)
        ·
          refine ⟨23185486512006160285484945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15456991008004106856989963 23185486512006160285484945)
          ·
            refine ⟨17389114884004620214113709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23185486512006160285484945 17389114884004620214113709)
            ·
              refine ⟨6520918081501732580292641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17389114884004620214113709 6520918081501732580292641)
              ·
                refine ⟨4890688561126299435219481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6520918081501732580292641 4890688561126299435219481)
                ·
                  refine ⟨3668016420844724576414611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4890688561126299435219481 3668016420844724576414611)
                  ·
                    refine ⟨5502024631267086864621917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668016420844724576414611 5502024631267086864621917)
                    ·
                      refine ⟨2063259236725157574233219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502024631267086864621917 2063259236725157574233219)
                      ·
                        rfl

theorem cell23_4018183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_4018183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018183 prefixEnd_4018183 := by exact prefixLift 4018183
  have htrace : WordTrace (prefixWord ++ tailWord_4018183) baseStart_4018183 baseEnd_4018183 := by
    simpa [prefixWord, tailWord_4018183, baseEnd_4018183] using wordTrace_append hprefix tailTrace_4018183
  have hstable : (prefixWord ++ tailWord_4018183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018183).length < 2 ^ (prefixWord ++ tailWord_4018183).sum := by decide
  have hdescent : baseEnd_4018183 < baseStart_4018183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018192 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_4018192 : Nat := 118140960795 + 4018192 * 2 ^ 59
def prefixEnd_4018192 : Nat := 4983230072969 + 3 ^ 40 * 4018192 * 2
def baseEnd_4018192 : Nat := 2063263858051048039020677

theorem tailTrace_4018192 : CollatzResearch.WordTrace tailWord_4018192 prefixEnd_4018192 2063263858051048039020677 := by
  unfold tailWord_4018192
  simp only [CollatzResearch.WordTrace]
  refine ⟨73277751129392055701676415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97703668172522740935568553 73277751129392055701676415)
  ·
    refine ⟨109916626694088083552514623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73277751129392055701676415 109916626694088083552514623)
    ·
      refine ⟨164874940041132125328771935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109916626694088083552514623 164874940041132125328771935)
      ·
        refine ⟨247312410061698187993157903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164874940041132125328771935 247312410061698187993157903)
        ·
          refine ⟨370968615092547281989736855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247312410061698187993157903 370968615092547281989736855)
          ·
            refine ⟨556452922638820922984605283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370968615092547281989736855 556452922638820922984605283)
            ·
              refine ⟨834679383958231384476907925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556452922638820922984605283 834679383958231384476907925)
              ·
                refine ⟨39125596123042096147355059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 834679383958231384476907925 39125596123042096147355059)
                ·
                  refine ⟨58688394184563144221032589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39125596123042096147355059 58688394184563144221032589)
                  ·
                    refine ⟨22008147819211179082887221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58688394184563144221032589 22008147819211179082887221)
                    ·
                      refine ⟨2063263858051048039020677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22008147819211179082887221 2063263858051048039020677)
                      ·
                        rfl

theorem cell23_4018192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_4018192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018192 prefixEnd_4018192 := by exact prefixLift 4018192
  have htrace : WordTrace (prefixWord ++ tailWord_4018192) baseStart_4018192 baseEnd_4018192 := by
    simpa [prefixWord, tailWord_4018192, baseEnd_4018192] using wordTrace_append hprefix tailTrace_4018192
  have hstable : (prefixWord ++ tailWord_4018192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018192).length < 2 ^ (prefixWord ++ tailWord_4018192).sum := by decide
  have hdescent : baseEnd_4018192 < baseStart_4018192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018239 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_4018239 : Nat := 118140960795 + 4018239 * 2 ^ 59
def prefixEnd_4018239 : Nat := 4983230072969 + 3 ^ 40 * 4018239 * 2
def baseEnd_4018239 : Nat := 2063287991641809355132961

theorem tailTrace_4018239 : CollatzResearch.WordTrace tailWord_4018239 prefixEnd_4018239 2063287991641809355132961 := by
  unfold tailWord_4018239
  simp only [CollatzResearch.WordTrace]
  refine ⟨146557216489613838430313771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97704810993075892286875847 146557216489613838430313771)
  ·
    refine ⟨219835824734420757645470657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146557216489613838430313771 219835824734420757645470657)
    ·
      refine ⟨164876868550815568234102993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219835824734420757645470657 164876868550815568234102993)
      ·
        refine ⟨123657651413111676175577245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164876868550815568234102993 123657651413111676175577245)
        ·
          refine ⟨46371619279916878565841467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123657651413111676175577245 46371619279916878565841467)
          ·
            refine ⟨69557428919875317848762201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46371619279916878565841467 69557428919875317848762201)
            ·
              refine ⟨52168071689906488386571651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69557428919875317848762201 52168071689906488386571651)
              ·
                refine ⟨78252107534859732579857477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52168071689906488386571651 78252107534859732579857477)
                ·
                  refine ⟨14672270162786199858723277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78252107534859732579857477 14672270162786199858723277)
                  ·
                    refine ⟨5502101311044824947021229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14672270162786199858723277 5502101311044824947021229)
                    ·
                      refine ⟨2063287991641809355132961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502101311044824947021229 2063287991641809355132961)
                      ·
                        rfl

theorem cell23_4018239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_4018239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018239 prefixEnd_4018239 := by exact prefixLift 4018239
  have htrace : WordTrace (prefixWord ++ tailWord_4018239) baseStart_4018239 baseEnd_4018239 := by
    simpa [prefixWord, tailWord_4018239, baseEnd_4018239] using wordTrace_append hprefix tailTrace_4018239
  have hstable : (prefixWord ++ tailWord_4018239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018239).length < 2 ^ (prefixWord ++ tailWord_4018239).sum := by decide
  have hdescent : baseEnd_4018239 < baseStart_4018239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018296 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 2, 4, 2]
def baseStart_4018296 : Nat := 118140960795 + 4018296 * 2 ^ 59
def prefixEnd_4018296 : Nat := 4983230072969 + 3 ^ 40 * 4018296 * 2
def baseEnd_4018296 : Nat := 2063317260039115632120199

theorem tailTrace_4018296 : CollatzResearch.WordTrace tailWord_4018296 prefixEnd_4018296 2063317260039115632120199 := by
  unfold tailWord_4018296
  simp only [CollatzResearch.WordTrace]
  refine ⟨73279647725203668582569371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97706196966938224776759161 73279647725203668582569371)
  ·
    refine ⟨109919471587805502873854057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73279647725203668582569371 109919471587805502873854057)
    ·
      refine ⟨82439603690854127155390543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109919471587805502873854057 82439603690854127155390543)
      ·
        refine ⟨123659405536281190733085815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82439603690854127155390543 123659405536281190733085815)
        ·
          refine ⟨185489108304421786099628723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123659405536281190733085815 185489108304421786099628723)
          ·
            refine ⟨278233662456632679149443085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185489108304421786099628723 278233662456632679149443085)
            ·
              refine ⟨104337623421237254681041157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278233662456632679149443085 104337623421237254681041157)
              ·
                refine ⟨19563304391481985252695217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104337623421237254681041157 19563304391481985252695217)
                ·
                  refine ⟨14672478293611488939521413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19563304391481985252695217 14672478293611488939521413)
                  ·
                    refine ⟨2751089680052154176160265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14672478293611488939521413 2751089680052154176160265)
                    ·
                      refine ⟨2063317260039115632120199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751089680052154176160265 2063317260039115632120199)
                      ·
                        rfl

theorem cell23_4018296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_4018296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018296 prefixEnd_4018296 := by exact prefixLift 4018296
  have htrace : WordTrace (prefixWord ++ tailWord_4018296) baseStart_4018296 baseEnd_4018296 := by
    simpa [prefixWord, tailWord_4018296, baseEnd_4018296] using wordTrace_append hprefix tailTrace_4018296
  have hstable : (prefixWord ++ tailWord_4018296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018296).length < 2 ^ (prefixWord ++ tailWord_4018296).sum := by decide
  have hdescent : baseEnd_4018296 < baseStart_4018296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018299 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 3]
def baseStart_4018299 : Nat := 118140960795 + 4018299 * 2 ^ 59
def prefixEnd_4018299 : Nat := 4983230072969 + 3 ^ 40 * 4018299 * 2
def baseEnd_4018299 : Nat := 2063318800481079120382685

theorem tailTrace_4018299 : CollatzResearch.WordTrace tailWord_4018299 prefixEnd_4018299 2063318800481079120382685 := by
  unfold tailWord_4018299
  simp only [CollatzResearch.WordTrace]
  refine ⟨146559404869396468677497951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97706269912930979118331967 146559404869396468677497951)
  ·
    refine ⟨219839107304094703016246927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146559404869396468677497951 219839107304094703016246927)
    ·
      refine ⟨329758660956142054524370391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219839107304094703016246927 329758660956142054524370391)
      ·
        refine ⟨494637991434213081786555587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329758660956142054524370391 494637991434213081786555587)
        ·
          refine ⟨741956987151319622679833381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494637991434213081786555587 741956987151319622679833381)
          ·
            refine ⟨139116935090872429252468759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741956987151319622679833381 139116935090872429252468759)
            ·
              refine ⟨208675402636308643878703139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139116935090872429252468759 208675402636308643878703139)
              ·
                refine ⟨313013103954462965818054709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208675402636308643878703139 313013103954462965818054709)
                ·
                  refine ⟨29344978495730903045442629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313013103954462965818054709 29344978495730903045442629)
                  ·
                    refine ⟨5502183467949544321020493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29344978495730903045442629 5502183467949544321020493)
                    ·
                      refine ⟨2063318800481079120382685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502183467949544321020493 2063318800481079120382685)
                      ·
                        rfl

theorem cell23_4018299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 3].length) (baseStart_4018299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018299 prefixEnd_4018299 := by exact prefixLift 4018299
  have htrace : WordTrace (prefixWord ++ tailWord_4018299) baseStart_4018299 baseEnd_4018299 := by
    simpa [prefixWord, tailWord_4018299, baseEnd_4018299] using wordTrace_append hprefix tailTrace_4018299
  have hstable : (prefixWord ++ tailWord_4018299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018299).length < 2 ^ (prefixWord ++ tailWord_4018299).sum := by decide
  have hdescent : baseEnd_4018299 < baseStart_4018299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018330 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4018330 : Nat := 118140960795 + 4018330 * 2 ^ 59
def prefixEnd_4018330 : Nat := 4983230072969 + 3 ^ 40 * 4018330 * 2
def baseEnd_4018330 : Nat := 2063334718381368499095043

theorem tailTrace_4018330 : CollatzResearch.WordTrace tailWord_4018330 prefixEnd_4018330 2063334718381368499095043 := by
  unfold tailWord_4018330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36640133883071040242969111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97707023688189440647917629 36640133883071040242969111)
  ·
    refine ⟨54960200824606560364453667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36640133883071040242969111 54960200824606560364453667)
    ·
      refine ⟨82440301236909840546680501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54960200824606560364453667 82440301236909840546680501)
      ·
        refine ⟨7728778240960297551251297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82440301236909840546680501 7728778240960297551251297)
        ·
          refine ⟨5796583680720223163438473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7728778240960297551251297 5796583680720223163438473)
          ·
            refine ⟨4347437760540167372578855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5796583680720223163438473 4347437760540167372578855)
            ·
              refine ⟨6521156640810251058868283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347437760540167372578855 6521156640810251058868283)
              ·
                refine ⟨9781734961215376588302425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521156640810251058868283 9781734961215376588302425)
                ·
                  refine ⟨7336301220911532441226819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9781734961215376588302425 7336301220911532441226819)
                  ·
                    refine ⟨11004451831367298661840229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336301220911532441226819 11004451831367298661840229)
                    ·
                      refine ⟨2063334718381368499095043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11004451831367298661840229 2063334718381368499095043)
                      ·
                        rfl

theorem cell23_4018330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4018330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018330 prefixEnd_4018330 := by exact prefixLift 4018330
  have htrace : WordTrace (prefixWord ++ tailWord_4018330) baseStart_4018330 baseEnd_4018330 := by
    simpa [prefixWord, tailWord_4018330, baseEnd_4018330] using wordTrace_append hprefix tailTrace_4018330
  have hstable : (prefixWord ++ tailWord_4018330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018330).length < 2 ^ (prefixWord ++ tailWord_4018330).sum := by decide
  have hdescent : baseEnd_4018330 < baseStart_4018330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018333 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_4018333 : Nat := 118140960795 + 4018333 * 2 ^ 59
def prefixEnd_4018333 : Nat := 4983230072969 + 3 ^ 40 * 4018333 * 2
def baseEnd_4018333 : Nat := 2063336258823331987357529

theorem tailTrace_4018333 : CollatzResearch.WordTrace tailWord_4018333 prefixEnd_4018333 2063336258823331987357529 := by
  unfold tailWord_4018333
  simp only [CollatzResearch.WordTrace]
  refine ⟨146560644951273292484235653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97707096634182194989490435 146560644951273292484235653)
  ·
    refine ⟨27480120928363742340794185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146560644951273292484235653 27480120928363742340794185)
    ·
      refine ⟨20610090696272806755595639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27480120928363742340794185 20610090696272806755595639)
      ·
        refine ⟨30915136044409210133393459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20610090696272806755595639 30915136044409210133393459)
        ·
          refine ⟨46372704066613815200090189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30915136044409210133393459 46372704066613815200090189)
          ·
            refine ⟨17389764024980180700033821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46372704066613815200090189 17389764024980180700033821)
            ·
              refine ⟨6521161509367567762512683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17389764024980180700033821 6521161509367567762512683)
              ·
                refine ⟨9781742264051351643769025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521161509367567762512683 9781742264051351643769025)
                ·
                  refine ⟨7336306698038513732826769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9781742264051351643769025 7336306698038513732826769)
                  ·
                    refine ⟨5502230023528885299620077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336306698038513732826769 5502230023528885299620077)
                    ·
                      refine ⟨2063336258823331987357529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502230023528885299620077 2063336258823331987357529)
                      ·
                        rfl

theorem cell23_4018333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_4018333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018333 prefixEnd_4018333 := by exact prefixLift 4018333
  have htrace : WordTrace (prefixWord ++ tailWord_4018333) baseStart_4018333 baseEnd_4018333 := by
    simpa [prefixWord, tailWord_4018333, baseEnd_4018333] using wordTrace_append hprefix tailTrace_4018333
  have hstable : (prefixWord ++ tailWord_4018333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018333).length < 2 ^ (prefixWord ++ tailWord_4018333).sum := by decide
  have hdescent : baseEnd_4018333 < baseStart_4018333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018363 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 3]
def baseStart_4018363 : Nat := 118140960795 + 4018363 * 2 ^ 59
def prefixEnd_4018363 : Nat := 4983230072969 + 3 ^ 40 * 4018363 * 2
def baseEnd_4018363 : Nat := 2063351663242966869982391

theorem tailTrace_4018363 : CollatzResearch.WordTrace tailWord_4018363 prefixEnd_4018363 2063351663242966869982391 := by
  unfold tailWord_4018363
  simp only [CollatzResearch.WordTrace]
  refine ⟨146561739141164607607827743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97707826094109738405218495 146561739141164607607827743)
  ·
    refine ⟨219842608711746911411741615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146561739141164607607827743 219842608711746911411741615)
    ·
      refine ⟨329763913067620367117612423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219842608711746911411741615 329763913067620367117612423)
      ·
        refine ⟨494645869601430550676418635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329763913067620367117612423 494645869601430550676418635)
        ·
          refine ⟨741968804402145826014627953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494645869601430550676418635 741968804402145826014627953)
          ·
            refine ⟨556476603301609369510970965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741968804402145826014627953 556476603301609369510970965)
            ·
              refine ⟨6521210194940734798956691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 556476603301609369510970965 6521210194940734798956691)
              ·
                refine ⟨9781815292411102198435037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521210194940734798956691 9781815292411102198435037)
                ·
                  refine ⟨3668180734654163324413139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9781815292411102198435037 3668180734654163324413139)
                  ·
                    refine ⟨5502271101981244986619709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668180734654163324413139 5502271101981244986619709)
                    ·
                      refine ⟨2063351663242966869982391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502271101981244986619709 2063351663242966869982391)
                      ·
                        rfl

theorem cell23_4018363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 3].length) (baseStart_4018363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018363 prefixEnd_4018363 := by exact prefixLift 4018363
  have htrace : WordTrace (prefixWord ++ tailWord_4018363) baseStart_4018363 baseEnd_4018363 := by
    simpa [prefixWord, tailWord_4018363, baseEnd_4018363] using wordTrace_append hprefix tailTrace_4018363
  have hstable : (prefixWord ++ tailWord_4018363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018363).length < 2 ^ (prefixWord ++ tailWord_4018363).sum := by decide
  have hdescent : baseEnd_4018363 < baseStart_4018363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018426 : List Nat := [3, 1, 1, 1, 1, 6, 2, 8]
def baseStart_4018426 : Nat := 118140960795 + 4018426 * 2 ^ 59
def prefixEnd_4018426 : Nat := 4983230072969 + 3 ^ 40 * 4018426 * 2
def baseEnd_4018426 : Nat := 76421630093488893462763

theorem tailTrace_4018426 : CollatzResearch.WordTrace tailWord_4018426 prefixEnd_4018426 76421630093488893462763 := by
  unfold tailWord_4018426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36641009234984092341842783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97709357959957579578247421 36641009234984092341842783)
  ·
    refine ⟨54961513852476138512764175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36641009234984092341842783 54961513852476138512764175)
    ·
      refine ⟨82442270778714207769146263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54961513852476138512764175 82442270778714207769146263)
      ·
        refine ⟨123663406168071311653719395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82442270778714207769146263 123663406168071311653719395)
        ·
          refine ⟨185495109252106967480579093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123663406168071311653719395 185495109252106967480579093)
          ·
            refine ⟨8695083246192514100652145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185495109252106967480579093 8695083246192514100652145)
            ·
              refine ⟨6521312434644385575489109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8695083246192514100652145 6521312434644385575489109)
              ·
                refine ⟨76421630093488893462763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6521312434644385575489109 76421630093488893462763)
                ·
                  rfl

theorem cell23_4018426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_4018426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018426 prefixEnd_4018426 := by exact prefixLift 4018426
  have htrace : WordTrace (prefixWord ++ tailWord_4018426) baseStart_4018426 baseEnd_4018426 := by
    simpa [prefixWord, tailWord_4018426, baseEnd_4018426] using wordTrace_append hprefix tailTrace_4018426
  have hstable : (prefixWord ++ tailWord_4018426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018426).length < 2 ^ (prefixWord ++ tailWord_4018426).sum := by decide
  have hdescent : baseEnd_4018426 < baseStart_4018426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018430 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4018430 : Nat := 118140960795 + 4018430 * 2 ^ 59
def prefixEnd_4018430 : Nat := 4983230072969 + 3 ^ 40 * 4018430 * 2
def baseEnd_4018430 : Nat := 687795355482272702614861

theorem tailTrace_4018430 : CollatzResearch.WordTrace tailWord_4018430 prefixEnd_4018430 687795355482272702614861 := by
  unfold tailWord_4018430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320522853990234756314593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97709455221281252033677829 18320522853990234756314593)
  ·
    refine ⟨13740392140492676067235945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18320522853990234756314593 13740392140492676067235945)
    ·
      refine ⟨10305294105369507050426959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13740392140492676067235945 10305294105369507050426959)
      ·
        refine ⟨15457941158054260575640439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305294105369507050426959 15457941158054260575640439)
        ·
          refine ⟨23186911737081390863460659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15457941158054260575640439 23186911737081390863460659)
          ·
            refine ⟨34780367605622086295190989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23186911737081390863460659 34780367605622086295190989)
            ·
              refine ⟨13042637852108282360696621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34780367605622086295190989 13042637852108282360696621)
              ·
                refine ⟨4890989194540605885261233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042637852108282360696621 4890989194540605885261233)
                ·
                  refine ⟨3668241895905454413945925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4890989194540605885261233 3668241895905454413945925)
                  ·
                    refine ⟨687795355482272702614861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668241895905454413945925 687795355482272702614861)
                    ·
                      rfl

theorem cell23_4018430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4018430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018430 prefixEnd_4018430 := by exact prefixLift 4018430
  have htrace : WordTrace (prefixWord ++ tailWord_4018430) baseStart_4018430 baseEnd_4018430 := by
    simpa [prefixWord, tailWord_4018430, baseEnd_4018430] using wordTrace_append hprefix tailTrace_4018430
  have hstable : (prefixWord ++ tailWord_4018430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018430).length < 2 ^ (prefixWord ++ tailWord_4018430).sum := by decide
  have hdescent : baseEnd_4018430 < baseStart_4018430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018440 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_4018440 : Nat := 118140960795 + 4018440 * 2 ^ 59
def prefixEnd_4018440 : Nat := 4983230072969 + 3 ^ 40 * 4018440 * 2
def baseEnd_4018440 : Nat := 2063391201253363068719537

theorem tailTrace_4018440 : CollatzResearch.WordTrace tailWord_4018440 prefixEnd_4018440 2063391201253363068719537 := by
  unfold tailWord_4018440
  simp only [CollatzResearch.WordTrace]
  refine ⟨73282273780942824879190387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97709698374590433172253849 73282273780942824879190387)
  ·
    refine ⟨109923410671414237318785581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73282273780942824879190387 109923410671414237318785581)
    ·
      refine ⟨41221279001780338994544593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109923410671414237318785581 41221279001780338994544593)
      ·
        refine ⟨30915959251335254245908445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41221279001780338994544593 30915959251335254245908445)
        ·
          refine ⟨11593484719250720342215667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30915959251335254245908445 11593484719250720342215667)
          ·
            refine ⟨17390227078876080513323501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593484719250720342215667 17390227078876080513323501)
            ·
              refine ⟨6521335154578530192496313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17390227078876080513323501 6521335154578530192496313)
              ·
                refine ⟨4891001365933897644372235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521335154578530192496313 4891001365933897644372235)
                ·
                  refine ⟨7336502048900846466558353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891001365933897644372235 7336502048900846466558353)
                  ·
                    refine ⟨5502376536675634849918765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336502048900846466558353 5502376536675634849918765)
                    ·
                      refine ⟨2063391201253363068719537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502376536675634849918765 2063391201253363068719537)
                      ·
                        rfl

theorem cell23_4018440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_4018440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018440 prefixEnd_4018440 := by exact prefixLift 4018440
  have htrace : WordTrace (prefixWord ++ tailWord_4018440) baseStart_4018440 baseEnd_4018440 := by
    simpa [prefixWord, tailWord_4018440, baseEnd_4018440] using wordTrace_append hprefix tailTrace_4018440
  have hstable : (prefixWord ++ tailWord_4018440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018440).length < 2 ^ (prefixWord ++ tailWord_4018440).sum := by decide
  have hdescent : baseEnd_4018440 < baseStart_4018440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018453 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_4018453 : Nat := 118140960795 + 4018453 * 2 ^ 59
def prefixEnd_4018453 : Nat := 4983230072969 + 3 ^ 40 * 4018453 * 2
def baseEnd_4018453 : Nat := 2063397876501871517856977

theorem tailTrace_4018453 : CollatzResearch.WordTrace tailWord_4018453 prefixEnd_4018453 2063397876501871517856977 := by
  unfold tailWord_4018453
  simp only [CollatzResearch.WordTrace]
  refine ⟨146565021710838552978604013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97710014473892368652402675 146565021710838552978604013)
  ·
    refine ⟨54961883141564457366976505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146565021710838552978604013 54961883141564457366976505)
    ·
      refine ⟨41221412356173343025232379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54961883141564457366976505 41221412356173343025232379)
      ·
        refine ⟨61832118534260014537848569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41221412356173343025232379 61832118534260014537848569)
        ·
          refine ⟨46374088900695010903386427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61832118534260014537848569 46374088900695010903386427)
          ·
            refine ⟨69561133351042516355079641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46374088900695010903386427 69561133351042516355079641)
            ·
              refine ⟨52170850013281887266309731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69561133351042516355079641 52170850013281887266309731)
              ·
                refine ⟨78256275019922830899464597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52170850013281887266309731 78256275019922830899464597)
                ·
                  refine ⟨3668262891558882698412403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78256275019922830899464597 3668262891558882698412403)
                  ·
                    refine ⟨5502394337338324047618605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668262891558882698412403 5502394337338324047618605)
                    ·
                      refine ⟨2063397876501871517856977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502394337338324047618605 2063397876501871517856977)
                      ·
                        rfl

theorem cell23_4018453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_4018453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018453 prefixEnd_4018453 := by exact prefixLift 4018453
  have htrace : WordTrace (prefixWord ++ tailWord_4018453) baseStart_4018453 baseEnd_4018453 := by
    simpa [prefixWord, tailWord_4018453, baseEnd_4018453] using wordTrace_append hprefix tailTrace_4018453
  have hstable : (prefixWord ++ tailWord_4018453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018453).length < 2 ^ (prefixWord ++ tailWord_4018453).sum := by decide
  have hdescent : baseEnd_4018453 < baseStart_4018453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018476 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_4018476 : Nat := 118140960795 + 4018476 * 2 ^ 59
def prefixEnd_4018476 : Nat := 4983230072969 + 3 ^ 40 * 4018476 * 2
def baseEnd_4018476 : Nat := 2063409686556924927869371

theorem tailTrace_4018476 : CollatzResearch.WordTrace tailWord_4018476 prefixEnd_4018476 2063409686556924927869371 := by
  unfold tailWord_4018476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73282930294877613953345641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97710573726503485271127521 73282930294877613953345641)
  ·
    refine ⟨54962197721158210465009231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73282930294877613953345641 54962197721158210465009231)
    ·
      refine ⟨82443296581737315697513847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54962197721158210465009231 82443296581737315697513847)
      ·
        refine ⟨123664944872605973546270771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82443296581737315697513847 123664944872605973546270771)
        ·
          refine ⟨185497417308908960319406157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123664944872605973546270771 185497417308908960319406157)
          ·
            refine ⟨69561531490840860119777309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185497417308908960319406157 69561531490840860119777309)
            ·
              refine ⟨26085574309065322544916491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69561531490840860119777309 26085574309065322544916491)
              ·
                refine ⟨39128361463597983817374737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26085574309065322544916491 39128361463597983817374737)
                ·
                  refine ⟨29346271097698487863031053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39128361463597983817374737 29346271097698487863031053)
                  ·
                    refine ⟨11004851661636932948636645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29346271097698487863031053 11004851661636932948636645)
                    ·
                      refine ⟨2063409686556924927869371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11004851661636932948636645 2063409686556924927869371)
                      ·
                        rfl

theorem cell23_4018476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_4018476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018476 prefixEnd_4018476 := by exact prefixLift 4018476
  have htrace : WordTrace (prefixWord ++ tailWord_4018476) baseStart_4018476 baseEnd_4018476 := by
    simpa [prefixWord, tailWord_4018476, baseEnd_4018476] using wordTrace_append hprefix tailTrace_4018476
  have hstable : (prefixWord ++ tailWord_4018476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018476).length < 2 ^ (prefixWord ++ tailWord_4018476).sum := by decide
  have hdescent : baseEnd_4018476 < baseStart_4018476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018477 : List Nat := [1, 5, 3, 1, 3, 1, 1, 8]
def baseStart_4018477 : Nat := 118140960795 + 4018477 * 2 ^ 59
def prefixEnd_4018477 : Nat := 4983230072969 + 3 ^ 40 * 4018477 * 2
def baseEnd_4018477 : Nat := 76422600001391830516921

theorem tailTrace_4018477 : CollatzResearch.WordTrace tailWord_4018477 prefixEnd_4018477 76422600001391830516921 := by
  unfold tailWord_4018477
  simp only [CollatzResearch.WordTrace]
  refine ⟨146565897062751605077477685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97710598041834403384985123 146565897062751605077477685)
  ·
    refine ⟨13740552849632962976013533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146565897062751605077477685 13740552849632962976013533)
    ·
      refine ⟨5152707318612361116005075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13740552849632962976013533 5152707318612361116005075)
      ·
        refine ⟨7729060977918541674007613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152707318612361116005075 7729060977918541674007613)
        ·
          refine ⟨2898397866719453127752855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7729060977918541674007613 2898397866719453127752855)
          ·
            refine ⟨4347596800079179691629283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898397866719453127752855 4347596800079179691629283)
            ·
              refine ⟨6521395200118769537443925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347596800079179691629283 6521395200118769537443925)
              ·
                refine ⟨76422600001391830516921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6521395200118769537443925 76422600001391830516921)
                ·
                  rfl

theorem cell23_4018477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 8].length) (baseStart_4018477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018477 prefixEnd_4018477 := by exact prefixLift 4018477
  have htrace : WordTrace (prefixWord ++ tailWord_4018477) baseStart_4018477 baseEnd_4018477 := by
    simpa [prefixWord, tailWord_4018477, baseEnd_4018477] using wordTrace_append hprefix tailTrace_4018477
  have hstable : (prefixWord ++ tailWord_4018477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018477).length < 2 ^ (prefixWord ++ tailWord_4018477).sum := by decide
  have hdescent : baseEnd_4018477 < baseStart_4018477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018496 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_4018496 : Nat := 118140960795 + 4018496 * 2 ^ 59
def prefixEnd_4018496 : Nat := 4983230072969 + 3 ^ 40 * 4018496 * 2
def baseEnd_4018496 : Nat := 2063419956170014849619279

theorem tailTrace_4018496 : CollatzResearch.WordTrace tailWord_4018496 prefixEnd_4018496 2063419956170014849619279 := by
  unfold tailWord_4018496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73283295024841385661209671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97711060033121847548279561 73283295024841385661209671)
  ·
    refine ⟨109924942537262078491814507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73283295024841385661209671 109924942537262078491814507)
    ·
      refine ⟨164887413805893117737721761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109924942537262078491814507 164887413805893117737721761)
      ·
        refine ⟨123665560354419838303291321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164887413805893117737721761 123665560354419838303291321)
        ·
          refine ⟨92749170265814878727468491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123665560354419838303291321 92749170265814878727468491)
          ·
            refine ⟨139123755398722318091202737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92749170265814878727468491 139123755398722318091202737)
            ·
              refine ⟨104342816549041738568402053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139123755398722318091202737 104342816549041738568402053)
              ·
                refine ⟨19564278102945325981575385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104342816549041738568402053 19564278102945325981575385)
                ·
                  refine ⟨14673208577208994486181539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19564278102945325981575385 14673208577208994486181539)
                  ·
                    refine ⟨22009812865813491729272309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14673208577208994486181539 22009812865813491729272309)
                    ·
                      refine ⟨2063419956170014849619279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22009812865813491729272309 2063419956170014849619279)
                      ·
                        rfl

theorem cell23_4018496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_4018496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018496 prefixEnd_4018496 := by exact prefixLift 4018496
  have htrace : WordTrace (prefixWord ++ tailWord_4018496) baseStart_4018496 baseEnd_4018496 := by
    simpa [prefixWord, tailWord_4018496, baseEnd_4018496] using wordTrace_append hprefix tailTrace_4018496
  have hstable : (prefixWord ++ tailWord_4018496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018496).length < 2 ^ (prefixWord ++ tailWord_4018496).sum := by decide
  have hdescent : baseEnd_4018496 < baseStart_4018496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018527 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 2, 2, 2]
def baseStart_4018527 : Nat := 118140960795 + 4018527 * 2 ^ 59
def prefixEnd_4018527 : Nat := 4983230072969 + 3 ^ 40 * 4018527 * 2
def baseEnd_4018527 : Nat := 2063435874070304228331637

theorem tailTrace_4018527 : CollatzResearch.WordTrace tailWord_4018527 prefixEnd_4018527 2063435874070304228331637 := by
  unfold tailWord_4018527
  simp only [CollatzResearch.WordTrace]
  refine ⟨146567720712570463616797835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97711813808380309077865223 146567720712570463616797835)
  ·
    refine ⟨219851581068855695425196753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146567720712570463616797835 219851581068855695425196753)
    ·
      refine ⟨164888685801641771568897565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219851581068855695425196753 164888685801641771568897565)
      ·
        refine ⟨61833257175615664338336587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164888685801641771568897565 61833257175615664338336587)
        ·
          refine ⟨92749885763423496507504881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61833257175615664338336587 92749885763423496507504881)
          ·
            refine ⟨69562414322567622380628661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92749885763423496507504881 69562414322567622380628661)
            ·
              refine ⟨6521476342740714598183937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69562414322567622380628661 6521476342740714598183937)
              ·
                refine ⟨4891107257055535948637953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521476342740714598183937 4891107257055535948637953)
                ·
                  refine ⟨3668330442791651961478465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4891107257055535948637953 3668330442791651961478465)
                  ·
                    refine ⟨2751247832093738971108849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3668330442791651961478465 2751247832093738971108849)
                    ·
                      refine ⟨2063435874070304228331637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751247832093738971108849 2063435874070304228331637)
                      ·
                        rfl

theorem cell23_4018527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_4018527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018527 prefixEnd_4018527 := by exact prefixLift 4018527
  have htrace : WordTrace (prefixWord ++ tailWord_4018527) baseStart_4018527 baseEnd_4018527 := by
    simpa [prefixWord, tailWord_4018527, baseEnd_4018527] using wordTrace_append hprefix tailTrace_4018527
  have hstable : (prefixWord ++ tailWord_4018527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018527).length < 2 ^ (prefixWord ++ tailWord_4018527).sum := by decide
  have hdescent : baseEnd_4018527 < baseStart_4018527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018533 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 7]
def baseStart_4018533 : Nat := 118140960795 + 4018533 * 2 ^ 59
def prefixEnd_4018533 : Nat := 4983230072969 + 3 ^ 40 * 4018533 * 2
def baseEnd_4018533 : Nat := 229270994994914578317401

theorem tailTrace_4018533 : CollatzResearch.WordTrace tailWord_4018533 prefixEnd_4018533 229270994994914578317401 := by
  unfold tailWord_4018533
  simp only [CollatzResearch.WordTrace]
  refine ⟨146567939550548726641516253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97711959700365817761010835 146567939550548726641516253)
  ·
    refine ⟨54962977331455772490568595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146567939550548726641516253 54962977331455772490568595)
    ·
      refine ⟨82444465997183658735852893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54962977331455772490568595 82444465997183658735852893)
      ·
        refine ⟨30916674748943872025944835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82444465997183658735852893 30916674748943872025944835)
        ·
          refine ⟨46375012123415808038917253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30916674748943872025944835 46375012123415808038917253)
          ·
            refine ⟨8695314773140464007296985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46375012123415808038917253 8695314773140464007296985)
            ·
              refine ⟨6521486079855348005472739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8695314773140464007296985 6521486079855348005472739)
              ·
                refine ⟨9782229119783022008209109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521486079855348005472739 9782229119783022008209109)
                ·
                  refine ⟨229270994994914578317401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9782229119783022008209109 229270994994914578317401)
                  ·
                    rfl

theorem cell23_4018533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_4018533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018533 prefixEnd_4018533 := by exact prefixLift 4018533
  have htrace : WordTrace (prefixWord ++ tailWord_4018533) baseStart_4018533 baseEnd_4018533 := by
    simpa [prefixWord, tailWord_4018533, baseEnd_4018533] using wordTrace_append hprefix tailTrace_4018533
  have hstable : (prefixWord ++ tailWord_4018533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018533).length < 2 ^ (prefixWord ++ tailWord_4018533).sum := by decide
  have hdescent : baseEnd_4018533 < baseStart_4018533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018544 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 2, 2, 2]
def baseStart_4018544 : Nat := 118140960795 + 4018544 * 2 ^ 59
def prefixEnd_4018544 : Nat := 4983230072969 + 3 ^ 40 * 4018544 * 2
def baseEnd_4018544 : Nat := 2063444603241430661819059

theorem tailTrace_4018544 : CollatzResearch.WordTrace tailWord_4018544 prefixEnd_4018544 2063444603241430661819059 := by
  unfold tailWord_4018544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73284170376754437760083343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97712227169005917013444457 73284170376754437760083343)
  ·
    refine ⟨109926255565131656640125015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73284170376754437760083343 109926255565131656640125015)
    ·
      refine ⟨164889383347697484960187523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109926255565131656640125015 164889383347697484960187523)
      ·
        refine ⟨247334075021546227440281285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164889383347697484960187523 247334075021546227440281285)
        ·
          refine ⟨46375139066539917645052741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247334075021546227440281285 46375139066539917645052741)
          ·
            refine ⟨8695338574976234558447389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46375139066539917645052741 8695338574976234558447389)
            ·
              refine ⟨3260751965616087959417771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8695338574976234558447389 3260751965616087959417771)
              ·
                refine ⟨4891127948424131939126657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260751965616087959417771 4891127948424131939126657)
                ·
                  refine ⟨3668345961318098954344993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4891127948424131939126657 3668345961318098954344993)
                  ·
                    refine ⟨2751259470988574215758745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3668345961318098954344993 2751259470988574215758745)
                    ·
                      refine ⟨2063444603241430661819059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751259470988574215758745 2063444603241430661819059)
                      ·
                        rfl

theorem cell23_4018544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 2, 2].length) (baseStart_4018544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018544 prefixEnd_4018544 := by exact prefixLift 4018544
  have htrace : WordTrace (prefixWord ++ tailWord_4018544) baseStart_4018544 baseEnd_4018544 := by
    simpa [prefixWord, tailWord_4018544, baseEnd_4018544] using wordTrace_append hprefix tailTrace_4018544
  have hstable : (prefixWord ++ tailWord_4018544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018544).length < 2 ^ (prefixWord ++ tailWord_4018544).sum := by decide
  have hdescent : baseEnd_4018544 < baseStart_4018544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018556 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_4018556 : Nat := 118140960795 + 4018556 * 2 ^ 59
def prefixEnd_4018556 : Nat := 4983230072969 + 3 ^ 40 * 4018556 * 2
def baseEnd_4018556 : Nat := 2063450765009284614869003

theorem tailTrace_4018556 : CollatzResearch.WordTrace tailWord_4018556 prefixEnd_4018556 2063450765009284614869003 := by
  unfold tailWord_4018556
  simp only [CollatzResearch.WordTrace]
  refine ⟨73284389214732700784801761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97712518952976934379735681 73284389214732700784801761)
  ·
    refine ⟨54963291911049525588601321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73284389214732700784801761 54963291911049525588601321)
    ·
      refine ⟨41222468933287144191450991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54963291911049525588601321 41222468933287144191450991)
      ·
        refine ⟨61833703399930716287176487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41222468933287144191450991 61833703399930716287176487)
        ·
          refine ⟨92750555099896074430764731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61833703399930716287176487 92750555099896074430764731)
          ·
            refine ⟨139125832649844111646147097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92750555099896074430764731 139125832649844111646147097)
            ·
              refine ⟨104344374487383083734610323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139125832649844111646147097 104344374487383083734610323)
              ·
                refine ⟨156516561731074625601915485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104344374487383083734610323 156516561731074625601915485)
                ·
                  refine ⟨58693710649152984600718307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156516561731074625601915485 58693710649152984600718307)
                  ·
                    refine ⟨88040565973729476901077461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58693710649152984600718307 88040565973729476901077461)
                    ·
                      refine ⟨2063450765009284614869003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88040565973729476901077461 2063450765009284614869003)
                      ·
                        rfl

theorem cell23_4018556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_4018556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018556 prefixEnd_4018556 := by exact prefixLift 4018556
  have htrace : WordTrace (prefixWord ++ tailWord_4018556) baseStart_4018556 baseEnd_4018556 := by
    simpa [prefixWord, tailWord_4018556, baseEnd_4018556] using wordTrace_append hprefix tailTrace_4018556
  have hstable : (prefixWord ++ tailWord_4018556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018556).length < 2 ^ (prefixWord ++ tailWord_4018556).sum := by decide
  have hdescent : baseEnd_4018556 < baseStart_4018556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018583 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4018583 : Nat := 118140960795 + 4018583 * 2 ^ 59
def prefixEnd_4018583 : Nat := 4983230072969 + 3 ^ 40 * 4018583 * 2
def baseEnd_4018583 : Nat := 2063464628986956009231379

theorem tailTrace_4018583 : CollatzResearch.WordTrace tailWord_4018583 prefixEnd_4018583 2063464628986956009231379 := by
  unfold tailWord_4018583
  simp only [CollatzResearch.WordTrace]
  refine ⟨146569763200367585180836403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97713175466911723453890935 146569763200367585180836403)
  ·
    refine ⟨219854644800551377771254605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146569763200367585180836403 219854644800551377771254605)
    ·
      refine ⟨82445491800206766664220477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219854644800551377771254605 82445491800206766664220477)
      ·
        refine ⟨30917059425077537499082679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82445491800206766664220477 30917059425077537499082679)
        ·
          refine ⟨46375589137616306248624019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30917059425077537499082679 46375589137616306248624019)
          ·
            refine ⟨69563383706424459372936029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46375589137616306248624019 69563383706424459372936029)
            ·
              refine ⟨26086268889909172264851011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69563383706424459372936029 26086268889909172264851011)
              ·
                refine ⟨39129403334863758397276517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26086268889909172264851011 39129403334863758397276517)
                ·
                  refine ⟨7336763125286954699489347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39129403334863758397276517 7336763125286954699489347)
                  ·
                    refine ⟨11005144687930432049234021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336763125286954699489347 11005144687930432049234021)
                    ·
                      refine ⟨2063464628986956009231379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11005144687930432049234021 2063464628986956009231379)
                      ·
                        rfl

theorem cell23_4018583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4018583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018583 prefixEnd_4018583 := by exact prefixLift 4018583
  have htrace : WordTrace (prefixWord ++ tailWord_4018583) baseStart_4018583 baseEnd_4018583 := by
    simpa [prefixWord, tailWord_4018583, baseEnd_4018583] using wordTrace_append hprefix tailTrace_4018583
  have hstable : (prefixWord ++ tailWord_4018583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018583).length < 2 ^ (prefixWord ++ tailWord_4018583).sum := by decide
  have hdescent : baseEnd_4018583 < baseStart_4018583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018590 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4018590 : Nat := 118140960795 + 4018590 * 2 ^ 59
def prefixEnd_4018590 : Nat := 4983230072969 + 3 ^ 40 * 4018590 * 2
def baseEnd_4018590 : Nat := 2063468223351537481843847

theorem tailTrace_4018590 : CollatzResearch.WordTrace tailWord_4018590 prefixEnd_4018590 2063468223351537481843847 := by
  unfold tailWord_4018590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18321252313917778172042653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97713345674228150250894149 18321252313917778172042653)
  ·
    refine ⟨6870469617719166814515995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18321252313917778172042653 6870469617719166814515995)
    ·
      refine ⟨10305704426578750221773993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870469617719166814515995 10305704426578750221773993)
      ·
        refine ⟨7729278319934062666330495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10305704426578750221773993 7729278319934062666330495)
        ·
          refine ⟨11593917479901093999495743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729278319934062666330495 11593917479901093999495743)
          ·
            refine ⟨17390876219851640999243615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593917479901093999495743 17390876219851640999243615)
            ·
              refine ⟨26086314329777461498865423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17390876219851640999243615 26086314329777461498865423)
              ·
                refine ⟨39129471494666192248298135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26086314329777461498865423 39129471494666192248298135)
                ·
                  refine ⟨58694207241999288372447203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39129471494666192248298135 58694207241999288372447203)
                  ·
                    refine ⟨88041310862998932558670805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58694207241999288372447203 88041310862998932558670805)
                    ·
                      refine ⟨2063468223351537481843847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88041310862998932558670805 2063468223351537481843847)
                      ·
                        rfl

theorem cell23_4018590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4018590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018590 prefixEnd_4018590 := by exact prefixLift 4018590
  have htrace : WordTrace (prefixWord ++ tailWord_4018590) baseStart_4018590 baseEnd_4018590 := by
    simpa [prefixWord, tailWord_4018590, baseEnd_4018590] using wordTrace_append hprefix tailTrace_4018590
  have hstable : (prefixWord ++ tailWord_4018590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018590).length < 2 ^ (prefixWord ++ tailWord_4018590).sum := by decide
  have hdescent : baseEnd_4018590 < baseStart_4018590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018644 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_4018644 : Nat := 118140960795 + 4018644 * 2 ^ 59
def prefixEnd_4018644 : Nat := 4983230072969 + 3 ^ 40 * 4018644 * 2
def baseEnd_4018644 : Nat := 687831983768960090189533

theorem tailTrace_4018644 : CollatzResearch.WordTrace tailWord_4018644 prefixEnd_4018644 687831983768960090189533 := by
  unfold tailWord_4018644
  simp only [CollatzResearch.WordTrace]
  refine ⟨73285994026573296299403493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97714658702097728399204657 73285994026573296299403493)
  ·
    refine ⟨13741123879982493056138155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73285994026573296299403493 13741123879982493056138155)
    ·
      refine ⟨20611685819973739584207233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13741123879982493056138155 20611685819973739584207233)
      ·
        refine ⟨15458764364980304688155425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20611685819973739584207233 15458764364980304688155425)
        ·
          refine ⟨11594073273735228516116569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15458764364980304688155425 11594073273735228516116569)
          ·
            refine ⟨8695554955301421387087427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11594073273735228516116569 8695554955301421387087427)
            ·
              refine ⟨13043332432952132080631141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695554955301421387087427 13043332432952132080631141)
              ·
                refine ⟨2445624831178524765118339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13043332432952132080631141 2445624831178524765118339)
                ·
                  refine ⟨3668437246767787147677509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445624831178524765118339 3668437246767787147677509)
                  ·
                    refine ⟨687831983768960090189533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668437246767787147677509 687831983768960090189533)
                    ·
                      rfl

theorem cell23_4018644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_4018644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018644 prefixEnd_4018644 := by exact prefixLift 4018644
  have htrace : WordTrace (prefixWord ++ tailWord_4018644) baseStart_4018644 baseEnd_4018644 := by
    simpa [prefixWord, tailWord_4018644, baseEnd_4018644] using wordTrace_append hprefix tailTrace_4018644
  have hstable : (prefixWord ++ tailWord_4018644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018644).length < 2 ^ (prefixWord ++ tailWord_4018644).sum := by decide
  have hdescent : baseEnd_4018644 < baseStart_4018644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018663 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4018663 : Nat := 118140960795 + 4018663 * 2 ^ 59
def prefixEnd_4018663 : Nat := 4983230072969 + 3 ^ 40 * 4018663 * 2
def baseEnd_4018663 : Nat := 2063505707439315696231011

theorem tailTrace_4018663 : CollatzResearch.WordTrace tailWord_4018663 prefixEnd_4018663 2063505707439315696231011 := by
  unfold tailWord_4018663
  simp only [CollatzResearch.WordTrace]
  refine ⟨146572681040077758843748643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97715120693385172562499095 146572681040077758843748643)
  ·
    refine ⟨219859021560116638265622965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146572681040077758843748643 219859021560116638265622965)
    ·
      refine ⟨20611783271260934837402153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219859021560116638265622965 20611783271260934837402153)
      ·
        refine ⟨15458837453445701128051615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20611783271260934837402153 15458837453445701128051615)
        ·
          refine ⟨23188256180168551692077423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15458837453445701128051615 23188256180168551692077423)
          ·
            refine ⟨34782384270252827538116135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23188256180168551692077423 34782384270252827538116135)
            ·
              refine ⟨52173576405379241307174203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34782384270252827538116135 52173576405379241307174203)
              ·
                refine ⟨78260364608068861960761305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52173576405379241307174203 78260364608068861960761305)
                ·
                  refine ⟨58695273456051646470570979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78260364608068861960761305 58695273456051646470570979)
                  ·
                    refine ⟨88042910184077469705856469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58695273456051646470570979 88042910184077469705856469)
                    ·
                      refine ⟨2063505707439315696231011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88042910184077469705856469 2063505707439315696231011)
                      ·
                        rfl

theorem cell23_4018663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4018663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018663 prefixEnd_4018663 := by exact prefixLift 4018663
  have htrace : WordTrace (prefixWord ++ tailWord_4018663) baseStart_4018663 baseEnd_4018663 := by
    simpa [prefixWord, tailWord_4018663, baseEnd_4018663] using wordTrace_append hprefix tailTrace_4018663
  have hstable : (prefixWord ++ tailWord_4018663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018663).length < 2 ^ (prefixWord ++ tailWord_4018663).sum := by decide
  have hdescent : baseEnd_4018663 < baseStart_4018663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018670 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4018670 : Nat := 118140960795 + 4018670 * 2 ^ 59
def prefixEnd_4018670 : Nat := 4983230072969 + 3 ^ 40 * 4018670 * 2
def baseEnd_4018670 : Nat := 687836433934632389614493

theorem tailTrace_4018670 : CollatzResearch.WordTrace tailWord_4018670 prefixEnd_4018670 687836433934632389614493 := by
  unfold tailWord_4018670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18321617043881549879906683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97715290900701599359502309 18321617043881549879906683)
  ·
    refine ⟨27482425565822324819860025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18321617043881549879906683 27482425565822324819860025)
    ·
      refine ⟨20611819174366743614895019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27482425565822324819860025 20611819174366743614895019)
      ·
        refine ⟨30917728761550115422342529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20611819174366743614895019 30917728761550115422342529)
        ·
          refine ⟨23188296571162586566756897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30917728761550115422342529 23188296571162586566756897)
          ·
            refine ⟨17391222428371939925067673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23188296571162586566756897 17391222428371939925067673)
            ·
              refine ⟨13043416821278954943800755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17391222428371939925067673 13043416821278954943800755)
              ·
                refine ⟨19565125231918432415701133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13043416821278954943800755 19565125231918432415701133)
                ·
                  refine ⟨7336921961969412155887925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19565125231918432415701133 7336921961969412155887925)
                  ·
                    refine ⟨687836433934632389614493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7336921961969412155887925 687836433934632389614493)
                    ·
                      rfl

theorem cell23_4018670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4018670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018670 prefixEnd_4018670 := by exact prefixLift 4018670
  have htrace : WordTrace (prefixWord ++ tailWord_4018670) baseStart_4018670 baseEnd_4018670 := by
    simpa [prefixWord, tailWord_4018670, baseEnd_4018670] using wordTrace_append hprefix tailTrace_4018670
  have hstable : (prefixWord ++ tailWord_4018670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018670).length < 2 ^ (prefixWord ++ tailWord_4018670).sum := by decide
  have hdescent : baseEnd_4018670 < baseStart_4018670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018694 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4018694 : Nat := 118140960795 + 4018694 * 2 ^ 59
def prefixEnd_4018694 : Nat := 4983230072969 + 3 ^ 40 * 4018694 * 2
def baseEnd_4018694 : Nat := 2063521625339605074943369

theorem tailTrace_4018694 : CollatzResearch.WordTrace tailWord_4018694 prefixEnd_4018694 2063521625339605074943369 := by
  unfold tailWord_4018694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580431615717670348066473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97715874468643634092084757 4580431615717670348066473)
  ·
    refine ⟨3435323711788252761049855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4580431615717670348066473 3435323711788252761049855)
    ·
      refine ⟨5152985567682379141574783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3435323711788252761049855 5152985567682379141574783)
      ·
        refine ⟨7729478351523568712362175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152985567682379141574783 7729478351523568712362175)
        ·
          refine ⟨11594217527285353068543263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729478351523568712362175 11594217527285353068543263)
          ·
            refine ⟨17391326290928029602814895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11594217527285353068543263 17391326290928029602814895)
            ·
              refine ⟨26086989436392044404222343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391326290928029602814895 26086989436392044404222343)
              ·
                refine ⟨39130484154588066606333515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26086989436392044404222343 39130484154588066606333515)
                ·
                  refine ⟨58695726231882099909500273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39130484154588066606333515 58695726231882099909500273)
                  ·
                    refine ⟨44021794673911574932125205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58695726231882099909500273 44021794673911574932125205)
                    ·
                      refine ⟨2063521625339605074943369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44021794673911574932125205 2063521625339605074943369)
                      ·
                        rfl

theorem cell23_4018694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4018694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018694 prefixEnd_4018694 := by exact prefixLift 4018694
  have htrace : WordTrace (prefixWord ++ tailWord_4018694) baseStart_4018694 baseEnd_4018694 := by
    simpa [prefixWord, tailWord_4018694, baseEnd_4018694] using wordTrace_append hprefix tailTrace_4018694
  have hstable : (prefixWord ++ tailWord_4018694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018694).length < 2 ^ (prefixWord ++ tailWord_4018694).sum := by decide
  have hdescent : baseEnd_4018694 < baseStart_4018694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018701 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4018701 : Nat := 118140960795 + 4018701 * 2 ^ 59
def prefixEnd_4018701 : Nat := 4983230072969 + 3 ^ 40 * 4018701 * 2
def baseEnd_4018701 : Nat := 2063525219704186547555837

theorem tailTrace_4018701 : CollatzResearch.WordTrace tailWord_4018701 prefixEnd_4018701 2063525219704186547555837 := by
  unfold tailWord_4018701
  simp only [CollatzResearch.WordTrace]
  refine ⟨146574067013940091333631957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97716044675960060889087971 146574067013940091333631957)
  ·
    refine ⟨3435329695639220890631999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 146574067013940091333631957 3435329695639220890631999)
    ·
      refine ⟨5152994543458831335947999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3435329695639220890631999 5152994543458831335947999)
      ·
        refine ⟨7729491815188247003921999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152994543458831335947999 7729491815188247003921999)
        ·
          refine ⟨11594237722782370505882999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729491815188247003921999 11594237722782370505882999)
          ·
            refine ⟨17391356584173555758824499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11594237722782370505882999 17391356584173555758824499)
            ·
              refine ⟨26087034876260333638236749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391356584173555758824499 26087034876260333638236749)
              ·
                refine ⟨9782638078597625114338781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26087034876260333638236749 9782638078597625114338781)
                ·
                  refine ⟨3668489279474109417877043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9782638078597625114338781 3668489279474109417877043)
                  ·
                    refine ⟨5502733919211164126815565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668489279474109417877043 5502733919211164126815565)
                    ·
                      refine ⟨2063525219704186547555837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502733919211164126815565 2063525219704186547555837)
                      ·
                        rfl

theorem cell23_4018701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4018701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018701 prefixEnd_4018701 := by exact prefixLift 4018701
  have htrace : WordTrace (prefixWord ++ tailWord_4018701) baseStart_4018701 baseEnd_4018701 := by
    simpa [prefixWord, tailWord_4018701, baseEnd_4018701] using wordTrace_append hprefix tailTrace_4018701
  have hstable : (prefixWord ++ tailWord_4018701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018701).length < 2 ^ (prefixWord ++ tailWord_4018701).sum := by decide
  have hdescent : baseEnd_4018701 < baseStart_4018701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018703 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_4018703 : Nat := 118140960795 + 4018703 * 2 ^ 59
def prefixEnd_4018703 : Nat := 4983230072969 + 3 ^ 40 * 4018703 * 2
def baseEnd_4018703 : Nat := 2063526246665495539730827

theorem tailTrace_4018703 : CollatzResearch.WordTrace tailWord_4018703 prefixEnd_4018703 2063526246665495539730827 := by
  unfold tailWord_4018703
  simp only [CollatzResearch.WordTrace]
  refine ⟨146574139959932845675204763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97716093306621897116803175 146574139959932845675204763)
  ·
    refine ⟨219861209939899268512807145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146574139959932845675204763 219861209939899268512807145)
    ·
      refine ⟨164895907454924451384605359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219861209939899268512807145 164895907454924451384605359)
      ·
        refine ⟨247343861182386677076908039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164895907454924451384605359 247343861182386677076908039)
        ·
          refine ⟨371015791773580015615362059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247343861182386677076908039 371015791773580015615362059)
          ·
            refine ⟨556523687660370023423043089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371015791773580015615362059 556523687660370023423043089)
            ·
              refine ⟨417392765745277517567282317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556523687660370023423043089 417392765745277517567282317)
              ·
                refine ⟨156522287154479069087730869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417392765745277517567282317 156522287154479069087730869)
                ·
                  refine ⟨14673964420732412726974769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156522287154479069087730869 14673964420732412726974769)
                  ·
                    refine ⟨11005473315549309545231077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14673964420732412726974769 11005473315549309545231077)
                    ·
                      refine ⟨2063526246665495539730827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11005473315549309545231077 2063526246665495539730827)
                      ·
                        rfl

theorem cell23_4018703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_4018703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018703 prefixEnd_4018703 := by exact prefixLift 4018703
  have htrace : WordTrace (prefixWord ++ tailWord_4018703) baseStart_4018703 baseEnd_4018703 := by
    simpa [prefixWord, tailWord_4018703, baseEnd_4018703] using wordTrace_append hprefix tailTrace_4018703
  have hstable : (prefixWord ++ tailWord_4018703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018703).length < 2 ^ (prefixWord ++ tailWord_4018703).sum := by decide
  have hdescent : baseEnd_4018703 < baseStart_4018703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018717 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_4018717 : Nat := 118140960795 + 4018717 * 2 ^ 59
def prefixEnd_4018717 : Nat := 4983230072969 + 3 ^ 40 * 4018717 * 2
def baseEnd_4018717 : Nat := 687844478464886161651921

theorem tailTrace_4018717 : CollatzResearch.WordTrace tailWord_4018717 prefixEnd_4018717 687844478464886161651921 := by
  unfold tailWord_4018717
  simp only [CollatzResearch.WordTrace]
  refine ⟨146574650581882126066214405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97716433721254750710809603 146574650581882126066214405)
  ·
    refine ⟨27482746984102898637415201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146574650581882126066214405 27482746984102898637415201)
    ·
      refine ⟨20612060238077173978061401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27482746984102898637415201 20612060238077173978061401)
      ·
        refine ⟨15459045178557880483546051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20612060238077173978061401 15459045178557880483546051)
        ·
          refine ⟨23188567767836820725319077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15459045178557880483546051 23188567767836820725319077)
          ·
            refine ⟨4347856456469403885997327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23188567767836820725319077 4347856456469403885997327)
            ·
              refine ⟨6521784684704105828995991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347856456469403885997327 6521784684704105828995991)
              ·
                refine ⟨9782677027056158743493987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521784684704105828995991 9782677027056158743493987)
                ·
                  refine ⟨14674015540584238115240981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9782677027056158743493987 14674015540584238115240981)
                  ·
                    refine ⟨687844478464886161651921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14674015540584238115240981 687844478464886161651921)
                    ·
                      rfl

theorem cell23_4018717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_4018717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018717 prefixEnd_4018717 := by exact prefixLift 4018717
  have htrace : WordTrace (prefixWord ++ tailWord_4018717) baseStart_4018717 baseEnd_4018717 := by
    simpa [prefixWord, tailWord_4018717, baseEnd_4018717] using wordTrace_append hprefix tailTrace_4018717
  have hstable : (prefixWord ++ tailWord_4018717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018717).length < 2 ^ (prefixWord ++ tailWord_4018717).sum := by decide
  have hdescent : baseEnd_4018717 < baseStart_4018717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018730 : List Nat := [3, 1, 4, 1, 1, 3, 1, 9]
def baseStart_4018730 : Nat := 118140960795 + 4018730 * 2 ^ 59
def prefixEnd_4018730 : Nat := 4983230072969 + 3 ^ 40 * 4018730 * 2
def baseEnd_4018730 : Nat := 76427411505302479040489

theorem tailTrace_4018730 : CollatzResearch.WordTrace tailWord_4018730 prefixEnd_4018730 76427411505302479040489 := by
  unfold tailWord_4018730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643781182708757321609411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97716749820556686190958429 36643781182708757321609411)
  ·
    refine ⟨54965671774063135982414117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36643781182708757321609411 54965671774063135982414117)
    ·
      refine ⟨10306063457636837996702647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54965671774063135982414117 10306063457636837996702647)
      ·
        refine ⟨15459095186455256995053971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306063457636837996702647 15459095186455256995053971)
        ·
          refine ⟨23188642779682885492580957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15459095186455256995053971 23188642779682885492580957)
          ·
            refine ⟨8695741042381082059717859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23188642779682885492580957 8695741042381082059717859)
            ·
              refine ⟨13043611563571623089576789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695741042381082059717859 13043611563571623089576789)
              ·
                refine ⟨76427411505302479040489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13043611563571623089576789 76427411505302479040489)
                ·
                  rfl

theorem cell23_4018730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_4018730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018730 prefixEnd_4018730 := by exact prefixLift 4018730
  have htrace : WordTrace (prefixWord ++ tailWord_4018730) baseStart_4018730 baseEnd_4018730 := by
    simpa [prefixWord, tailWord_4018730, baseEnd_4018730] using wordTrace_append hprefix tailTrace_4018730
  have hstable : (prefixWord ++ tailWord_4018730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018730).length < 2 ^ (prefixWord ++ tailWord_4018730).sum := by decide
  have hdescent : baseEnd_4018730 < baseStart_4018730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018757 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_4018757 : Nat := 118140960795 + 4018757 * 2 ^ 59
def prefixEnd_4018757 : Nat := 4983230072969 + 3 ^ 40 * 4018757 * 2
def baseEnd_4018757 : Nat := 2063553974620838328455579

theorem tailTrace_4018757 : CollatzResearch.WordTrace tailWord_4018757 prefixEnd_4018757 2063553974620838328455579 := by
  unfold tailWord_4018757
  simp only [CollatzResearch.WordTrace]
  refine ⟨146576109501737212897670525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97717406334491475265113683 146576109501737212897670525)
  ·
    refine ⟨54966041063151454836626447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146576109501737212897670525 54966041063151454836626447)
    ·
      refine ⟨82449061594727182254939671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54966041063151454836626447 82449061594727182254939671)
      ·
        refine ⟨123673592392090773382409507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82449061594727182254939671 123673592392090773382409507)
        ·
          refine ⟨185510388588136160073614261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123673592392090773382409507 185510388588136160073614261)
          ·
            refine ⟨17391598930137765006901337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185510388588136160073614261 17391598930137765006901337)
            ·
              refine ⟨13043699197603323755176003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17391598930137765006901337 13043699197603323755176003)
              ·
                refine ⟨19565548796404985632764005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13043699197603323755176003 19565548796404985632764005)
                ·
                  refine ⟨3668540399325934806143251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19565548796404985632764005 3668540399325934806143251)
                  ·
                    refine ⟨5502810598988902209214877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668540399325934806143251 5502810598988902209214877)
                    ·
                      refine ⟨2063553974620838328455579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5502810598988902209214877 2063553974620838328455579)
                      ·
                        rfl

theorem cell23_4018757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_4018757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018757 prefixEnd_4018757 := by exact prefixLift 4018757
  have htrace : WordTrace (prefixWord ++ tailWord_4018757) baseStart_4018757 baseEnd_4018757 := by
    simpa [prefixWord, tailWord_4018757, baseEnd_4018757] using wordTrace_append hprefix tailTrace_4018757
  have hstable : (prefixWord ++ tailWord_4018757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018757).length < 2 ^ (prefixWord ++ tailWord_4018757).sum := by decide
  have hdescent : baseEnd_4018757 < baseStart_4018757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018758 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4018758 : Nat := 118140960795 + 4018758 * 2 ^ 59
def prefixEnd_4018758 : Nat := 4983230072969 + 3 ^ 40 * 4018758 * 2
def baseEnd_4018758 : Nat := 2063554488101492824543075

theorem tailTrace_4018758 : CollatzResearch.WordTrace tailWord_4018758 prefixEnd_4018758 2063554488101492824543075 := by
  unfold tailWord_4018758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580504561710424689639279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97717430649822393378971285 4580504561710424689639279)
  ·
    refine ⟨6870756842565637034458919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580504561710424689639279 6870756842565637034458919)
    ·
      refine ⟨10306135263848455551688379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870756842565637034458919 10306135263848455551688379)
      ·
        refine ⟨15459202895772683327532569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306135263848455551688379 15459202895772683327532569)
        ·
          refine ⟨11594402171829512495649427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15459202895772683327532569 11594402171829512495649427)
          ·
            refine ⟨17391603257744268743474141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11594402171829512495649427 17391603257744268743474141)
            ·
              refine ⟨6521851221654100778802803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17391603257744268743474141 6521851221654100778802803)
              ·
                refine ⟨9782776832481151168204205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521851221654100778802803 9782776832481151168204205)
                ·
                  refine ⟨3668541312180431688076577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9782776832481151168204205 3668541312180431688076577)
                  ·
                    refine ⟨2751405984135323766057433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3668541312180431688076577 2751405984135323766057433)
                    ·
                      refine ⟨2063554488101492824543075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751405984135323766057433 2063554488101492824543075)
                      ·
                        rfl

theorem cell23_4018758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4018758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018758 prefixEnd_4018758 := by exact prefixLift 4018758
  have htrace : WordTrace (prefixWord ++ tailWord_4018758) baseStart_4018758 baseEnd_4018758 := by
    simpa [prefixWord, tailWord_4018758, baseEnd_4018758] using wordTrace_append hprefix tailTrace_4018758
  have hstable : (prefixWord ++ tailWord_4018758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018758).length < 2 ^ (prefixWord ++ tailWord_4018758).sum := by decide
  have hdescent : baseEnd_4018758 < baseStart_4018758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018784 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 1, 3, 2]
def baseStart_4018784 : Nat := 118140960795 + 4018784 * 2 ^ 59
def prefixEnd_4018784 : Nat := 4983230072969 + 3 ^ 40 * 4018784 * 2
def baseEnd_4018784 : Nat := 2063567838598509722817955

theorem tailTrace_4018784 : CollatzResearch.WordTrace tailWord_4018784 prefixEnd_4018784 2063567838598509722817955 := by
  unfold tailWord_4018784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73288547136319698254451703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97718062848426264339268937 73288547136319698254451703)
  ·
    refine ⟨109932820704479547381677555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73288547136319698254451703 109932820704479547381677555)
    ·
      refine ⟨164899231056719321072516333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109932820704479547381677555 164899231056719321072516333)
      ·
        refine ⟨61837211646269745402193625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164899231056719321072516333 61837211646269745402193625)
        ·
          refine ⟨46377908734702309051645219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61837211646269745402193625 46377908734702309051645219)
          ·
            refine ⟨69566863102053463577467829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46377908734702309051645219 69566863102053463577467829)
            ·
              refine ⟨6521893415817512210387609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69566863102053463577467829 6521893415817512210387609)
              ·
                refine ⟨4891420061863134157790707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521893415817512210387609 4891420061863134157790707)
                ·
                  refine ⟨7337130092794701236686061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891420061863134157790707 7337130092794701236686061)
                  ·
                    refine ⟨2751423784798012963757273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7337130092794701236686061 2751423784798012963757273)
                    ·
                      refine ⟨2063567838598509722817955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751423784798012963757273 2063567838598509722817955)
                      ·
                        rfl

theorem cell23_4018784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_4018784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018784 prefixEnd_4018784 := by exact prefixLift 4018784
  have htrace : WordTrace (prefixWord ++ tailWord_4018784) baseStart_4018784 baseEnd_4018784 := by
    simpa [prefixWord, tailWord_4018784, baseEnd_4018784] using wordTrace_append hprefix tailTrace_4018784
  have hstable : (prefixWord ++ tailWord_4018784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018784).length < 2 ^ (prefixWord ++ tailWord_4018784).sum := by decide
  have hdescent : baseEnd_4018784 < baseStart_4018784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018803 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 11]
def baseStart_4018803 : Nat := 118140960795 + 4018803 * 2 ^ 59
def prefixEnd_4018803 : Nat := 4983230072969 + 3 ^ 40 * 4018803 * 2
def baseEnd_4018803 : Nat := 229286399414549460942263

theorem tailTrace_4018803 : CollatzResearch.WordTrace tailWord_4018803 prefixEnd_4018803 229286399414549460942263 := by
  unfold tailWord_4018803
  simp only [CollatzResearch.WordTrace]
  refine ⟨146577787259570562753845063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97718524839713708502563375 146577787259570562753845063)
  ·
    refine ⟨219866680889355844130767595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146577787259570562753845063 219866680889355844130767595)
    ·
      refine ⟨329800021334033766196151393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219866680889355844130767595 329800021334033766196151393)
      ·
        refine ⟨247350016000525324647113545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329800021334033766196151393 247350016000525324647113545)
        ·
          refine ⟨185512512000393993485335159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247350016000525324647113545 185512512000393993485335159)
          ·
            refine ⟨278268768000590990228002739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185512512000393993485335159 278268768000590990228002739)
            ·
              refine ⟨417403152000886485342004109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278268768000590990228002739 417403152000886485342004109)
              ·
                refine ⟨156526182000332432003251541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417403152000886485342004109 156526182000332432003251541)
                ·
                  refine ⟨229286399414549460942263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 156526182000332432003251541 229286399414549460942263)
                  ·
                    rfl

theorem cell23_4018803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 11].length) (baseStart_4018803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018803 prefixEnd_4018803 := by exact prefixLift 4018803
  have htrace : WordTrace (prefixWord ++ tailWord_4018803) baseStart_4018803 baseEnd_4018803 := by
    simpa [prefixWord, tailWord_4018803, baseEnd_4018803] using wordTrace_append hprefix tailTrace_4018803
  have hstable : (prefixWord ++ tailWord_4018803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018803).length < 2 ^ (prefixWord ++ tailWord_4018803).sum := by decide
  have hdescent : baseEnd_4018803 < baseStart_4018803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018865 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4018865 : Nat := 118140960795 + 4018865 * 2 ^ 59
def prefixEnd_4018865 : Nat := 4983230072969 + 3 ^ 40 * 4018865 * 2
def baseEnd_4018865 : Nat := 2063609430531523905905083

theorem tailTrace_4018865 : CollatzResearch.WordTrace tailWord_4018865 prefixEnd_4018865 2063609430531523905905083 := by
  unfold tailWord_4018865
  simp only [CollatzResearch.WordTrace]
  refine ⟨146580048585345947342602049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97720032390230631561734699 146580048585345947342602049)
  ·
    refine ⟨109935036439009460506951537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146580048585345947342602049 109935036439009460506951537)
    ·
      refine ⟨82451277329257095380213653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109935036439009460506951537 82451277329257095380213653)
      ·
        refine ⟨3864903624808926345947515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82451277329257095380213653 3864903624808926345947515)
        ·
          refine ⟨5797355437213389518921273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864903624808926345947515 5797355437213389518921273)
          ·
            refine ⟨4348016577910042139190955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797355437213389518921273 4348016577910042139190955)
            ·
              refine ⟨6522024866865063208786433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348016577910042139190955 6522024866865063208786433)
              ·
                refine ⟨4891518650148797406589825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6522024866865063208786433 4891518650148797406589825)
                ·
                  refine ⟨3668638987611598054942369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4891518650148797406589825 3668638987611598054942369)
                  ·
                    refine ⟨2751479240708698541206777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3668638987611598054942369 2751479240708698541206777)
                    ·
                      refine ⟨2063609430531523905905083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751479240708698541206777 2063609430531523905905083)
                      ·
                        rfl

theorem cell23_4018865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4018865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018865 prefixEnd_4018865 := by exact prefixLift 4018865
  have htrace : WordTrace (prefixWord ++ tailWord_4018865) baseStart_4018865 baseEnd_4018865 := by
    simpa [prefixWord, tailWord_4018865, baseEnd_4018865] using wordTrace_append hprefix tailTrace_4018865
  have hstable : (prefixWord ++ tailWord_4018865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018865).length < 2 ^ (prefixWord ++ tailWord_4018865).sum := by decide
  have hdescent : baseEnd_4018865 < baseStart_4018865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018887 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_4018887 : Nat := 118140960795 + 4018887 * 2 ^ 59
def prefixEnd_4018887 : Nat := 4983230072969 + 3 ^ 40 * 4018887 * 2
def baseEnd_4018887 : Nat := 2063620727105922819829981

theorem tailTrace_4018887 : CollatzResearch.WordTrace tailWord_4018887 prefixEnd_4018887 2063620727105922819829981 := by
  unfold tailWord_4018887
  simp only [CollatzResearch.WordTrace]
  refine ⟨146580850991266245099902915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97720567327510830066601943 146580850991266245099902915)
  ·
    refine ⟨219871276486899367649854373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146580850991266245099902915 219871276486899367649854373)
    ·
      refine ⟨41225864341293631434347695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219871276486899367649854373 41225864341293631434347695)
      ·
        refine ⟨61838796511940447151521543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41225864341293631434347695 61838796511940447151521543)
        ·
          refine ⟨92758194767910670727282315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61838796511940447151521543 92758194767910670727282315)
          ·
            refine ⟨139137292151866006090923473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92758194767910670727282315 139137292151866006090923473)
            ·
              refine ⟨104352969113899504568192605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139137292151866006090923473 104352969113899504568192605)
              ·
                refine ⟨39132363417712314213072227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104352969113899504568192605 39132363417712314213072227)
                ·
                  refine ⟨58698545126568471319608341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39132363417712314213072227 58698545126568471319608341)
                  ·
                    refine ⟨2751494302807897093106641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58698545126568471319608341 2751494302807897093106641)
                    ·
                      refine ⟨2063620727105922819829981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751494302807897093106641 2063620727105922819829981)
                      ·
                        rfl

theorem cell23_4018887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_4018887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018887 prefixEnd_4018887 := by exact prefixLift 4018887
  have htrace : WordTrace (prefixWord ++ tailWord_4018887) baseStart_4018887 baseEnd_4018887 := by
    simpa [prefixWord, tailWord_4018887, baseEnd_4018887] using wordTrace_append hprefix tailTrace_4018887
  have hstable : (prefixWord ++ tailWord_4018887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018887).length < 2 ^ (prefixWord ++ tailWord_4018887).sum := by decide
  have hdescent : baseEnd_4018887 < baseStart_4018887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018897 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 3, 4]
def baseStart_4018897 : Nat := 118140960795 + 4018897 * 2 ^ 59
def prefixEnd_4018897 : Nat := 4983230072969 + 3 ^ 40 * 4018897 * 2
def baseEnd_4018897 : Nat := 687875287304155926901645

theorem tailTrace_4018897 : CollatzResearch.WordTrace tailWord_4018897 prefixEnd_4018897 687875287304155926901645 := by
  unfold tailWord_4018897
  simp only [CollatzResearch.WordTrace]
  refine ⟨146581215721230016807766945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97720810480820011205177963 146581215721230016807766945)
  ·
    refine ⟨109935911790922512605825209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146581215721230016807766945 109935911790922512605825209)
    ·
      refine ⟨82451933843191884454368907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109935911790922512605825209 82451933843191884454368907)
      ·
        refine ⟨123677900764787826681553361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82451933843191884454368907 123677900764787826681553361)
        ·
          refine ⟨92758425573590870011165021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123677900764787826681553361 92758425573590870011165021)
          ·
            refine ⟨34784409590096576254186883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92758425573590870011165021 34784409590096576254186883)
            ·
              refine ⟨52176614385144864381280325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34784409590096576254186883 52176614385144864381280325)
              ·
                refine ⟨9783115197214662071490061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52176614385144864381280325 9783115197214662071490061)
                ·
                  refine ⟨3668668198955498276808773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9783115197214662071490061 3668668198955498276808773)
                  ·
                    refine ⟨687875287304155926901645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668668198955498276808773 687875287304155926901645)
                    ·
                      rfl

theorem cell23_4018897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_4018897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018897 prefixEnd_4018897 := by exact prefixLift 4018897
  have htrace : WordTrace (prefixWord ++ tailWord_4018897) baseStart_4018897 baseEnd_4018897 := by
    simpa [prefixWord, tailWord_4018897, baseEnd_4018897] using wordTrace_append hprefix tailTrace_4018897
  have hstable : (prefixWord ++ tailWord_4018897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018897).length < 2 ^ (prefixWord ++ tailWord_4018897).sum := by decide
  have hdescent : baseEnd_4018897 < baseStart_4018897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018954 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_4018954 : Nat := 118140960795 + 4018954 * 2 ^ 59
def prefixEnd_4018954 : Nat := 4983230072969 + 3 ^ 40 * 4018954 * 2
def baseEnd_4018954 : Nat := 2063655130309774057692173

theorem tailTrace_4018954 : CollatzResearch.WordTrace tailWord_4018954 prefixEnd_4018954 2063655130309774057692173 := by
  unfold tailWord_4018954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36645823670505878885647979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97722196454682343695061277 36645823670505878885647979)
  ·
    refine ⟨54968735505758818328471969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36645823670505878885647979 54968735505758818328471969)
    ·
      refine ⟨41226551629319113746353977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54968735505758818328471969 41226551629319113746353977)
      ·
        refine ⟨30919913721989335309765483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41226551629319113746353977 30919913721989335309765483)
        ·
          refine ⟨46379870582984002964648225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30919913721989335309765483 46379870582984002964648225)
          ·
            refine ⟨34784902937238002223486169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46379870582984002964648225 34784902937238002223486169)
            ·
              refine ⟨26088677202928501667614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34784902937238002223486169 26088677202928501667614627)
              ·
                refine ⟨39133015804392752501421941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26088677202928501667614627 39133015804392752501421941)
                ·
                  refine ⟨3668720231661820547008307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39133015804392752501421941 3668720231661820547008307)
                  ·
                    refine ⟨5503080347492730820512461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668720231661820547008307 5503080347492730820512461)
                    ·
                      refine ⟨2063655130309774057692173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5503080347492730820512461 2063655130309774057692173)
                      ·
                        rfl

theorem cell23_4018954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_4018954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4018954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4018954 prefixEnd_4018954 := by exact prefixLift 4018954
  have htrace : WordTrace (prefixWord ++ tailWord_4018954) baseStart_4018954 baseEnd_4018954 := by
    simpa [prefixWord, tailWord_4018954, baseEnd_4018954] using wordTrace_append hprefix tailTrace_4018954
  have hstable : (prefixWord ++ tailWord_4018954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018954).length < 2 ^ (prefixWord ++ tailWord_4018954).sum := by decide
  have hdescent : baseEnd_4018954 < baseStart_4018954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019011 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 3, 2, 2]
def baseStart_4019011 : Nat := 118140960795 + 4019011 * 2 ^ 59
def prefixEnd_4019011 : Nat := 4983230072969 + 3 ^ 40 * 4019011 * 2
def baseEnd_4019011 : Nat := 2063684398707080334679411

theorem tailTrace_4019011 : CollatzResearch.WordTrace tailWord_4019011 prefixEnd_4019011 2063684398707080334679411 := by
  unfold tailWord_4019011
  simp only [CollatzResearch.WordTrace]
  refine ⟨146585373642817014277416887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97723582428544676184944591 146585373642817014277416887)
  ·
    refine ⟨219878060464225521416125331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146585373642817014277416887 219878060464225521416125331)
    ·
      refine ⟨329817090696338282124187997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219878060464225521416125331 329817090696338282124187997)
      ·
        refine ⟨123681409011126855796570499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329817090696338282124187997 123681409011126855796570499)
        ·
          refine ⟨185522113516690283694855749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123681409011126855796570499 185522113516690283694855749)
          ·
            refine ⟨34785396284379428192785453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185522113516690283694855749 34785396284379428192785453)
            ·
              refine ⟨13044523606642285572294545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34785396284379428192785453 13044523606642285572294545)
              ·
                refine ⟨9783392704981714179220909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13044523606642285572294545 9783392704981714179220909)
                ·
                  refine ⟨3668772264368142817207841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9783392704981714179220909 3668772264368142817207841)
                  ·
                    refine ⟨2751579198276107112905881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3668772264368142817207841 2751579198276107112905881)
                    ·
                      refine ⟨2063684398707080334679411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751579198276107112905881 2063684398707080334679411)
                      ·
                        rfl

theorem cell23_4019011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_4019011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019011 prefixEnd_4019011 := by exact prefixLift 4019011
  have htrace : WordTrace (prefixWord ++ tailWord_4019011) baseStart_4019011 baseEnd_4019011 := by
    simpa [prefixWord, tailWord_4019011, baseEnd_4019011] using wordTrace_append hprefix tailTrace_4019011
  have hstable : (prefixWord ++ tailWord_4019011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019011).length < 2 ^ (prefixWord ++ tailWord_4019011).sum := by decide
  have hdescent : baseEnd_4019011 < baseStart_4019011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019031 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_4019031 : Nat := 118140960795 + 4019031 * 2 ^ 59
def prefixEnd_4019031 : Nat := 4983230072969 + 3 ^ 40 * 4019031 * 2
def baseEnd_4019031 : Nat := 2063694668320170256429319

theorem tailTrace_4019031 : CollatzResearch.WordTrace tailWord_4019031 prefixEnd_4019031 2063694668320170256429319 := by
  unfold tailWord_4019031
  simp only [CollatzResearch.WordTrace]
  refine ⟨146586103102744557693144947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97724068735163038462096631 146586103102744557693144947)
  ·
    refine ⟨219879154654116836539717421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146586103102744557693144947 219879154654116836539717421)
    ·
      refine ⟨82454682995293813702394033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219879154654116836539717421 82454682995293813702394033)
      ·
        refine ⟨61841012246470360276795525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82454682995293813702394033 61841012246470360276795525)
        ·
          refine ⟨11595189796213192551899161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61841012246470360276795525 11595189796213192551899161)
          ·
            refine ⟨8696392347159894413924371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11595189796213192551899161 8696392347159894413924371)
            ·
              refine ⟨13044588520739841620886557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696392347159894413924371 13044588520739841620886557)
              ·
                refine ⟨4891720695277440607832459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13044588520739841620886557 4891720695277440607832459)
                ·
                  refine ⟨7337581042916160911748689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891720695277440607832459 7337581042916160911748689)
                  ·
                    refine ⟨5503185782187120683811517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7337581042916160911748689 5503185782187120683811517)
                    ·
                      refine ⟨2063694668320170256429319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5503185782187120683811517 2063694668320170256429319)
                      ·
                        rfl

theorem cell23_4019031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_4019031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019031 prefixEnd_4019031 := by exact prefixLift 4019031
  have htrace : WordTrace (prefixWord ++ tailWord_4019031) baseStart_4019031 baseEnd_4019031 := by
    simpa [prefixWord, tailWord_4019031, baseEnd_4019031] using wordTrace_append hprefix tailTrace_4019031
  have hstable : (prefixWord ++ tailWord_4019031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019031).length < 2 ^ (prefixWord ++ tailWord_4019031).sum := by decide
  have hdescent : baseEnd_4019031 < baseStart_4019031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019061 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4019061 : Nat := 118140960795 + 4019061 * 2 ^ 59
def prefixEnd_4019061 : Nat := 4983230072969 + 3 ^ 40 * 4019061 * 2
def baseEnd_4019061 : Nat := 2063710072739805139054181

theorem tailTrace_4019061 : CollatzResearch.WordTrace tailWord_4019061 prefixEnd_4019061 2063710072739805139054181 := by
  unfold tailWord_4019061
  simp only [CollatzResearch.WordTrace]
  refine ⟨146587197292635872816737037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97724798195090581877824691 146587197292635872816737037)
  ·
    refine ⟨54970198984738452306276389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146587197292635872816737037 54970198984738452306276389)
    ·
      refine ⟨10306912309638459807426823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54970198984738452306276389 10306912309638459807426823)
      ·
        refine ⟨15460368464457689711140235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306912309638459807426823 15460368464457689711140235)
        ·
          refine ⟨23190552696686534566710353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460368464457689711140235 23190552696686534566710353)
          ·
            refine ⟨17392914522514900925032765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23190552696686534566710353 17392914522514900925032765)
            ·
              refine ⟨6522342945943087846887287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17392914522514900925032765 6522342945943087846887287)
              ·
                refine ⟨9783514418914631770330931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522342945943087846887287 9783514418914631770330931)
                ·
                  refine ⟨14675271628371947655496397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9783514418914631770330931 14675271628371947655496397)
                  ·
                    refine ⟨5503226860639480370811149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14675271628371947655496397 5503226860639480370811149)
                    ·
                      refine ⟨2063710072739805139054181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5503226860639480370811149 2063710072739805139054181)
                      ·
                        rfl

theorem cell23_4019061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4019061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019061 prefixEnd_4019061 := by exact prefixLift 4019061
  have htrace : WordTrace (prefixWord ++ tailWord_4019061) baseStart_4019061 baseEnd_4019061 := by
    simpa [prefixWord, tailWord_4019061, baseEnd_4019061] using wordTrace_append hprefix tailTrace_4019061
  have hstable : (prefixWord ++ tailWord_4019061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019061).length < 2 ^ (prefixWord ++ tailWord_4019061).sum := by decide
  have hdescent : baseEnd_4019061 < baseStart_4019061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019067 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4]
def baseStart_4019067 : Nat := 118140960795 + 4019067 * 2 ^ 59
def prefixEnd_4019067 : Nat := 4983230072969 + 3 ^ 40 * 4019067 * 2
def baseEnd_4019067 : Nat := 2063713153623732115579153

theorem tailTrace_4019067 : CollatzResearch.WordTrace tailWord_4019067 prefixEnd_4019067 2063713153623732115579153 := by
  unfold tailWord_4019067
  simp only [CollatzResearch.WordTrace]
  refine ⟨146587416130614135841455455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97724944087076090560970303 146587416130614135841455455)
  ·
    refine ⟨219881124195921203762183183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146587416130614135841455455 219881124195921203762183183)
    ·
      refine ⟨329821686293881805643274775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219881124195921203762183183 329821686293881805643274775)
      ·
        refine ⟨494732529440822708464912163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329821686293881805643274775 494732529440822708464912163)
        ·
          refine ⟨742098794161234062697368245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494732529440822708464912163 742098794161234062697368245)
          ·
            refine ⟨69571761952615693377878273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 742098794161234062697368245 69571761952615693377878273)
            ·
              refine ⟨52178821464461770033408705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69571761952615693377878273 52178821464461770033408705)
              ·
                refine ⟨39134116098346327525056529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52178821464461770033408705 39134116098346327525056529)
                ·
                  refine ⟨29350587073759745643792397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39134116098346327525056529 29350587073759745643792397)
                  ·
                    refine ⟨11006470152659904616422149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29350587073759745643792397 11006470152659904616422149)
                    ·
                      refine ⟨2063713153623732115579153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11006470152659904616422149 2063713153623732115579153)
                      ·
                        rfl

theorem cell23_4019067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_4019067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019067 prefixEnd_4019067 := by exact prefixLift 4019067
  have htrace : WordTrace (prefixWord ++ tailWord_4019067) baseStart_4019067 baseEnd_4019067 := by
    simpa [prefixWord, tailWord_4019067, baseEnd_4019067] using wordTrace_append hprefix tailTrace_4019067
  have hstable : (prefixWord ++ tailWord_4019067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019067).length < 2 ^ (prefixWord ++ tailWord_4019067).sum := by decide
  have hdescent : baseEnd_4019067 < baseStart_4019067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019071 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 1, 3, 2]
def baseStart_4019071 : Nat := 118140960795 + 4019071 * 2 ^ 59
def prefixEnd_4019071 : Nat := 4983230072969 + 3 ^ 40 * 4019071 * 2
def baseEnd_4019071 : Nat := 2063715207546350099929135

theorem tailTrace_4019071 : CollatzResearch.WordTrace tailWord_4019071 prefixEnd_4019071 2063715207546350099929135 := by
  unfold tailWord_4019071
  simp only [CollatzResearch.WordTrace]
  refine ⟨146587562022599644524601067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97725041348399763016400711 146587562022599644524601067)
  ·
    refine ⟨219881343033899466786901601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146587562022599644524601067 219881343033899466786901601)
    ·
      refine ⟨164911007275424600090176201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219881343033899466786901601 164911007275424600090176201)
      ·
        refine ⟨123683255456568450067632151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164911007275424600090176201 123683255456568450067632151)
        ·
          refine ⟨185524883184852675101448227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123683255456568450067632151 185524883184852675101448227)
          ·
            refine ⟨278287324777279012652172341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185524883184852675101448227 278287324777279012652172341)
            ·
              refine ⟨26089436697869907436141157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278287324777279012652172341 26089436697869907436141157)
              ·
                refine ⟨4891769380850607644276467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26089436697869907436141157 4891769380850607644276467)
                ·
                  refine ⟨7337654071275911466414701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891769380850607644276467 7337654071275911466414701)
                  ·
                    refine ⟨2751620276728466799905513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7337654071275911466414701 2751620276728466799905513)
                    ·
                      refine ⟨2063715207546350099929135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751620276728466799905513 2063715207546350099929135)
                      ·
                        rfl

theorem cell23_4019071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_4019071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019071 prefixEnd_4019071 := by exact prefixLift 4019071
  have htrace : WordTrace (prefixWord ++ tailWord_4019071) baseStart_4019071 baseEnd_4019071 := by
    simpa [prefixWord, tailWord_4019071, baseEnd_4019071] using wordTrace_append hprefix tailTrace_4019071
  have hstable : (prefixWord ++ tailWord_4019071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019071).length < 2 ^ (prefixWord ++ tailWord_4019071).sum := by decide
  have hdescent : baseEnd_4019071 < baseStart_4019071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019161 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 2, 5, 2]
def baseStart_4019161 : Nat := 118140960795 + 4019161 * 2 ^ 59
def prefixEnd_4019161 : Nat := 4983230072969 + 3 ^ 40 * 4019161 * 2
def baseEnd_4019161 : Nat := 2063761420805254747803721

theorem tailTrace_4019161 : CollatzResearch.WordTrace tailWord_4019161 prefixEnd_4019161 2063761420805254747803721 := by
  unfold tailWord_4019161
  simp only [CollatzResearch.WordTrace]
  refine ⟨146590844592273589895377337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97727229728182393263584891 146590844592273589895377337)
  ·
    refine ⟨109943133444205192421533003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146590844592273589895377337 109943133444205192421533003)
    ·
      refine ⟨164914700166307788632299505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109943133444205192421533003 164914700166307788632299505)
      ·
        refine ⟨123686025124730841474224629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164914700166307788632299505 123686025124730841474224629)
        ·
          refine ⟨11595564855443516388208559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123686025124730841474224629 11595564855443516388208559)
          ·
            refine ⟨17393347283165274582312839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595564855443516388208559 17393347283165274582312839)
            ·
              refine ⟨26090020924747911873469259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17393347283165274582312839 26090020924747911873469259)
              ·
                refine ⟨39135031387121867810203889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26090020924747911873469259 39135031387121867810203889)
                ·
                  refine ⟨29351273540341400857652917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39135031387121867810203889 29351273540341400857652917)
                  ·
                    refine ⟨2751681894407006330404961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29351273540341400857652917 2751681894407006330404961)
                    ·
                      refine ⟨2063761420805254747803721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2751681894407006330404961 2063761420805254747803721)
                      ·
                        rfl

theorem cell23_4019161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_4019161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019161 prefixEnd_4019161 := by exact prefixLift 4019161
  have htrace : WordTrace (prefixWord ++ tailWord_4019161) baseStart_4019161 baseEnd_4019161 := by
    simpa [prefixWord, tailWord_4019161, baseEnd_4019161] using wordTrace_append hprefix tailTrace_4019161
  have hstable : (prefixWord ++ tailWord_4019161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019161).length < 2 ^ (prefixWord ++ tailWord_4019161).sum := by decide
  have hdescent : baseEnd_4019161 < baseStart_4019161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019252 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4019252 : Nat := 118140960795 + 4019252 * 2 ^ 59
def prefixEnd_4019252 : Nat := 4983230072969 + 3 ^ 40 * 4019252 * 2
def baseEnd_4019252 : Nat := 687936049181604630588601

theorem tailTrace_4019252 : CollatzResearch.WordTrace tailWord_4019252 prefixEnd_4019252 687936049181604630588601 := by
  unfold tailWord_4019252
  simp only [CollatzResearch.WordTrace]
  refine ⟨73297081817471956218470005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97729442423295941624626673 73297081817471956218470005)
  ·
    refine ⟨6871601420387995895481563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73297081817471956218470005 6871601420387995895481563)
    ·
      refine ⟨10307402130581993843222345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871601420387995895481563 10307402130581993843222345)
      ·
        refine ⟨7730551597936495382416759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10307402130581993843222345 7730551597936495382416759)
        ·
          refine ⟨11595827396904743073625139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730551597936495382416759 11595827396904743073625139)
          ·
            refine ⟨17393741095357114610437709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595827396904743073625139 17393741095357114610437709)
            ·
              refine ⟨6522652910758917978914141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17393741095357114610437709 6522652910758917978914141)
              ·
                refine ⟨2445994841534594242092803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6522652910758917978914141 2445994841534594242092803)
                ·
                  refine ⟨3668992262301891363139205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445994841534594242092803 3668992262301891363139205)
                  ·
                    refine ⟨687936049181604630588601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668992262301891363139205 687936049181604630588601)
                    ·
                      rfl

theorem cell23_4019252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4019252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019252 prefixEnd_4019252 := by exact prefixLift 4019252
  have htrace : WordTrace (prefixWord ++ tailWord_4019252) baseStart_4019252 baseEnd_4019252 := by
    simpa [prefixWord, tailWord_4019252, baseEnd_4019252] using wordTrace_append hprefix tailTrace_4019252
  have hstable : (prefixWord ++ tailWord_4019252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019252).length < 2 ^ (prefixWord ++ tailWord_4019252).sum := by decide
  have hdescent : baseEnd_4019252 < baseStart_4019252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019311 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_4019311 : Nat := 118140960795 + 4019311 * 2 ^ 59
def prefixEnd_4019311 : Nat := 4983230072969 + 3 ^ 40 * 4019311 * 2
def baseEnd_4019311 : Nat := 2063838442903429160928031

theorem tailTrace_4019311 : CollatzResearch.WordTrace tailWord_4019311 prefixEnd_4019311 2063838442903429160928031 := by
  unfold tailWord_4019311
  simp only [CollatzResearch.WordTrace]
  refine ⟨146596315541730165513337787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97730877027820110342225191 146596315541730165513337787)
  ·
    refine ⟨219894473312595248270006681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146596315541730165513337787 219894473312595248270006681)
    ·
      refine ⟨164920854984446436202505011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219894473312595248270006681 164920854984446436202505011)
      ·
        refine ⟨247381282476669654303757517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164920854984446436202505011 247381282476669654303757517)
        ·
          refine ⟨92767980928751120363909069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247381282476669654303757517 92767980928751120363909069)
          ·
            refine ⟨34787992848281670136465901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92767980928751120363909069 34787992848281670136465901)
            ·
              refine ⟨13045497318105626301174713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34787992848281670136465901 13045497318105626301174713)
              ·
                refine ⟨9784122988579219725881035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045497318105626301174713 9784122988579219725881035)
                ·
                  refine ⟨14676184482868829588821553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784122988579219725881035 14676184482868829588821553)
                  ·
                    refine ⟨11007138362151622191616165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14676184482868829588821553 11007138362151622191616165)
                    ·
                      refine ⟨2063838442903429160928031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11007138362151622191616165 2063838442903429160928031)
                      ·
                        rfl

theorem cell23_4019311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_4019311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019311 prefixEnd_4019311 := by exact prefixLift 4019311
  have htrace : WordTrace (prefixWord ++ tailWord_4019311) baseStart_4019311 baseEnd_4019311 := by
    simpa [prefixWord, tailWord_4019311, baseEnd_4019311] using wordTrace_append hprefix tailTrace_4019311
  have hstable : (prefixWord ++ tailWord_4019311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019311).length < 2 ^ (prefixWord ++ tailWord_4019311).sum := by decide
  have hdescent : baseEnd_4019311 < baseStart_4019311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019321 : List Nat := [1, 2, 1, 3, 6, 10]
def baseStart_4019321 : Nat := 118140960795 + 4019321 * 2 ^ 59
def prefixEnd_4019321 : Nat := 4983230072969 + 3 ^ 40 * 4019321 * 2
def baseEnd_4019321 : Nat := 8493183447366148649395

theorem tailTrace_4019321 : CollatzResearch.WordTrace tailWord_4019321 prefixEnd_4019321 8493183447366148649395 := by
  unfold tailWord_4019321
  simp only [CollatzResearch.WordTrace]
  refine ⟨146596680271693937221201817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97731120181129291480801211 146596680271693937221201817)
  ·
    refine ⟨109947510203770452915901363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146596680271693937221201817 109947510203770452915901363)
    ·
      refine ⟨164921265305655679373852045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109947510203770452915901363 164921265305655679373852045)
      ·
        refine ⟨61845474489620879765194517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164921265305655679373852045 61845474489620879765194517)
        ·
          refine ⟨2899006616700978738993493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61845474489620879765194517 2899006616700978738993493)
          ·
            refine ⟨8493183447366148649395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2899006616700978738993493 8493183447366148649395)
            ·
              rfl

theorem cell23_4019321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 10].length) (baseStart_4019321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019321 prefixEnd_4019321 := by exact prefixLift 4019321
  have htrace : WordTrace (prefixWord ++ tailWord_4019321) baseStart_4019321 baseEnd_4019321 := by
    simpa [prefixWord, tailWord_4019321, baseEnd_4019321] using wordTrace_append hprefix tailTrace_4019321
  have hstable : (prefixWord ++ tailWord_4019321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019321).length < 2 ^ (prefixWord ++ tailWord_4019321).sum := by decide
  have hdescent : baseEnd_4019321 < baseStart_4019321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019331 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 3]
def baseStart_4019331 : Nat := 118140960795 + 4019331 * 2 ^ 59
def prefixEnd_4019331 : Nat := 4983230072969 + 3 ^ 40 * 4019331 * 2
def baseEnd_4019331 : Nat := 2063848712516519082677939

theorem tailTrace_4019331 : CollatzResearch.WordTrace tailWord_4019331 prefixEnd_4019331 2063848712516519082677939 := by
  unfold tailWord_4019331
  simp only [CollatzResearch.WordTrace]
  refine ⟨146597045001657708929065847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97731363334438472619377231 146597045001657708929065847)
  ·
    refine ⟨219895567502486563393598771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146597045001657708929065847 219895567502486563393598771)
    ·
      refine ⟨329843351253729845090398157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219895567502486563393598771 329843351253729845090398157)
      ·
        refine ⟨123691256720148691908899309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329843351253729845090398157 123691256720148691908899309)
        ·
          refine ⟨46384221270055759465837241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123691256720148691908899309 46384221270055759465837241)
          ·
            refine ⟨34788165952541819599377931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46384221270055759465837241 34788165952541819599377931)
            ·
              refine ⟨52182248928812729399066897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34788165952541819599377931 52182248928812729399066897)
              ·
                refine ⟨39136686696609547049300173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52182248928812729399066897 39136686696609547049300173)
                ·
                  refine ⟨14676257511228580143487565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39136686696609547049300173 14676257511228580143487565)
                  ·
                    refine ⟨5503596566710717553807837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14676257511228580143487565 5503596566710717553807837)
                    ·
                      refine ⟨2063848712516519082677939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5503596566710717553807837 2063848712516519082677939)
                      ·
                        rfl

theorem cell23_4019331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_4019331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019331 prefixEnd_4019331 := by exact prefixLift 4019331
  have htrace : WordTrace (prefixWord ++ tailWord_4019331) baseStart_4019331 baseEnd_4019331 := by
    simpa [prefixWord, tailWord_4019331, baseEnd_4019331] using wordTrace_append hprefix tailTrace_4019331
  have hstable : (prefixWord ++ tailWord_4019331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019331).length < 2 ^ (prefixWord ++ tailWord_4019331).sum := by decide
  have hdescent : baseEnd_4019331 < baseStart_4019331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019361 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4019361 : Nat := 118140960795 + 4019361 * 2 ^ 59
def prefixEnd_4019361 : Nat := 4983230072969 + 3 ^ 40 * 4019361 * 2
def baseEnd_4019361 : Nat := 2063864116936153965302801

theorem tailTrace_4019361 : CollatzResearch.WordTrace tailWord_4019361 prefixEnd_4019361 2063864116936153965302801 := by
  unfold tailWord_4019361
  simp only [CollatzResearch.WordTrace]
  refine ⟨146598139191549024052657937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97732092794366016035105291 146598139191549024052657937)
  ·
    refine ⟨109948604393661768039493453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146598139191549024052657937 109948604393661768039493453)
    ·
      refine ⟨41230726647623163014810045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109948604393661768039493453 41230726647623163014810045)
      ·
        refine ⟨15461522492858686130553767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41230726647623163014810045 15461522492858686130553767)
        ·
          refine ⟨23192283739288029195830651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15461522492858686130553767 23192283739288029195830651)
          ·
            refine ⟨34788425608932043793745977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23192283739288029195830651 34788425608932043793745977)
            ·
              refine ⟨26091319206699032845309483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34788425608932043793745977 26091319206699032845309483)
              ·
                refine ⟨39136978810048549267964225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26091319206699032845309483 39136978810048549267964225)
                ·
                  refine ⟨29352734107536411950973169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39136978810048549267964225 29352734107536411950973169)
                  ·
                    refine ⟨22014550580652308963229877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29352734107536411950973169 22014550580652308963229877)
                    ·
                      refine ⟨2063864116936153965302801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22014550580652308963229877 2063864116936153965302801)
                      ·
                        rfl

theorem cell23_4019361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4019361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019361 prefixEnd_4019361 := by exact prefixLift 4019361
  have htrace : WordTrace (prefixWord ++ tailWord_4019361) baseStart_4019361 baseEnd_4019361 := by
    simpa [prefixWord, tailWord_4019361, baseEnd_4019361] using wordTrace_append hprefix tailTrace_4019361
  have hstable : (prefixWord ++ tailWord_4019361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019361).length < 2 ^ (prefixWord ++ tailWord_4019361).sum := by decide
  have hdescent : baseEnd_4019361 < baseStart_4019361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019391 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_4019391 : Nat := 118140960795 + 4019391 * 2 ^ 59
def prefixEnd_4019391 : Nat := 4983230072969 + 3 ^ 40 * 4019391 * 2
def baseEnd_4019391 : Nat := 2063879521355788847927663

theorem tailTrace_4019391 : CollatzResearch.WordTrace tailWord_4019391 prefixEnd_4019391 2063879521355788847927663 := by
  unfold tailWord_4019391
  simp only [CollatzResearch.WordTrace]
  refine ⟨146599233381440339176250027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97732822254293559450833351 146599233381440339176250027)
  ·
    refine ⟨219898850072160508764375041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146599233381440339176250027 219898850072160508764375041)
    ·
      refine ⟨164924137554120381573281281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219898850072160508764375041 164924137554120381573281281)
      ·
        refine ⟨123693103165590286179960961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164924137554120381573281281 123693103165590286179960961)
        ·
          refine ⟨92769827374192714634970721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123693103165590286179960961 92769827374192714634970721)
          ·
            refine ⟨69577370530644535976228041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92769827374192714634970721 69577370530644535976228041)
            ·
              refine ⟨52183027897983401982171031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69577370530644535976228041 52183027897983401982171031)
              ·
                refine ⟨78274541846975102973256547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52183027897983401982171031 78274541846975102973256547)
                ·
                  refine ⟨117411812770462654459884821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78274541846975102973256547 117411812770462654459884821)
                  ·
                    refine ⟨5503678723615436927807101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117411812770462654459884821 5503678723615436927807101)
                    ·
                      refine ⟨2063879521355788847927663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5503678723615436927807101 2063879521355788847927663)
                      ·
                        rfl

theorem cell23_4019391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_4019391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019391 prefixEnd_4019391 := by exact prefixLift 4019391
  have htrace : WordTrace (prefixWord ++ tailWord_4019391) baseStart_4019391 baseEnd_4019391 := by
    simpa [prefixWord, tailWord_4019391, baseEnd_4019391] using wordTrace_append hprefix tailTrace_4019391
  have hstable : (prefixWord ++ tailWord_4019391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019391).length < 2 ^ (prefixWord ++ tailWord_4019391).sum := by decide
  have hdescent : baseEnd_4019391 < baseStart_4019391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019438 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_4019438 : Nat := 118140960795 + 4019438 * 2 ^ 59
def prefixEnd_4019438 : Nat := 4983230072969 + 3 ^ 40 * 4019438 * 2
def baseEnd_4019438 : Nat := 2063903654946550164039947

theorem tailTrace_4019438 : CollatzResearch.WordTrace tailWord_4019438 prefixEnd_4019438 2063903654946550164039947 := by
  unfold tailWord_4019438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18325118451533758275401371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97733965074846710802140645 18325118451533758275401371)
  ·
    refine ⟨27487677677300637413102057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18325118451533758275401371 27487677677300637413102057)
    ·
      refine ⟨20615758257975478059826543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27487677677300637413102057 20615758257975478059826543)
      ·
        refine ⟨30923637386963217089739815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20615758257975478059826543 30923637386963217089739815)
        ·
          refine ⟨46385456080444825634609723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30923637386963217089739815 46385456080444825634609723)
          ·
            refine ⟨69578184120667238451914585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46385456080444825634609723 69578184120667238451914585)
            ·
              refine ⟨52183638090500428838935939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69578184120667238451914585 52183638090500428838935939)
              ·
                refine ⟨78275457135750643258403909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52183638090500428838935939 78275457135750643258403909)
                ·
                  refine ⟨14676648212953245610950733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78275457135750643258403909 14676648212953245610950733)
                  ·
                    refine ⟨5503743079857467104106525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14676648212953245610950733 5503743079857467104106525)
                    ·
                      refine ⟨2063903654946550164039947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5503743079857467104106525 2063903654946550164039947)
                      ·
                        rfl

theorem cell23_4019438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_4019438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019438 prefixEnd_4019438 := by exact prefixLift 4019438
  have htrace : WordTrace (prefixWord ++ tailWord_4019438) baseStart_4019438 baseEnd_4019438 := by
    simpa [prefixWord, tailWord_4019438, baseEnd_4019438] using wordTrace_append hprefix tailTrace_4019438
  have hstable : (prefixWord ++ tailWord_4019438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019438).length < 2 ^ (prefixWord ++ tailWord_4019438).sum := by decide
  have hdescent : baseEnd_4019438 < baseStart_4019438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019526 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_4019526 : Nat := 118140960795 + 4019526 * 2 ^ 59
def prefixEnd_4019526 : Nat := 4983230072969 + 3 ^ 40 * 4019526 * 2
def baseEnd_4019526 : Nat := 687982947081381939913181

theorem tailTrace_4019526 : CollatzResearch.WordTrace tailWord_4019526 prefixEnd_4019526 687982947081381939913181 := by
  unfold tailWord_4019526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581379913623476788512951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97736104823967504821609621 4581379913623476788512951)
  ·
    refine ⟨6872069870435215182769427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581379913623476788512951 6872069870435215182769427)
    ·
      refine ⟨10308104805652822774154141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872069870435215182769427 10308104805652822774154141)
      ·
        refine ⟨3865539302119808540307803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10308104805652822774154141 3865539302119808540307803)
        ·
          refine ⟨5798308953179712810461705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865539302119808540307803 5798308953179712810461705)
          ·
            refine ⟨4348731714884784607846279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5798308953179712810461705 4348731714884784607846279)
            ·
              refine ⟨6523097572327176911769419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348731714884784607846279 6523097572327176911769419)
              ·
                refine ⟨9784646358490765367654129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523097572327176911769419 9784646358490765367654129)
                ·
                  refine ⟨7338484768868074025740597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9784646358490765367654129 7338484768868074025740597)
                  ·
                    refine ⟨687982947081381939913181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7338484768868074025740597 687982947081381939913181)
                    ·
                      rfl

theorem cell23_4019526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_4019526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019526 prefixEnd_4019526 := by exact prefixLift 4019526
  have htrace : WordTrace (prefixWord ++ tailWord_4019526) baseStart_4019526 baseEnd_4019526 := by
    simpa [prefixWord, tailWord_4019526, baseEnd_4019526] using wordTrace_append hprefix tailTrace_4019526
  have hstable : (prefixWord ++ tailWord_4019526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019526).length < 2 ^ (prefixWord ++ tailWord_4019526).sum := by decide
  have hdescent : baseEnd_4019526 < baseStart_4019526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019532 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4019532 : Nat := 118140960795 + 4019532 * 2 ^ 59
def prefixEnd_4019532 : Nat := 4983230072969 + 3 ^ 40 * 4019532 * 2
def baseEnd_4019532 : Nat := 2063951922128072796264515

theorem tailTrace_4019532 : CollatzResearch.WordTrace tailWord_4019532 prefixEnd_4019532 2063951922128072796264515 := by
  unfold tailWord_4019532
  simp only [CollatzResearch.WordTrace]
  refine ⟨73302188036964760128566425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97736250715953013504755233 73302188036964760128566425)
  ·
    refine ⟨54976641027723570096424819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73302188036964760128566425 54976641027723570096424819)
    ·
      refine ⟨82464961541585355144637229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54976641027723570096424819 82464961541585355144637229)
      ·
        refine ⟨30924360578094508179238961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82464961541585355144637229 30924360578094508179238961)
        ·
          refine ⟨23193270433570881134429221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30924360578094508179238961 23193270433570881134429221)
          ·
            refine ⟨4348738206294540212705479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23193270433570881134429221 4348738206294540212705479)
            ·
              refine ⟨6523107309441810319058219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348738206294540212705479 6523107309441810319058219)
              ·
                refine ⟨9784660964162715478587329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523107309441810319058219 9784660964162715478587329)
                ·
                  refine ⟨7338495723122036608940497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9784660964162715478587329 7338495723122036608940497)
                  ·
                    refine ⟨5503871792341527456705373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7338495723122036608940497 5503871792341527456705373)
                    ·
                      refine ⟨2063951922128072796264515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5503871792341527456705373 2063951922128072796264515)
                      ·
                        rfl

theorem cell23_4019532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4019532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019532 prefixEnd_4019532 := by exact prefixLift 4019532
  have htrace : WordTrace (prefixWord ++ tailWord_4019532) baseStart_4019532 baseEnd_4019532 := by
    simpa [prefixWord, tailWord_4019532, baseEnd_4019532] using wordTrace_append hprefix tailTrace_4019532
  have hstable : (prefixWord ++ tailWord_4019532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019532).length < 2 ^ (prefixWord ++ tailWord_4019532).sum := by decide
  have hdescent : baseEnd_4019532 < baseStart_4019532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019629 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4019629 : Nat := 118140960795 + 4019629 * 2 ^ 59
def prefixEnd_4019629 : Nat := 4983230072969 + 3 ^ 40 * 4019629 * 2
def baseEnd_4019629 : Nat := 688000576583852972250523

theorem tailTrace_4019629 : CollatzResearch.WordTrace tailWord_4019629 prefixEnd_4019629 688000576583852972250523 := by
  unfold tailWord_4019629
  simp only [CollatzResearch.WordTrace]
  refine ⟨146607913954578105823413941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97738609303052070548942627 146607913954578105823413941)
  ·
    refine ⟨13744491933241697420945057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146607913954578105823413941 13744491933241697420945057)
    ·
      refine ⟨10308368949931273065708793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13744491933241697420945057 10308368949931273065708793)
      ·
        refine ⟨7731276712448454799281595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10308368949931273065708793 7731276712448454799281595)
        ·
          refine ⟨11596915068672682198922393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731276712448454799281595 11596915068672682198922393)
          ·
            refine ⟨8697686301504511649191795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11596915068672682198922393 8697686301504511649191795)
            ·
              refine ⟨13046529452256767473787693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697686301504511649191795 13046529452256767473787693)
              ·
                refine ⟨4892448544596287802670385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13046529452256767473787693 4892448544596287802670385)
                ·
                  refine ⟨3669336408447215852002789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4892448544596287802670385 3669336408447215852002789)
                  ·
                    refine ⟨688000576583852972250523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669336408447215852002789 688000576583852972250523)
                    ·
                      rfl

theorem cell23_4019629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4019629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019629 prefixEnd_4019629 := by exact prefixLift 4019629
  have htrace : WordTrace (prefixWord ++ tailWord_4019629) baseStart_4019629 baseEnd_4019629 := by
    simpa [prefixWord, tailWord_4019629, baseEnd_4019629] using wordTrace_append hprefix tailTrace_4019629
  have hstable : (prefixWord ++ tailWord_4019629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019629).length < 2 ^ (prefixWord ++ tailWord_4019629).sum := by decide
  have hdescent : baseEnd_4019629 < baseStart_4019629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019648 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_4019648 : Nat := 118140960795 + 4019648 * 2 ^ 59
def prefixEnd_4019648 : Nat := 4983230072969 + 3 ^ 40 * 4019648 * 2
def baseEnd_4019648 : Nat := 2064011485883994342413981

theorem tailTrace_4019648 : CollatzResearch.WordTrace tailWord_4019648 prefixEnd_4019648 2064011485883994342413981 := by
  unfold tailWord_4019648
  simp only [CollatzResearch.WordTrace]
  refine ⟨73304303470754636034177799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97739071294339514712237065 73304303470754636034177799)
  ·
    refine ⟨109956455206131954051266699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73304303470754636034177799 109956455206131954051266699)
    ·
      refine ⟨164934682809197931076900049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109956455206131954051266699 164934682809197931076900049)
      ·
        refine ⟨123701012106898448307675037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164934682809197931076900049 123701012106898448307675037)
        ·
          refine ⟨46387879540086918115378139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123701012106898448307675037 46387879540086918115378139)
          ·
            refine ⟨69581819310130377173067209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46387879540086918115378139 69581819310130377173067209)
            ·
              refine ⟨52186364482597782879800407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69581819310130377173067209 52186364482597782879800407)
              ·
                refine ⟨78279546723896674319700611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52186364482597782879800407 78279546723896674319700611)
                ·
                  refine ⟨117419320085845011479550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78279546723896674319700611 117419320085845011479550917)
                  ·
                    refine ⟨22016122516095939652415797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117419320085845011479550917 22016122516095939652415797)
                    ·
                      refine ⟨2064011485883994342413981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22016122516095939652415797 2064011485883994342413981)
                      ·
                        rfl

theorem cell23_4019648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_4019648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019648 prefixEnd_4019648 := by exact prefixLift 4019648
  have htrace : WordTrace (prefixWord ++ tailWord_4019648) baseStart_4019648 baseEnd_4019648 := by
    simpa [prefixWord, tailWord_4019648, baseEnd_4019648] using wordTrace_append hprefix tailTrace_4019648
  have hstable : (prefixWord ++ tailWord_4019648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019648).length < 2 ^ (prefixWord ++ tailWord_4019648).sum := by decide
  have hdescent : baseEnd_4019648 < baseStart_4019648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019650 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4019650 : Nat := 118140960795 + 4019650 * 2 ^ 59
def prefixEnd_4019650 : Nat := 4983230072969 + 3 ^ 40 * 4019650 * 2
def baseEnd_4019650 : Nat := 688004170948434444862991

theorem tailTrace_4019650 : CollatzResearch.WordTrace tailWord_4019650 prefixEnd_4019650 688004170948434444862991 := by
  unfold tailWord_4019650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36652169971875506602482101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97739119925001350939952269 36652169971875506602482101)
  ·
    refine ⟨3436140934863328743982697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36652169971875506602482101 3436140934863328743982697)
    ·
      refine ⟨2577105701147496557987023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3436140934863328743982697 2577105701147496557987023)
      ·
        refine ⟨3865658551721244836980535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577105701147496557987023 3865658551721244836980535)
        ·
          refine ⟨5798487827581867255470803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865658551721244836980535 5798487827581867255470803)
          ·
            refine ⟨8697731741372800883206205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798487827581867255470803 8697731741372800883206205)
            ·
              refine ⟨3261649403014800331202327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8697731741372800883206205 3261649403014800331202327)
              ·
                refine ⟨4892474104522200496803491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261649403014800331202327 4892474104522200496803491)
                ·
                  refine ⟨7338711156783300745205237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892474104522200496803491 7338711156783300745205237)
                  ·
                    refine ⟨688004170948434444862991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7338711156783300745205237 688004170948434444862991)
                    ·
                      rfl

theorem cell23_4019650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4019650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019650 prefixEnd_4019650 := by exact prefixLift 4019650
  have htrace : WordTrace (prefixWord ++ tailWord_4019650) baseStart_4019650 baseEnd_4019650 := by
    simpa [prefixWord, tailWord_4019650, baseEnd_4019650] using wordTrace_append hprefix tailTrace_4019650
  have hstable : (prefixWord ++ tailWord_4019650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019650).length < 2 ^ (prefixWord ++ tailWord_4019650).sum := by decide
  have hdescent : baseEnd_4019650 < baseStart_4019650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019652 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4019652 : Nat := 118140960795 + 4019652 * 2 ^ 59
def prefixEnd_4019652 : Nat := 4983230072969 + 3 ^ 40 * 4019652 * 2
def baseEnd_4019652 : Nat := 2064013539806612326763963

theorem tailTrace_4019652 : CollatzResearch.WordTrace tailWord_4019652 prefixEnd_4019652 2064013539806612326763963 := by
  unfold tailWord_4019652
  simp only [CollatzResearch.WordTrace]
  refine ⟨73304376416747390375750605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97739168555663187167667473 73304376416747390375750605)
  ·
    refine ⟨27489141156280271390906477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73304376416747390375750605 27489141156280271390906477)
    ·
      refine ⟨10308427933605101771589929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27489141156280271390906477 10308427933605101771589929)
      ·
        refine ⟨7731320950203826328692447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10308427933605101771589929 7731320950203826328692447)
        ·
          refine ⟨11596981425305739493038671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731320950203826328692447 11596981425305739493038671)
          ·
            refine ⟨17395472137958609239558007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11596981425305739493038671 17395472137958609239558007)
            ·
              refine ⟨26093208206937913859337011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17395472137958609239558007 26093208206937913859337011)
              ·
                refine ⟨39139812310406870789005517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26093208206937913859337011 39139812310406870789005517)
                ·
                  refine ⟨14677429616402576545877069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39139812310406870789005517 14677429616402576545877069)
                  ·
                    refine ⟨5504036106150966204703901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14677429616402576545877069 5504036106150966204703901)
                    ·
                      refine ⟨2064013539806612326763963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5504036106150966204703901 2064013539806612326763963)
                      ·
                        rfl

theorem cell23_4019652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4019652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019652 prefixEnd_4019652 := by exact prefixLift 4019652
  have htrace : WordTrace (prefixWord ++ tailWord_4019652) baseStart_4019652 baseEnd_4019652 := by
    simpa [prefixWord, tailWord_4019652, baseEnd_4019652] using wordTrace_append hprefix tailTrace_4019652
  have hstable : (prefixWord ++ tailWord_4019652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019652).length < 2 ^ (prefixWord ++ tailWord_4019652).sum := by decide
  have hdescent : baseEnd_4019652 < baseStart_4019652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019669 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4019669 : Nat := 118140960795 + 4019669 * 2 ^ 59
def prefixEnd_4019669 : Nat := 4983230072969 + 3 ^ 40 * 4019669 * 2
def baseEnd_4019669 : Nat := 2064022268977738760251385

theorem tailTrace_4019669 : CollatzResearch.WordTrace tailWord_4019669 prefixEnd_4019669 2064022268977738760251385 := by
  unfold tailWord_4019669
  simp only [CollatzResearch.WordTrace]
  refine ⟨146609372874433192654870061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97739581916288795103246707 146609372874433192654870061)
  ·
    refine ⟨54978514827912447245576273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146609372874433192654870061 54978514827912447245576273)
    ·
      refine ⟨41233886120934335434182205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54978514827912447245576273 41233886120934335434182205)
      ·
        refine ⟨15462707295350375787818327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41233886120934335434182205 15462707295350375787818327)
        ·
          refine ⟨23194060943025563681727491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462707295350375787818327 23194060943025563681727491)
          ·
            refine ⟨34791091414538345522591237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23194060943025563681727491 34791091414538345522591237)
            ·
              refine ⟨6523329640225939785485857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34791091414538345522591237 6523329640225939785485857)
              ·
                refine ⟨4892497230169454839114393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523329640225939785485857 4892497230169454839114393)
                ·
                  refine ⟨3669372922627091129335795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4892497230169454839114393 3669372922627091129335795)
                  ·
                    refine ⟨5504059383940636694003693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3669372922627091129335795 5504059383940636694003693)
                    ·
                      refine ⟨2064022268977738760251385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5504059383940636694003693 2064022268977738760251385)
                      ·
                        rfl

theorem cell23_4019669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4019669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019669 prefixEnd_4019669 := by exact prefixLift 4019669
  have htrace : WordTrace (prefixWord ++ tailWord_4019669) baseStart_4019669 baseEnd_4019669 := by
    simpa [prefixWord, tailWord_4019669, baseEnd_4019669] using wordTrace_append hprefix tailTrace_4019669
  have hstable : (prefixWord ++ tailWord_4019669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019669).length < 2 ^ (prefixWord ++ tailWord_4019669).sum := by decide
  have hdescent : baseEnd_4019669 < baseStart_4019669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019670 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_4019670 : Nat := 118140960795 + 4019670 * 2 ^ 59
def prefixEnd_4019670 : Nat := 4983230072969 + 3 ^ 40 * 4019670 * 2
def baseEnd_4019670 : Nat := 2064022782458393256338881

theorem tailTrace_4019670 : CollatzResearch.WordTrace tailWord_4019670 prefixEnd_4019670 2064022782458393256338881 := by
  unfold tailWord_4019670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163088084214348114103529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97739606231619713217104309 9163088084214348114103529)
  ·
    refine ⟨6872316063160761085577647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9163088084214348114103529 6872316063160761085577647)
    ·
      refine ⟨10308474094741141628366471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872316063160761085577647 10308474094741141628366471)
      ·
        refine ⟨15462711142111712442549707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10308474094741141628366471 15462711142111712442549707)
        ·
          refine ⟨23194066713167568663824561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462711142111712442549707 23194066713167568663824561)
          ·
            refine ⟨17395550034875676497868421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23194066713167568663824561 17395550034875676497868421)
            ·
              refine ⟨3261665631539189343350329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17395550034875676497868421 3261665631539189343350329)
              ·
                refine ⟨2446249223654392007512747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261665631539189343350329 2446249223654392007512747)
                ·
                  refine ⟨3669373835481588011269121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446249223654392007512747 3669373835481588011269121)
                  ·
                    refine ⟨2752030376611191008451841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3669373835481588011269121 2752030376611191008451841)
                    ·
                      refine ⟨2064022782458393256338881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752030376611191008451841 2064022782458393256338881)
                      ·
                        rfl

theorem cell23_4019670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_4019670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019670 prefixEnd_4019670 := by exact prefixLift 4019670
  have htrace : WordTrace (prefixWord ++ tailWord_4019670) baseStart_4019670 baseEnd_4019670 := by
    simpa [prefixWord, tailWord_4019670, baseEnd_4019670] using wordTrace_append hprefix tailTrace_4019670
  have hstable : (prefixWord ++ tailWord_4019670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019670).length < 2 ^ (prefixWord ++ tailWord_4019670).sum := by decide
  have hdescent : baseEnd_4019670 < baseStart_4019670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019685 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_4019685 : Nat := 118140960795 + 4019685 * 2 ^ 59
def prefixEnd_4019685 : Nat := 4983230072969 + 3 ^ 40 * 4019685 * 2
def baseEnd_4019685 : Nat := 688010161556070232550437

theorem tailTrace_4019685 : CollatzResearch.WordTrace tailWord_4019685 prefixEnd_4019685 688010161556070232550437 := by
  unfold tailWord_4019685
  simp only [CollatzResearch.WordTrace]
  refine ⟨146609956442375227387452509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97739970961583484924968339 146609956442375227387452509)
  ·
    refine ⟨54978733665890710270294691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146609956442375227387452509 54978733665890710270294691)
    ·
      refine ⟨82468100498836065405442037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54978733665890710270294691 82468100498836065405442037)
      ·
        refine ⟨7731384421765881131760191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82468100498836065405442037 7731384421765881131760191)
        ·
          refine ⟨11597076632648821697640287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731384421765881131760191 11597076632648821697640287)
          ·
            refine ⟨17395614948973232546460431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11597076632648821697640287 17395614948973232546460431)
            ·
              refine ⟨26093422423459848819690647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17395614948973232546460431 26093422423459848819690647)
              ·
                refine ⟨39140133635189773229535971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26093422423459848819690647 39140133635189773229535971)
                ·
                  refine ⟨58710200452784659844303957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39140133635189773229535971 58710200452784659844303957)
                  ·
                    refine ⟨688010161556070232550437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58710200452784659844303957 688010161556070232550437)
                    ·
                      rfl

theorem cell23_4019685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_4019685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019685 prefixEnd_4019685 := by exact prefixLift 4019685
  have htrace : WordTrace (prefixWord ++ tailWord_4019685) baseStart_4019685 baseEnd_4019685 := by
    simpa [prefixWord, tailWord_4019685, baseEnd_4019685] using wordTrace_append hprefix tailTrace_4019685
  have hstable : (prefixWord ++ tailWord_4019685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019685).length < 2 ^ (prefixWord ++ tailWord_4019685).sum := by decide
  have hdescent : baseEnd_4019685 < baseStart_4019685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019713 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_4019713 : Nat := 118140960795 + 4019713 * 2 ^ 59
def prefixEnd_4019713 : Nat := 4983230072969 + 3 ^ 40 * 4019713 * 2
def baseEnd_4019713 : Nat := 2064044862126536588101183

theorem tailTrace_4019713 : CollatzResearch.WordTrace tailWord_4019713 prefixEnd_4019713 2064044862126536588101183 := by
  unfold tailWord_4019713
  simp only [CollatzResearch.WordTrace]
  refine ⟨146610977686273788169471793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97740651790849192112981195 146610977686273788169471793)
  ·
    refine ⟨109958233264705341127103845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146610977686273788169471793 109958233264705341127103845)
    ·
      refine ⟨20617168737132251461331971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109958233264705341127103845 20617168737132251461331971)
      ·
        refine ⟨30925753105698377191997957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20617168737132251461331971 30925753105698377191997957)
        ·
          refine ⟨5798578707318445723499617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30925753105698377191997957 5798578707318445723499617)
          ·
            refine ⟨4348934030488834292624713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5798578707318445723499617 4348934030488834292624713)
            ·
              refine ⟨3261700522866625719468535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348934030488834292624713 3261700522866625719468535)
              ·
                refine ⟨4892550784299938579202803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261700522866625719468535 4892550784299938579202803)
                ·
                  refine ⟨7338826176449907868804205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892550784299938579202803 7338826176449907868804205)
                  ·
                    refine ⟨2752059816168715450801577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7338826176449907868804205 2752059816168715450801577)
                    ·
                      refine ⟨2064044862126536588101183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752059816168715450801577 2064044862126536588101183)
                      ·
                        rfl

theorem cell23_4019713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_4019713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019713 prefixEnd_4019713 := by exact prefixLift 4019713
  have htrace : WordTrace (prefixWord ++ tailWord_4019713) baseStart_4019713 baseEnd_4019713 := by
    simpa [prefixWord, tailWord_4019713, baseEnd_4019713] using wordTrace_append hprefix tailTrace_4019713
  have hstable : (prefixWord ++ tailWord_4019713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019713).length < 2 ^ (prefixWord ++ tailWord_4019713).sum := by decide
  have hdescent : baseEnd_4019713 < baseStart_4019713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019726 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_4019726 : Nat := 118140960795 + 4019726 * 2 ^ 59
def prefixEnd_4019726 : Nat := 4983230072969 + 3 ^ 40 * 4019726 * 2
def baseEnd_4019726 : Nat := 2064051537375045037238623

theorem tailTrace_4019726 : CollatzResearch.WordTrace tailWord_4019726 prefixEnd_4019726 2064051537375045037238623 := by
  unfold tailWord_4019726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18326431479403336423711879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97740967890151127593130021 18326431479403336423711879)
  ·
    refine ⟨27489647219105004635567819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18326431479403336423711879 27489647219105004635567819)
    ·
      refine ⟨41234470828657506953351729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27489647219105004635567819 41234470828657506953351729)
      ·
        refine ⟨30925853121493130215013797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41234470828657506953351729 30925853121493130215013797)
        ·
          refine ⟨5798597460279961915315087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30925853121493130215013797 5798597460279961915315087)
          ·
            refine ⟨8697896190419942872972631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798597460279961915315087 8697896190419942872972631)
            ·
              refine ⟨13046844285629914309458947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697896190419942872972631 13046844285629914309458947)
              ·
                refine ⟨19570266428444871464188421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13046844285629914309458947 19570266428444871464188421)
                ·
                  refine ⟨3669424955333413399535329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19570266428444871464188421 3669424955333413399535329)
                  ·
                    refine ⟨2752068716500060049651497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3669424955333413399535329 2752068716500060049651497)
                    ·
                      refine ⟨2064051537375045037238623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752068716500060049651497 2064051537375045037238623)
                      ·
                        rfl

theorem cell23_4019726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_4019726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019726 prefixEnd_4019726 := by exact prefixLift 4019726
  have htrace : WordTrace (prefixWord ++ tailWord_4019726) baseStart_4019726 baseEnd_4019726 := by
    simpa [prefixWord, tailWord_4019726, baseEnd_4019726] using wordTrace_append hprefix tailTrace_4019726
  have hstable : (prefixWord ++ tailWord_4019726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019726).length < 2 ^ (prefixWord ++ tailWord_4019726).sum := by decide
  have hdescent : baseEnd_4019726 < baseStart_4019726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019745 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_4019745 : Nat := 118140960795 + 4019745 * 2 ^ 59
def prefixEnd_4019745 : Nat := 4983230072969 + 3 ^ 40 * 4019745 * 2
def baseEnd_4019745 : Nat := 688020431169160154300345

theorem tailTrace_4019745 : CollatzResearch.WordTrace tailWord_4019745 prefixEnd_4019745 688020431169160154300345 := by
  unfold tailWord_4019745
  simp only [CollatzResearch.WordTrace]
  refine ⟨146612144822157857634636689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97741429881438571756424459 146612144822157857634636689)
  ·
    refine ⟨109959108616618393225977517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146612144822157857634636689 109959108616618393225977517)
    ·
      refine ⟨41234665731231897459741569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109959108616618393225977517 41234665731231897459741569)
      ·
        refine ⟨30925999298423923094806177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41234665731231897459741569 30925999298423923094806177)
        ·
          refine ⟨23194499473817942321104633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30925999298423923094806177 23194499473817942321104633)
          ·
            refine ⟨17395874605363456740828475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23194499473817942321104633 17395874605363456740828475)
            ·
              refine ⟨26093811908045185111242713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17395874605363456740828475 26093811908045185111242713)
              ·
                refine ⟨19570358931033888833432035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26093811908045185111242713 19570358931033888833432035)
                ·
                  refine ⟨29355538396550833250148053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19570358931033888833432035 29355538396550833250148053)
                  ·
                    refine ⟨688020431169160154300345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29355538396550833250148053 688020431169160154300345)
                    ·
                      rfl

theorem cell23_4019745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_4019745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019745 prefixEnd_4019745 := by exact prefixLift 4019745
  have htrace : WordTrace (prefixWord ++ tailWord_4019745) baseStart_4019745 baseEnd_4019745 := by
    simpa [prefixWord, tailWord_4019745, baseEnd_4019745] using wordTrace_append hprefix tailTrace_4019745
  have hstable : (prefixWord ++ tailWord_4019745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019745).length < 2 ^ (prefixWord ++ tailWord_4019745).sum := by decide
  have hdescent : baseEnd_4019745 < baseStart_4019745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019789 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4019789 : Nat := 118140960795 + 4019789 * 2 ^ 59
def prefixEnd_4019789 : Nat := 4983230072969 + 3 ^ 40 * 4019789 * 2
def baseEnd_4019789 : Nat := 2064083886656278290750833

theorem tailTrace_4019789 : CollatzResearch.WordTrace tailWord_4019789 prefixEnd_4019789 2064083886656278290750833 := by
  unfold tailWord_4019789
  simp only [CollatzResearch.WordTrace]
  refine ⟨146613749633998453149238421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97742499755998968766158947 146613749633998453149238421)
  ·
    refine ⟨6872519514093677491370551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146613749633998453149238421 6872519514093677491370551)
    ·
      refine ⟨10308779271140516237055827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872519514093677491370551 10308779271140516237055827)
      ·
        refine ⟨15463168906710774355583741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10308779271140516237055827 15463168906710774355583741)
        ·
          refine ⟨5798688340016540383343903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15463168906710774355583741 5798688340016540383343903)
          ·
            refine ⟨8698032510024810575015855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798688340016540383343903 8698032510024810575015855)
            ·
              refine ⟨13047048765037215862523783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698032510024810575015855 13047048765037215862523783)
              ·
                refine ⟨19570573147555823793785675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13047048765037215862523783 19570573147555823793785675)
                ·
                  refine ⟨29355859721333735690678513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19570573147555823793785675 29355859721333735690678513)
                  ·
                    refine ⟨22016894791000301768008885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29355859721333735690678513 22016894791000301768008885)
                    ·
                      refine ⟨2064083886656278290750833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22016894791000301768008885 2064083886656278290750833)
                      ·
                        rfl

theorem cell23_4019789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4019789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019789 prefixEnd_4019789 := by exact prefixLift 4019789
  have htrace : WordTrace (prefixWord ++ tailWord_4019789) baseStart_4019789 baseEnd_4019789 := by
    simpa [prefixWord, tailWord_4019789, baseEnd_4019789] using wordTrace_append hprefix tailTrace_4019789
  have hstable : (prefixWord ++ tailWord_4019789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019789).length < 2 ^ (prefixWord ++ tailWord_4019789).sum := by decide
  have hdescent : baseEnd_4019789 < baseStart_4019789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019855 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_4019855 : Nat := 118140960795 + 4019855 * 2 ^ 59
def prefixEnd_4019855 : Nat := 4983230072969 + 3 ^ 40 * 4019855 * 2
def baseEnd_4019855 : Nat := 2064117776379475032525529

theorem tailTrace_4019855 : CollatzResearch.WordTrace tailWord_4019855 prefixEnd_4019855 2064117776379475032525529 := by
  unfold tailWord_4019855
  simp only [CollatzResearch.WordTrace]
  refine ⟨146616156851759346421141019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97744104567839564280760679 146616156851759346421141019)
  ·
    refine ⟨219924235277639019631711529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146616156851759346421141019 219924235277639019631711529)
    ·
      refine ⟨164943176458229264723783647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219924235277639019631711529 164943176458229264723783647)
      ·
        refine ⟨247414764687343897085675471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164943176458229264723783647 247414764687343897085675471)
        ·
          refine ⟨371122147031015845628513207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247414764687343897085675471 371122147031015845628513207)
          ·
            refine ⟨556683220546523768442769811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371122147031015845628513207 556683220546523768442769811)
            ·
              refine ⟨835024830819785652664154717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556683220546523768442769811 835024830819785652664154717)
              ·
                refine ⟨313134311557419619749058019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835024830819785652664154717 313134311557419619749058019)
                ·
                  refine ⟨469701467336129429623587029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313134311557419619749058019 469701467336129429623587029)
                  ·
                    refine ⟨11008628140690533506802821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 469701467336129429623587029 11008628140690533506802821)
                    ·
                      refine ⟨2064117776379475032525529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11008628140690533506802821 2064117776379475032525529)
                      ·
                        rfl

theorem cell23_4019855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_4019855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019855 prefixEnd_4019855 := by exact prefixLift 4019855
  have htrace : WordTrace (prefixWord ++ tailWord_4019855) baseStart_4019855 baseEnd_4019855 := by
    simpa [prefixWord, tailWord_4019855, baseEnd_4019855] using wordTrace_append hprefix tailTrace_4019855
  have hstable : (prefixWord ++ tailWord_4019855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019855).length < 2 ^ (prefixWord ++ tailWord_4019855).sum := by decide
  have hdescent : baseEnd_4019855 < baseStart_4019855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019876 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_4019876 : Nat := 118140960795 + 4019876 * 2 ^ 59
def prefixEnd_4019876 : Nat := 4983230072969 + 3 ^ 40 * 4019876 * 2
def baseEnd_4019876 : Nat := 2064128559473219450362933

theorem tailTrace_4019876 : CollatzResearch.WordTrace tailWord_4019876 prefixEnd_4019876 2064128559473219450362933 := by
  unfold tailWord_4019876
  simp only [CollatzResearch.WordTrace]
  refine ⟨73308461392341633503827741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97744615189788844671770321 73308461392341633503827741)
  ·
    refine ⟨27490673022128112563935403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73308461392341633503827741 27490673022128112563935403)
    ·
      refine ⟨41236009533192168845903105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27490673022128112563935403 41236009533192168845903105)
      ·
        refine ⟨30927007149894126634427329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41236009533192168845903105 30927007149894126634427329)
        ·
          refine ⟨23195255362420594975820497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30927007149894126634427329 23195255362420594975820497)
          ·
            refine ⟨17396441521815446231865373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23195255362420594975820497 17396441521815446231865373)
            ·
              refine ⟨6523665570680792336949515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17396441521815446231865373 6523665570680792336949515)
              ·
                refine ⟨9785498356021188505424273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523665570680792336949515 9785498356021188505424273)
                ·
                  refine ⟨7339123767015891379068205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9785498356021188505424273 7339123767015891379068205)
                  ·
                    refine ⟨2752171412630959267150577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7339123767015891379068205 2752171412630959267150577)
                    ·
                      refine ⟨2064128559473219450362933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752171412630959267150577 2064128559473219450362933)
                      ·
                        rfl

theorem cell23_4019876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_4019876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019876 prefixEnd_4019876 := by exact prefixLift 4019876
  have htrace : WordTrace (prefixWord ++ tailWord_4019876) baseStart_4019876 baseEnd_4019876 := by
    simpa [prefixWord, tailWord_4019876, baseEnd_4019876] using wordTrace_append hprefix tailTrace_4019876
  have hstable : (prefixWord ++ tailWord_4019876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019876).length < 2 ^ (prefixWord ++ tailWord_4019876).sum := by decide
  have hdescent : baseEnd_4019876 < baseStart_4019876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019916 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_4019916 : Nat := 118140960795 + 4019916 * 2 ^ 59
def prefixEnd_4019916 : Nat := 4983230072969 + 3 ^ 40 * 4019916 * 2
def baseEnd_4019916 : Nat := 688049699566466431287583

theorem tailTrace_4019916 : CollatzResearch.WordTrace tailWord_4019916 prefixEnd_4019916 688049699566466431287583 := by
  unfold tailWord_4019916
  simp only [CollatzResearch.WordTrace]
  refine ⟨73309190852269176919555801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97745587803025569226074401 73309190852269176919555801)
  ·
    refine ⟨54981893139201882689666851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73309190852269176919555801 54981893139201882689666851)
    ·
      refine ⟨82472839708802824034500277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54981893139201882689666851 82472839708802824034500277)
      ·
        refine ⟨7731828722700264753234401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82472839708802824034500277 7731828722700264753234401)
        ·
          refine ⟨5798871542025198564925801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7731828722700264753234401 5798871542025198564925801)
          ·
            refine ⟨4349153656518898923694351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5798871542025198564925801 4349153656518898923694351)
            ·
              refine ⟨6523730484778348385541527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349153656518898923694351 6523730484778348385541527)
              ·
                refine ⟨9785595727167522578312291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523730484778348385541527 9785595727167522578312291)
                ·
                  refine ⟨14678393590751283867468437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9785595727167522578312291 14678393590751283867468437)
                  ·
                    refine ⟨688049699566466431287583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14678393590751283867468437 688049699566466431287583)
                    ·
                      rfl

theorem cell23_4019916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_4019916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019916 prefixEnd_4019916 := by exact prefixLift 4019916
  have htrace : WordTrace (prefixWord ++ tailWord_4019916) baseStart_4019916 baseEnd_4019916 := by
    simpa [prefixWord, tailWord_4019916, baseEnd_4019916] using wordTrace_append hprefix tailTrace_4019916
  have hstable : (prefixWord ++ tailWord_4019916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019916).length < 2 ^ (prefixWord ++ tailWord_4019916).sum := by decide
  have hdescent : baseEnd_4019916 < baseStart_4019916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019929 : List Nat := [1, 2, 1, 2, 3, 5, 2, 7]
def baseStart_4019929 : Nat := 118140960795 + 4019929 * 2 ^ 59
def prefixEnd_4019929 : Nat := 4983230072969 + 3 ^ 40 * 4019929 * 2
def baseEnd_4019929 : Nat := 76450213849922509000007

theorem tailTrace_4019929 : CollatzResearch.WordTrace tailWord_4019929 prefixEnd_4019929 76450213849922509000007 := by
  unfold tailWord_4019929
  simp only [CollatzResearch.WordTrace]
  refine ⟨146618855853491257059334841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97745903902327504706223227 146618855853491257059334841)
  ·
    refine ⟨109964141890118442794501131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146618855853491257059334841 109964141890118442794501131)
    ·
      refine ⟨164946212835177664191751697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109964141890118442794501131 164946212835177664191751697)
      ·
        refine ⟨123709659626383248143813773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164946212835177664191751697 123709659626383248143813773)
        ·
          refine ⟨46391122359893718053930165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123709659626383248143813773 46391122359893718053930165)
          ·
            refine ⟨4349167721240036067555953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46391122359893718053930165 4349167721240036067555953)
            ·
              refine ⟨3261875790930027050666965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349167721240036067555953 3261875790930027050666965)
              ·
                refine ⟨76450213849922509000007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3261875790930027050666965 76450213849922509000007)
                ·
                  rfl

theorem cell23_4019929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 7].length) (baseStart_4019929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019929 prefixEnd_4019929 := by exact prefixLift 4019929
  have htrace : WordTrace (prefixWord ++ tailWord_4019929) baseStart_4019929 baseEnd_4019929 := by
    simpa [prefixWord, tailWord_4019929, baseEnd_4019929] using wordTrace_append hprefix tailTrace_4019929
  have hstable : (prefixWord ++ tailWord_4019929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019929).length < 2 ^ (prefixWord ++ tailWord_4019929).sum := by decide
  have hdescent : baseEnd_4019929 < baseStart_4019929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019962 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_4019962 : Nat := 118140960795 + 4019962 * 2 ^ 59
def prefixEnd_4019962 : Nat := 4983230072969 + 3 ^ 40 * 4019962 * 2
def baseEnd_4019962 : Nat := 2064172718809506113887537

theorem tailTrace_4019962 : CollatzResearch.WordTrace tailWord_4019962 prefixEnd_4019962 2064172718809506113887537 := by
  unfold tailWord_4019962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36655014865592925923821535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97746706308247802463524093 36655014865592925923821535)
  ·
    refine ⟨54982522298389388885732303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36655014865592925923821535 54982522298389388885732303)
    ·
      refine ⟨82473783447584083328598455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54982522298389388885732303 82473783447584083328598455)
      ·
        refine ⟨123710675171376124992897683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82473783447584083328598455 123710675171376124992897683)
        ·
          refine ⟨185566012757064187489346525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123710675171376124992897683 185566012757064187489346525)
          ·
            refine ⟨69587254783899070308504947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185566012757064187489346525 69587254783899070308504947)
            ·
              refine ⟨104380882175848605462757421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69587254783899070308504947 104380882175848605462757421)
              ·
                refine ⟨39142830815943227048534033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104380882175848605462757421 39142830815943227048534033)
                ·
                  refine ⟨29357123111957420286400525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39142830815943227048534033 29357123111957420286400525)
                  ·
                    refine ⟨11008921166984032607400197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29357123111957420286400525 11008921166984032607400197)
                    ·
                      refine ⟨2064172718809506113887537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11008921166984032607400197 2064172718809506113887537)
                      ·
                        rfl

theorem cell23_4019962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_4019962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019962 prefixEnd_4019962 := by exact prefixLift 4019962
  have htrace : WordTrace (prefixWord ++ tailWord_4019962) baseStart_4019962 baseEnd_4019962 := by
    simpa [prefixWord, tailWord_4019962, baseEnd_4019962] using wordTrace_append hprefix tailTrace_4019962
  have hstable : (prefixWord ++ tailWord_4019962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019962).length < 2 ^ (prefixWord ++ tailWord_4019962).sum := by decide
  have hdescent : baseEnd_4019962 < baseStart_4019962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019996 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_4019996 : Nat := 118140960795 + 4019996 * 2 ^ 59
def prefixEnd_4019996 : Nat := 4983230072969 + 3 ^ 40 * 4019996 * 2
def baseEnd_4019996 : Nat := 2064190177151758980862381

theorem tailTrace_4019996 : CollatzResearch.WordTrace tailWord_4019996 prefixEnd_4019996 2064190177151758980862381 := by
  unfold tailWord_4019996
  simp only [CollatzResearch.WordTrace]
  refine ⟨73310649772124263751011921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97747533029499018334682561 73310649772124263751011921)
  ·
    refine ⟨54982987329093197813258941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73310649772124263751011921 54982987329093197813258941)
    ·
      refine ⟨20618620248409949179972103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54982987329093197813258941 20618620248409949179972103)
      ·
        refine ⟨30927930372614923769958155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20618620248409949179972103 30927930372614923769958155)
        ·
          refine ⟨46391895558922385654937233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30927930372614923769958155 46391895558922385654937233)
          ·
            refine ⟨34793921669191789241202925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46391895558922385654937233 34793921669191789241202925)
            ·
              refine ⟨13047720625946920965451097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34793921669191789241202925 13047720625946920965451097)
              ·
                refine ⟨9785790469460190724088323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13047720625946920965451097 9785790469460190724088323)
                ·
                  refine ⟨14678685704190286086132485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9785790469460190724088323 14678685704190286086132485)
                  ·
                    refine ⟨2752253569535678641149841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14678685704190286086132485 2752253569535678641149841)
                    ·
                      refine ⟨2064190177151758980862381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752253569535678641149841 2064190177151758980862381)
                      ·
                        rfl

theorem cell23_4019996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_4019996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4019996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4019996 prefixEnd_4019996 := by exact prefixLift 4019996
  have htrace : WordTrace (prefixWord ++ tailWord_4019996) baseStart_4019996 baseEnd_4019996 := by
    simpa [prefixWord, tailWord_4019996, baseEnd_4019996] using wordTrace_append hprefix tailTrace_4019996
  have hstable : (prefixWord ++ tailWord_4019996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019996).length < 2 ^ (prefixWord ++ tailWord_4019996).sum := by decide
  have hdescent : baseEnd_4019996 < baseStart_4019996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020030 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_4020030 : Nat := 118140960795 + 4020030 * 2 ^ 59
def prefixEnd_4020030 : Nat := 4983230072969 + 3 ^ 40 * 4020030 * 2
def baseEnd_4020030 : Nat := 2064207635494011847837225

theorem tailTrace_4020030 : CollatzResearch.WordTrace tailWord_4020030 prefixEnd_4020030 2064207635494011847837225 := by
  unfold tailWord_4020030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327817453265668913595193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97748359750750234205841029 18327817453265668913595193)
  ·
    refine ⟨13745863089949251685196395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18327817453265668913595193 13745863089949251685196395)
    ·
      refine ⟨20618794634923877527794593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13745863089949251685196395 20618794634923877527794593)
      ·
        refine ⟨15464095976192908145845945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20618794634923877527794593 15464095976192908145845945)
        ·
          refine ⟨11598071982144681109384459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15464095976192908145845945 11598071982144681109384459)
          ·
            refine ⟨17397107973217021664076689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11598071982144681109384459 17397107973217021664076689)
            ·
              refine ⟨13047830979912766248057517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17397107973217021664076689 13047830979912766248057517)
              ·
                refine ⟨4892936617467287343021569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13047830979912766248057517 4892936617467287343021569)
                ·
                  refine ⟨3669702463100465507266177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4892936617467287343021569 3669702463100465507266177)
                  ·
                    refine ⟨2752276847325349130449633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3669702463100465507266177 2752276847325349130449633)
                    ·
                      refine ⟨2064207635494011847837225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752276847325349130449633 2064207635494011847837225)
                      ·
                        rfl

theorem cell23_4020030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_4020030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020030 prefixEnd_4020030 := by exact prefixLift 4020030
  have htrace : WordTrace (prefixWord ++ tailWord_4020030) baseStart_4020030 baseEnd_4020030 := by
    simpa [prefixWord, tailWord_4020030, baseEnd_4020030] using wordTrace_append hprefix tailTrace_4020030
  have hstable : (prefixWord ++ tailWord_4020030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020030).length < 2 ^ (prefixWord ++ tailWord_4020030).sum := by decide
  have hdescent : baseEnd_4020030 < baseStart_4020030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020049 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_4020049 : Nat := 118140960795 + 4020049 * 2 ^ 59
def prefixEnd_4020049 : Nat := 4983230072969 + 3 ^ 40 * 4020049 * 2
def baseEnd_4020049 : Nat := 688072463875482424499879

theorem tailTrace_4020049 : CollatzResearch.WordTrace tailWord_4020049 prefixEnd_4020049 688072463875482424499879 := by
  unfold tailWord_4020049
  simp only [CollatzResearch.WordTrace]
  refine ⟨146623232613056517553703201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97748821742037678369135467 146623232613056517553703201)
  ·
    refine ⟨109967424459792388165277401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146623232613056517553703201 109967424459792388165277401)
    ·
      refine ⟨82475568344844291123958051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109967424459792388165277401 82475568344844291123958051)
      ·
        refine ⟨123713352517266436685937077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82475568344844291123958051 123713352517266436685937077)
        ·
          refine ⟨11598126798493728439306601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123713352517266436685937077 11598126798493728439306601)
          ·
            refine ⟨8698595098870296329479951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11598126798493728439306601 8698595098870296329479951)
            ·
              refine ⟨13047892648305444494219927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698595098870296329479951 13047892648305444494219927)
              ·
                refine ⟨19571838972458166741329891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13047892648305444494219927 19571838972458166741329891)
                ·
                  refine ⟨29357758458687250111994837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19571838972458166741329891 29357758458687250111994837)
                  ·
                    refine ⟨688072463875482424499879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29357758458687250111994837 688072463875482424499879)
                    ·
                      rfl

theorem cell23_4020049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_4020049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020049 prefixEnd_4020049 := by exact prefixLift 4020049
  have htrace : WordTrace (prefixWord ++ tailWord_4020049) baseStart_4020049 baseEnd_4020049 := by
    simpa [prefixWord, tailWord_4020049, baseEnd_4020049] using wordTrace_append hprefix tailTrace_4020049
  have hstable : (prefixWord ++ tailWord_4020049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020049).length < 2 ^ (prefixWord ++ tailWord_4020049).sum := by decide
  have hdescent : baseEnd_4020049 < baseStart_4020049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020069 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4020069 : Nat := 118140960795 + 4020069 * 2 ^ 59
def prefixEnd_4020069 : Nat := 4983230072969 + 3 ^ 40 * 4020069 * 2
def baseEnd_4020069 : Nat := 2064227661239537195249545

theorem tailTrace_4020069 : CollatzResearch.WordTrace tailWord_4020069 prefixEnd_4020069 2064227661239537195249545 := by
  unfold tailWord_4020069
  simp only [CollatzResearch.WordTrace]
  refine ⟨146623962072984060969431261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97749308048656040646287507 146623962072984060969431261)
  ·
    refine ⟨54983985777369022863536723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146623962072984060969431261 54983985777369022863536723)
    ·
      refine ⟨82475978666053534295305085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54983985777369022863536723 82475978666053534295305085)
      ·
        refine ⟨30928491999770075360739407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82475978666053534295305085 30928491999770075360739407)
        ·
          refine ⟨46392737999655113041109111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30928491999770075360739407 46392737999655113041109111)
          ·
            refine ⟨69589106999482669561663667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46392737999655113041109111 69589106999482669561663667)
            ·
              refine ⟨104383660499224004342495501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69589106999482669561663667 104383660499224004342495501)
              ·
                refine ⟨39143872687209001628435813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104383660499224004342495501 39143872687209001628435813)
                ·
                  refine ⟨7339476128851687805331715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39143872687209001628435813 7339476128851687805331715)
                  ·
                    refine ⟨11009214193277531707997573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339476128851687805331715 11009214193277531707997573)
                    ·
                      refine ⟨2064227661239537195249545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11009214193277531707997573 2064227661239537195249545)
                      ·
                        rfl

theorem cell23_4020069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4020069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020069 prefixEnd_4020069 := by exact prefixLift 4020069
  have htrace : WordTrace (prefixWord ++ tailWord_4020069) baseStart_4020069 baseEnd_4020069 := by
    simpa [prefixWord, tailWord_4020069, baseEnd_4020069] using wordTrace_append hprefix tailTrace_4020069
  have hstable : (prefixWord ++ tailWord_4020069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020069).length < 2 ^ (prefixWord ++ tailWord_4020069).sum := by decide
  have hdescent : baseEnd_4020069 < baseStart_4020069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020089 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_4020089 : Nat := 118140960795 + 4020089 * 2 ^ 59
def prefixEnd_4020089 : Nat := 4983230072969 + 3 ^ 40 * 4020089 * 2
def baseEnd_4020089 : Nat := 2064237930852627116999453

theorem tailTrace_4020089 : CollatzResearch.WordTrace tailWord_4020089 prefixEnd_4020089 2064237930852627116999453 := by
  unfold tailWord_4020089
  simp only [CollatzResearch.WordTrace]
  refine ⟨146624691532911604385159321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97749794355274402923439547 146624691532911604385159321)
  ·
    refine ⟨109968518649683703288869491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146624691532911604385159321 109968518649683703288869491)
    ·
      refine ⟨164952777974525554933304237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109968518649683703288869491 164952777974525554933304237)
      ·
        refine ⟨61857291740447083099989089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164952777974525554933304237 61857291740447083099989089)
        ·
          refine ⟨46392968805335312324991817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61857291740447083099989089 46392968805335312324991817)
          ·
            refine ⟨34794726604001484243743863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46392968805335312324991817 34794726604001484243743863)
            ·
              refine ⟨52192089906002226365615795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34794726604001484243743863 52192089906002226365615795)
              ·
                refine ⟨78288134859003339548423693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52192089906002226365615795 78288134859003339548423693)
                ·
                  refine ⟨29358050572126252330658885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78288134859003339548423693 29358050572126252330658885)
                  ·
                    refine ⟨5504634482273672311998541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29358050572126252330658885 5504634482273672311998541)
                    ·
                      refine ⟨2064237930852627116999453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5504634482273672311998541 2064237930852627116999453)
                      ·
                        rfl

theorem cell23_4020089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_4020089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020089 prefixEnd_4020089 := by exact prefixLift 4020089
  have htrace : WordTrace (prefixWord ++ tailWord_4020089) baseStart_4020089 baseEnd_4020089 := by
    simpa [prefixWord, tailWord_4020089, baseEnd_4020089] using wordTrace_append hprefix tailTrace_4020089
  have hstable : (prefixWord ++ tailWord_4020089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020089).length < 2 ^ (prefixWord ++ tailWord_4020089).sum := by decide
  have hdescent : baseEnd_4020089 < baseStart_4020089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020113 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 1, 4]
def baseStart_4020113 : Nat := 118140960795 + 4020113 * 2 ^ 59
def prefixEnd_4020113 : Nat := 4983230072969 + 3 ^ 40 * 4020113 * 2
def baseEnd_4020113 : Nat := 688083418129445007699781

theorem tailTrace_4020113 : CollatzResearch.WordTrace tailWord_4020113 prefixEnd_4020113 688083418129445007699781 := by
  unfold tailWord_4020113
  simp only [CollatzResearch.WordTrace]
  refine ⟨146625566884824656484032993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97750377923216437656021995 146625566884824656484032993)
  ·
    refine ⟨109969175163618492363024745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146625566884824656484032993 109969175163618492363024745)
    ·
      refine ⟨82476881372713869272268559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109969175163618492363024745 82476881372713869272268559)
      ·
        refine ⟨123715322059070803908402839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82476881372713869272268559 123715322059070803908402839)
        ·
          refine ⟨185572983088606205862604259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123715322059070803908402839 185572983088606205862604259)
          ·
            refine ⟨278359474632909308793906389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185572983088606205862604259 278359474632909308793906389)
            ·
              refine ⟨6524050186708811924857181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278359474632909308793906389 6524050186708811924857181)
              ·
                refine ⟨2446518820015804471821443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6524050186708811924857181 2446518820015804471821443)
                ·
                  refine ⟨3669778230023706707732165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446518820015804471821443 3669778230023706707732165)
                  ·
                    refine ⟨688083418129445007699781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669778230023706707732165 688083418129445007699781)
                    ·
                      rfl

theorem cell23_4020113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_4020113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020113 prefixEnd_4020113 := by exact prefixLift 4020113
  have htrace : WordTrace (prefixWord ++ tailWord_4020113) baseStart_4020113 baseEnd_4020113 := by
    simpa [prefixWord, tailWord_4020113, baseEnd_4020113] using wordTrace_append hprefix tailTrace_4020113
  have hstable : (prefixWord ++ tailWord_4020113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020113).length < 2 ^ (prefixWord ++ tailWord_4020113).sum := by decide
  have hdescent : baseEnd_4020113 < baseStart_4020113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020130 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4020130 : Nat := 118140960795 + 4020130 * 2 ^ 59
def prefixEnd_4020130 : Nat := 4983230072969 + 3 ^ 40 * 4020130 * 2
def baseEnd_4020130 : Nat := 688086327853153818862255

theorem tailTrace_4020130 : CollatzResearch.WordTrace tailWord_4020130 prefixEnd_4020130 688086327853153818862255 := by
  unfold tailWord_4020130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36656546731440767096850461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97750791283842045591601229 36656546731440767096850461)
  ·
    refine ⟨13746205024290287661318923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36656546731440767096850461 13746205024290287661318923)
    ·
      refine ⟨20619307536435431491978385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13746205024290287661318923 20619307536435431491978385)
      ·
        refine ⟨15464480652326573618983789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20619307536435431491978385 15464480652326573618983789)
        ·
          refine ⟨5799180244622465107118921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15464480652326573618983789 5799180244622465107118921)
          ·
            refine ⟨4349385183466848830339191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799180244622465107118921 4349385183466848830339191)
            ·
              refine ⟨6524077775200273245508787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349385183466848830339191 6524077775200273245508787)
              ·
                refine ⟨9786116662800409868263181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524077775200273245508787 9786116662800409868263181)
                ·
                  refine ⟨3669793748550153700598693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9786116662800409868263181 3669793748550153700598693)
                  ·
                    refine ⟨688086327853153818862255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669793748550153700598693 688086327853153818862255)
                    ·
                      rfl

theorem cell23_4020130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4020130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020130 prefixEnd_4020130 := by exact prefixLift 4020130
  have htrace : WordTrace (prefixWord ++ tailWord_4020130) baseStart_4020130 baseEnd_4020130 := by
    simpa [prefixWord, tailWord_4020130, baseEnd_4020130] using wordTrace_append hprefix tailTrace_4020130
  have hstable : (prefixWord ++ tailWord_4020130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020130).length < 2 ^ (prefixWord ++ tailWord_4020130).sum := by decide
  have hdescent : baseEnd_4020130 < baseStart_4020130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020146 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_4020146 : Nat := 118140960795 + 4020146 * 2 ^ 59
def prefixEnd_4020146 : Nat := 4983230072969 + 3 ^ 40 * 4020146 * 2
def baseEnd_4020146 : Nat := 2064267199249933393986691

theorem tailTrace_4020146 : CollatzResearch.WordTrace tailWord_4020146 prefixEnd_4020146 2064267199249933393986691 := by
  unfold tailWord_4020146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36656692623426275779996073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97751180329136735413322861 36656692623426275779996073)
  ·
    refine ⟨27492519467569706834997055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36656692623426275779996073 27492519467569706834997055)
    ·
      refine ⟨41238779201354560252495583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27492519467569706834997055 41238779201354560252495583)
      ·
        refine ⟨61858168802031840378743375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41238779201354560252495583 61858168802031840378743375)
        ·
          refine ⟨92787253203047760568115063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61858168802031840378743375 92787253203047760568115063)
          ·
            refine ⟨139180879804571640852172595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92787253203047760568115063 139180879804571640852172595)
            ·
              refine ⟨208771319706857461278258893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139180879804571640852172595 208771319706857461278258893)
              ·
                refine ⟨78289244890071547979347085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208771319706857461278258893 78289244890071547979347085)
                ·
                  refine ⟨29358466833776830492255157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78289244890071547979347085 29358466833776830492255157)
                  ·
                    refine ⟨2752356265666577858648921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29358466833776830492255157 2752356265666577858648921)
                    ·
                      refine ⟨2064267199249933393986691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752356265666577858648921 2064267199249933393986691)
                      ·
                        rfl

theorem cell23_4020146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_4020146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020146 prefixEnd_4020146 := by exact prefixLift 4020146
  have htrace : WordTrace (prefixWord ++ tailWord_4020146) baseStart_4020146 baseEnd_4020146 := by
    simpa [prefixWord, tailWord_4020146, baseEnd_4020146] using wordTrace_append hprefix tailTrace_4020146
  have hstable : (prefixWord ++ tailWord_4020146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020146).length < 2 ^ (prefixWord ++ tailWord_4020146).sum := by decide
  have hdescent : baseEnd_4020146 < baseStart_4020146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020169 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_4020169 : Nat := 118140960795 + 4020169 * 2 ^ 59
def prefixEnd_4020169 : Nat := 4983230072969 + 3 ^ 40 * 4020169 * 2
def baseEnd_4020169 : Nat := 688093003101662267999695

theorem tailTrace_4020169 : CollatzResearch.WordTrace tailWord_4020169 prefixEnd_4020169 688093003101662267999695 := by
  unfold tailWord_4020169
  simp only [CollatzResearch.WordTrace]
  refine ⟨146627609372621778048071561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97751739581747852032047707 146627609372621778048071561)
  ·
    refine ⟨109970707029466333536053671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146627609372621778048071561 109970707029466333536053671)
    ·
      refine ⟨164956060544199500304080507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109970707029466333536053671 164956060544199500304080507)
      ·
        refine ⟨247434090816299250456120761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164956060544199500304080507 247434090816299250456120761)
        ·
          refine ⟨185575568112224437842090571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247434090816299250456120761 185575568112224437842090571)
          ·
            refine ⟨278363352168336656763135857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185575568112224437842090571 278363352168336656763135857)
            ·
              refine ⟨208772514126252492572351893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278363352168336656763135857 208772514126252492572351893)
              ·
                refine ⟨9786211599668085589328995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208772514126252492572351893 9786211599668085589328995)
                ·
                  refine ⟨14679317399502128383993493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9786211599668085589328995 14679317399502128383993493)
                  ·
                    refine ⟨688093003101662267999695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14679317399502128383993493 688093003101662267999695)
                    ·
                      rfl

theorem cell23_4020169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_4020169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020169 prefixEnd_4020169 := by exact prefixLift 4020169
  have htrace : WordTrace (prefixWord ++ tailWord_4020169) baseStart_4020169 baseEnd_4020169 := by
    simpa [prefixWord, tailWord_4020169, baseEnd_4020169] using wordTrace_append hprefix tailTrace_4020169
  have hstable : (prefixWord ++ tailWord_4020169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020169).length < 2 ^ (prefixWord ++ tailWord_4020169).sum := by decide
  have hdescent : baseEnd_4020169 < baseStart_4020169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020176 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4]
def baseStart_4020176 : Nat := 118140960795 + 4020176 * 2 ^ 59
def prefixEnd_4020176 : Nat := 4983230072969 + 3 ^ 40 * 4020176 * 2
def baseEnd_4020176 : Nat := 2064282603669568276611553

theorem tailTrace_4020176 : CollatzResearch.WordTrace tailWord_4020176 prefixEnd_4020176 2064282603669568276611553 := by
  unfold tailWord_4020176
  simp only [CollatzResearch.WordTrace]
  refine ⟨73313932341798209121788191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97751909789064278829050921 73313932341798209121788191)
  ·
    refine ⟨109970898512697313682682287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73313932341798209121788191 109970898512697313682682287)
    ·
      refine ⟨164956347769045970524023431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109970898512697313682682287 164956347769045970524023431)
      ·
        refine ⟨247434521653568955786035147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164956347769045970524023431 247434521653568955786035147)
        ·
          refine ⟨371151782480353433679052721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247434521653568955786035147 371151782480353433679052721)
          ·
            refine ⟨278363836860265075259289541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371151782480353433679052721 278363836860265075259289541)
            ·
              refine ⟨52193219411299701611116789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278363836860265075259289541 52193219411299701611116789)
              ·
                refine ⟨4893114319809347026042199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52193219411299701611116789 4893114319809347026042199)
                ·
                  refine ⟨7339671479714020539063299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893114319809347026042199 7339671479714020539063299)
                  ·
                    refine ⟨11009507219571030808594949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339671479714020539063299 11009507219571030808594949)
                    ·
                      refine ⟨2064282603669568276611553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11009507219571030808594949 2064282603669568276611553)
                      ·
                        rfl

theorem cell23_4020176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_4020176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020176 prefixEnd_4020176 := by exact prefixLift 4020176
  have htrace : WordTrace (prefixWord ++ tailWord_4020176) baseStart_4020176 baseEnd_4020176 := by
    simpa [prefixWord, tailWord_4020176, baseEnd_4020176] using wordTrace_append hprefix tailTrace_4020176
  have hstable : (prefixWord ++ tailWord_4020176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020176).length < 2 ^ (prefixWord ++ tailWord_4020176).sum := by decide
  have hdescent : baseEnd_4020176 < baseStart_4020176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020196 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_4020196 : Nat := 118140960795 + 4020196 * 2 ^ 59
def prefixEnd_4020196 : Nat := 4983230072969 + 3 ^ 40 * 4020196 * 2
def baseEnd_4020196 : Nat := 2064292873282658198361461

theorem tailTrace_4020196 : CollatzResearch.WordTrace tailWord_4020196 prefixEnd_4020196 2064292873282658198361461 := by
  unfold tailWord_4020196
  simp only [CollatzResearch.WordTrace]
  refine ⟨73314297071761980829652221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97752396095682641106202961 73314297071761980829652221)
  ·
    refine ⟨27492861401910742811119583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73314297071761980829652221 27492861401910742811119583)
    ·
      refine ⟨41239292102866114216679375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27492861401910742811119583 41239292102866114216679375)
      ·
        refine ⟨61858938154299171325019063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41239292102866114216679375 61858938154299171325019063)
        ·
          refine ⟨92788407231448756987528595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61858938154299171325019063 92788407231448756987528595)
          ·
            refine ⟨139182610847173135481292893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92788407231448756987528595 139182610847173135481292893)
            ·
              refine ⟨52193479067689925805484835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139182610847173135481292893 52193479067689925805484835)
              ·
                refine ⟨78290218601534888708227253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52193479067689925805484835 78290218601534888708227253)
                ·
                  refine ⟨7339707993893895816396305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78290218601534888708227253 7339707993893895816396305)
                  ·
                    refine ⟨5504780995420421862297229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7339707993893895816396305 5504780995420421862297229)
                    ·
                      refine ⟨2064292873282658198361461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5504780995420421862297229 2064292873282658198361461)
                      ·
                        rfl

theorem cell23_4020196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_4020196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020196 prefixEnd_4020196 := by exact prefixLift 4020196
  have htrace : WordTrace (prefixWord ++ tailWord_4020196) baseStart_4020196 baseEnd_4020196 := by
    simpa [prefixWord, tailWord_4020196, baseEnd_4020196] using wordTrace_append hprefix tailTrace_4020196
  have hstable : (prefixWord ++ tailWord_4020196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020196).length < 2 ^ (prefixWord ++ tailWord_4020196).sum := by decide
  have hdescent : baseEnd_4020196 < baseStart_4020196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020214 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_4020214 : Nat := 118140960795 + 4020214 * 2 ^ 59
def prefixEnd_4020214 : Nat := 4983230072969 + 3 ^ 40 * 4020214 * 2
def baseEnd_4020214 : Nat := 2064302115934439127936379

theorem tailTrace_4020214 : CollatzResearch.WordTrace tailWord_4020214 prefixEnd_4020214 2064302115934439127936379 := by
  unfold tailWord_4020214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164328166091171920841231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97752833771639167155639797 9164328166091171920841231)
  ·
    refine ⟨13746492249136757881261847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9164328166091171920841231 13746492249136757881261847)
    ·
      refine ⟨20619738373705136821892771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13746492249136757881261847 20619738373705136821892771)
      ·
        refine ⟨30929607560557705232839157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20619738373705136821892771 30929607560557705232839157)
        ·
          refine ⟨2899650708802284865578671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30929607560557705232839157 2899650708802284865578671)
          ·
            refine ⟨4349476063203427298368007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899650708802284865578671 4349476063203427298368007)
            ·
              refine ⟨6524214094805140947552011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349476063203427298368007 6524214094805140947552011)
              ·
                refine ⟨9786321142207711421328017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524214094805140947552011 9786321142207711421328017)
                ·
                  refine ⟨7339740856655783565996013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9786321142207711421328017 7339740856655783565996013)
                  ·
                    refine ⟨2752402821245918837248505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7339740856655783565996013 2752402821245918837248505)
                    ·
                      refine ⟨2064302115934439127936379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752402821245918837248505 2064302115934439127936379)
                      ·
                        rfl

theorem cell23_4020214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_4020214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020214 prefixEnd_4020214 := by exact prefixLift 4020214
  have htrace : WordTrace (prefixWord ++ tailWord_4020214) baseStart_4020214 baseEnd_4020214 := by
    simpa [prefixWord, tailWord_4020214, baseEnd_4020214] using wordTrace_append hprefix tailTrace_4020214
  have hstable : (prefixWord ++ tailWord_4020214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020214).length < 2 ^ (prefixWord ++ tailWord_4020214).sum := by decide
  have hdescent : baseEnd_4020214 < baseStart_4020214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020296 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_4020296 : Nat := 118140960795 + 4020296 * 2 ^ 59
def prefixEnd_4020296 : Nat := 4983230072969 + 3 ^ 40 * 4020296 * 2
def baseEnd_4020296 : Nat := 2064344221348107807111001

theorem tailTrace_4020296 : CollatzResearch.WordTrace tailWord_4020296 prefixEnd_4020296 2064344221348107807111001 := by
  unfold tailWord_4020296
  simp only [CollatzResearch.WordTrace]
  refine ⟨73316120721580839368972371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97754827628774452491963161 73316120721580839368972371)
  ·
    refine ⟨109974181082371259053458557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73316120721580839368972371 109974181082371259053458557)
    ·
      refine ⟨41240317905889222145046959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109974181082371259053458557 41240317905889222145046959)
      ·
        refine ⟨61860476858833833217570439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41240317905889222145046959 61860476858833833217570439)
        ·
          refine ⟨92790715288250749826355659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61860476858833833217570439 92790715288250749826355659)
          ·
            refine ⟨139186072932376124739533489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92790715288250749826355659 139186072932376124739533489)
            ·
              refine ⟨104389554699282093554650117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139186072932376124739533489 104389554699282093554650117)
              ·
                refine ⟨19573041506115392541496897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104389554699282093554650117 19573041506115392541496897)
                ·
                  refine ⟨14679781129586544406122673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19573041506115392541496897 14679781129586544406122673)
                  ·
                    refine ⟨11009835847189908304592005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14679781129586544406122673 11009835847189908304592005)
                    ·
                      refine ⟨2064344221348107807111001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11009835847189908304592005 2064344221348107807111001)
                      ·
                        rfl

theorem cell23_4020296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_4020296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020296 prefixEnd_4020296 := by exact prefixLift 4020296
  have htrace : WordTrace (prefixWord ++ tailWord_4020296) baseStart_4020296 baseEnd_4020296 := by
    simpa [prefixWord, tailWord_4020296, baseEnd_4020296] using wordTrace_append hprefix tailTrace_4020296
  have hstable : (prefixWord ++ tailWord_4020296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020296).length < 2 ^ (prefixWord ++ tailWord_4020296).sum := by decide
  have hdescent : baseEnd_4020296 < baseStart_4020296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020300 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4020300 : Nat := 118140960795 + 4020300 * 2 ^ 59
def prefixEnd_4020300 : Nat := 4983230072969 + 3 ^ 40 * 4020300 * 2
def baseEnd_4020300 : Nat := 2064346275270725791460983

theorem tailTrace_4020300 : CollatzResearch.WordTrace tailWord_4020300 prefixEnd_4020300 2064346275270725791460983 := by
  unfold tailWord_4020300
  simp only [CollatzResearch.WordTrace]
  refine ⟨73316193667573593710545177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97754924890098124947393569 73316193667573593710545177)
  ·
    refine ⟨54987145250680195282908883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73316193667573593710545177 54987145250680195282908883)
    ·
      refine ⟨82480717876020292924363325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54987145250680195282908883 82480717876020292924363325)
      ·
        refine ⟨30930269203507609846636247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82480717876020292924363325 30930269203507609846636247)
        ·
          refine ⟨46395403805261414769954371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30930269203507609846636247 46395403805261414769954371)
          ·
            refine ⟨69593105707892122154931557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46395403805261414769954371 69593105707892122154931557)
            ·
              refine ⟨13048707320229772904049667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69593105707892122154931557 13048707320229772904049667)
              ·
                refine ⟨19573060980344659356074501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13048707320229772904049667 19573060980344659356074501)
                ·
                  refine ⟨3669948933814623629263969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19573060980344659356074501 3669948933814623629263969)
                  ·
                    refine ⟨2752461700360967721947977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3669948933814623629263969 2752461700360967721947977)
                    ·
                      refine ⟨2064346275270725791460983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752461700360967721947977 2064346275270725791460983)
                      ·
                        rfl

theorem cell23_4020300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4020300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020300 prefixEnd_4020300 := by exact prefixLift 4020300
  have htrace : WordTrace (prefixWord ++ tailWord_4020300) baseStart_4020300 baseEnd_4020300 := by
    simpa [prefixWord, tailWord_4020300, baseEnd_4020300] using wordTrace_append hprefix tailTrace_4020300
  have hstable : (prefixWord ++ tailWord_4020300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020300).length < 2 ^ (prefixWord ++ tailWord_4020300).sum := by decide
  have hdescent : baseEnd_4020300 < baseStart_4020300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020357 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 5]
def baseStart_4020357 : Nat := 118140960795 + 4020357 * 2 ^ 59
def prefixEnd_4020357 : Nat := 4983230072969 + 3 ^ 40 * 4020357 * 2
def baseEnd_4020357 : Nat := 229375060407559118716469

theorem tailTrace_4020357 : CollatzResearch.WordTrace tailWord_4020357 prefixEnd_4020357 229375060407559118716469 := by
  unfold tailWord_4020357
  simp only [CollatzResearch.WordTrace]
  refine ⟨146634466295940686155915325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97756310863960457437276883 146634466295940686155915325)
  ·
    refine ⟨54987924860977757308468247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146634466295940686155915325 54987924860977757308468247)
    ·
      refine ⟨82481887291466635962702371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54987924860977757308468247 82481887291466635962702371)
      ·
        refine ⟨123722830937199953944053557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82481887291466635962702371 123722830937199953944053557)
        ·
          refine ⟨11599015400362495682255021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123722830937199953944053557 11599015400362495682255021)
          ·
            refine ⟨4349630775135935880845633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11599015400362495682255021 4349630775135935880845633)
            ·
              refine ⟨3262223081351951910634225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349630775135935880845633 3262223081351951910634225)
              ·
                refine ⟨2446667311013963932975669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3262223081351951910634225 2446667311013963932975669)
                ·
                  refine ⟨229375060407559118716469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446667311013963932975669 229375060407559118716469)
                  ·
                    rfl

theorem cell23_4020357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_4020357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020357 prefixEnd_4020357 := by exact prefixLift 4020357
  have htrace : WordTrace (prefixWord ++ tailWord_4020357) baseStart_4020357 baseEnd_4020357 := by
    simpa [prefixWord, tailWord_4020357, baseEnd_4020357] using wordTrace_append hprefix tailTrace_4020357
  have hstable : (prefixWord ++ tailWord_4020357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020357).length < 2 ^ (prefixWord ++ tailWord_4020357).sum := by decide
  have hdescent : baseEnd_4020357 < baseStart_4020357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020360 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4020360 : Nat := 118140960795 + 4020360 * 2 ^ 59
def prefixEnd_4020360 : Nat := 4983230072969 + 3 ^ 40 * 4020360 * 2
def baseEnd_4020360 : Nat := 2064377084109995556710707

theorem tailTrace_4020360 : CollatzResearch.WordTrace tailWord_4020360 prefixEnd_4020360 2064377084109995556710707 := by
  unfold tailWord_4020360
  simp only [CollatzResearch.WordTrace]
  refine ⟨73317287857464908834137267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97756383809953211778849689 73317287857464908834137267)
  ·
    refine ⟨109975931786197363251205901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73317287857464908834137267 109975931786197363251205901)
    ·
      refine ⟨41240974419824011219202213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109975931786197363251205901 41240974419824011219202213)
      ·
        refine ⟨7732682703717002103600415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41240974419824011219202213 7732682703717002103600415)
        ·
          refine ⟨11599024055575503155400623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7732682703717002103600415 11599024055575503155400623)
          ·
            refine ⟨17398536083363254733100935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11599024055575503155400623 17398536083363254733100935)
            ·
              refine ⟨26097804125044882099651403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17398536083363254733100935 26097804125044882099651403)
              ·
                refine ⟨39146706187567323149477105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26097804125044882099651403 39146706187567323149477105)
                ·
                  refine ⟨29360029640675492362107829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39146706187567323149477105 29360029640675492362107829)
                  ·
                    refine ⟨2752502778813327408947609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29360029640675492362107829 2752502778813327408947609)
                    ·
                      refine ⟨2064377084109995556710707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752502778813327408947609 2064377084109995556710707)
                      ·
                        rfl

theorem cell23_4020360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4020360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020360 prefixEnd_4020360 := by exact prefixLift 4020360
  have htrace : WordTrace (prefixWord ++ tailWord_4020360) baseStart_4020360 baseEnd_4020360 := by
    simpa [prefixWord, tailWord_4020360, baseEnd_4020360] using wordTrace_append hprefix tailTrace_4020360
  have hstable : (prefixWord ++ tailWord_4020360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020360).length < 2 ^ (prefixWord ++ tailWord_4020360).sum := by decide
  have hdescent : baseEnd_4020360 < baseStart_4020360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020443 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 1, 5]
def baseStart_4020443 : Nat := 118140960795 + 4020443 * 2 ^ 59
def prefixEnd_4020443 : Nat := 4983230072969 + 3 ^ 40 * 4020443 * 2
def baseEnd_4020443 : Nat := 688139901001439577324275

theorem tailTrace_4020443 : CollatzResearch.WordTrace tailWord_4020443 prefixEnd_4020443 688139901001439577324275 := by
  unfold tailWord_4020443
  simp only [CollatzResearch.WordTrace]
  refine ⟨146637602973629122843545983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97758401982419415229030655 146637602973629122843545983)
  ·
    refine ⟨219956404460443684265318975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146637602973629122843545983 219956404460443684265318975)
    ·
      refine ⟨329934606690665526397978463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219956404460443684265318975 329934606690665526397978463)
      ·
        refine ⟨494901910035998289596967695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329934606690665526397978463 494901910035998289596967695)
        ·
          refine ⟨742352865053997434395451543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494901910035998289596967695 742352865053997434395451543)
          ·
            refine ⟨1113529297580996151593177315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742352865053997434395451543 1113529297580996151593177315)
            ·
              refine ⟨1670293946371494227389765973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113529297580996151593177315 1670293946371494227389765973)
              ·
                refine ⟨4893439296010236994305955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1670293946371494227389765973 4893439296010236994305955)
                ·
                  refine ⟨7340158944015355491458933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893439296010236994305955 7340158944015355491458933)
                  ·
                    refine ⟨688139901001439577324275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7340158944015355491458933 688139901001439577324275)
                    ·
                      rfl

theorem cell23_4020443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 5].length) (baseStart_4020443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020443 prefixEnd_4020443 := by exact prefixLift 4020443
  have htrace : WordTrace (prefixWord ++ tailWord_4020443) baseStart_4020443 baseEnd_4020443 := by
    simpa [prefixWord, tailWord_4020443, baseEnd_4020443] using wordTrace_append hprefix tailTrace_4020443
  have hstable : (prefixWord ++ tailWord_4020443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020443).length < 2 ^ (prefixWord ++ tailWord_4020443).sum := by decide
  have hdescent : baseEnd_4020443 < baseStart_4020443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020451 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 1, 4]
def baseStart_4020451 : Nat := 118140960795 + 4020451 * 2 ^ 59
def prefixEnd_4020451 : Nat := 4983230072969 + 3 ^ 40 * 4020451 * 2
def baseEnd_4020451 : Nat := 688141270283184900224263

theorem tailTrace_4020451 : CollatzResearch.WordTrace tailWord_4020451 prefixEnd_4020451 688141270283184900224263 := by
  unfold tailWord_4020451
  simp only [CollatzResearch.WordTrace]
  refine ⟨146637894757600140209837207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97758596505066760139891471 146637894757600140209837207)
  ·
    refine ⟨219956842136400210314755811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146637894757600140209837207 219956842136400210314755811)
    ·
      refine ⟨329935263204600315472133717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219956842136400210314755811 329935263204600315472133717)
      ·
        refine ⟨3866428865678909946939067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 329935263204600315472133717 3866428865678909946939067)
        ·
          refine ⟨5799643298518364920408601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866428865678909946939067 5799643298518364920408601)
          ·
            refine ⟨4349732473888773690306451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799643298518364920408601 4349732473888773690306451)
            ·
              refine ⟨6524598710833160535459677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349732473888773690306451 6524598710833160535459677)
              ·
                refine ⟨2446724516562435200797379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6524598710833160535459677 2446724516562435200797379)
                ·
                  refine ⟨3670086774843652801196069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446724516562435200797379 3670086774843652801196069)
                  ·
                    refine ⟨688141270283184900224263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670086774843652801196069 688141270283184900224263)
                    ·
                      rfl

theorem cell23_4020451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 4].length) (baseStart_4020451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020451 prefixEnd_4020451 := by exact prefixLift 4020451
  have htrace : WordTrace (prefixWord ++ tailWord_4020451) baseStart_4020451 baseEnd_4020451 := by
    simpa [prefixWord, tailWord_4020451, baseEnd_4020451] using wordTrace_append hprefix tailTrace_4020451
  have hstable : (prefixWord ++ tailWord_4020451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020451).length < 2 ^ (prefixWord ++ tailWord_4020451).sum := by decide
  have hdescent : baseEnd_4020451 < baseStart_4020451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020483 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5]
def baseStart_4020483 : Nat := 118140960795 + 4020483 * 2 ^ 59
def prefixEnd_4020483 : Nat := 4983230072969 + 3 ^ 40 * 4020483 * 2
def baseEnd_4020483 : Nat := 2064440242230498575472641

theorem tailTrace_4020483 : CollatzResearch.WordTrace tailWord_4020483 prefixEnd_4020483 2064440242230498575472641 := by
  unfold tailWord_4020483
  simp only [CollatzResearch.WordTrace]
  refine ⟨146639061893484209675002103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97759374595656139783334735 146639061893484209675002103)
  ·
    refine ⟨219958592840226314512503155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146639061893484209675002103 219958592840226314512503155)
    ·
      refine ⟨329937889260339471768754733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219958592840226314512503155 329937889260339471768754733)
      ·
        refine ⟨123726708472627301913283025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329937889260339471768754733 123726708472627301913283025)
        ·
          refine ⟨92795031354470476434962269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123726708472627301913283025 92795031354470476434962269)
          ·
            refine ⟨34798136757926428663110851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92795031354470476434962269 34798136757926428663110851)
            ·
              refine ⟨52197205136889642994666277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34798136757926428663110851 52197205136889642994666277)
              ·
                refine ⟨9786975963166808061499927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52197205136889642994666277 9786975963166808061499927)
                ·
                  refine ⟨14680463944750212092249891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9786975963166808061499927 14680463944750212092249891)
                  ·
                    refine ⟨22020695917125318138374837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14680463944750212092249891 22020695917125318138374837)
                    ·
                      refine ⟨2064440242230498575472641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22020695917125318138374837 2064440242230498575472641)
                      ·
                        rfl

theorem cell23_4020483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_4020483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020483 prefixEnd_4020483 := by exact prefixLift 4020483
  have htrace : WordTrace (prefixWord ++ tailWord_4020483) baseStart_4020483 baseEnd_4020483 := by
    simpa [prefixWord, tailWord_4020483, baseEnd_4020483] using wordTrace_append hprefix tailTrace_4020483
  have hstable : (prefixWord ++ tailWord_4020483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020483).length < 2 ^ (prefixWord ++ tailWord_4020483).sum := by decide
  have hdescent : baseEnd_4020483 < baseStart_4020483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020497 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_4020497 : Nat := 118140960795 + 4020497 * 2 ^ 59
def prefixEnd_4020497 : Nat := 4983230072969 + 3 ^ 40 * 4020497 * 2
def baseEnd_4020497 : Nat := 2064447430959661520697577

theorem tailTrace_4020497 : CollatzResearch.WordTrace tailWord_4020497 prefixEnd_4020497 2064447430959661520697577 := by
  unfold tailWord_4020497
  simp only [CollatzResearch.WordTrace]
  refine ⟨146639572515433490066011745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97759715010288993377341163 146639572515433490066011745)
  ·
    refine ⟨109979679386575117549508809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146639572515433490066011745 109979679386575117549508809)
    ·
      refine ⟨82484759539931338162131607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109979679386575117549508809 82484759539931338162131607)
      ·
        refine ⟨123727139309897007243197411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82484759539931338162131607 123727139309897007243197411)
        ·
          refine ⟨185590708964845510864796117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123727139309897007243197411 185590708964845510864796117)
          ·
            refine ⟨4349782241363566660893659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 185590708964845510864796117 4349782241363566660893659)
            ·
              refine ⟨6524673362045349991340489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349782241363566660893659 6524673362045349991340489)
              ·
                refine ⟨4893505021534012493505367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6524673362045349991340489 4893505021534012493505367)
                ·
                  refine ⟨7340257532301018740258051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893505021534012493505367 7340257532301018740258051)
                  ·
                    refine ⟨11010386298451528110387077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7340257532301018740258051 11010386298451528110387077)
                    ·
                      refine ⟨2064447430959661520697577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11010386298451528110387077 2064447430959661520697577)
                      ·
                        rfl

theorem cell23_4020497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_4020497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020497 prefixEnd_4020497 := by exact prefixLift 4020497
  have htrace : WordTrace (prefixWord ++ tailWord_4020497) baseStart_4020497 baseEnd_4020497 := by
    simpa [prefixWord, tailWord_4020497, baseEnd_4020497] using wordTrace_append hprefix tailTrace_4020497
  have hstable : (prefixWord ++ tailWord_4020497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020497).length < 2 ^ (prefixWord ++ tailWord_4020497).sum := by decide
  have hdescent : baseEnd_4020497 < baseStart_4020497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020503 : List Nat := [1, 1, 3, 4, 1, 2, 2, 9]
def baseStart_4020503 : Nat := 118140960795 + 4020503 * 2 ^ 59
def prefixEnd_4020503 : Nat := 4983230072969 + 3 ^ 40 * 4020503 * 2
def baseEnd_4020503 : Nat := 76461130068281055452687

theorem tailTrace_4020503 : CollatzResearch.WordTrace tailWord_4020503 prefixEnd_4020503 76461130068281055452687 := by
  unfold tailWord_4020503
  simp only [CollatzResearch.WordTrace]
  refine ⟨146639791353411753090730163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97759860902274502060486775 146639791353411753090730163)
  ·
    refine ⟨219959687030117629636095245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146639791353411753090730163 219959687030117629636095245)
    ·
      refine ⟨82484882636294111113535717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219959687030117629636095245 82484882636294111113535717)
      ·
        refine ⟨15465915494305145833787947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82484882636294111113535717 15465915494305145833787947)
        ·
          refine ⟨23198873241457718750681921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15465915494305145833787947 23198873241457718750681921)
          ·
            refine ⟨17399154931093289063011441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23198873241457718750681921 17399154931093289063011441)
            ·
              refine ⟨13049366198319966797258581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17399154931093289063011441 13049366198319966797258581)
              ·
                refine ⟨76461130068281055452687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13049366198319966797258581 76461130068281055452687)
                ·
                  rfl

theorem cell23_4020503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 9].length) (baseStart_4020503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020503 prefixEnd_4020503 := by exact prefixLift 4020503
  have htrace : WordTrace (prefixWord ++ tailWord_4020503) baseStart_4020503 baseEnd_4020503 := by
    simpa [prefixWord, tailWord_4020503, baseEnd_4020503] using wordTrace_append hprefix tailTrace_4020503
  have hstable : (prefixWord ++ tailWord_4020503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020503).length < 2 ^ (prefixWord ++ tailWord_4020503).sum := by decide
  have hdescent : baseEnd_4020503 < baseStart_4020503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020514 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_4020514 : Nat := 118140960795 + 4020514 * 2 ^ 59
def prefixEnd_4020514 : Nat := 4983230072969 + 3 ^ 40 * 4020514 * 2
def baseEnd_4020514 : Nat := 2064456160130787954184999

theorem tailTrace_4020514 : CollatzResearch.WordTrace tailWord_4020514 prefixEnd_4020514 2064456160130787954184999 := by
  unfold tailWord_4020514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36660048139092975492345149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97760128370914601312920397 36660048139092975492345149)
  ·
    refine ⟨13747518052159865809629431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36660048139092975492345149 13747518052159865809629431)
    ·
      refine ⟨20621277078239798714444147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13747518052159865809629431 20621277078239798714444147)
      ·
        refine ⟨30931915617359698071666221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20621277078239798714444147 30931915617359698071666221)
        ·
          refine ⟨11599468356509886776874833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30931915617359698071666221 11599468356509886776874833)
          ·
            refine ⟨8699601267382415082656125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11599468356509886776874833 8699601267382415082656125)
            ·
              refine ⟨3262350475268405655996047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8699601267382415082656125 3262350475268405655996047)
              ·
                refine ⟨4893525712902608483994071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262350475268405655996047 4893525712902608483994071)
                ·
                  refine ⟨7340288569353912725991107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893525712902608483994071 7340288569353912725991107)
                  ·
                    refine ⟨11010432854030869088986661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7340288569353912725991107 11010432854030869088986661)
                    ·
                      refine ⟨2064456160130787954184999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11010432854030869088986661 2064456160130787954184999)
                      ·
                        rfl

theorem cell23_4020514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_4020514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020514 prefixEnd_4020514 := by exact prefixLift 4020514
  have htrace : WordTrace (prefixWord ++ tailWord_4020514) baseStart_4020514 baseEnd_4020514 := by
    simpa [prefixWord, tailWord_4020514, baseEnd_4020514] using wordTrace_append hprefix tailTrace_4020514
  have hstable : (prefixWord ++ tailWord_4020514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020514).length < 2 ^ (prefixWord ++ tailWord_4020514).sum := by decide
  have hdescent : baseEnd_4020514 < baseStart_4020514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020517 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_4020517 : Nat := 118140960795 + 4020517 * 2 ^ 59
def prefixEnd_4020517 : Nat := 4983230072969 + 3 ^ 40 * 4020517 * 2
def baseEnd_4020517 : Nat := 2064457700572751442447485

theorem tailTrace_4020517 : CollatzResearch.WordTrace tailWord_4020517 prefixEnd_4020517 2064457700572751442447485 := by
  unfold tailWord_4020517
  simp only [CollatzResearch.WordTrace]
  refine ⟨146640301975361033481739805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97760201316907355654493203 146640301975361033481739805)
  ·
    refine ⟨54990113240760387555652427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146640301975361033481739805 54990113240760387555652427)
    ·
      refine ⟨82485169861140581333478641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54990113240760387555652427 82485169861140581333478641)
      ·
        refine ⟨61863877395855436000108981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82485169861140581333478641 61863877395855436000108981)
        ·
          refine ⟨5799738505861447125010217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61863877395855436000108981 5799738505861447125010217)
          ·
            refine ⟨4349803879396085343757663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799738505861447125010217 4349803879396085343757663)
            ·
              refine ⟨6524705819094128015636495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349803879396085343757663 6524705819094128015636495)
              ·
                refine ⟨9787058728641192023454743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524705819094128015636495 9787058728641192023454743)
                ·
                  refine ⟨14680588092961788035182115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787058728641192023454743 14680588092961788035182115)
                  ·
                    refine ⟨22020882139442682052773173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14680588092961788035182115 22020882139442682052773173)
                    ·
                      refine ⟨2064457700572751442447485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22020882139442682052773173 2064457700572751442447485)
                      ·
                        rfl

theorem cell23_4020517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_4020517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020517 prefixEnd_4020517 := by exact prefixLift 4020517
  have htrace : WordTrace (prefixWord ++ tailWord_4020517) baseStart_4020517 baseEnd_4020517 := by
    simpa [prefixWord, tailWord_4020517, baseEnd_4020517] using wordTrace_append hprefix tailTrace_4020517
  have hstable : (prefixWord ++ tailWord_4020517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020517).length < 2 ^ (prefixWord ++ tailWord_4020517).sum := by decide
  have hdescent : baseEnd_4020517 < baseStart_4020517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020520 : List Nat := [2, 1, 5, 1, 4, 10]
def baseStart_4020520 : Nat := 118140960795 + 4020520 * 2 ^ 59
def prefixEnd_4020520 : Nat := 4983230072969 + 3 ^ 40 * 4020520 * 2
def baseEnd_4020520 : Nat := 8495717041212818644897

theorem tailTrace_4020520 : CollatzResearch.WordTrace tailWord_4020520 prefixEnd_4020520 8495717041212818644897 := by
  unfold tailWord_4020520
  simp only [CollatzResearch.WordTrace]
  refine ⟨73320205697175082497049507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97760274262900109996066009 73320205697175082497049507)
  ·
    refine ⟨109980308545762623745574261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73320205697175082497049507 109980308545762623745574261)
    ·
      refine ⟨10310653926165245976147587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109980308545762623745574261 10310653926165245976147587)
      ·
        refine ⟨15465980889247868964221381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310653926165245976147587 15465980889247868964221381)
        ·
          refine ⟨2899871416733975430791509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15465980889247868964221381 2899871416733975430791509)
          ·
            refine ⟨8495717041212818644897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2899871416733975430791509 8495717041212818644897)
            ·
              rfl

theorem cell23_4020520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 10].length) (baseStart_4020520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020520 prefixEnd_4020520 := by exact prefixLift 4020520
  have htrace : WordTrace (prefixWord ++ tailWord_4020520) baseStart_4020520 baseEnd_4020520 := by
    simpa [prefixWord, tailWord_4020520, baseEnd_4020520] using wordTrace_append hprefix tailTrace_4020520
  have hstable : (prefixWord ++ tailWord_4020520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020520).length < 2 ^ (prefixWord ++ tailWord_4020520).sum := by decide
  have hdescent : baseEnd_4020520 < baseStart_4020520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020525 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4020525 : Nat := 118140960795 + 4020525 * 2 ^ 59
def prefixEnd_4020525 : Nat := 4983230072969 + 3 ^ 40 * 4020525 * 2
def baseEnd_4020525 : Nat := 2064461808417987411147449

theorem tailTrace_4020525 : CollatzResearch.WordTrace tailWord_4020525 prefixEnd_4020525 2064461808417987411147449 := by
  unfold tailWord_4020525
  simp only [CollatzResearch.WordTrace]
  refine ⟨146640593759332050848031029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97760395839554700565354019 146640593759332050848031029)
  ·
    refine ⟨13747555664937379767002909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146640593759332050848031029 13747555664937379767002909)
    ·
      refine ⟨5155333374351517412626091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13747555664937379767002909 5155333374351517412626091)
      ·
        refine ⟨7733000061527276118939137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5155333374351517412626091 7733000061527276118939137)
        ·
          refine ⟨5799750046145457089204353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7733000061527276118939137 5799750046145457089204353)
          ·
            refine ⟨4349812534609092816903265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799750046145457089204353 4349812534609092816903265)
            ·
              refine ⟨3262359400956819612677449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349812534609092816903265 3262359400956819612677449)
              ·
                refine ⟨2446769550717614709508087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3262359400956819612677449 2446769550717614709508087)
                ·
                  refine ⟨3670154326076422064262131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446769550717614709508087 3670154326076422064262131)
                  ·
                    refine ⟨5505231489114633096393197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3670154326076422064262131 5505231489114633096393197)
                    ·
                      refine ⟨2064461808417987411147449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5505231489114633096393197 2064461808417987411147449)
                      ·
                        rfl

theorem cell23_4020525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4020525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020525 prefixEnd_4020525 := by exact prefixLift 4020525
  have htrace : WordTrace (prefixWord ++ tailWord_4020525) baseStart_4020525 baseEnd_4020525 := by
    simpa [prefixWord, tailWord_4020525, baseEnd_4020525] using wordTrace_append hprefix tailTrace_4020525
  have hstable : (prefixWord ++ tailWord_4020525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020525).length < 2 ^ (prefixWord ++ tailWord_4020525).sum := by decide
  have hdescent : baseEnd_4020525 < baseStart_4020525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020533 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_4020533 : Nat := 118140960795 + 4020533 * 2 ^ 59
def prefixEnd_4020533 : Nat := 4983230072969 + 3 ^ 40 * 4020533 * 2
def baseEnd_4020533 : Nat := 688155305421074459949137

theorem tailTrace_4020533 : CollatzResearch.WordTrace tailWord_4020533 prefixEnd_4020533 688155305421074459949137 := by
  unfold tailWord_4020533
  simp only [CollatzResearch.WordTrace]
  refine ⟨146640885543303068214322253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97760590362202045476214835 146640885543303068214322253)
  ·
    refine ⟨54990332078738650580370845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146640885543303068214322253 54990332078738650580370845)
    ·
      refine ⟨20621374529526993967639067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54990332078738650580370845 20621374529526993967639067)
      ·
        refine ⟨30932061794290490951458601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20621374529526993967639067 30932061794290490951458601)
        ·
          refine ⟨23199046345717868213593951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30932061794290490951458601 23199046345717868213593951)
          ·
            refine ⟨34798569518576802320390927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23199046345717868213593951 34798569518576802320390927)
            ·
              refine ⟨52197854277865203480586391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34798569518576802320390927 52197854277865203480586391)
              ·
                refine ⟨78296781416797805220879587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52197854277865203480586391 78296781416797805220879587)
                ·
                  refine ⟨117445172125196707831319381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78296781416797805220879587 117445172125196707831319381)
                  ·
                    refine ⟨688155305421074459949137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117445172125196707831319381 688155305421074459949137)
                    ·
                      rfl

theorem cell23_4020533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_4020533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020533 prefixEnd_4020533 := by exact prefixLift 4020533
  have htrace : WordTrace (prefixWord ++ tailWord_4020533) baseStart_4020533 baseEnd_4020533 := by
    simpa [prefixWord, tailWord_4020533, baseEnd_4020533] using wordTrace_append hprefix tailTrace_4020533
  have hstable : (prefixWord ++ tailWord_4020533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020533).length < 2 ^ (prefixWord ++ tailWord_4020533).sum := by decide
  have hdescent : baseEnd_4020533 < baseStart_4020533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020547 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 3]
def baseStart_4020547 : Nat := 118140960795 + 4020547 * 2 ^ 59
def prefixEnd_4020547 : Nat := 4983230072969 + 3 ^ 40 * 4020547 * 2
def baseEnd_4020547 : Nat := 2064473104992386325072347

theorem tailTrace_4020547 : CollatzResearch.WordTrace tailWord_4020547 prefixEnd_4020547 2064473104992386325072347 := by
  unfold tailWord_4020547
  simp only [CollatzResearch.WordTrace]
  refine ⟨146641396165252348605331895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97760930776834899070221263 146641396165252348605331895)
  ·
    refine ⟨219962094247878522907997843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146641396165252348605331895 219962094247878522907997843)
    ·
      refine ⟨329943141371817784361996765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219962094247878522907997843 329943141371817784361996765)
      ·
        refine ⟨123728678014431669135748787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329943141371817784361996765 123728678014431669135748787)
        ·
          refine ⟨185593017021647503703623181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123728678014431669135748787 185593017021647503703623181)
          ·
            refine ⟨69597381383117813888858693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185593017021647503703623181 69597381383117813888858693)
            ·
              refine ⟨13049509009334590104161005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69597381383117813888858693 13049509009334590104161005)
              ·
                refine ⟨4893565878500471289060377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13049509009334590104161005 4893565878500471289060377)
                ·
                  refine ⟨3670174408875353466795283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4893565878500471289060377 3670174408875353466795283)
                  ·
                    refine ⟨5505261613313030200192925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3670174408875353466795283 5505261613313030200192925)
                    ·
                      refine ⟨2064473104992386325072347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5505261613313030200192925 2064473104992386325072347)
                      ·
                        rfl

theorem cell23_4020547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_4020547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020547 prefixEnd_4020547 := by exact prefixLift 4020547
  have htrace : WordTrace (prefixWord ++ tailWord_4020547) baseStart_4020547 baseEnd_4020547 := by
    simpa [prefixWord, tailWord_4020547, baseEnd_4020547] using wordTrace_append hprefix tailTrace_4020547
  have hstable : (prefixWord ++ tailWord_4020547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020547).length < 2 ^ (prefixWord ++ tailWord_4020547).sum := by decide
  have hdescent : baseEnd_4020547 < baseStart_4020547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020553 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_4020553 : Nat := 118140960795 + 4020553 * 2 ^ 59
def prefixEnd_4020553 : Nat := 4983230072969 + 3 ^ 40 * 4020553 * 2
def baseEnd_4020553 : Nat := 2064476185876313301597319

theorem tailTrace_4020553 : CollatzResearch.WordTrace tailWord_4020553 prefixEnd_4020553 2064476185876313301597319 := by
  unfold tailWord_4020553
  simp only [CollatzResearch.WordTrace]
  refine ⟨146641615003230611630050313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97761076668820407753366875 146641615003230611630050313)
  ·
    refine ⟨109981211252422958722537735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146641615003230611630050313 109981211252422958722537735)
    ·
      refine ⟨164971816878634438083806603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109981211252422958722537735 164971816878634438083806603)
      ·
        refine ⟨247457725317951657125709905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164971816878634438083806603 247457725317951657125709905)
        ·
          refine ⟨185593293988463742844282429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247457725317951657125709905 185593293988463742844282429)
          ·
            refine ⟨69597485245673903566605911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185593293988463742844282429 69597485245673903566605911)
            ·
              refine ⟨104396227868510855349908867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69597485245673903566605911 104396227868510855349908867)
              ·
                refine ⟨156594341802766283024863301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104396227868510855349908867 156594341802766283024863301)
                ·
                  refine ⟨29361439088018678067161869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156594341802766283024863301 29361439088018678067161869)
                  ·
                    refine ⟨11010539658007004275185701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29361439088018678067161869 11010539658007004275185701)
                    ·
                      refine ⟨2064476185876313301597319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11010539658007004275185701 2064476185876313301597319)
                      ·
                        rfl

theorem cell23_4020553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_4020553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020553 prefixEnd_4020553 := by exact prefixLift 4020553
  have htrace : WordTrace (prefixWord ++ tailWord_4020553) baseStart_4020553 baseEnd_4020553 := by
    simpa [prefixWord, tailWord_4020553, baseEnd_4020553] using wordTrace_append hprefix tailTrace_4020553
  have hstable : (prefixWord ++ tailWord_4020553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020553).length < 2 ^ (prefixWord ++ tailWord_4020553).sum := by decide
  have hdescent : baseEnd_4020553 < baseStart_4020553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020587 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 4, 2, 2]
def baseStart_4020587 : Nat := 118140960795 + 4020587 * 2 ^ 59
def prefixEnd_4020587 : Nat := 4983230072969 + 3 ^ 40 * 4020587 * 2
def baseEnd_4020587 : Nat := 2064493644218566168572163

theorem tailTrace_4020587 : CollatzResearch.WordTrace tailWord_4020587 prefixEnd_4020587 2064493644218566168572163 := by
  unfold tailWord_4020587
  simp only [CollatzResearch.WordTrace]
  refine ⟨146642855085107435436788015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97761903390071623624525343 146642855085107435436788015)
  ·
    refine ⟨219964282627661153155182023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146642855085107435436788015 219964282627661153155182023)
    ·
      refine ⟨329946423941491729732773035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219964282627661153155182023 329946423941491729732773035)
      ·
        refine ⟨494919635912237594599159553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329946423941491729732773035 494919635912237594599159553)
        ·
          refine ⟨371189726934178195949369665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494919635912237594599159553 371189726934178195949369665)
          ·
            refine ⟨278392295200633646962027249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371189726934178195949369665 278392295200633646962027249)
            ·
              refine ⟨208794221400475235221520437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278392295200633646962027249 208794221400475235221520437)
              ·
                refine ⟨19574458256294553302017541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208794221400475235221520437 19574458256294553302017541)
                ·
                  refine ⟨3670210923055228744128289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19574458256294553302017541 3670210923055228744128289)
                  ·
                    refine ⟨2752658192291421558096217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3670210923055228744128289 2752658192291421558096217)
                    ·
                      refine ⟨2064493644218566168572163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752658192291421558096217 2064493644218566168572163)
                      ·
                        rfl

theorem cell23_4020587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 2, 2].length) (baseStart_4020587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020587 prefixEnd_4020587 := by exact prefixLift 4020587
  have htrace : WordTrace (prefixWord ++ tailWord_4020587) baseStart_4020587 baseEnd_4020587 := by
    simpa [prefixWord, tailWord_4020587, baseEnd_4020587] using wordTrace_append hprefix tailTrace_4020587
  have hstable : (prefixWord ++ tailWord_4020587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020587).length < 2 ^ (prefixWord ++ tailWord_4020587).sum := by decide
  have hdescent : baseEnd_4020587 < baseStart_4020587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020598 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4020598 : Nat := 118140960795 + 4020598 * 2 ^ 59
def prefixEnd_4020598 : Nat := 4983230072969 + 3 ^ 40 * 4020598 * 2
def baseEnd_4020598 : Nat := 2064499292505765625534613

theorem tailTrace_4020598 : CollatzResearch.WordTrace tailWord_4020598 prefixEnd_4020598 2064499292505765625534613 := by
  unfold tailWord_4020598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165203518004224019714903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97762170858711722876958965 9165203518004224019714903)
  ·
    refine ⟨13747805277006336029572355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9165203518004224019714903 13747805277006336029572355)
    ·
      refine ⟨20621707915509504044358533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13747805277006336029572355 20621707915509504044358533)
      ·
        refine ⟨3866570234158032008317225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20621707915509504044358533 3866570234158032008317225)
        ·
          refine ⟨2899927675618524006237919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3866570234158032008317225 2899927675618524006237919)
          ·
            refine ⟨4349891513427786009356879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899927675618524006237919 4349891513427786009356879)
            ·
              refine ⟨6524837270141679014035319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349891513427786009356879 6524837270141679014035319)
              ·
                refine ⟨9787255905212518521052979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524837270141679014035319 9787255905212518521052979)
                ·
                  refine ⟨14680883857818777781579469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787255905212518521052979 14680883857818777781579469)
                  ·
                    refine ⟨5505331446682041668092301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14680883857818777781579469 5505331446682041668092301)
                    ·
                      refine ⟨2064499292505765625534613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5505331446682041668092301 2064499292505765625534613)
                      ·
                        rfl

theorem cell23_4020598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4020598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020598 prefixEnd_4020598 := by exact prefixLift 4020598
  have htrace : WordTrace (prefixWord ++ tailWord_4020598) baseStart_4020598 baseEnd_4020598 := by
    simpa [prefixWord, tailWord_4020598, baseEnd_4020598] using wordTrace_append hprefix tailTrace_4020598
  have hstable : (prefixWord ++ tailWord_4020598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020598).length < 2 ^ (prefixWord ++ tailWord_4020598).sum := by decide
  have hdescent : baseEnd_4020598 < baseStart_4020598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020640 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_4020640 : Nat := 118140960795 + 4020640 * 2 ^ 59
def prefixEnd_4020640 : Nat := 4983230072969 + 3 ^ 40 * 4020640 * 2
def baseEnd_4020640 : Nat := 688173619564418153736473

theorem tailTrace_4020640 : CollatzResearch.WordTrace tailWord_4020640 prefixEnd_4020640 688173619564418153736473 := by
  unfold tailWord_4020640
  simp only [CollatzResearch.WordTrace]
  refine ⟨73322394076957712744233687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97763192102610283658978249 73322394076957712744233687)
  ·
    refine ⟨109983591115436569116350531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73322394076957712744233687 109983591115436569116350531)
    ·
      refine ⟨164975386673154853674525797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109983591115436569116350531 164975386673154853674525797)
      ·
        refine ⟨30932885001216535063973587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164975386673154853674525797 30932885001216535063973587)
        ·
          refine ⟨46399327501824802595960381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30932885001216535063973587 46399327501824802595960381)
          ·
            refine ⟨17399747813184300973485143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46399327501824802595960381 17399747813184300973485143)
            ·
              refine ⟨26099621719776451460227715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17399747813184300973485143 26099621719776451460227715)
              ·
                refine ⟨39149432579664677190341573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26099621719776451460227715 39149432579664677190341573)
                ·
                  refine ⟨7340518608687126973189045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39149432579664677190341573 7340518608687126973189045)
                  ·
                    refine ⟨688173619564418153736473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7340518608687126973189045 688173619564418153736473)
                    ·
                      rfl

theorem cell23_4020640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_4020640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020640 prefixEnd_4020640 := by exact prefixLift 4020640
  have htrace : WordTrace (prefixWord ++ tailWord_4020640) baseStart_4020640 baseEnd_4020640 := by
    simpa [prefixWord, tailWord_4020640, baseEnd_4020640] using wordTrace_append hprefix tailTrace_4020640
  have hstable : (prefixWord ++ tailWord_4020640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020640).length < 2 ^ (prefixWord ++ tailWord_4020640).sum := by decide
  have hdescent : baseEnd_4020640 < baseStart_4020640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020670 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4020670 : Nat := 118140960795 + 4020670 * 2 ^ 59
def prefixEnd_4020670 : Nat := 4983230072969 + 3 ^ 40 * 4020670 * 2
def baseEnd_4020670 : Nat := 688178754370963114611427

theorem tailTrace_4020670 : CollatzResearch.WordTrace tailWord_4020670 prefixEnd_4020670 688178754370963114611427 := by
  unfold tailWord_4020670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18330735292975842576507433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97763921562537827074706309 18330735292975842576507433)
  ·
    refine ⟨13748051469731881932380575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18330735292975842576507433 13748051469731881932380575)
    ·
      refine ⟨20622077204597822898570863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13748051469731881932380575 20622077204597822898570863)
      ·
        refine ⟨30933115806896734347856295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20622077204597822898570863 30933115806896734347856295)
        ·
          refine ⟨46399673710345101521784443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30933115806896734347856295 46399673710345101521784443)
          ·
            refine ⟨69599510565517652282676665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46399673710345101521784443 69599510565517652282676665)
            ·
              refine ⟨52199632924138239212007499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69599510565517652282676665 52199632924138239212007499)
              ·
                refine ⟨78299449386207358818011249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52199632924138239212007499 78299449386207358818011249)
                ·
                  refine ⟨58724587039655519113508437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78299449386207358818011249 58724587039655519113508437)
                  ·
                    refine ⟨688178754370963114611427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58724587039655519113508437 688178754370963114611427)
                    ·
                      rfl

theorem cell23_4020670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4020670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020670 prefixEnd_4020670 := by exact prefixLift 4020670
  have htrace : WordTrace (prefixWord ++ tailWord_4020670) baseStart_4020670 baseEnd_4020670 := by
    simpa [prefixWord, tailWord_4020670, baseEnd_4020670] using wordTrace_append hprefix tailTrace_4020670
  have hstable : (prefixWord ++ tailWord_4020670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020670).length < 2 ^ (prefixWord ++ tailWord_4020670).sum := by decide
  have hdescent : baseEnd_4020670 < baseStart_4020670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020694 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4020694 : Nat := 118140960795 + 4020694 * 2 ^ 59
def prefixEnd_4020694 : Nat := 4983230072969 + 3 ^ 40 * 4020694 * 2
def baseEnd_4020694 : Nat := 2064548586648597249934171

theorem tailTrace_4020694 : CollatzResearch.WordTrace tailWord_4020694 prefixEnd_4020694 2064548586648597249934171 := by
  unfold tailWord_4020694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165422355982487044433321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97764505130479861807288757 9165422355982487044433321)
  ·
    refine ⟨6874066766986865283324991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9165422355982487044433321 6874066766986865283324991)
    ·
      refine ⟨10311100150480297924987487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874066766986865283324991 10311100150480297924987487)
      ·
        refine ⟨15466650225720446887481231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311100150480297924987487 15466650225720446887481231)
        ·
          refine ⟨23199975338580670331221847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15466650225720446887481231 23199975338580670331221847)
          ·
            refine ⟨34799963007871005496832771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23199975338580670331221847 34799963007871005496832771)
            ·
              refine ⟨52199944511806508245249157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34799963007871005496832771 52199944511806508245249157)
              ·
                refine ⟨9787489595963720295984217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52199944511806508245249157 9787489595963720295984217)
                ·
                  refine ⟨7340617196972790221988163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9787489595963720295984217 7340617196972790221988163)
                  ·
                    refine ⟨11010925795459185332982245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7340617196972790221988163 11010925795459185332982245)
                    ·
                      refine ⟨2064548586648597249934171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11010925795459185332982245 2064548586648597249934171)
                      ·
                        rfl

theorem cell23_4020694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4020694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020694 prefixEnd_4020694 := by exact prefixLift 4020694
  have htrace : WordTrace (prefixWord ++ tailWord_4020694) baseStart_4020694 baseEnd_4020694 := by
    simpa [prefixWord, tailWord_4020694, baseEnd_4020694] using wordTrace_append hprefix tailTrace_4020694
  have hstable : (prefixWord ++ tailWord_4020694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020694).length < 2 ^ (prefixWord ++ tailWord_4020694).sum := by decide
  have hdescent : baseEnd_4020694 < baseStart_4020694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020697 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_4020697 : Nat := 118140960795 + 4020697 * 2 ^ 59
def prefixEnd_4020697 : Nat := 4983230072969 + 3 ^ 40 * 4020697 * 2
def baseEnd_4020697 : Nat := 2064550127090560738196657

theorem tailTrace_4020697 : CollatzResearch.WordTrace tailWord_4020697 prefixEnd_4020697 2064550127090560738196657 := by
  unfold tailWord_4020697
  simp only [CollatzResearch.WordTrace]
  refine ⟨146646867114708924223292345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97764578076472616148861563 146646867114708924223292345)
  ·
    refine ⟨109985150336031693167469259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146646867114708924223292345 109985150336031693167469259)
    ·
      refine ⟨164977725504047539751203889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109985150336031693167469259 164977725504047539751203889)
      ·
        refine ⟨123733294128035654813402917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164977725504047539751203889 123733294128035654813402917)
        ·
          refine ⟨23199992649006685277513047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123733294128035654813402917 23199992649006685277513047)
          ·
            refine ⟨34799988973510027916269571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23199992649006685277513047 34799988973510027916269571)
            ·
              refine ⟨52199983460265041874404357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34799988973510027916269571 52199983460265041874404357)
              ·
                refine ⟨9787496898799695351450817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52199983460265041874404357 9787496898799695351450817)
                ·
                  refine ⟨7340622674099771513588113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9787496898799695351450817 7340622674099771513588113)
                  ·
                    refine ⟨5505467005574828635191085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7340622674099771513588113 5505467005574828635191085)
                    ·
                      refine ⟨2064550127090560738196657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5505467005574828635191085 2064550127090560738196657)
                      ·
                        rfl

theorem cell23_4020697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_4020697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020697 prefixEnd_4020697 := by exact prefixLift 4020697
  have htrace : WordTrace (prefixWord ++ tailWord_4020697) baseStart_4020697 baseEnd_4020697 := by
    simpa [prefixWord, tailWord_4020697, baseEnd_4020697] using wordTrace_append hprefix tailTrace_4020697
  have hstable : (prefixWord ++ tailWord_4020697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020697).length < 2 ^ (prefixWord ++ tailWord_4020697).sum := by decide
  have hdescent : baseEnd_4020697 < baseStart_4020697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020704 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 1, 4]
def baseStart_4020704 : Nat := 118140960795 + 4020704 * 2 ^ 59
def prefixEnd_4020704 : Nat := 4983230072969 + 3 ^ 40 * 4020704 * 2
def baseEnd_4020704 : Nat := 688184573818380736936375

theorem tailTrace_4020704 : CollatzResearch.WordTrace tailWord_4020704 prefixEnd_4020704 688184573818380736936375 := by
  unfold tailWord_4020704
  simp only [CollatzResearch.WordTrace]
  refine ⟨73323561212841782209398583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97764748283789042945864777 73323561212841782209398583)
  ·
    refine ⟨109985341819262673314097875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73323561212841782209398583 109985341819262673314097875)
    ·
      refine ⟨164978012728894009971146813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109985341819262673314097875 164978012728894009971146813)
      ·
        refine ⟨61866754773335253739180055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164978012728894009971146813 61866754773335253739180055)
        ·
          refine ⟨92800132160002880608770083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61866754773335253739180055 92800132160002880608770083)
          ·
            refine ⟨139200198240004320913155125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92800132160002880608770083 139200198240004320913155125)
            ·
              refine ⟨13050018585000405085608293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139200198240004320913155125 13050018585000405085608293)
              ·
                refine ⟨2446878484687575953551555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13050018585000405085608293 2446878484687575953551555)
                ·
                  refine ⟨3670317727031363930327333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446878484687575953551555 3670317727031363930327333)
                  ·
                    refine ⟨688184573818380736936375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670317727031363930327333 688184573818380736936375)
                    ·
                      rfl

theorem cell23_4020704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 4].length) (baseStart_4020704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020704 prefixEnd_4020704 := by exact prefixLift 4020704
  have htrace : WordTrace (prefixWord ++ tailWord_4020704) baseStart_4020704 baseEnd_4020704 := by
    simpa [prefixWord, tailWord_4020704, baseEnd_4020704] using wordTrace_append hprefix tailTrace_4020704
  have hstable : (prefixWord ++ tailWord_4020704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020704).length < 2 ^ (prefixWord ++ tailWord_4020704).sum := by decide
  have hdescent : baseEnd_4020704 < baseStart_4020704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020807 : List Nat := [1, 1, 4, 1, 4, 3, 9]
def baseStart_4020807 : Nat := 118140960795 + 4020807 * 2 ^ 59
def prefixEnd_4020807 : Nat := 4983230072969 + 3 ^ 40 * 4020807 * 2
def baseEnd_4020807 : Nat := 25488970493364880343471

theorem tailTrace_4020807 : CollatzResearch.WordTrace tailWord_4020807 prefixEnd_4020807 25488970493364880343471 := by
  unfold tailWord_4020807
  simp only [CollatzResearch.WordTrace]
  refine ⟨146650879144310413009796675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97767252762873608673197783 146650879144310413009796675)
  ·
    refine ⟨219976318716465619514695013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146650879144310413009796675 219976318716465619514695013)
    ·
      refine ⟨41245559759337303659005315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219976318716465619514695013 41245559759337303659005315)
      ·
        refine ⟨61868339639005955488507973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41245559759337303659005315 61868339639005955488507973)
        ·
          refine ⟨11600313682313616654095245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61868339639005955488507973 11600313682313616654095245)
          ·
            refine ⟨4350117630867606245285717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11600313682313616654095245 4350117630867606245285717)
            ·
              refine ⟨25488970493364880343471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4350117630867606245285717 25488970493364880343471)
              ·
                rfl

theorem cell23_4020807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 9].length) (baseStart_4020807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020807 prefixEnd_4020807 := by exact prefixLift 4020807
  have htrace : WordTrace (prefixWord ++ tailWord_4020807) baseStart_4020807 baseEnd_4020807 := by
    simpa [prefixWord, tailWord_4020807, baseEnd_4020807] using wordTrace_append hprefix tailTrace_4020807
  have hstable : (prefixWord ++ tailWord_4020807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020807).length < 2 ^ (prefixWord ++ tailWord_4020807).sum := by decide
  have hdescent : baseEnd_4020807 < baseStart_4020807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020868 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_4020868 : Nat := 118140960795 + 4020868 * 2 ^ 59
def prefixEnd_4020868 : Nat := 4983230072969 + 3 ^ 40 * 4020868 * 2
def baseEnd_4020868 : Nat := 2064637932282479569158371

theorem tailTrace_4020868 : CollatzResearch.WordTrace tailWord_4020868 prefixEnd_4020868 2064637932282479569158371 := by
  unfold tailWord_4020868
  simp only [CollatzResearch.WordTrace]
  refine ⟨73326551998544710213883629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97768735998059613618511505 73326551998544710213883629)
  ·
    refine ⟨27497456999454266330206361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73326551998544710213883629 27497456999454266330206361)
    ·
      refine ⟨20623092749590699747654771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27497456999454266330206361 20623092749590699747654771)
      ·
        refine ⟨30934639124386049621482157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20623092749590699747654771 30934639124386049621482157)
        ·
          refine ⟨11600489671644768608055809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30934639124386049621482157 11600489671644768608055809)
          ·
            refine ⟨8700367253733576456041857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11600489671644768608055809 8700367253733576456041857)
            ·
              refine ⟨6525275440300182342031393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700367253733576456041857 6525275440300182342031393)
              ·
                refine ⟨4893956580225136756523545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525275440300182342031393 4893956580225136756523545)
                ·
                  refine ⟨3670467435168852567392659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4893956580225136756523545 3670467435168852567392659)
                  ·
                    refine ⟨5505701152753278851088989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3670467435168852567392659 5505701152753278851088989)
                    ·
                      refine ⟨2064637932282479569158371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5505701152753278851088989 2064637932282479569158371)
                      ·
                        rfl

theorem cell23_4020868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_4020868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020868 prefixEnd_4020868 := by exact prefixLift 4020868
  have htrace : WordTrace (prefixWord ++ tailWord_4020868) baseStart_4020868 baseEnd_4020868 := by
    simpa [prefixWord, tailWord_4020868, baseEnd_4020868] using wordTrace_append hprefix tailTrace_4020868
  have hstable : (prefixWord ++ tailWord_4020868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020868).length < 2 ^ (prefixWord ++ tailWord_4020868).sum := by decide
  have hdescent : baseEnd_4020868 < baseStart_4020868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020884 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_4020884 : Nat := 118140960795 + 4020884 * 2 ^ 59
def prefixEnd_4020884 : Nat := 4983230072969 + 3 ^ 40 * 4020884 * 2
def baseEnd_4020884 : Nat := 688215382657650502186099

theorem tailTrace_4020884 : CollatzResearch.WordTrace tailWord_4020884 prefixEnd_4020884 688215382657650502186099 := by
  unfold tailWord_4020884
  simp only [CollatzResearch.WordTrace]
  refine ⟨73326843782515727580174853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97769125043354303440233137 73326843782515727580174853)
  ·
    refine ⟨13748783209221698921282785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73326843782515727580174853 13748783209221698921282785)
    ·
      refine ⟨10311587406916274190962089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13748783209221698921282785 10311587406916274190962089)
      ·
        refine ⟨7733690555187205643221567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10311587406916274190962089 7733690555187205643221567)
        ·
          refine ⟨11600535832780808464832351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733690555187205643221567 11600535832780808464832351)
          ·
            refine ⟨17400803749171212697248527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600535832780808464832351 17400803749171212697248527)
            ·
              refine ⟨26101205623756819045872791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17400803749171212697248527 26101205623756819045872791)
              ·
                refine ⟨39151808435635228568809187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26101205623756819045872791 39151808435635228568809187)
                ·
                  refine ⟨58727712653452842853213781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39151808435635228568809187 58727712653452842853213781)
                  ·
                    refine ⟨688215382657650502186099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58727712653452842853213781 688215382657650502186099)
                    ·
                      rfl

theorem cell23_4020884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_4020884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020884 prefixEnd_4020884 := by exact prefixLift 4020884
  have htrace : WordTrace (prefixWord ++ tailWord_4020884) baseStart_4020884 baseEnd_4020884 := by
    simpa [prefixWord, tailWord_4020884, baseEnd_4020884] using wordTrace_append hprefix tailTrace_4020884
  have hstable : (prefixWord ++ tailWord_4020884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020884).length < 2 ^ (prefixWord ++ tailWord_4020884).sum := by decide
  have hdescent : baseEnd_4020884 < baseStart_4020884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020924 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_4020924 : Nat := 118140960795 + 4020924 * 2 ^ 59
def prefixEnd_4020924 : Nat := 4983230072969 + 3 ^ 40 * 4020924 * 2
def baseEnd_4020924 : Nat := 2064666687199131350058113

theorem tailTrace_4020924 : CollatzResearch.WordTrace tailWord_4020924 prefixEnd_4020924 2064666687199131350058113 := by
  unfold tailWord_4020924
  simp only [CollatzResearch.WordTrace]
  refine ⟨73327573242443270995902913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97770097656591027994537217 73327573242443270995902913)
  ·
    refine ⟨54995679931832453246927185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73327573242443270995902913 54995679931832453246927185)
    ·
      refine ⟨41246759948874339935195389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54995679931832453246927185 41246759948874339935195389)
      ·
        refine ⟨15467534980827877475698271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41246759948874339935195389 15467534980827877475698271)
        ·
          refine ⟨23201302471241816213547407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15467534980827877475698271 23201302471241816213547407)
          ·
            refine ⟨34801953706862724320321111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23201302471241816213547407 34801953706862724320321111)
            ·
              refine ⟨52202930560294086480481667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34801953706862724320321111 52202930560294086480481667)
              ·
                refine ⟨78304395840441129720722501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52202930560294086480481667 78304395840441129720722501)
                ·
                  refine ⟨14682074220082711822635469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78304395840441129720722501 14682074220082711822635469)
                  ·
                    refine ⟨5505777832531016933488301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14682074220082711822635469 5505777832531016933488301)
                    ·
                      refine ⟨2064666687199131350058113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5505777832531016933488301 2064666687199131350058113)
                      ·
                        rfl

theorem cell23_4020924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_4020924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020924 prefixEnd_4020924 := by exact prefixLift 4020924
  have htrace : WordTrace (prefixWord ++ tailWord_4020924) baseStart_4020924 baseEnd_4020924 := by
    simpa [prefixWord, tailWord_4020924, baseEnd_4020924] using wordTrace_append hprefix tailTrace_4020924
  have hstable : (prefixWord ++ tailWord_4020924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020924).length < 2 ^ (prefixWord ++ tailWord_4020924).sum := by decide
  have hdescent : baseEnd_4020924 < baseStart_4020924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020925 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_4020925 : Nat := 118140960795 + 4020925 * 2 ^ 59
def prefixEnd_4020925 : Nat := 4983230072969 + 3 ^ 40 * 4020925 * 2
def baseEnd_4020925 : Nat := 2064667200679785846145609

theorem tailTrace_4020925 : CollatzResearch.WordTrace tailWord_4020925 prefixEnd_4020925 2064667200679785846145609 := by
  unfold tailWord_4020925
  simp only [CollatzResearch.WordTrace]
  refine ⟨146655182957882919162592229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97770121971921946108394819 146655182957882919162592229)
  ·
    refine ⟨27497846804603047342986043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146655182957882919162592229 27497846804603047342986043)
    ·
      refine ⟨41246770206904571014479065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27497846804603047342986043 41246770206904571014479065)
      ·
        refine ⟨30935077655178428260859299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41246770206904571014479065 30935077655178428260859299)
        ·
          refine ⟨46402616482767642391288949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30935077655178428260859299 46402616482767642391288949)
          ·
            refine ⟨4350245295259466474183339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46402616482767642391288949 4350245295259466474183339)
            ·
              refine ⟨6525367942889199711275009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350245295259466474183339 6525367942889199711275009)
              ·
                refine ⟨4894025957166899783456257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525367942889199711275009 4894025957166899783456257)
                ·
                  refine ⟨3670519467875174837592193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894025957166899783456257 3670519467875174837592193)
                  ·
                    refine ⟨2752889600906381128194145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3670519467875174837592193 2752889600906381128194145)
                    ·
                      refine ⟨2064667200679785846145609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2752889600906381128194145 2064667200679785846145609)
                      ·
                        rfl

theorem cell23_4020925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_4020925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020925 prefixEnd_4020925 := by exact prefixLift 4020925
  have htrace : WordTrace (prefixWord ++ tailWord_4020925) baseStart_4020925 baseEnd_4020925 := by
    simpa [prefixWord, tailWord_4020925, baseEnd_4020925] using wordTrace_append hprefix tailTrace_4020925
  have hstable : (prefixWord ++ tailWord_4020925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020925).length < 2 ^ (prefixWord ++ tailWord_4020925).sum := by decide
  have hdescent : baseEnd_4020925 < baseStart_4020925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020964 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_4020964 : Nat := 118140960795 + 4020964 * 2 ^ 59
def prefixEnd_4020964 : Nat := 4983230072969 + 3 ^ 40 * 4020964 * 2
def baseEnd_4020964 : Nat := 2064687226425311193557929

theorem tailTrace_4020964 : CollatzResearch.WordTrace tailWord_4020964 prefixEnd_4020964 2064687226425311193557929 := by
  unfold tailWord_4020964
  simp only [CollatzResearch.WordTrace]
  refine ⟨73328302702370814411630973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97771070269827752548841297 73328302702370814411630973)
  ·
    refine ⟨27498113513389055404361615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73328302702370814411630973 27498113513389055404361615)
    ·
      refine ⟨41247170270083583106542423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27498113513389055404361615 41247170270083583106542423)
      ·
        refine ⟨61870755405125374659813635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41247170270083583106542423 61870755405125374659813635)
        ·
          refine ⟨92806133107688061989720453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61870755405125374659813635 92806133107688061989720453)
          ·
            refine ⟨17401149957691511623072585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92806133107688061989720453 17401149957691511623072585)
            ·
              refine ⟨13050862468268633717304439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17401149957691511623072585 13050862468268633717304439)
              ·
                refine ⟨19576293702402950575956659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050862468268633717304439 19576293702402950575956659)
                ·
                  refine ⟨29364440553604425863934989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19576293702402950575956659 29364440553604425863934989)
                  ·
                    refine ⟨11011665207601659698975621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29364440553604425863934989 11011665207601659698975621)
                    ·
                      refine ⟨2064687226425311193557929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11011665207601659698975621 2064687226425311193557929)
                      ·
                        rfl

theorem cell23_4020964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_4020964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4020964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4020964 prefixEnd_4020964 := by exact prefixLift 4020964
  have htrace : WordTrace (prefixWord ++ tailWord_4020964) baseStart_4020964 baseEnd_4020964 := by
    simpa [prefixWord, tailWord_4020964, baseEnd_4020964] using wordTrace_append hprefix tailTrace_4020964
  have hstable : (prefixWord ++ tailWord_4020964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020964).length < 2 ^ (prefixWord ++ tailWord_4020964).sum := by decide
  have hdescent : baseEnd_4020964 < baseStart_4020964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021038 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_4021038 : Nat := 118140960795 + 4021038 * 2 ^ 59
def prefixEnd_4021038 : Nat := 4983230072969 + 3 ^ 40 * 4021038 * 2
def baseEnd_4021038 : Nat := 229413913777082656003621

theorem tailTrace_4021038 : CollatzResearch.WordTrace tailWord_4021038 prefixEnd_4021038 229413913777082656003621 := by
  unfold tailWord_4021038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332413050809192432681971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97772869604315692974303845 18332413050809192432681971)
  ·
    refine ⟨27498619576213788649022957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18332413050809192432681971 27498619576213788649022957)
    ·
      refine ⟨10311982341080170743383609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27498619576213788649022957 10311982341080170743383609)
      ·
        refine ⟨7733986755810128057537707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10311982341080170743383609 7733986755810128057537707)
        ·
          refine ⟨11600980133715192086306561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733986755810128057537707 11600980133715192086306561)
          ·
            refine ⟨8700735100286394064729921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11600980133715192086306561 8700735100286394064729921)
            ·
              refine ⟨6525551325214795548547441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700735100286394064729921 6525551325214795548547441)
              ·
                refine ⟨4894163493911096661410581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525551325214795548547441 4894163493911096661410581)
                ·
                  refine ⟨229413913777082656003621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4894163493911096661410581 229413913777082656003621)
                  ·
                    rfl

theorem cell23_4021038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_4021038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021038 prefixEnd_4021038 := by exact prefixLift 4021038
  have htrace : WordTrace (prefixWord ++ tailWord_4021038) baseStart_4021038 baseEnd_4021038 := by
    simpa [prefixWord, tailWord_4021038, baseEnd_4021038] using wordTrace_append hprefix tailTrace_4021038
  have hstable : (prefixWord ++ tailWord_4021038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021038).length < 2 ^ (prefixWord ++ tailWord_4021038).sum := by decide
  have hdescent : baseEnd_4021038 < baseStart_4021038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021088 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 5, 2, 2]
def baseStart_4021088 : Nat := 118140960795 + 4021088 * 2 ^ 59
def prefixEnd_4021088 : Nat := 4983230072969 + 3 ^ 40 * 4021088 * 2
def baseEnd_4021088 : Nat := 2064750898026468708407359

theorem tailTrace_4021088 : CollatzResearch.WordTrace tailWord_4021088 prefixEnd_4021088 2064750898026468708407359 := by
  unfold tailWord_4021088
  simp only [CollatzResearch.WordTrace]
  refine ⟨73330564028146199000387959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97774085370861598667183945 73330564028146199000387959)
  ·
    refine ⟨109995846042219298500581939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73330564028146199000387959 109995846042219298500581939)
    ·
      refine ⟨164993769063328947750872909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109995846042219298500581939 164993769063328947750872909)
      ·
        refine ⟨61872663398748355406577341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164993769063328947750872909 61872663398748355406577341)
        ·
          refine ⟨23202248774530633277466503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61872663398748355406577341 23202248774530633277466503)
          ·
            refine ⟨34803373161795949916199755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23202248774530633277466503 34803373161795949916199755)
            ·
              refine ⟨52205059742693924874299633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34803373161795949916199755 52205059742693924874299633)
              ·
                refine ⟨39153794807020443655724725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52205059742693924874299633 39153794807020443655724725)
                ·
                  refine ⟨3670668263158166592724193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39153794807020443655724725 3670668263158166592724193)
                  ·
                    refine ⟨2753001197368624944543145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3670668263158166592724193 2753001197368624944543145)
                    ·
                      refine ⟨2064750898026468708407359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753001197368624944543145 2064750898026468708407359)
                      ·
                        rfl

theorem cell23_4021088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_4021088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021088 prefixEnd_4021088 := by exact prefixLift 4021088
  have htrace : WordTrace (prefixWord ++ tailWord_4021088) baseStart_4021088 baseEnd_4021088 := by
    simpa [prefixWord, tailWord_4021088, baseEnd_4021088] using wordTrace_append hprefix tailTrace_4021088
  have hstable : (prefixWord ++ tailWord_4021088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021088).length < 2 ^ (prefixWord ++ tailWord_4021088).sum := by decide
  have hdescent : baseEnd_4021088 < baseStart_4021088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021105 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 3, 2, 2]
def baseStart_4021105 : Nat := 118140960795 + 4021105 * 2 ^ 59
def prefixEnd_4021105 : Nat := 4983230072969 + 3 ^ 40 * 4021105 * 2
def baseEnd_4021105 : Nat := 2064759627197595141894781

theorem tailTrace_4021105 : CollatzResearch.WordTrace tailWord_4021105 prefixEnd_4021105 2064759627197595141894781 := by
  unfold tailWord_4021105
  simp only [CollatzResearch.WordTrace]
  refine ⟨146661748097230809904144769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97774498731487206602763179 146661748097230809904144769)
  ·
    refine ⟨109996311072923107428108577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146661748097230809904144769 109996311072923107428108577)
    ·
      refine ⟨82497233304692330571081433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109996311072923107428108577 82497233304692330571081433)
      ·
        refine ⟨61872924978519247928311075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82497233304692330571081433 61872924978519247928311075)
        ·
          refine ⟨92809387467778871892466613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61872924978519247928311075 92809387467778871892466613)
          ·
            refine ⟨8700880075104269239918745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92809387467778871892466613 8700880075104269239918745)
            ·
              refine ⟨6525660056328201929939059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700880075104269239918745 6525660056328201929939059)
              ·
                refine ⟨9788490084492302894908589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525660056328201929939059 9788490084492302894908589)
                ·
                  refine ⟨3670683781684613585590721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9788490084492302894908589 3670683781684613585590721)
                  ·
                    refine ⟨2753012836263460189193041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3670683781684613585590721 2753012836263460189193041)
                    ·
                      refine ⟨2064759627197595141894781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753012836263460189193041 2064759627197595141894781)
                      ·
                        rfl

theorem cell23_4021105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_4021105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021105 prefixEnd_4021105 := by exact prefixLift 4021105
  have htrace : WordTrace (prefixWord ++ tailWord_4021105) baseStart_4021105 baseEnd_4021105 := by
    simpa [prefixWord, tailWord_4021105, baseEnd_4021105] using wordTrace_append hprefix tailTrace_4021105
  have hstable : (prefixWord ++ tailWord_4021105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021105).length < 2 ^ (prefixWord ++ tailWord_4021105).sum := by decide
  have hdescent : baseEnd_4021105 < baseStart_4021105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021128 : List Nat := [2, 1, 3, 3, 2, 3, 2, 7]
def baseStart_4021128 : Nat := 118140960795 + 4021128 * 2 ^ 59
def prefixEnd_4021128 : Nat := 4983230072969 + 3 ^ 40 * 4021128 * 2
def baseEnd_4021128 : Nat := 76473016194542538959525

theorem tailTrace_4021128 : CollatzResearch.WordTrace tailWord_4021128 prefixEnd_4021128 76473016194542538959525 := by
  unfold tailWord_4021128
  simp only [CollatzResearch.WordTrace]
  refine ⟨73331293488073742416116019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97775057984098323221488025 73331293488073742416116019)
  ·
    refine ⟨109996940232110613624174029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73331293488073742416116019 109996940232110613624174029)
    ·
      refine ⟨41248852587041480109065261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109996940232110613624174029 41248852587041480109065261)
      ·
        refine ⟨15468319720140555040899473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41248852587041480109065261 15468319720140555040899473)
        ·
          refine ⟨11601239790105416280674605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15468319720140555040899473 11601239790105416280674605)
          ·
            refine ⟨4350464921289531105252977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11601239790105416280674605 4350464921289531105252977)
            ·
              refine ⟨3262848690967148328939733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350464921289531105252977 3262848690967148328939733)
              ·
                refine ⟨76473016194542538959525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3262848690967148328939733 76473016194542538959525)
                ·
                  rfl

theorem cell23_4021128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 7].length) (baseStart_4021128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021128 prefixEnd_4021128 := by exact prefixLift 4021128
  have htrace : WordTrace (prefixWord ++ tailWord_4021128) baseStart_4021128 baseEnd_4021128 := by
    simpa [prefixWord, tailWord_4021128, baseEnd_4021128] using wordTrace_append hprefix tailTrace_4021128
  have hstable : (prefixWord ++ tailWord_4021128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021128).length < 2 ^ (prefixWord ++ tailWord_4021128).sum := by decide
  have hdescent : baseEnd_4021128 < baseStart_4021128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021142 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4021142 : Nat := 118140960795 + 4021142 * 2 ^ 59
def prefixEnd_4021142 : Nat := 4983230072969 + 3 ^ 40 * 4021142 * 2
def baseEnd_4021142 : Nat := 2064778625981811497132111

theorem tailTrace_4021142 : CollatzResearch.WordTrace tailWord_4021142 prefixEnd_4021142 2064778625981811497132111 := by
  unfold tailWord_4021142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166443599881047826452605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97775398398731176815494453 9166443599881047826452605)
  ·
    refine ⟨3437416349955392934919727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9166443599881047826452605 3437416349955392934919727)
    ·
      refine ⟨5156124524933089402379591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437416349955392934919727 5156124524933089402379591)
      ·
        refine ⟨7734186787399634103569387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156124524933089402379591 7734186787399634103569387)
        ·
          refine ⟨11601280181099451155354081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734186787399634103569387 11601280181099451155354081)
          ·
            refine ⟨8700960135824588366515561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11601280181099451155354081 8700960135824588366515561)
            ·
              refine ⟨6525720101868441274886671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700960135824588366515561 6525720101868441274886671)
              ·
                refine ⟨9788580152802661912330007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525720101868441274886671 9788580152802661912330007)
                ·
                  refine ⟨14682870229203992868495011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9788580152802661912330007 14682870229203992868495011)
                  ·
                    refine ⟨22024305343805989302742517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14682870229203992868495011 22024305343805989302742517)
                    ·
                      refine ⟨2064778625981811497132111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22024305343805989302742517 2064778625981811497132111)
                      ·
                        rfl

theorem cell23_4021142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4021142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021142 prefixEnd_4021142 := by exact prefixLift 4021142
  have htrace : WordTrace (prefixWord ++ tailWord_4021142) baseStart_4021142 baseEnd_4021142 := by
    simpa [prefixWord, tailWord_4021142, baseEnd_4021142] using wordTrace_append hprefix tailTrace_4021142
  have hstable : (prefixWord ++ tailWord_4021142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021142).length < 2 ^ (prefixWord ++ tailWord_4021142).sum := by decide
  have hdescent : baseEnd_4021142 < baseStart_4021142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021178 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2]
def baseStart_4021178 : Nat := 118140960795 + 4021178 * 2 ^ 59
def prefixEnd_4021178 : Nat := 4983230072969 + 3 ^ 40 * 4021178 * 2
def baseEnd_4021178 : Nat := 2064797111285373356281945

theorem tailTrace_4021178 : CollatzResearch.WordTrace tailWord_4021178 prefixEnd_4021178 2064797111285373356281945 := by
  unfold tailWord_4021178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36666102656491585842888047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97776273750644228914368125 36666102656491585842888047)
  ·
    refine ⟨54999153984737378764332071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36666102656491585842888047 54999153984737378764332071)
    ·
      refine ⟨82498730977106068146498107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54999153984737378764332071 82498730977106068146498107)
      ·
        refine ⟨123748096465659102219747161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82498730977106068146498107 123748096465659102219747161)
        ·
          refine ⟨92811072349244326664810371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123748096465659102219747161 92811072349244326664810371)
          ·
            refine ⟨139216608523866489997215557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92811072349244326664810371 139216608523866489997215557)
            ·
              refine ⟨26103114098224966874477917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139216608523866489997215557 26103114098224966874477917)
              ·
                refine ⟨9788667786834362577929219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26103114098224966874477917 9788667786834362577929219)
                ·
                  refine ⟨14683001680251543866893829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9788667786834362577929219 14683001680251543866893829)
                  ·
                    refine ⟨2753062815047164475042593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14683001680251543866893829 2753062815047164475042593)
                    ·
                      refine ⟨2064797111285373356281945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753062815047164475042593 2064797111285373356281945)
                      ·
                        rfl

theorem cell23_4021178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_4021178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021178 prefixEnd_4021178 := by exact prefixLift 4021178
  have htrace : WordTrace (prefixWord ++ tailWord_4021178) baseStart_4021178 baseEnd_4021178 := by
    simpa [prefixWord, tailWord_4021178, baseEnd_4021178] using wordTrace_append hprefix tailTrace_4021178
  have hstable : (prefixWord ++ tailWord_4021178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021178).length < 2 ^ (prefixWord ++ tailWord_4021178).sum := by decide
  have hdescent : baseEnd_4021178 < baseStart_4021178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021362 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4021362 : Nat := 118140960795 + 4021362 * 2 ^ 59
def prefixEnd_4021362 : Nat := 4983230072969 + 3 ^ 40 * 4021362 * 2
def baseEnd_4021362 : Nat := 2064891591725800636381099

theorem tailTrace_4021362 : CollatzResearch.WordTrace tailWord_4021362 prefixEnd_4021362 2064891591725800636381099 := by
  unfold tailWord_4021362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36667780414324935699062585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97780747771533161864166893 36667780414324935699062585)
  ·
    refine ⟨27500835310743701774296939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36667780414324935699062585 27500835310743701774296939)
    ·
      refine ⟨41251252966115552661445409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500835310743701774296939 41251252966115552661445409)
      ·
        refine ⟨30938439724586664496084057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41251252966115552661445409 30938439724586664496084057)
        ·
          refine ⟨23203829793439998372063043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30938439724586664496084057 23203829793439998372063043)
          ·
            refine ⟨34805744690159997558094565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23203829793439998372063043 34805744690159997558094565)
            ·
              refine ⟨6526077129404999542142731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34805744690159997558094565 6526077129404999542142731)
              ·
                refine ⟨9789115694107499313214097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526077129404999542142731 9789115694107499313214097)
                ·
                  refine ⟨7341836770580624484910573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9789115694107499313214097 7341836770580624484910573)
                  ·
                    refine ⟨2753188788967734181841465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7341836770580624484910573 2753188788967734181841465)
                    ·
                      refine ⟨2064891591725800636381099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753188788967734181841465 2064891591725800636381099)
                      ·
                        rfl

theorem cell23_4021362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4021362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021362 prefixEnd_4021362 := by exact prefixLift 4021362
  have htrace : WordTrace (prefixWord ++ tailWord_4021362) baseStart_4021362 baseEnd_4021362 := by
    simpa [prefixWord, tailWord_4021362, baseEnd_4021362] using wordTrace_append hprefix tailTrace_4021362
  have hstable : (prefixWord ++ tailWord_4021362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021362).length < 2 ^ (prefixWord ++ tailWord_4021362).sum := by decide
  have hdescent : baseEnd_4021362 < baseStart_4021362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021368 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 6, 4]
def baseStart_4021368 : Nat := 118140960795 + 4021368 * 2 ^ 59
def prefixEnd_4021368 : Nat := 4983230072969 + 3 ^ 40 * 4021368 * 2
def baseEnd_4021368 : Nat := 688298224203242537635357

theorem tailTrace_4021368 : CollatzResearch.WordTrace tailWord_4021368 prefixEnd_4021368 688298224203242537635357 := by
  unfold tailWord_4021368
  simp only [CollatzResearch.WordTrace]
  refine ⟨73335670247639002910484379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97780893663518670547312505 73335670247639002910484379)
  ·
    refine ⟨110003505371458504365726569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73335670247639002910484379 110003505371458504365726569)
    ·
      refine ⟨82502629028593878274294927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110003505371458504365726569 82502629028593878274294927)
      ·
        refine ⟨123753943542890817411442391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82502629028593878274294927 123753943542890817411442391)
        ·
          refine ⟨185630915314336226117163587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123753943542890817411442391 185630915314336226117163587)
          ·
            refine ⟨278446372971504339175745381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185630915314336226117163587 278446372971504339175745381)
            ·
              refine ⟨52208694932157063595452259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278446372971504339175745381 52208694932157063595452259)
              ·
                refine ⟨78313042398235595393178389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52208694932157063595452259 78313042398235595393178389)
                ·
                  refine ⟨3670923862417293534055237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78313042398235595393178389 3670923862417293534055237)
                  ·
                    refine ⟨688298224203242537635357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670923862417293534055237 688298224203242537635357)
                    ·
                      rfl

theorem cell23_4021368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_4021368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021368 prefixEnd_4021368 := by exact prefixLift 4021368
  have htrace : WordTrace (prefixWord ++ tailWord_4021368) baseStart_4021368 baseEnd_4021368 := by
    simpa [prefixWord, tailWord_4021368, baseEnd_4021368] using wordTrace_append hprefix tailTrace_4021368
  have hstable : (prefixWord ++ tailWord_4021368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021368).length < 2 ^ (prefixWord ++ tailWord_4021368).sum := by decide
  have hdescent : baseEnd_4021368 < baseStart_4021368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021381 : List Nat := [1, 3, 1, 1, 17]
def baseStart_4021381 : Nat := 118140960795 + 4021381 * 2 ^ 59
def prefixEnd_4021381 : Nat := 4983230072969 + 3 ^ 40 * 4021381 * 2
def baseEnd_4021381 : Nat := 2832512136979747684559

theorem tailTrace_4021381 : CollatzResearch.WordTrace tailWord_4021381 prefixEnd_4021381 2832512136979747684559 := by
  unfold tailWord_4021381
  simp only [CollatzResearch.WordTrace]
  refine ⟨146671814644230909041191997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97781209762820606027461331 146671814644230909041191997)
  ·
    refine ⟨55001930491586590890446999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146671814644230909041191997 55001930491586590890446999)
    ·
      refine ⟨82502895737379886335670499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55001930491586590890446999 82502895737379886335670499)
      ·
        refine ⟨123754343606069829503505749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82502895737379886335670499 123754343606069829503505749)
        ·
          refine ⟨2832512136979747684559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 123754343606069829503505749 2832512136979747684559)
          ·
            rfl

theorem cell23_4021381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 17].length) (baseStart_4021381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021381 prefixEnd_4021381 := by exact prefixLift 4021381
  have htrace : WordTrace (prefixWord ++ tailWord_4021381) baseStart_4021381 baseEnd_4021381 := by
    simpa [prefixWord, tailWord_4021381, baseEnd_4021381] using wordTrace_append hprefix tailTrace_4021381
  have hstable : (prefixWord ++ tailWord_4021381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021381).length < 2 ^ (prefixWord ++ tailWord_4021381).sum := by decide
  have hdescent : baseEnd_4021381 < baseStart_4021381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021385 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 2, 4]
def baseStart_4021385 : Nat := 118140960795 + 4021385 * 2 ^ 59
def prefixEnd_4021385 : Nat := 4983230072969 + 3 ^ 40 * 4021385 * 2
def baseEnd_4021385 : Nat := 688301133926951348797831

theorem tailTrace_4021385 : CollatzResearch.WordTrace tailWord_4021385 prefixEnd_4021385 688301133926951348797831 := by
  unfold tailWord_4021385
  simp only [CollatzResearch.WordTrace]
  refine ⟨146671960536216417724337609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97781307024144278482891739 146671960536216417724337609)
  ·
    refine ⟨110003970402162313293253207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146671960536216417724337609 110003970402162313293253207)
    ·
      refine ⟨165005955603243469939879811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110003970402162313293253207 165005955603243469939879811)
      ·
        refine ⟨247508933404865204909819717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165005955603243469939879811 247508933404865204909819717)
        ·
          refine ⟨46407925013412225920591197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247508933404865204909819717 46407925013412225920591197)
          ·
            refine ⟨17402971880029584720221699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46407925013412225920591197 17402971880029584720221699)
            ·
              refine ⟨26104457820044377080332549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17402971880029584720221699 26104457820044377080332549)
              ·
                refine ⟨4894585841258320702562353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26104457820044377080332549 4894585841258320702562353)
                ·
                  refine ⟨3670939380943740526921765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894585841258320702562353 3670939380943740526921765)
                  ·
                    refine ⟨688301133926951348797831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670939380943740526921765 688301133926951348797831)
                    ·
                      rfl

theorem cell23_4021385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_4021385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021385 prefixEnd_4021385 := by exact prefixLift 4021385
  have htrace : WordTrace (prefixWord ++ tailWord_4021385) baseStart_4021385 baseEnd_4021385 := by
    simpa [prefixWord, tailWord_4021385, baseEnd_4021385] using wordTrace_append hprefix tailTrace_4021385
  have hstable : (prefixWord ++ tailWord_4021385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021385).length < 2 ^ (prefixWord ++ tailWord_4021385).sum := by decide
  have hdescent : baseEnd_4021385 < baseStart_4021385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021402 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_4021402 : Nat := 118140960795 + 4021402 * 2 ^ 59
def prefixEnd_4021402 : Nat := 4983230072969 + 3 ^ 40 * 4021402 * 2
def baseEnd_4021402 : Nat := 688304043650660159960305

theorem tailTrace_4021402 : CollatzResearch.WordTrace tailWord_4021402 prefixEnd_4021402 688304043650660159960305 := by
  unfold tailWord_4021402
  simp only [CollatzResearch.WordTrace]
  refine ⟨36668145144288707406926615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97781720384769886418470973 36668145144288707406926615)
  ·
    refine ⟨55002217716433061110389923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36668145144288707406926615 55002217716433061110389923)
    ·
      refine ⟨82503326574649591665584885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55002217716433061110389923 82503326574649591665584885)
      ·
        refine ⟨7734686866373399218648583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82503326574649591665584885 7734686866373399218648583)
        ·
          refine ⟨11602030299560098827972875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734686866373399218648583 11602030299560098827972875)
          ·
            refine ⟨17403045449340148241959313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602030299560098827972875 17403045449340148241959313)
            ·
              refine ⟨13052284087005111181469485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17403045449340148241959313 13052284087005111181469485)
              ·
                refine ⟨4894606532626916693051057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13052284087005111181469485 4894606532626916693051057)
                ·
                  refine ⟨3670954899470187519788293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894606532626916693051057 3670954899470187519788293)
                  ·
                    refine ⟨688304043650660159960305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670954899470187519788293 688304043650660159960305)
                    ·
                      rfl

theorem cell23_4021402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_4021402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021402 prefixEnd_4021402 := by exact prefixLift 4021402
  have htrace : WordTrace (prefixWord ++ tailWord_4021402) baseStart_4021402 baseEnd_4021402 := by
    simpa [prefixWord, tailWord_4021402, baseEnd_4021402] using wordTrace_append hprefix tailTrace_4021402
  have hstable : (prefixWord ++ tailWord_4021402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021402).length < 2 ^ (prefixWord ++ tailWord_4021402).sum := by decide
  have hdescent : baseEnd_4021402 < baseStart_4021402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021405 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_4021405 : Nat := 118140960795 + 4021405 * 2 ^ 59
def prefixEnd_4021405 : Nat := 4983230072969 + 3 ^ 40 * 4021405 * 2
def baseEnd_4021405 : Nat := 2064913671393943968143401

theorem tailTrace_4021405 : CollatzResearch.WordTrace tailWord_4021405 prefixEnd_4021405 2064913671393943968143401 := by
  unfold tailWord_4021405
  simp only [CollatzResearch.WordTrace]
  refine ⟨146672689996143961140065669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97781793330762640760043779 146672689996143961140065669)
  ·
    refine ⟨27501129374276992713762313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146672689996143961140065669 27501129374276992713762313)
    ·
      refine ⟨20625847030707744535321735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27501129374276992713762313 20625847030707744535321735)
      ·
        refine ⟨30938770546061616802982603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20625847030707744535321735 30938770546061616802982603)
        ·
          refine ⟨46408155819092425204473905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30938770546061616802982603 46408155819092425204473905)
          ·
            refine ⟨34806116864319318903355429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46408155819092425204473905 34806116864319318903355429)
            ·
              refine ⟨6526146912059872294379143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34806116864319318903355429 6526146912059872294379143)
              ·
                refine ⟨9789220368089808441568715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526146912059872294379143 9789220368089808441568715)
                ·
                  refine ⟨14683830552134712662353073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789220368089808441568715 14683830552134712662353073)
                  ·
                    refine ⟨11012872914101034496764805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14683830552134712662353073 11012872914101034496764805)
                    ·
                      refine ⟨2064913671393943968143401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11012872914101034496764805 2064913671393943968143401)
                      ·
                        rfl

theorem cell23_4021405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_4021405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021405 prefixEnd_4021405 := by exact prefixLift 4021405
  have htrace : WordTrace (prefixWord ++ tailWord_4021405) baseStart_4021405 baseEnd_4021405 := by
    simpa [prefixWord, tailWord_4021405, baseEnd_4021405] using wordTrace_append hprefix tailTrace_4021405
  have hstable : (prefixWord ++ tailWord_4021405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021405).length < 2 ^ (prefixWord ++ tailWord_4021405).sum := by decide
  have hdescent : baseEnd_4021405 < baseStart_4021405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021426 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_4021426 : Nat := 118140960795 + 4021426 * 2 ^ 59
def prefixEnd_4021426 : Nat := 4983230072969 + 3 ^ 40 * 4021426 * 2
def baseEnd_4021426 : Nat := 2064924454487688385980805

theorem tailTrace_4021426 : CollatzResearch.WordTrace tailWord_4021426 prefixEnd_4021426 2064924454487688385980805 := by
  unfold tailWord_4021426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36668363982266970431645033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97782303952711921151053421 36668363982266970431645033)
  ·
    refine ⟨27501272986700227823733775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36668363982266970431645033 27501272986700227823733775)
    ·
      refine ⟨41251909480050341735600663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27501272986700227823733775 41251909480050341735600663)
      ·
        refine ⟨61877864220075512603400995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41251909480050341735600663 61877864220075512603400995)
        ·
          refine ⟨92816796330113268905101493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61877864220075512603400995 92816796330113268905101493)
          ·
            refine ⟨8701574655948118959853265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92816796330113268905101493 8701574655948118959853265)
            ·
              refine ⟨6526180991961089219889949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8701574655948118959853265 6526180991961089219889949)
              ·
                refine ⟨2447317871985408457458731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6526180991961089219889949 2447317871985408457458731)
                ·
                  refine ⟨3670976807978112686188097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447317871985408457458731 3670976807978112686188097)
                  ·
                    refine ⟨2753232605983584514641073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3670976807978112686188097 2753232605983584514641073)
                    ·
                      refine ⟨2064924454487688385980805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753232605983584514641073 2064924454487688385980805)
                      ·
                        rfl

theorem cell23_4021426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_4021426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021426 prefixEnd_4021426 := by exact prefixLift 4021426
  have htrace : WordTrace (prefixWord ++ tailWord_4021426) baseStart_4021426 baseEnd_4021426 := by
    simpa [prefixWord, tailWord_4021426, baseEnd_4021426] using wordTrace_append hprefix tailTrace_4021426
  have hstable : (prefixWord ++ tailWord_4021426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021426).length < 2 ^ (prefixWord ++ tailWord_4021426).sum := by decide
  have hdescent : baseEnd_4021426 < baseStart_4021426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4021435 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 5, 3, 2]
def baseStart_4021435 : Nat := 118140960795 + 4021435 * 2 ^ 59
def prefixEnd_4021435 : Nat := 4983230072969 + 3 ^ 40 * 4021435 * 2
def baseEnd_4021435 : Nat := 2064929075813578850768263

theorem tailTrace_4021435 : CollatzResearch.WordTrace tailWord_4021435 prefixEnd_4021435 2064929075813578850768263 := by
  unfold tailWord_4021435
  simp only [CollatzResearch.WordTrace]
  refine ⟨146673784186035276263657759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97782522790690184175771839 146673784186035276263657759)
  ·
    refine ⟨220010676279052914395486639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146673784186035276263657759 220010676279052914395486639)
    ·
      refine ⟨330016014418579371593229959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220010676279052914395486639 330016014418579371593229959)
      ·
        refine ⟨495024021627869057389844939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330016014418579371593229959 495024021627869057389844939)
        ·
          refine ⟨742536032441803586084767409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495024021627869057389844939 742536032441803586084767409)
          ·
            refine ⟨556902024331352689563575557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742536032441803586084767409 556902024331352689563575557)
            ·
              refine ⟨104419129562128629293170417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556902024331352689563575557 104419129562128629293170417)
              ·
                refine ⟨78314347171596471969877813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104419129562128629293170417 78314347171596471969877813)
                ·
                  refine ⟨7341970047337169247176045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78314347171596471969877813 7341970047337169247176045)
                  ·
                    refine ⟨2753238767751438467691017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7341970047337169247176045 2753238767751438467691017)
                    ·
                      refine ⟨2064929075813578850768263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2753238767751438467691017 2064929075813578850768263)
                      ·
                        rfl

theorem cell23_4021435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3, 2].length) (baseStart_4021435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4021435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4021435 prefixEnd_4021435 := by exact prefixLift 4021435
  have htrace : WordTrace (prefixWord ++ tailWord_4021435) baseStart_4021435 baseEnd_4021435 := by
    simpa [prefixWord, tailWord_4021435, baseEnd_4021435] using wordTrace_append hprefix tailTrace_4021435
  have hstable : (prefixWord ++ tailWord_4021435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4021435).length < 2 ^ (prefixWord ++ tailWord_4021435).sum := by decide
  have hdescent : baseEnd_4021435 < baseStart_4021435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4021435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
