import V185TrunkScan23Chunk0484

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2869224 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2869224 : Nat := 118140960795 + 2869224 * 2 ^ 59
def prefixEnd_2869224 : Nat := 4983230072969 + 3 ^ 40 * 2869224 * 2
def baseEnd_2869224 : Nat := 1473291017415987381604685

theorem tailTrace_2869224 : CollatzResearch.WordTrace tailWord_2869224 prefixEnd_2869224 1473291017415987381604685 := by
  unfold tailWord_2869224
  simp only [CollatzResearch.WordTrace]
  refine ⟨52324598278649473645735363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69766131038199298194313817 52324598278649473645735363)
  ·
    refine ⟨78486897417974210468603045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52324598278649473645735363 78486897417974210468603045)
    ·
      refine ⟨14716293265870164462863071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78486897417974210468603045 14716293265870164462863071)
      ·
        refine ⟨22074439898805246694294607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14716293265870164462863071 22074439898805246694294607)
        ·
          refine ⟨33111659848207870041441911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22074439898805246694294607 33111659848207870041441911)
          ·
            refine ⟨49667489772311805062162867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33111659848207870041441911 49667489772311805062162867)
            ·
              refine ⟨74501234658467707593244301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49667489772311805062162867 74501234658467707593244301)
              ·
                refine ⟨27937962996925390347466613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74501234658467707593244301 27937962996925390347466613)
                ·
                  refine ⟨2619184030961755345074995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27937962996925390347466613 2619184030961755345074995)
                  ·
                    refine ⟨3928776046442633017612493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2619184030961755345074995 3928776046442633017612493)
                    ·
                      refine ⟨1473291017415987381604685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928776046442633017612493 1473291017415987381604685)
                      ·
                        rfl

theorem cell23_2869224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2869224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869224 prefixEnd_2869224 := by exact prefixLift 2869224
  have htrace : WordTrace (prefixWord ++ tailWord_2869224) baseStart_2869224 baseEnd_2869224 := by
    simpa [prefixWord, tailWord_2869224, baseEnd_2869224] using wordTrace_append hprefix tailTrace_2869224
  have hstable : (prefixWord ++ tailWord_2869224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869224).length < 2 ^ (prefixWord ++ tailWord_2869224).sum := by decide
  have hdescent : baseEnd_2869224 < baseStart_2869224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869252 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2869252 : Nat := 118140960795 + 2869252 * 2 ^ 59
def prefixEnd_2869252 : Nat := 4983230072969 + 3 ^ 40 * 2869252 * 2
def baseEnd_2869252 : Nat := 491101798291437757351519

theorem tailTrace_2869252 : CollatzResearch.WordTrace tailWord_2869252 prefixEnd_2869252 491101798291437757351519 := by
  unfold tailWord_2869252
  simp only [CollatzResearch.WordTrace]
  refine ⟨52325108900598754036745005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69766811867465005382326673 52325108900598754036745005)
  ·
    refine ⟨19621915837724532763779377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52325108900598754036745005 19621915837724532763779377)
    ·
      refine ⟨14716436878293399572834533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19621915837724532763779377 14716436878293399572834533)
      ·
        refine ⟨2759331914680012419906475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14716436878293399572834533 2759331914680012419906475)
        ·
          refine ⟨4138997872020018629859713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759331914680012419906475 4138997872020018629859713)
          ·
            refine ⟨3104248404015013972394785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4138997872020018629859713 3104248404015013972394785)
            ·
              refine ⟨2328186303011260479296089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104248404015013972394785 2328186303011260479296089)
              ·
                refine ⟨1746139727258445359472067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328186303011260479296089 1746139727258445359472067)
                ·
                  refine ⟨2619209590887668039208101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746139727258445359472067 2619209590887668039208101)
                  ·
                    refine ⟨491101798291437757351519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619209590887668039208101 491101798291437757351519)
                    ·
                      rfl

theorem cell23_2869252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2869252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869252 prefixEnd_2869252 := by exact prefixLift 2869252
  have htrace : WordTrace (prefixWord ++ tailWord_2869252) baseStart_2869252 baseEnd_2869252 := by
    simpa [prefixWord, tailWord_2869252, baseEnd_2869252] using wordTrace_append hprefix tailTrace_2869252
  have hstable : (prefixWord ++ tailWord_2869252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869252).length < 2 ^ (prefixWord ++ tailWord_2869252).sum := by decide
  have hdescent : baseEnd_2869252 < baseStart_2869252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869267 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5]
def baseStart_2869267 : Nat := 118140960795 + 2869267 * 2 ^ 59
def prefixEnd_2869267 : Nat := 4983230072969 + 3 ^ 40 * 2869267 * 2
def baseEnd_2869267 : Nat := 1473313097084130713366987

theorem tailTrace_2869267 : CollatzResearch.WordTrace tailWord_2869267 prefixEnd_2869267 1473313097084130713366987 := by
  unfold tailWord_2869267
  simp only [CollatzResearch.WordTrace]
  refine ⟨104650764896143165635286055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69767176597428777090190703 104650764896143165635286055)
  ·
    refine ⟨156976147344214748452929083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104650764896143165635286055 156976147344214748452929083)
    ·
      refine ⟨235464221016322122679393625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156976147344214748452929083 235464221016322122679393625)
      ·
        refine ⟨176598165762241592009545219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235464221016322122679393625 176598165762241592009545219)
        ·
          refine ⟨264897248643362388014317829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176598165762241592009545219 264897248643362388014317829)
          ·
            refine ⟨49668234120630447752684593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264897248643362388014317829 49668234120630447752684593)
            ·
              refine ⟨37251175590472835814513445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49668234120630447752684593 37251175590472835814513445)
              ·
                refine ⟨6984595423213656715221271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37251175590472835814513445 6984595423213656715221271)
                ·
                  refine ⟨10476893134820485072831907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6984595423213656715221271 10476893134820485072831907)
                  ·
                    refine ⟨15715339702230727609247861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10476893134820485072831907 15715339702230727609247861)
                    ·
                      refine ⟨1473313097084130713366987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15715339702230727609247861 1473313097084130713366987)
                      ·
                        rfl

theorem cell23_2869267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_2869267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869267 prefixEnd_2869267 := by exact prefixLift 2869267
  have htrace : WordTrace (prefixWord ++ tailWord_2869267) baseStart_2869267 baseEnd_2869267 := by
    simpa [prefixWord, tailWord_2869267, baseEnd_2869267] using wordTrace_append hprefix tailTrace_2869267
  have hstable : (prefixWord ++ tailWord_2869267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869267).length < 2 ^ (prefixWord ++ tailWord_2869267).sum := by decide
  have hdescent : baseEnd_2869267 < baseStart_2869267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869274 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_2869274 : Nat := 118140960795 + 2869274 * 2 ^ 59
def prefixEnd_2869274 : Nat := 4983230072969 + 3 ^ 40 * 2869274 * 2
def baseEnd_2869274 : Nat := 491105563816237395326485

theorem tailTrace_2869274 : CollatzResearch.WordTrace tailWord_2869274 prefixEnd_2869274 491105563816237395326485 := by
  unfold tailWord_2869274
  simp only [CollatzResearch.WordTrace]
  refine ⟨26162755051779451457697719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69767346804745203887193917 26162755051779451457697719)
  ·
    refine ⟨39244132577669177186546579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26162755051779451457697719 39244132577669177186546579)
    ·
      refine ⟨58866198866503765779819869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39244132577669177186546579 58866198866503765779819869)
      ·
        refine ⟨22074824574938912167432451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58866198866503765779819869 22074824574938912167432451)
        ·
          refine ⟨33112236862408368251148677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22074824574938912167432451 33112236862408368251148677)
          ·
            refine ⟨6208544411701569047090377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33112236862408368251148677 6208544411701569047090377)
            ·
              refine ⟨4656408308776176785317783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6208544411701569047090377 4656408308776176785317783)
              ·
                refine ⟨6984612463164265177976675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656408308776176785317783 6984612463164265177976675)
                ·
                  refine ⟨10476918694746397766965013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6984612463164265177976675 10476918694746397766965013)
                  ·
                    refine ⟨491105563816237395326485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10476918694746397766965013 491105563816237395326485)
                    ·
                      rfl

theorem cell23_2869274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_2869274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869274 prefixEnd_2869274 := by exact prefixLift 2869274
  have htrace : WordTrace (prefixWord ++ tailWord_2869274) baseStart_2869274 baseEnd_2869274 := by
    simpa [prefixWord, tailWord_2869274, baseEnd_2869274] using wordTrace_append hprefix tailTrace_2869274
  have hstable : (prefixWord ++ tailWord_2869274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869274).length < 2 ^ (prefixWord ++ tailWord_2869274).sum := by decide
  have hdescent : baseEnd_2869274 < baseStart_2869274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869298 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_2869298 : Nat := 118140960795 + 2869298 * 2 ^ 59
def prefixEnd_2869298 : Nat := 4983230072969 + 3 ^ 40 * 2869298 * 2
def baseEnd_2869298 : Nat := 1473329014984420092079345

theorem tailTrace_2869298 : CollatzResearch.WordTrace tailWord_2869298 prefixEnd_2869298 1473329014984420092079345 := by
  unfold tailWord_2869298
  simp only [CollatzResearch.WordTrace]
  refine ⟨26162973889757714482416137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69767930372687238619776365 26162973889757714482416137)
  ·
    refine ⟨19622230417318285861812103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26162973889757714482416137 19622230417318285861812103)
    ·
      refine ⟨29433345625977428792718155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622230417318285861812103 29433345625977428792718155)
      ·
        refine ⟨44150018438966143189077233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29433345625977428792718155 44150018438966143189077233)
        ·
          refine ⟨33112513829224607391807925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44150018438966143189077233 33112513829224607391807925)
          ·
            refine ⟨3104298171489806942981993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33112513829224607391807925 3104298171489806942981993)
            ·
              refine ⟨2328223628617355207236495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104298171489806942981993 2328223628617355207236495)
              ·
                refine ⟨3492335442926032810854743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328223628617355207236495 3492335442926032810854743)
                ·
                  refine ⟨5238503164389049216282115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492335442926032810854743 5238503164389049216282115)
                  ·
                    refine ⟨7857754746583573824423173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5238503164389049216282115 7857754746583573824423173)
                    ·
                      refine ⟨1473329014984420092079345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7857754746583573824423173 1473329014984420092079345)
                      ·
                        rfl

theorem cell23_2869298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_2869298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869298 prefixEnd_2869298 := by exact prefixLift 2869298
  have htrace : WordTrace (prefixWord ++ tailWord_2869298) baseStart_2869298 baseEnd_2869298 := by
    simpa [prefixWord, tailWord_2869298, baseEnd_2869298] using wordTrace_append hprefix tailTrace_2869298
  have hstable : (prefixWord ++ tailWord_2869298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869298).length < 2 ^ (prefixWord ++ tailWord_2869298).sum := by decide
  have hdescent : baseEnd_2869298 < baseStart_2869298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869347 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 8]
def baseStart_2869347 : Nat := 118140960795 + 2869347 * 2 ^ 59
def prefixEnd_2869347 : Nat := 4983230072969 + 3 ^ 40 * 2869347 * 2
def baseEnd_2869347 : Nat := 491118058512163466788873

theorem tailTrace_2869347 : CollatzResearch.WordTrace tailWord_2869347 prefixEnd_2869347 491118058512163466788873 := by
  unfold tailWord_2869347
  simp only [CollatzResearch.WordTrace]
  refine ⟨104653682735853339298198295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69769121823902226198798863 104653682735853339298198295)
  ·
    refine ⟨156980524103780008947297443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104653682735853339298198295 156980524103780008947297443)
    ·
      refine ⟨235470786155670013420946165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156980524103780008947297443 235470786155670013420946165)
      ·
        refine ⟨22075386202094063758213703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235470786155670013420946165 22075386202094063758213703)
        ·
          refine ⟨33113079303141095637320555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22075386202094063758213703 33113079303141095637320555)
          ·
            refine ⟨49669618954711643455980833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33113079303141095637320555 49669618954711643455980833)
            ·
              refine ⟨37252214216033732591985625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49669618954711643455980833 37252214216033732591985625)
              ·
                refine ⟨27939160662025299443989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37252214216033732591985625 27939160662025299443989219)
                ·
                  refine ⟨41908740993037949165983829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27939160662025299443989219 41908740993037949165983829)
                  ·
                    refine ⟨491118058512163466788873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41908740993037949165983829 491118058512163466788873)
                    ·
                      rfl

theorem cell23_2869347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_2869347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869347 prefixEnd_2869347 := by exact prefixLift 2869347
  have htrace : WordTrace (prefixWord ++ tailWord_2869347) baseStart_2869347 baseEnd_2869347 := by
    simpa [prefixWord, tailWord_2869347, baseEnd_2869347] using wordTrace_append hprefix tailTrace_2869347
  have hstable : (prefixWord ++ tailWord_2869347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869347).length < 2 ^ (prefixWord ++ tailWord_2869347).sum := by decide
  have hdescent : baseEnd_2869347 < baseStart_2869347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869358 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2869358 : Nat := 118140960795 + 2869358 * 2 ^ 59
def prefixEnd_2869358 : Nat := 4983230072969 + 3 ^ 40 * 2869358 * 2
def baseEnd_2869358 : Nat := 1473359823823689857329069

theorem tailTrace_2869358 : CollatzResearch.WordTrace tailWord_2869358 prefixEnd_2869358 1473359823823689857329069 := by
  unfold tailWord_2869358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081760492351686022106091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69769389292542325451232485 13081760492351686022106091)
  ·
    refine ⟨19622640738527529033159137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081760492351686022106091 19622640738527529033159137)
    ·
      refine ⟨14716980553895646774869353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19622640738527529033159137 14716980553895646774869353)
      ·
        refine ⟨11037735415421735081152015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14716980553895646774869353 11037735415421735081152015)
        ·
          refine ⟨16556603123132602621728023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11037735415421735081152015 16556603123132602621728023)
          ·
            refine ⟨24834904684698903932592035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16556603123132602621728023 24834904684698903932592035)
            ·
              refine ⟨37252357027048355898888053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24834904684698903932592035 37252357027048355898888053)
              ·
                refine ⟨3492408471285783365520755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37252357027048355898888053 3492408471285783365520755)
                ·
                  refine ⟨5238612706928675048281133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492408471285783365520755 5238612706928675048281133)
                  ·
                    refine ⟨1964479765098253143105425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5238612706928675048281133 1964479765098253143105425)
                    ·
                      refine ⟨1473359823823689857329069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1964479765098253143105425 1473359823823689857329069)
                      ·
                        rfl

theorem cell23_2869358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2869358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869358 prefixEnd_2869358 := by exact prefixLift 2869358
  have htrace : WordTrace (prefixWord ++ tailWord_2869358) baseStart_2869358 baseEnd_2869358 := by
    simpa [prefixWord, tailWord_2869358, baseEnd_2869358] using wordTrace_append hprefix tailTrace_2869358
  have hstable : (prefixWord ++ tailWord_2869358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869358).length < 2 ^ (prefixWord ++ tailWord_2869358).sum := by decide
  have hdescent : baseEnd_2869358 < baseStart_2869358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869394 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_2869394 : Nat := 118140960795 + 2869394 * 2 ^ 59
def prefixEnd_2869394 : Nat := 4983230072969 + 3 ^ 40 * 2869394 * 2
def baseEnd_2869394 : Nat := 163708701014139079608767

theorem tailTrace_2869394 : CollatzResearch.WordTrace tailWord_2869394 prefixEnd_2869394 163708701014139079608767 := by
  unfold tailWord_2869394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26163849241670766581289809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69770264644455377550106157 26163849241670766581289809)
  ·
    refine ⟨19622886931253074935967357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26163849241670766581289809 19622886931253074935967357)
    ·
      refine ⟨7358582599219903100987759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19622886931253074935967357 7358582599219903100987759)
      ·
        refine ⟨11037873898829854651481639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7358582599219903100987759 11037873898829854651481639)
        ·
          refine ⟨16556810848244781977222459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11037873898829854651481639 16556810848244781977222459)
          ·
            refine ⟨24835216272367172965833689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16556810848244781977222459 24835216272367172965833689)
            ·
              refine ⟨18626412204275379724375267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24835216272367172965833689 18626412204275379724375267)
              ·
                refine ⟨27939618306413069586562901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18626412204275379724375267 27939618306413069586562901)
                ·
                  refine ⟨163708701014139079608767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27939618306413069586562901 163708701014139079608767)
                  ·
                    rfl

theorem cell23_2869394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_2869394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869394 prefixEnd_2869394 := by exact prefixLift 2869394
  have htrace : WordTrace (prefixWord ++ tailWord_2869394) baseStart_2869394 baseEnd_2869394 := by
    simpa [prefixWord, tailWord_2869394, baseEnd_2869394] using wordTrace_append hprefix tailTrace_2869394
  have hstable : (prefixWord ++ tailWord_2869394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869394).length < 2 ^ (prefixWord ++ tailWord_2869394).sum := by decide
  have hdescent : baseEnd_2869394 < baseStart_2869394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869431 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 2, 5, 2]
def baseStart_2869431 : Nat := 118140960795 + 2869431 * 2 ^ 59
def prefixEnd_2869431 : Nat := 4983230072969 + 3 ^ 40 * 2869431 * 2
def baseEnd_2869431 : Nat := 1473397307911468071716233

theorem tailTrace_2869431 : CollatzResearch.WordTrace tailWord_2869431 prefixEnd_2869431 1473397307911468071716233 := by
  unfold tailWord_2869431
  simp only [CollatzResearch.WordTrace]
  refine ⟨104656746467549021644256147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69771164311699347762837431 104656746467549021644256147)
  ·
    refine ⟨156985119701323532466384221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104656746467549021644256147 156985119701323532466384221)
    ·
      refine ⟨58869419887996324674894083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156985119701323532466384221 58869419887996324674894083)
      ·
        refine ⟨88304129831994487012341125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58869419887996324674894083 88304129831994487012341125)
        ·
          refine ⟨16557024343498966314813961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88304129831994487012341125 16557024343498966314813961)
          ·
            refine ⟨12417768257624224736110471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16557024343498966314813961 12417768257624224736110471)
            ·
              refine ⟨18626652386436337104165707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417768257624224736110471 18626652386436337104165707)
              ·
                refine ⟨27939978579654505656248561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18626652386436337104165707 27939978579654505656248561)
                ·
                  refine ⟨20954983934740879242186421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27939978579654505656248561 20954983934740879242186421)
                  ·
                    refine ⟨1964529743881957428954977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20954983934740879242186421 1964529743881957428954977)
                    ·
                      refine ⟨1473397307911468071716233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1964529743881957428954977 1473397307911468071716233)
                      ·
                        rfl

theorem cell23_2869431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_2869431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869431 prefixEnd_2869431 := by exact prefixLift 2869431
  have htrace : WordTrace (prefixWord ++ tailWord_2869431) baseStart_2869431 baseEnd_2869431 := by
    simpa [prefixWord, tailWord_2869431, baseEnd_2869431] using wordTrace_append hprefix tailTrace_2869431
  have hstable : (prefixWord ++ tailWord_2869431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869431).length < 2 ^ (prefixWord ++ tailWord_2869431).sum := by decide
  have hdescent : baseEnd_2869431 < baseStart_2869431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869434 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_2869434 : Nat := 118140960795 + 2869434 * 2 ^ 59
def prefixEnd_2869434 : Nat := 4983230072969 + 3 ^ 40 * 2869434 * 2
def baseEnd_2869434 : Nat := 1473398848353431559978719

theorem tailTrace_2869434 : CollatzResearch.WordTrace tailWord_2869434 prefixEnd_2869434 1473398848353431559978719 := by
  unfold tailWord_2869434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26164213971634538289153839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69771237257692102104410237 26164213971634538289153839)
  ·
    refine ⟨39246320957451807433730759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26164213971634538289153839 39246320957451807433730759)
    ·
      refine ⟨58869481436177711150596139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39246320957451807433730759 58869481436177711150596139)
      ·
        refine ⟨88304222154266566725894209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58869481436177711150596139 88304222154266566725894209)
        ·
          refine ⟨66228166615699925044420657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88304222154266566725894209 66228166615699925044420657)
          ·
            refine ⟨49671124961774943783315493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66228166615699925044420657 49671124961774943783315493)
            ·
              refine ⟨9313335930332801959371655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49671124961774943783315493 9313335930332801959371655)
              ·
                refine ⟨13970003895499202939057483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313335930332801959371655 13970003895499202939057483)
                ·
                  refine ⟨20955005843248804408586225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13970003895499202939057483 20955005843248804408586225)
                  ·
                    refine ⟨15716254382436603306439669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20955005843248804408586225 15716254382436603306439669)
                    ·
                      refine ⟨1473398848353431559978719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15716254382436603306439669 1473398848353431559978719)
                      ·
                        rfl

theorem cell23_2869434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_2869434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869434 prefixEnd_2869434 := by exact prefixLift 2869434
  have htrace : WordTrace (prefixWord ++ tailWord_2869434) baseStart_2869434 baseEnd_2869434 := by
    simpa [prefixWord, tailWord_2869434, baseEnd_2869434] using wordTrace_append hprefix tailTrace_2869434
  have hstable : (prefixWord ++ tailWord_2869434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869434).length < 2 ^ (prefixWord ++ tailWord_2869434).sum := by decide
  have hdescent : baseEnd_2869434 < baseStart_2869434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869438 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2869438 : Nat := 118140960795 + 2869438 * 2 ^ 59
def prefixEnd_2869438 : Nat := 4983230072969 + 3 ^ 40 * 2869438 * 2
def baseEnd_2869438 : Nat := 1473400902276049544328701

theorem tailTrace_2869438 : CollatzResearch.WordTrace tailWord_2869438 prefixEnd_2869438 1473400902276049544328701 := by
  unfold tailWord_2869438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13082125222315457729970121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69771334519015774559840645 13082125222315457729970121)
  ·
    refine ⟨9811593916736593297477591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13082125222315457729970121 9811593916736593297477591)
    ·
      refine ⟨14717390875104889946216387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811593916736593297477591 14717390875104889946216387)
      ·
        refine ⟨22076086312657334919324581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14717390875104889946216387 22076086312657334919324581)
        ·
          refine ⟨4139266183623250297373359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22076086312657334919324581 4139266183623250297373359)
          ·
            refine ⟨6208899275434875446060039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139266183623250297373359 6208899275434875446060039)
            ·
              refine ⟨9313348913152313169090059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208899275434875446060039 9313348913152313169090059)
              ·
                refine ⟨13970023369728469753635089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313348913152313169090059 13970023369728469753635089)
                ·
                  refine ⟨10477517527296352315226317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13970023369728469753635089 10477517527296352315226317)
                  ·
                    refine ⟨3929069072736132118209869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10477517527296352315226317 3929069072736132118209869)
                    ·
                      refine ⟨1473400902276049544328701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929069072736132118209869 1473400902276049544328701)
                      ·
                        rfl

theorem cell23_2869438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2869438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869438 prefixEnd_2869438 := by exact prefixLift 2869438
  have htrace : WordTrace (prefixWord ++ tailWord_2869438) baseStart_2869438 baseEnd_2869438 := by
    simpa [prefixWord, tailWord_2869438, baseEnd_2869438] using wordTrace_append hprefix tailTrace_2869438
  have hstable : (prefixWord ++ tailWord_2869438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869438).length < 2 ^ (prefixWord ++ tailWord_2869438).sum := by decide
  have hdescent : baseEnd_2869438 < baseStart_2869438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869458 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2869458 : Nat := 118140960795 + 2869458 * 2 ^ 59
def prefixEnd_2869458 : Nat := 4983230072969 + 3 ^ 40 * 2869458 * 2
def baseEnd_2869458 : Nat := 491137057296379822026203

theorem tailTrace_2869458 : CollatzResearch.WordTrace tailWord_2869458 prefixEnd_2869458 491137057296379822026203 := by
  unfold tailWord_2869458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26164432809612801313872257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69771820825634136836992685 26164432809612801313872257)
  ·
    refine ⟨19623324607209600985404193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26164432809612801313872257 19623324607209600985404193)
    ·
      refine ⟨14717493455407200739053145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19623324607209600985404193 14717493455407200739053145)
      ·
        refine ⟨11038120091555400554289859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14717493455407200739053145 11038120091555400554289859)
        ·
          refine ⟨16557180137333100831434789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11038120091555400554289859 16557180137333100831434789)
          ·
            refine ⟨3104471275749956405894023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16557180137333100831434789 3104471275749956405894023)
            ·
              refine ⟨4656706913624934608841035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104471275749956405894023 4656706913624934608841035)
              ·
                refine ⟨6985060370437401913261553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656706913624934608841035 6985060370437401913261553)
                ·
                  refine ⟨5238795277828051434946165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6985060370437401913261553 5238795277828051434946165)
                  ·
                    refine ⟨491137057296379822026203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5238795277828051434946165 491137057296379822026203)
                    ·
                      rfl

theorem cell23_2869458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2869458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869458 prefixEnd_2869458 := by exact prefixLift 2869458
  have htrace : WordTrace (prefixWord ++ tailWord_2869458) baseStart_2869458 baseEnd_2869458 := by
    simpa [prefixWord, tailWord_2869458, baseEnd_2869458] using wordTrace_append hprefix tailTrace_2869458
  have hstable : (prefixWord ++ tailWord_2869458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869458).length < 2 ^ (prefixWord ++ tailWord_2869458).sum := by decide
  have hdescent : baseEnd_2869458 < baseStart_2869458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869484 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 8]
def baseStart_2869484 : Nat := 118140960795 + 2869484 * 2 ^ 59
def prefixEnd_2869484 : Nat := 4983230072969 + 3 ^ 40 * 2869484 * 2
def baseEnd_2869484 : Nat := 163713835820684040483721

theorem tailTrace_2869484 : CollatzResearch.WordTrace tailWord_2869484 prefixEnd_2869484 163713835820684040483721 := by
  unfold tailWord_2869484
  simp only [CollatzResearch.WordTrace]
  refine ⟨52329339768178505847967753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69772453024238007797290337 52329339768178505847967753)
  ·
    refine ⟨39247004826133879385975815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52329339768178505847967753 39247004826133879385975815)
    ·
      refine ⟨58870507239200819078963723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39247004826133879385975815 58870507239200819078963723)
      ·
        refine ⟨88305760858801228618445585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58870507239200819078963723 88305760858801228618445585)
        ·
          refine ⟨66229320644100921463834189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88305760858801228618445585 66229320644100921463834189)
          ·
            refine ⟨24835995241537845548937821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66229320644100921463834189 24835995241537845548937821)
            ·
              refine ⟨9313498215576692080851683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24835995241537845548937821 9313498215576692080851683)
              ·
                refine ⟨13970247323365038121277525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313498215576692080851683 13970247323365038121277525)
                ·
                  refine ⟨163713835820684040483721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13970247323365038121277525 163713835820684040483721)
                  ·
                    rfl

theorem cell23_2869484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_2869484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869484 prefixEnd_2869484 := by exact prefixLift 2869484
  have htrace : WordTrace (prefixWord ++ tailWord_2869484) baseStart_2869484 baseEnd_2869484 := by
    simpa [prefixWord, tailWord_2869484, baseEnd_2869484] using wordTrace_append hprefix tailTrace_2869484
  have hstable : (prefixWord ++ tailWord_2869484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869484).length < 2 ^ (prefixWord ++ tailWord_2869484).sum := by decide
  have hdescent : baseEnd_2869484 < baseStart_2869484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869531 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 1, 5]
def baseStart_2869531 : Nat := 118140960795 + 2869531 * 2 ^ 59
def prefixEnd_2869531 : Nat := 4983230072969 + 3 ^ 40 * 2869531 * 2
def baseEnd_2869531 : Nat := 491149551992305893488591

theorem tailTrace_2869531 : CollatzResearch.WordTrace tailWord_2869531 prefixEnd_2869531 491149551992305893488591 := by
  unfold tailWord_2869531
  simp only [CollatzResearch.WordTrace]
  refine ⟨104660393767186738722896447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69773595844791159148597631 104660393767186738722896447)
  ·
    refine ⟨156990590650780108084344671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104660393767186738722896447 156990590650780108084344671)
    ·
      refine ⟨235485885976170162126517007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156990590650780108084344671 235485885976170162126517007)
      ·
        refine ⟨353228828964255243189775511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235485885976170162126517007 353228828964255243189775511)
        ·
          refine ⟨529843243446382864784663267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353228828964255243189775511 529843243446382864784663267)
          ·
            refine ⟨794764865169574297176994901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529843243446382864784663267 794764865169574297176994901)
            ·
              refine ⟨9313650763705948795042909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 794764865169574297176994901 9313650763705948795042909)
              ·
                refine ⟨3492619036389730798141091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9313650763705948795042909 3492619036389730798141091)
                ·
                  refine ⟨5238928554584596197211637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492619036389730798141091 5238928554584596197211637)
                  ·
                    refine ⟨491149551992305893488591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5238928554584596197211637 491149551992305893488591)
                    ·
                      rfl

theorem cell23_2869531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 5].length) (baseStart_2869531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869531 prefixEnd_2869531 := by exact prefixLift 2869531
  have htrace : WordTrace (prefixWord ++ tailWord_2869531) baseStart_2869531 baseEnd_2869531 := by
    simpa [prefixWord, tailWord_2869531, baseEnd_2869531] using wordTrace_append hprefix tailTrace_2869531
  have hstable : (prefixWord ++ tailWord_2869531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869531).length < 2 ^ (prefixWord ++ tailWord_2869531).sum := by decide
  have hdescent : baseEnd_2869531 < baseStart_2869531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869585 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 1, 1, 4]
def baseStart_2869585 : Nat := 118140960795 + 2869585 * 2 ^ 59
def prefixEnd_2869585 : Nat := 4983230072969 + 3 ^ 40 * 2869585 * 2
def baseEnd_2869585 : Nat := 1473476383932260469190525

theorem tailTrace_2869585 : CollatzResearch.WordTrace tailWord_2869585 prefixEnd_2869585 1473476383932260469190525 := by
  unfold tailWord_2869585
  simp only [CollatzResearch.WordTrace]
  refine ⟨104662363308991105945362209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69774908872660737296908139 104662363308991105945362209)
  ·
    refine ⟨78496772481743329459021657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104662363308991105945362209 78496772481743329459021657)
    ·
      refine ⟨58872579361307497094266243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78496772481743329459021657 58872579361307497094266243)
      ·
        refine ⟨88308869041961245641399365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58872579361307497094266243 88308869041961245641399365)
        ·
          refine ⟨16557912945367733557762381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88308869041961245641399365 16557912945367733557762381)
          ·
            refine ⟨6209217354512900084160893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16557912945367733557762381 6209217354512900084160893)
            ·
              refine ⟨2328456507942337531560335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6209217354512900084160893 2328456507942337531560335)
              ·
                refine ⟨3492684761913506297340503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328456507942337531560335 3492684761913506297340503)
                ·
                  refine ⟨5239027142870259446010755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492684761913506297340503 5239027142870259446010755)
                  ·
                    refine ⟨7858540714305389169016133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5239027142870259446010755 7858540714305389169016133)
                    ·
                      refine ⟨1473476383932260469190525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7858540714305389169016133 1473476383932260469190525)
                      ·
                        rfl

theorem cell23_2869585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_2869585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869585 prefixEnd_2869585 := by exact prefixLift 2869585
  have htrace : WordTrace (prefixWord ++ tailWord_2869585) baseStart_2869585 baseEnd_2869585 := by
    simpa [prefixWord, tailWord_2869585, baseEnd_2869585] using wordTrace_append hprefix tailTrace_2869585
  have hstable : (prefixWord ++ tailWord_2869585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869585).length < 2 ^ (prefixWord ++ tailWord_2869585).sum := by decide
  have hdescent : baseEnd_2869585 < baseStart_2869585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869588 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2869588 : Nat := 118140960795 + 2869588 * 2 ^ 59
def prefixEnd_2869588 : Nat := 4983230072969 + 3 ^ 40 * 2869588 * 2
def baseEnd_2869588 : Nat := 1473477924374223957453011

theorem tailTrace_2869588 : CollatzResearch.WordTrace tailWord_2869588 prefixEnd_2869588 1473477924374223957453011 := by
  unfold tailWord_2869588
  simp only [CollatzResearch.WordTrace]
  refine ⟨52331236363990118728860709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69774981818653491638480945 52331236363990118728860709)
  ·
    refine ⟨9812106818248147261661383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52331236363990118728860709 9812106818248147261661383)
    ·
      refine ⟨14718160227372220892492075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9812106818248147261661383 14718160227372220892492075)
      ·
        refine ⟨22077240341058331338738113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14718160227372220892492075 22077240341058331338738113)
        ·
          refine ⟨16557930255793748504053585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22077240341058331338738113 16557930255793748504053585)
          ·
            refine ⟨12418447691845311378040189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16557930255793748504053585 12418447691845311378040189)
            ·
              refine ⟨4656917884441991766765071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12418447691845311378040189 4656917884441991766765071)
              ·
                refine ⟨6985376826662987650147607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656917884441991766765071 6985376826662987650147607)
                ·
                  refine ⟨10478065239994481475221411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985376826662987650147607 10478065239994481475221411)
                  ·
                    refine ⟨15717097859991722212832117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10478065239994481475221411 15717097859991722212832117)
                    ·
                      refine ⟨1473477924374223957453011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15717097859991722212832117 1473477924374223957453011)
                      ·
                        rfl

theorem cell23_2869588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2869588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869588 prefixEnd_2869588 := by exact prefixLift 2869588
  have htrace : WordTrace (prefixWord ++ tailWord_2869588) baseStart_2869588 baseEnd_2869588 := by
    simpa [prefixWord, tailWord_2869588, baseEnd_2869588] using wordTrace_append hprefix tailTrace_2869588
  have hstable : (prefixWord ++ tailWord_2869588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869588).length < 2 ^ (prefixWord ++ tailWord_2869588).sum := by decide
  have hdescent : baseEnd_2869588 < baseStart_2869588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869608 : List Nat := [2, 1, 4, 2, 2, 3, 1, 8]
def baseStart_2869608 : Nat := 118140960795 + 2869608 * 2 ^ 59
def prefixEnd_2869608 : Nat := 4983230072969 + 3 ^ 40 * 2869608 * 2
def baseEnd_2869608 : Nat := 54573636814344958488997

theorem tailTrace_2869608 : CollatzResearch.WordTrace tailWord_2869608 prefixEnd_2869608 54573636814344958488997 := by
  unfold tailWord_2869608
  simp only [CollatzResearch.WordTrace]
  refine ⟨52331601093953890436724739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69775468125271853915632985 52331601093953890436724739)
  ·
    refine ⟨78497401640930835655087109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52331601093953890436724739 78497401640930835655087109)
    ·
      refine ⟨14718262807674531685328833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78497401640930835655087109 14718262807674531685328833)
      ·
        refine ⟨11038697105755898763996625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14718262807674531685328833 11038697105755898763996625)
        ·
          refine ⟨8279022829316924072997469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11038697105755898763996625 8279022829316924072997469)
          ·
            refine ⟨3104633560993846527374051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8279022829316924072997469 3104633560993846527374051)
            ·
              refine ⟨4656950341490769791061077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104633560993846527374051 4656950341490769791061077)
              ·
                refine ⟨54573636814344958488997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4656950341490769791061077 54573636814344958488997)
                ·
                  rfl

theorem cell23_2869608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 8].length) (baseStart_2869608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869608 prefixEnd_2869608 := by exact prefixLift 2869608
  have htrace : WordTrace (prefixWord ++ tailWord_2869608) baseStart_2869608 baseEnd_2869608 := by
    simpa [prefixWord, tailWord_2869608, baseEnd_2869608] using wordTrace_append hprefix tailTrace_2869608
  have hstable : (prefixWord ++ tailWord_2869608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869608).length < 2 ^ (prefixWord ++ tailWord_2869608).sum := by decide
  have hdescent : baseEnd_2869608 < baseStart_2869608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869618 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2869618 : Nat := 118140960795 + 2869618 * 2 ^ 59
def prefixEnd_2869618 : Nat := 4983230072969 + 3 ^ 40 * 2869618 * 2
def baseEnd_2869618 : Nat := 1473493328793858840077873

theorem tailTrace_2869618 : CollatzResearch.WordTrace tailWord_2869618 prefixEnd_2869618 1473493328793858840077873 := by
  unfold tailWord_2869618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26165891729467888145328377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69775711278581035054209005 26165891729467888145328377)
  ·
    refine ⟨19624418797100916108996283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26165891729467888145328377 19624418797100916108996283)
    ·
      refine ⟨29436628195651374163494425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19624418797100916108996283 29436628195651374163494425)
      ·
        refine ⟨22077471146738530622620819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29436628195651374163494425 22077471146738530622620819)
        ·
          refine ⟨33116206720107795933931229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22077471146738530622620819 33116206720107795933931229)
          ·
            refine ⟨12418577520040423475224211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33116206720107795933931229 12418577520040423475224211)
            ·
              refine ⟨18627866280060635212836317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418577520040423475224211 18627866280060635212836317)
              ·
                refine ⟨6985449855022738204813619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18627866280060635212836317 6985449855022738204813619)
                ·
                  refine ⟨10478174782534107307220429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985449855022738204813619 10478174782534107307220429)
                  ·
                    refine ⟨3929315543450290240207661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10478174782534107307220429 3929315543450290240207661)
                    ·
                      refine ⟨1473493328793858840077873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929315543450290240207661 1473493328793858840077873)
                      ·
                        rfl

theorem cell23_2869618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2869618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869618 prefixEnd_2869618 := by exact prefixLift 2869618
  have htrace : WordTrace (prefixWord ++ tailWord_2869618) baseStart_2869618 baseEnd_2869618 := by
    simpa [prefixWord, tailWord_2869618, baseEnd_2869618] using wordTrace_append hprefix tailTrace_2869618
  have hstable : (prefixWord ++ tailWord_2869618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869618).length < 2 ^ (prefixWord ++ tailWord_2869618).sum := by decide
  have hdescent : baseEnd_2869618 < baseStart_2869618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869652 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2869652 : Nat := 118140960795 + 2869652 * 2 ^ 59
def prefixEnd_2869652 : Nat := 4983230072969 + 3 ^ 40 * 2869652 * 2
def baseEnd_2869652 : Nat := 1473510787136111707052717

theorem tailTrace_2869652 : CollatzResearch.WordTrace tailWord_2869652 prefixEnd_2869652 1473510787136111707052717 := by
  unfold tailWord_2869652
  simp only [CollatzResearch.WordTrace]
  refine ⟨52332403499874188194025605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69776537999832250925367473 52332403499874188194025605)
  ·
    refine ⟨9812325656226410286379801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52332403499874188194025605 9812325656226410286379801)
    ·
      refine ⟨7359244242169807714784851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9812325656226410286379801 7359244242169807714784851)
      ·
        refine ⟨11038866363254711572177277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7359244242169807714784851 11038866363254711572177277)
        ·
          refine ⟨4139574886220516839566479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11038866363254711572177277 4139574886220516839566479)
          ·
            refine ⟨6209362329330775259349719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139574886220516839566479 6209362329330775259349719)
            ·
              refine ⟨9314043493996162889024579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209362329330775259349719 9314043493996162889024579)
              ·
                refine ⟨13971065240994244333536869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9314043493996162889024579 13971065240994244333536869)
                ·
                  refine ⟨2619574732686420812538163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13971065240994244333536869 2619574732686420812538163)
                  ·
                    refine ⟨3929362099029631218807245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2619574732686420812538163 3929362099029631218807245)
                    ·
                      refine ⟨1473510787136111707052717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929362099029631218807245 1473510787136111707052717)
                      ·
                        rfl

theorem cell23_2869652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2869652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869652 prefixEnd_2869652 := by exact prefixLift 2869652
  have htrace : WordTrace (prefixWord ++ tailWord_2869652) baseStart_2869652 baseEnd_2869652 := by
    simpa [prefixWord, tailWord_2869652, baseEnd_2869652] using wordTrace_append hprefix tailTrace_2869652
  have hstable : (prefixWord ++ tailWord_2869652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869652).length < 2 ^ (prefixWord ++ tailWord_2869652).sum := by decide
  have hdescent : baseEnd_2869652 < baseStart_2869652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869692 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2869692 : Nat := 118140960795 + 2869692 * 2 ^ 59
def prefixEnd_2869692 : Nat := 4983230072969 + 3 ^ 40 * 2869692 * 2
def baseEnd_2869692 : Nat := 1473531326362291550552533

theorem tailTrace_2869692 : CollatzResearch.WordTrace tailWord_2869692 prefixEnd_2869692 1473531326362291550552533 := by
  unfold tailWord_2869692
  simp only [CollatzResearch.WordTrace]
  refine ⟨52333132959801731609753665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69777510613068975479671553 52333132959801731609753665)
  ·
    refine ⟨39249849719851298707315249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52333132959801731609753665 39249849719851298707315249)
    ·
      refine ⟨29437387289888474030486437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39249849719851298707315249 29437387289888474030486437)
      ·
        refine ⟨5519510116854088880716207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29437387289888474030486437 5519510116854088880716207)
        ·
          refine ⟨8279265175281133321074311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5519510116854088880716207 8279265175281133321074311)
          ·
            refine ⟨12418897762921699981611467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8279265175281133321074311 12418897762921699981611467)
            ·
              refine ⟨18628346644382549972417201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418897762921699981611467 18628346644382549972417201)
              ·
                refine ⟨13971259983286912479312901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18628346644382549972417201 13971259983286912479312901)
                ·
                  refine ⟨2619611246866296089871169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13971259983286912479312901 2619611246866296089871169)
                  ·
                    refine ⟨1964708435149722067403377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2619611246866296089871169 1964708435149722067403377)
                    ·
                      refine ⟨1473531326362291550552533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1964708435149722067403377 1473531326362291550552533)
                      ·
                        rfl

theorem cell23_2869692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2869692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869692 prefixEnd_2869692 := by exact prefixLift 2869692
  have htrace : WordTrace (prefixWord ++ tailWord_2869692) baseStart_2869692 baseEnd_2869692 := by
    simpa [prefixWord, tailWord_2869692, baseEnd_2869692] using wordTrace_append hprefix tailTrace_2869692
  have hstable : (prefixWord ++ tailWord_2869692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869692).length < 2 ^ (prefixWord ++ tailWord_2869692).sum := by decide
  have hdescent : baseEnd_2869692 < baseStart_2869692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869766 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2869766 : Nat := 118140960795 + 2869766 * 2 ^ 59
def prefixEnd_2869766 : Nat := 4983230072969 + 3 ^ 40 * 2869766 * 2
def baseEnd_2869766 : Nat := 163729924881191584558577

theorem tailTrace_2869766 : CollatzResearch.WordTrace tailWord_2869766 prefixEnd_2869766 163729924881191584558577 := by
  unfold tailWord_2869766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270905153791730433053161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69779309947556915905134101 3270905153791730433053161)
  ·
    refine ⟨2453178865343797824789871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3270905153791730433053161 2453178865343797824789871)
    ·
      refine ⟨3679768298015696737184807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2453178865343797824789871 3679768298015696737184807)
      ·
        refine ⟨5519652447023545105777211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679768298015696737184807 5519652447023545105777211)
        ·
          refine ⟨8279478670535317658665817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5519652447023545105777211 8279478670535317658665817)
          ·
            refine ⟨6209609002901488243999363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8279478670535317658665817 6209609002901488243999363)
            ·
              refine ⟨9314413504352232365999045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209609002901488243999363 9314413504352232365999045)
              ·
                refine ⟨1746452532066043568624821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9314413504352232365999045 1746452532066043568624821)
                ·
                  refine ⟨163729924881191584558577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1746452532066043568624821 163729924881191584558577)
                  ·
                    rfl

theorem cell23_2869766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2869766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869766 prefixEnd_2869766 := by exact prefixLift 2869766
  have htrace : WordTrace (prefixWord ++ tailWord_2869766) baseStart_2869766 baseEnd_2869766 := by
    simpa [prefixWord, tailWord_2869766, baseEnd_2869766] using wordTrace_append hprefix tailTrace_2869766
  have hstable : (prefixWord ++ tailWord_2869766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869766).length < 2 ^ (prefixWord ++ tailWord_2869766).sum := by decide
  have hdescent : baseEnd_2869766 < baseStart_2869766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869768 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2869768 : Nat := 118140960795 + 2869768 * 2 ^ 59
def prefixEnd_2869768 : Nat := 4983230072969 + 3 ^ 40 * 2869768 * 2
def baseEnd_2869768 : Nat := 1473570350892033253202183

theorem tailTrace_2869768 : CollatzResearch.WordTrace tailWord_2869768 prefixEnd_2869768 1473570350892033253202183 := by
  unfold tailWord_2869768
  simp only [CollatzResearch.WordTrace]
  refine ⟨52334518933664064099636979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69779358578218752132849305 52334518933664064099636979)
  ·
    refine ⟨78501778400496096149455469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52334518933664064099636979 78501778400496096149455469)
    ·
      refine ⟨29438166900186036056045801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78501778400496096149455469 29438166900186036056045801)
      ·
        refine ⟨22078625175139527042034351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29438166900186036056045801 22078625175139527042034351)
        ·
          refine ⟨33117937762709290563051527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22078625175139527042034351 33117937762709290563051527)
          ·
            refine ⟨49676906644063935844577291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33117937762709290563051527 49676906644063935844577291)
            ·
              refine ⟨74515359966095903766865937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49676906644063935844577291 74515359966095903766865937)
              ·
                refine ⟨55886519974571927825149453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74515359966095903766865937 55886519974571927825149453)
                ·
                  refine ⟨20957444990464472934431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55886519974571927825149453 20957444990464472934431045)
                  ·
                    refine ⟨3929520935712088675205821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20957444990464472934431045 3929520935712088675205821)
                    ·
                      refine ⟨1473570350892033253202183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929520935712088675205821 1473570350892033253202183)
                      ·
                        rfl

theorem cell23_2869768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2869768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869768 prefixEnd_2869768 := by exact prefixLift 2869768
  have htrace : WordTrace (prefixWord ++ tailWord_2869768) baseStart_2869768 baseEnd_2869768 := by
    simpa [prefixWord, tailWord_2869768, baseEnd_2869768] using wordTrace_append hprefix tailTrace_2869768
  have hstable : (prefixWord ++ tailWord_2869768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869768).length < 2 ^ (prefixWord ++ tailWord_2869768).sum := by decide
  have hdescent : baseEnd_2869768 < baseStart_2869768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869792 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 3, 4]
def baseStart_2869792 : Nat := 118140960795 + 2869792 * 2 ^ 59
def prefixEnd_2869792 : Nat := 4983230072969 + 3 ^ 40 * 2869792 * 2
def baseEnd_2869792 : Nat := 491194224809247053100691

theorem tailTrace_2869792 : CollatzResearch.WordTrace tailWord_2869792 prefixEnd_2869792 491194224809247053100691 := by
  unfold tailWord_2869792
  simp only [CollatzResearch.WordTrace]
  refine ⟨52334956609620590149073815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69779942146160786865431753 52334956609620590149073815)
  ·
    refine ⟨78502434914430885223610723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52334956609620590149073815 78502434914430885223610723)
    ·
      refine ⟨117753652371646327835416085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78502434914430885223610723 117753652371646327835416085)
      ·
        refine ⟨5519702454920921617285129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117753652371646327835416085 5519702454920921617285129)
        ·
          refine ⟨4139776841190691212963847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519702454920921617285129 4139776841190691212963847)
          ·
            refine ⟨6209665261786036819445771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139776841190691212963847 6209665261786036819445771)
            ·
              refine ⟨9314497892679055229168657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209665261786036819445771 9314497892679055229168657)
              ·
                refine ⟨6985873419509291421876493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9314497892679055229168657 6985873419509291421876493)
                ·
                  refine ⟨2619702532315984283203685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6985873419509291421876493 2619702532315984283203685)
                  ·
                    refine ⟨491194224809247053100691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619702532315984283203685 491194224809247053100691)
                    ·
                      rfl

theorem cell23_2869792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_2869792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869792 prefixEnd_2869792 := by exact prefixLift 2869792
  have htrace : WordTrace (prefixWord ++ tailWord_2869792) baseStart_2869792 baseEnd_2869792 := by
    simpa [prefixWord, tailWord_2869792, baseEnd_2869792] using wordTrace_append hprefix tailTrace_2869792
  have hstable : (prefixWord ++ tailWord_2869792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869792).length < 2 ^ (prefixWord ++ tailWord_2869792).sum := by decide
  have hdescent : baseEnd_2869792 < baseStart_2869792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869802 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2869802 : Nat := 118140960795 + 2869802 * 2 ^ 59
def prefixEnd_2869802 : Nat := 4983230072969 + 3 ^ 40 * 2869802 * 2
def baseEnd_2869802 : Nat := 1473587809234286120177027

theorem tailTrace_2869802 : CollatzResearch.WordTrace tailWord_2869802 prefixEnd_2869802 1473587809234286120177027 := by
  unfold tailWord_2869802
  simp only [CollatzResearch.WordTrace]
  refine ⟨26167569487301238001502915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69780185299469968004007773 26167569487301238001502915)
  ·
    refine ⟨39251354230951857002254373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26167569487301238001502915 39251354230951857002254373)
    ·
      refine ⟨7359628918303473187922695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39251354230951857002254373 7359628918303473187922695)
      ·
        refine ⟨11039443377455209781884043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7359628918303473187922695 11039443377455209781884043)
        ·
          refine ⟨16559165066182814672826065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039443377455209781884043 16559165066182814672826065)
          ·
            refine ⟨12419373799637111004619549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16559165066182814672826065 12419373799637111004619549)
            ·
              refine ⟨4657265174863916626732331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12419373799637111004619549 4657265174863916626732331)
              ·
                refine ⟨6985897762295874940098497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657265174863916626732331 6985897762295874940098497)
                ·
                  refine ⟨5239423321721906205073873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6985897762295874940098497 5239423321721906205073873)
                  ·
                    refine ⟨3929567491291429653805405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239423321721906205073873 3929567491291429653805405)
                    ·
                      refine ⟨1473587809234286120177027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929567491291429653805405 1473587809234286120177027)
                      ·
                        rfl

theorem cell23_2869802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2869802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869802 prefixEnd_2869802 := by exact prefixLift 2869802
  have htrace : WordTrace (prefixWord ++ tailWord_2869802) baseStart_2869802 baseEnd_2869802 := by
    simpa [prefixWord, tailWord_2869802, baseEnd_2869802] using wordTrace_append hprefix tailTrace_2869802
  have hstable : (prefixWord ++ tailWord_2869802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869802).length < 2 ^ (prefixWord ++ tailWord_2869802).sum := by decide
  have hdescent : baseEnd_2869802 < baseStart_2869802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869815 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_2869815 : Nat := 118140960795 + 2869815 * 2 ^ 59
def prefixEnd_2869815 : Nat := 4983230072969 + 3 ^ 40 * 2869815 * 2
def baseEnd_2869815 : Nat := 1473594484482794569314467

theorem tailTrace_2869815 : CollatzResearch.WordTrace tailWord_2869815 prefixEnd_2869815 1473594484482794569314467 := by
  unfold tailWord_2869815
  simp only [CollatzResearch.WordTrace]
  refine ⟨104670752098157855226234899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69780501398771903484156599 104670752098157855226234899)
  ·
    refine ⟨157006128147236782839352349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104670752098157855226234899 157006128147236782839352349)
    ·
      refine ⟨58877298055213793564757131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157006128147236782839352349 58877298055213793564757131)
      ·
        refine ⟨88315947082820690347135697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58877298055213793564757131 88315947082820690347135697)
        ·
          refine ⟨66236960312115517760351773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88315947082820690347135697 66236960312115517760351773)
          ·
            refine ⟨24838860117043319160131915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66236960312115517760351773 24838860117043319160131915)
            ·
              refine ⟨37258290175564978740197873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24838860117043319160131915 37258290175564978740197873)
              ·
                refine ⟨27943717631673734055148405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37258290175564978740197873 27943717631673734055148405)
                ·
                  refine ⟨2619723527969412567670163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27943717631673734055148405 2619723527969412567670163)
                  ·
                    refine ⟨3929585291954118851505245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2619723527969412567670163 3929585291954118851505245)
                    ·
                      refine ⟨1473594484482794569314467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929585291954118851505245 1473594484482794569314467)
                      ·
                        rfl

theorem cell23_2869815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_2869815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869815 prefixEnd_2869815 := by exact prefixLift 2869815
  have htrace : WordTrace (prefixWord ++ tailWord_2869815) baseStart_2869815 baseEnd_2869815 := by
    simpa [prefixWord, tailWord_2869815, baseEnd_2869815] using wordTrace_append hprefix tailTrace_2869815
  have hstable : (prefixWord ++ tailWord_2869815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869815).length < 2 ^ (prefixWord ++ tailWord_2869815).sum := by decide
  have hdescent : baseEnd_2869815 < baseStart_2869815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869822 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2869822 : Nat := 118140960795 + 2869822 * 2 ^ 59
def prefixEnd_2869822 : Nat := 4983230072969 + 3 ^ 40 * 2869822 * 2
def baseEnd_2869822 : Nat := 163733119871930671325215

theorem tailTrace_2869822 : CollatzResearch.WordTrace tailWord_2869822 prefixEnd_2869822 163733119871930671325215 := by
  unfold tailWord_2869822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083875926141561927717465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69780671606088330281159813 13083875926141561927717465)
  ·
    refine ⟨9812906944606171445788099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13083875926141561927717465 9812906944606171445788099)
    ·
      refine ⟨14719360416909257168682149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9812906944606171445788099 14719360416909257168682149)
      ·
        refine ⟨2759880078170485719127903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14719360416909257168682149 2759880078170485719127903)
        ·
          refine ⟨4139820117255728578691855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759880078170485719127903 4139820117255728578691855)
          ·
            refine ⟨6209730175883592868037783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139820117255728578691855 6209730175883592868037783)
            ·
              refine ⟨9314595263825389302056675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209730175883592868037783 9314595263825389302056675)
              ·
                refine ⟨13971892895738083953085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9314595263825389302056675 13971892895738083953085013)
                ·
                  refine ⟨163733119871930671325215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13971892895738083953085013 163733119871930671325215)
                  ·
                    rfl

theorem cell23_2869822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2869822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869822 prefixEnd_2869822 := by exact prefixLift 2869822
  have htrace : WordTrace (prefixWord ++ tailWord_2869822) baseStart_2869822 baseEnd_2869822 := by
    simpa [prefixWord, tailWord_2869822, baseEnd_2869822] using wordTrace_append hprefix tailTrace_2869822
  have hstable : (prefixWord ++ tailWord_2869822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869822).length < 2 ^ (prefixWord ++ tailWord_2869822).sum := by decide
  have hdescent : baseEnd_2869822 < baseStart_2869822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869890 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2869890 : Nat := 118140960795 + 2869890 * 2 ^ 59
def prefixEnd_2869890 : Nat := 4983230072969 + 3 ^ 40 * 2869890 * 2
def baseEnd_2869890 : Nat := 163736999503542419541847

theorem tailTrace_2869890 : CollatzResearch.WordTrace tailWord_2869890 prefixEnd_2869890 163736999503542419541847 := by
  unfold tailWord_2869890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26168371893221535758803781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69782325048590762023476749 26168371893221535758803781)
  ·
    refine ⟨4906569729979037954775709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26168371893221535758803781 4906569729979037954775709)
    ·
      refine ⟨1839963648742139233040891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4906569729979037954775709 1839963648742139233040891)
      ·
        refine ⟨2759945473113208849561337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839963648742139233040891 2759945473113208849561337)
        ·
          refine ⟨2069959104834906637171003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2759945473113208849561337 2069959104834906637171003)
          ·
            refine ⟨3104938657252359955756505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069959104834906637171003 3104938657252359955756505)
            ·
              refine ⟨2328703992939269966817379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104938657252359955756505 2328703992939269966817379)
              ·
                refine ⟨3493055989408904950226069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328703992939269966817379 3493055989408904950226069)
                ·
                  refine ⟨163736999503542419541847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3493055989408904950226069 163736999503542419541847)
                  ·
                    rfl

theorem cell23_2869890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2869890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869890 prefixEnd_2869890 := by exact prefixLift 2869890
  have htrace : WordTrace (prefixWord ++ tailWord_2869890) baseStart_2869890 baseEnd_2869890 := by
    simpa [prefixWord, tailWord_2869890, baseEnd_2869890] using wordTrace_append hprefix tailTrace_2869890
  have hstable : (prefixWord ++ tailWord_2869890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869890).length < 2 ^ (prefixWord ++ tailWord_2869890).sum := by decide
  have hdescent : baseEnd_2869890 < baseStart_2869890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869939 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 3]
def baseStart_2869939 : Nat := 118140960795 + 2869939 * 2 ^ 59
def prefixEnd_2869939 : Nat := 4983230072969 + 3 ^ 40 * 2869939 * 2
def baseEnd_2869939 : Nat := 1473658156083952084163897

theorem tailTrace_2869939 : CollatzResearch.WordTrace tailWord_2869939 prefixEnd_2869939 1473658156083952084163897 := by
  unfold tailWord_2869939
  simp only [CollatzResearch.WordTrace]
  refine ⟨104675274749708624403748871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69783516499805749602499247 104675274749708624403748871)
  ·
    refine ⟨157012912124562936605623307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104675274749708624403748871 157012912124562936605623307)
    ·
      refine ⟨235519368186844404908434961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157012912124562936605623307 235519368186844404908434961)
      ·
        refine ⟨176639526140133303681326221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235519368186844404908434961 176639526140133303681326221)
        ·
          refine ⟨66239822302549988880497333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176639526140133303681326221 66239822302549988880497333)
          ·
            refine ⟨6209983340864061457546625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66239822302549988880497333 6209983340864061457546625)
            ·
              refine ⟨4657487505648046093159969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209983340864061457546625 4657487505648046093159969)
              ·
                refine ⟨3493115629236034569869977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657487505648046093159969 3493115629236034569869977)
                ·
                  refine ⟨2619836721927025927402483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3493115629236034569869977 2619836721927025927402483)
                  ·
                    refine ⟨3929755082890538891103725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2619836721927025927402483 3929755082890538891103725)
                    ·
                      refine ⟨1473658156083952084163897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929755082890538891103725 1473658156083952084163897)
                      ·
                        rfl

theorem cell23_2869939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_2869939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869939 prefixEnd_2869939 := by exact prefixLift 2869939
  have htrace : WordTrace (prefixWord ++ tailWord_2869939) baseStart_2869939 baseEnd_2869939 := by
    simpa [prefixWord, tailWord_2869939, baseEnd_2869939] using wordTrace_append hprefix tailTrace_2869939
  have hstable : (prefixWord ++ tailWord_2869939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869939).length < 2 ^ (prefixWord ++ tailWord_2869939).sum := by decide
  have hdescent : baseEnd_2869939 < baseStart_2869939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870002 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_2870002 : Nat := 118140960795 + 2870002 * 2 ^ 59
def prefixEnd_2870002 : Nat := 4983230072969 + 3 ^ 40 * 2870002 * 2
def baseEnd_2870002 : Nat := 163743389485020593075123

theorem tailTrace_2870002 : CollatzResearch.WordTrace tailWord_2870002 prefixEnd_2870002 163743389485020593075123 := by
  unfold tailWord_2870002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26169393137120096540823065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69785048365653590775528173 26169393137120096540823065)
  ·
    refine ⟨19627044852840072405617299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26169393137120096540823065 19627044852840072405617299)
    ·
      refine ⟨29440567279260108608425949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19627044852840072405617299 29440567279260108608425949)
      ·
        refine ⟨11040212729722540728159731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29440567279260108608425949 11040212729722540728159731)
        ·
          refine ⟨16560319094583811092239597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11040212729722540728159731 16560319094583811092239597)
          ·
            refine ⟨6210119660468929159589849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16560319094583811092239597 6210119660468929159589849)
            ·
              refine ⟨4657589745351696869692387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210119660468929159589849 4657589745351696869692387)
              ·
                refine ⟨6986384618027545304538581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657589745351696869692387 6986384618027545304538581)
                ·
                  refine ⟨163743389485020593075123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6986384618027545304538581 163743389485020593075123)
                  ·
                    rfl

theorem cell23_2870002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_2870002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870002 prefixEnd_2870002 := by exact prefixLift 2870002
  have htrace : WordTrace (prefixWord ++ tailWord_2870002) baseStart_2870002 baseEnd_2870002 := by
    simpa [prefixWord, tailWord_2870002, baseEnd_2870002] using wordTrace_append hprefix tailTrace_2870002
  have hstable : (prefixWord ++ tailWord_2870002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870002).length < 2 ^ (prefixWord ++ tailWord_2870002).sum := by decide
  have hdescent : baseEnd_2870002 < baseStart_2870002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870012 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2870012 : Nat := 118140960795 + 2870012 * 2 ^ 59
def prefixEnd_2870012 : Nat := 4983230072969 + 3 ^ 40 * 2870012 * 2
def baseEnd_2870012 : Nat := 1473695640171730298551061

theorem tailTrace_2870012 : CollatzResearch.WordTrace tailWord_2870012 prefixEnd_2870012 1473695640171730298551061 := by
  unfold tailWord_2870012
  simp only [CollatzResearch.WordTrace]
  refine ⟨52338968639222078935578145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69785291518962771914104193 52338968639222078935578145)
  ·
    refine ⟨39254226479416559201683609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52338968639222078935578145 39254226479416559201683609)
    ·
      refine ⟨29440669859562419401262707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39254226479416559201683609 29440669859562419401262707)
      ·
        refine ⟨44161004789343629101894061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29440669859562419401262707 44161004789343629101894061)
        ·
          refine ⟨16560376796003860913210273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44161004789343629101894061 16560376796003860913210273)
          ·
            refine ⟨12420282597002895684907705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16560376796003860913210273 12420282597002895684907705)
            ·
              refine ⟨9315211947752171763680779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12420282597002895684907705 9315211947752171763680779)
              ·
                refine ⟨13972817921628257645521169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315211947752171763680779 13972817921628257645521169)
                ·
                  refine ⟨10479613441221193234140877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13972817921628257645521169 10479613441221193234140877)
                  ·
                    refine ⟨3929855040457947462802829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10479613441221193234140877 3929855040457947462802829)
                    ·
                      refine ⟨1473695640171730298551061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929855040457947462802829 1473695640171730298551061)
                      ·
                        rfl

theorem cell23_2870012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2870012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870012 prefixEnd_2870012 := by exact prefixLift 2870012
  have htrace : WordTrace (prefixWord ++ tailWord_2870012) baseStart_2870012 baseEnd_2870012 := by
    simpa [prefixWord, tailWord_2870012, baseEnd_2870012] using wordTrace_append hprefix tailTrace_2870012
  have hstable : (prefixWord ++ tailWord_2870012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870012).length < 2 ^ (prefixWord ++ tailWord_2870012).sum := by decide
  have hdescent : baseEnd_2870012 < baseStart_2870012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870035 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4]
def baseStart_2870035 : Nat := 118140960795 + 2870035 * 2 ^ 59
def prefixEnd_2870035 : Nat := 4983230072969 + 3 ^ 40 * 2870035 * 2
def baseEnd_2870035 : Nat := 1473707450226783708563455

theorem tailTrace_2870035 : CollatzResearch.WordTrace tailWord_2870035 prefixEnd_2870035 1473707450226783708563455 := by
  unfold tailWord_2870035
  simp only [CollatzResearch.WordTrace]
  refine ⟨104678776157360832799243559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69785850771573888532829039 104678776157360832799243559)
  ·
    refine ⟨157018164236041249198865339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104678776157360832799243559 157018164236041249198865339)
    ·
      refine ⟨235527246354061873798298009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157018164236041249198865339 235527246354061873798298009)
      ·
        refine ⟨176645434765546405348723507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235527246354061873798298009 176645434765546405348723507)
        ·
          refine ⟨264968152148319608023085261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176645434765546405348723507 264968152148319608023085261)
          ·
            refine ⟨99363057055619853008656973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264968152148319608023085261 99363057055619853008656973)
            ·
              refine ⟨37261146395857444878246365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99363057055619853008656973 37261146395857444878246365)
              ·
                refine ⟨13972929898446541829342387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37261146395857444878246365 13972929898446541829342387)
                ·
                  refine ⟨20959394847669812744013581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13972929898446541829342387 20959394847669812744013581)
                  ·
                    refine ⟨7859773067876179779005093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20959394847669812744013581 7859773067876179779005093)
                    ·
                      refine ⟨1473707450226783708563455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7859773067876179779005093 1473707450226783708563455)
                      ·
                        rfl

theorem cell23_2870035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_2870035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870035 prefixEnd_2870035 := by exact prefixLift 2870035
  have htrace : WordTrace (prefixWord ++ tailWord_2870035) baseStart_2870035 baseEnd_2870035 := by
    simpa [prefixWord, tailWord_2870035, baseEnd_2870035] using wordTrace_append hprefix tailTrace_2870035
  have hstable : (prefixWord ++ tailWord_2870035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870035).length < 2 ^ (prefixWord ++ tailWord_2870035).sum := by decide
  have hdescent : baseEnd_2870035 < baseStart_2870035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870072 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_2870072 : Nat := 118140960795 + 2870072 * 2 ^ 59
def prefixEnd_2870072 : Nat := 4983230072969 + 3 ^ 40 * 2870072 * 2
def baseEnd_2870072 : Nat := 1473726449011000063800785

theorem tailTrace_2870072 : CollatzResearch.WordTrace tailWord_2870072 prefixEnd_2870072 1473726449011000063800785 := by
  unfold tailWord_2870072
  simp only [CollatzResearch.WordTrace]
  refine ⟨52340062829113394059170235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69786750438817858745560313 52340062829113394059170235)
  ·
    refine ⟨78510094243670091088755353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52340062829113394059170235 78510094243670091088755353)
    ·
      refine ⟨58882570682752568316566515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78510094243670091088755353 58882570682752568316566515)
      ·
        refine ⟨88323856024128852474849773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58882570682752568316566515 88323856024128852474849773)
        ·
          refine ⟨33121446009048319678068665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88323856024128852474849773 33121446009048319678068665)
          ·
            refine ⟨24841084506786239758551499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33121446009048319678068665 24841084506786239758551499)
            ·
              refine ⟨37261626760179359637827249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24841084506786239758551499 37261626760179359637827249)
              ·
                refine ⟨27946220070134519728370437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37261626760179359637827249 27946220070134519728370437)
                ·
                  refine ⟨5239916263150222449069457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27946220070134519728370437 5239916263150222449069457)
                  ·
                    refine ⟨3929937197362666836802093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239916263150222449069457 3929937197362666836802093)
                    ·
                      refine ⟨1473726449011000063800785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929937197362666836802093 1473726449011000063800785)
                      ·
                        rfl

theorem cell23_2870072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_2870072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870072 prefixEnd_2870072 := by exact prefixLift 2870072
  have htrace : WordTrace (prefixWord ++ tailWord_2870072) baseStart_2870072 baseEnd_2870072 := by
    simpa [prefixWord, tailWord_2870072, baseEnd_2870072] using wordTrace_append hprefix tailTrace_2870072
  have hstable : (prefixWord ++ tailWord_2870072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870072).length < 2 ^ (prefixWord ++ tailWord_2870072).sum := by decide
  have hdescent : baseEnd_2870072 < baseStart_2870072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870089 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_2870089 : Nat := 118140960795 + 2870089 * 2 ^ 59
def prefixEnd_2870089 : Nat := 4983230072969 + 3 ^ 40 * 2870089 * 2
def baseEnd_2870089 : Nat := 1473735178182126497288207

theorem tailTrace_2870089 : CollatzResearch.WordTrace tailWord_2870089 prefixEnd_2870089 1473735178182126497288207 := by
  unfold tailWord_2870089
  simp only [CollatzResearch.WordTrace]
  refine ⟨104680745699165200021709321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69787163799443466681139547 104680745699165200021709321)
  ·
    refine ⟨78510559274373900016281991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104680745699165200021709321 78510559274373900016281991)
    ·
      refine ⟨117765838911560850024422987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78510559274373900016281991 117765838911560850024422987)
      ·
        refine ⟨176648758367341275036634481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117765838911560850024422987 176648758367341275036634481)
        ·
          refine ⟨132486568775505956277475861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176648758367341275036634481 132486568775505956277475861)
          ·
            refine ⟨6210307911351841700506681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132486568775505956277475861 6210307911351841700506681)
            ·
              refine ⟨4657730933513881275380011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210307911351841700506681 4657730933513881275380011)
              ·
                refine ⟨6986596400270821913070017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657730933513881275380011 6986596400270821913070017)
                ·
                  refine ⟨5239947300203116434802513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6986596400270821913070017 5239947300203116434802513)
                  ·
                    refine ⟨3929960475152337326101885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239947300203116434802513 3929960475152337326101885)
                    ·
                      refine ⟨1473735178182126497288207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3929960475152337326101885 1473735178182126497288207)
                      ·
                        rfl

theorem cell23_2870089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_2870089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870089 prefixEnd_2870089 := by exact prefixLift 2870089
  have htrace : WordTrace (prefixWord ++ tailWord_2870089) baseStart_2870089 baseEnd_2870089 := by
    simpa [prefixWord, tailWord_2870089, baseEnd_2870089] using wordTrace_append hprefix tailTrace_2870089
  have hstable : (prefixWord ++ tailWord_2870089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870089).length < 2 ^ (prefixWord ++ tailWord_2870089).sum := by decide
  have hdescent : baseEnd_2870089 < baseStart_2870089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870153 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 1, 1, 3]
def baseStart_2870153 : Nat := 118140960795 + 2870153 * 2 ^ 59
def prefixEnd_2870153 : Nat := 4983230072969 + 3 ^ 40 * 2870153 * 2
def baseEnd_2870153 : Nat := 1473768040944014246887913

theorem tailTrace_2870153 : CollatzResearch.WordTrace tailWord_2870153 prefixEnd_2870153 1473768040944014246887913 := by
  unfold tailWord_2870153
  simp only [CollatzResearch.WordTrace]
  refine ⟨104683079970933338952039113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69788719980622225968026075 104683079970933338952039113)
  ·
    refine ⟨78512309978200004214029335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104683079970933338952039113 78512309978200004214029335)
    ·
      refine ⟨117768464967300006321044003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78512309978200004214029335 117768464967300006321044003)
      ·
        refine ⟨176652697450950009481566005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117768464967300006321044003 176652697450950009481566005)
        ·
          refine ⟨16561190386026563388896813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176652697450950009481566005 16561190386026563388896813)
          ·
            refine ⟨6210446394759961270836305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16561190386026563388896813 6210446394759961270836305)
            ·
              refine ⟨4657834796069970953127229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210446394759961270836305 4657834796069970953127229)
              ·
                refine ⟨1746688048526239107422711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4657834796069970953127229 1746688048526239107422711)
                ·
                  refine ⟨2620032072789358661134067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746688048526239107422711 2620032072789358661134067)
                  ·
                    refine ⟨3930048109184037991701101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2620032072789358661134067 3930048109184037991701101)
                    ·
                      refine ⟨1473768040944014246887913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3930048109184037991701101 1473768040944014246887913)
                      ·
                        rfl

theorem cell23_2870153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 1, 3].length) (baseStart_2870153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870153 prefixEnd_2870153 := by exact prefixLift 2870153
  have htrace : WordTrace (prefixWord ++ tailWord_2870153) baseStart_2870153 baseEnd_2870153 := by
    simpa [prefixWord, tailWord_2870153, baseEnd_2870153] using wordTrace_append hprefix tailTrace_2870153
  have hstable : (prefixWord ++ tailWord_2870153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870153).length < 2 ^ (prefixWord ++ tailWord_2870153).sum := by decide
  have hdescent : baseEnd_2870153 < baseStart_2870153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870176 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 3, 2, 2]
def baseStart_2870176 : Nat := 118140960795 + 2870176 * 2 ^ 59
def prefixEnd_2870176 : Nat := 4983230072969 + 3 ^ 40 * 2870176 * 2
def baseEnd_2870176 : Nat := 1473779850999067656900307

theorem tailTrace_2870176 : CollatzResearch.WordTrace tailWord_2870176 prefixEnd_2870176 1473779850999067656900307 := by
  unfold tailWord_2870176
  simp only [CollatzResearch.WordTrace]
  refine ⟨52341959424925006940063191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69789279233233342586750921 52341959424925006940063191)
  ·
    refine ⟨78512939137387510410094787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52341959424925006940063191 78512939137387510410094787)
    ·
      refine ⟨117769408706081265615142181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78512939137387510410094787 117769408706081265615142181)
      ·
        refine ⟨22081764132390237302839159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117769408706081265615142181 22081764132390237302839159)
        ·
          refine ⟨33122646198585355954258739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22081764132390237302839159 33122646198585355954258739)
          ·
            refine ⟨49683969297878033931388109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33122646198585355954258739 49683969297878033931388109)
            ·
              refine ⟨18631488486704262724270541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49683969297878033931388109 18631488486704262724270541)
              ·
                refine ⟨6986808182514098521601453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18631488486704262724270541 6986808182514098521601453)
                ·
                  refine ⟨2620053068442786945600545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6986808182514098521601453 2620053068442786945600545)
                  ·
                    refine ⟨1965039801332090209200409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620053068442786945600545 1965039801332090209200409)
                    ·
                      refine ⟨1473779850999067656900307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965039801332090209200409 1473779850999067656900307)
                      ·
                        rfl

theorem cell23_2870176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_2870176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870176 prefixEnd_2870176 := by exact prefixLift 2870176
  have htrace : WordTrace (prefixWord ++ tailWord_2870176) baseStart_2870176 baseEnd_2870176 := by
    simpa [prefixWord, tailWord_2870176, baseEnd_2870176] using wordTrace_append hprefix tailTrace_2870176
  have hstable : (prefixWord ++ tailWord_2870176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870176).length < 2 ^ (prefixWord ++ tailWord_2870176).sum := by decide
  have hdescent : baseEnd_2870176 < baseStart_2870176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870214 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2870214 : Nat := 118140960795 + 2870214 * 2 ^ 59
def prefixEnd_2870214 : Nat := 4983230072969 + 3 ^ 40 * 2870214 * 2
def baseEnd_2870214 : Nat := 1473799363263938508225133

theorem tailTrace_2870214 : CollatzResearch.WordTrace tailWord_2870214 prefixEnd_2870214 1473799363263938508225133 := by
  unfold tailWord_2870214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3271415775741010824062803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69790203215808230913339797 3271415775741010824062803)
  ·
    refine ⟨4907123663611516236094205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3271415775741010824062803 4907123663611516236094205)
    ·
      refine ⟨1840171373854318588535327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4907123663611516236094205 1840171373854318588535327)
      ·
        refine ⟨2760257060781477882802991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840171373854318588535327 2760257060781477882802991)
        ·
          refine ⟨4140385591172216824204487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2760257060781477882802991 4140385591172216824204487)
          ·
            refine ⟨6210578386758325236306731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140385591172216824204487 6210578386758325236306731)
            ·
              refine ⟨9315867580137487854460097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210578386758325236306731 9315867580137487854460097)
              ·
                refine ⟨6986900685103115890845073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9315867580137487854460097 6986900685103115890845073)
                ·
                  refine ⟨5240175513827336918133805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6986900685103115890845073 5240175513827336918133805)
                  ·
                    refine ⟨1965065817685251344300177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5240175513827336918133805 1965065817685251344300177)
                    ·
                      refine ⟨1473799363263938508225133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965065817685251344300177 1473799363263938508225133)
                      ·
                        rfl

theorem cell23_2870214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2870214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870214 prefixEnd_2870214 := by exact prefixLift 2870214
  have htrace : WordTrace (prefixWord ++ tailWord_2870214) baseStart_2870214 baseEnd_2870214 := by
    simpa [prefixWord, tailWord_2870214, baseEnd_2870214] using wordTrace_append hprefix tailTrace_2870214
  have hstable : (prefixWord ++ tailWord_2870214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870214).length < 2 ^ (prefixWord ++ tailWord_2870214).sum := by decide
  have hdescent : baseEnd_2870214 < baseStart_2870214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870221 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2870221 : Nat := 118140960795 + 2870221 * 2 ^ 59
def prefixEnd_2870221 : Nat := 4983230072969 + 3 ^ 40 * 2870221 * 2
def baseEnd_2870221 : Nat := 1473802957628519980837601

theorem tailTrace_2870221 : CollatzResearch.WordTrace tailWord_2870221 prefixEnd_2870221 1473802957628519980837601 := by
  unfold tailWord_2870221
  simp only [CollatzResearch.WordTrace]
  refine ⟨104685560134686986565514517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69790373423124657710343011 104685560134686986565514517)
  ·
    refine ⟨4907135631313452495258493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104685560134686986565514517 4907135631313452495258493)
    ·
      refine ⟨1840175861742544685721935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4907135631313452495258493 1840175861742544685721935)
      ·
        refine ⟨2760263792613817028582903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840175861742544685721935 2760263792613817028582903)
        ·
          refine ⟨4140395688920725542874355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2760263792613817028582903 4140395688920725542874355)
          ·
            refine ⟨6210593533381088314311533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140395688920725542874355 6210593533381088314311533)
            ·
              refine ⟨2328972575017908117866825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6210593533381088314311533 2328972575017908117866825)
              ·
                refine ⟨1746729431263431088400119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328972575017908117866825 1746729431263431088400119)
                ·
                  refine ⟨2620094146895146632600179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746729431263431088400119 2620094146895146632600179)
                  ·
                    refine ⟨3930141220342719948900269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2620094146895146632600179 3930141220342719948900269)
                    ·
                      refine ⟨1473802957628519980837601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3930141220342719948900269 1473802957628519980837601)
                      ·
                        rfl

theorem cell23_2870221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2870221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870221 prefixEnd_2870221 := by exact prefixLift 2870221
  have htrace : WordTrace (prefixWord ++ tailWord_2870221) baseStart_2870221 baseEnd_2870221 := by
    simpa [prefixWord, tailWord_2870221, baseEnd_2870221] using wordTrace_append hprefix tailTrace_2870221
  have hstable : (prefixWord ++ tailWord_2870221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870221).length < 2 ^ (prefixWord ++ tailWord_2870221).sum := by decide
  have hdescent : baseEnd_2870221 < baseStart_2870221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870249 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 7, 4, 2]
def baseStart_2870249 : Nat := 118140960795 + 2870249 * 2 ^ 59
def prefixEnd_2870249 : Nat := 4983230072969 + 3 ^ 40 * 2870249 * 2
def baseEnd_2870249 : Nat := 1473817335086845871287471

theorem tailTrace_2870249 : CollatzResearch.WordTrace tailWord_2870249 prefixEnd_2870249 1473817335086845871287471 := by
  unfold tailWord_2870249
  simp only [CollatzResearch.WordTrace]
  refine ⟨104686581378585547347533801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69791054252390364898355867 104686581378585547347533801)
  ·
    refine ⟨78514936033939160510650351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104686581378585547347533801 78514936033939160510650351)
    ·
      refine ⟨117772404050908740765975527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78514936033939160510650351 117772404050908740765975527)
      ·
        refine ⟨176658606076363111148963291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117772404050908740765975527 176658606076363111148963291)
        ·
          refine ⟨264987909114544666723444937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176658606076363111148963291 264987909114544666723444937)
          ·
            refine ⟨198740931835908500042583703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264987909114544666723444937 198740931835908500042583703)
            ·
              refine ⟨298111397753862750063875555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198740931835908500042583703 298111397753862750063875555)
              ·
                refine ⟨447167096630794125095813333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298111397753862750063875555 447167096630794125095813333)
                ·
                  refine ⟨10480478827284237306933125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 447167096630794125095813333 10480478827284237306933125)
                  ·
                    refine ⟨1965089780115794495049961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10480478827284237306933125 1965089780115794495049961)
                    ·
                      refine ⟨1473817335086845871287471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965089780115794495049961 1473817335086845871287471)
                      ·
                        rfl

theorem cell23_2870249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 4, 2].length) (baseStart_2870249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870249 prefixEnd_2870249 := by exact prefixLift 2870249
  have htrace : WordTrace (prefixWord ++ tailWord_2870249) baseStart_2870249 baseEnd_2870249 := by
    simpa [prefixWord, tailWord_2870249, baseEnd_2870249] using wordTrace_append hprefix tailTrace_2870249
  have hstable : (prefixWord ++ tailWord_2870249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870249).length < 2 ^ (prefixWord ++ tailWord_2870249).sum := by decide
  have hdescent : baseEnd_2870249 < baseStart_2870249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870266 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2]
def baseStart_2870266 : Nat := 118140960795 + 2870266 * 2 ^ 59
def prefixEnd_2870266 : Nat := 4983230072969 + 3 ^ 40 * 2870266 * 2
def baseEnd_2870266 : Nat := 1473826064257972304774893

theorem tailTrace_2870266 : CollatzResearch.WordTrace tailWord_2870266 prefixEnd_2870266 1473826064257972304774893 := by
  unfold tailWord_2870266
  simp only [CollatzResearch.WordTrace]
  refine ⟨26171800354880989812725663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69791467613015972833935101 26171800354880989812725663)
  ·
    refine ⟨39257700532321484719088495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26171800354880989812725663 39257700532321484719088495)
    ·
      refine ⟨58886550798482227078632743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39257700532321484719088495 58886550798482227078632743)
      ·
        refine ⟨88329826197723340617949115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58886550798482227078632743 88329826197723340617949115)
        ·
          refine ⟨132494739296585010926923673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88329826197723340617949115 132494739296585010926923673)
          ·
            refine ⟨99371054472438758195192755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132494739296585010926923673 99371054472438758195192755)
            ·
              refine ⟨149056581708658137292789133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99371054472438758195192755 149056581708658137292789133)
              ·
                refine ⟨55896218140746801484795925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149056581708658137292789133 55896218140746801484795925)
                ·
                  refine ⟨2620135225347506319599809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55896218140746801484795925 2620135225347506319599809)
                  ·
                    refine ⟨1965101419010629739699857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620135225347506319599809 1965101419010629739699857)
                    ·
                      refine ⟨1473826064257972304774893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965101419010629739699857 1473826064257972304774893)
                      ·
                        rfl

theorem cell23_2870266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_2870266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870266 prefixEnd_2870266 := by exact prefixLift 2870266
  have htrace : WordTrace (prefixWord ++ tailWord_2870266) baseStart_2870266 baseEnd_2870266 := by
    simpa [prefixWord, tailWord_2870266, baseEnd_2870266] using wordTrace_append hprefix tailTrace_2870266
  have hstable : (prefixWord ++ tailWord_2870266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870266).length < 2 ^ (prefixWord ++ tailWord_2870266).sum := by decide
  have hdescent : baseEnd_2870266 < baseStart_2870266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870279 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2870279 : Nat := 118140960795 + 2870279 * 2 ^ 59
def prefixEnd_2870279 : Nat := 4983230072969 + 3 ^ 40 * 2870279 * 2
def baseEnd_2870279 : Nat := 1473832739506480753912333

theorem tailTrace_2870279 : CollatzResearch.WordTrace tailWord_2870279 prefixEnd_2870279 1473832739506480753912333 := by
  unfold tailWord_2870279
  simp only [CollatzResearch.WordTrace]
  refine ⟨104687675568476862471125891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69791783712317908314083927 104687675568476862471125891)
  ·
    refine ⟨157031513352715293706688837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104687675568476862471125891 157031513352715293706688837)
    ·
      refine ⟨29443408753634117570004157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157031513352715293706688837 29443408753634117570004157)
      ·
        refine ⟨11041278282612794088751559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29443408753634117570004157 11041278282612794088751559)
        ·
          refine ⟨16561917423919191133127339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11041278282612794088751559 16561917423919191133127339)
          ·
            refine ⟨24842876135878786699691009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16561917423919191133127339 24842876135878786699691009)
            ·
              refine ⟨18632157101909090024768257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24842876135878786699691009 18632157101909090024768257)
              ·
                refine ⟨13974117826431817518576193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18632157101909090024768257 13974117826431817518576193)
                ·
                  refine ⟨10480588369823863138932145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13974117826431817518576193 10480588369823863138932145)
                  ·
                    refine ⟨7860441277367897354199109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10480588369823863138932145 7860441277367897354199109)
                    ·
                      refine ⟨1473832739506480753912333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7860441277367897354199109 1473832739506480753912333)
                      ·
                        rfl

theorem cell23_2870279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2870279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870279 prefixEnd_2870279 := by exact prefixLift 2870279
  have htrace : WordTrace (prefixWord ++ tailWord_2870279) baseStart_2870279 baseEnd_2870279 := by
    simpa [prefixWord, tailWord_2870279, baseEnd_2870279] using wordTrace_append hprefix tailTrace_2870279
  have hstable : (prefixWord ++ tailWord_2870279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870279).length < 2 ^ (prefixWord ++ tailWord_2870279).sum := by decide
  have hdescent : baseEnd_2870279 < baseStart_2870279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870283 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 2, 2, 2]
def baseStart_2870283 : Nat := 118140960795 + 2870283 * 2 ^ 59
def prefixEnd_2870283 : Nat := 4983230072969 + 3 ^ 40 * 2870283 * 2
def baseEnd_2870283 : Nat := 1473834793429098738262315

theorem tailTrace_2870283 : CollatzResearch.WordTrace tailWord_2870283 prefixEnd_2870283 1473834793429098738262315 := by
  unfold tailWord_2870283
  simp only [CollatzResearch.WordTrace]
  refine ⟨104687821460462371154271503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69791880973641580769514335 104687821460462371154271503)
  ·
    refine ⟨157031732190693556731407255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104687821460462371154271503 157031732190693556731407255)
    ·
      refine ⟨235547598286040335097110883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157031732190693556731407255 235547598286040335097110883)
      ·
        refine ⟨353321397429060502645666325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235547598286040335097110883 353321397429060502645666325)
        ·
          refine ⟨16561940504487211061515609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 353321397429060502645666325 16561940504487211061515609)
          ·
            refine ⟨12421455378365408296136707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16561940504487211061515609 12421455378365408296136707)
            ·
              refine ⟨18632183067548112444205061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12421455378365408296136707 18632183067548112444205061)
              ·
                refine ⟨3493534325165271083288449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18632183067548112444205061 3493534325165271083288449)
                ·
                  refine ⟨2620150743873953312466337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3493534325165271083288449 2620150743873953312466337)
                  ·
                    refine ⟨1965113057905464984349753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620150743873953312466337 1965113057905464984349753)
                    ·
                      refine ⟨1473834793429098738262315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965113057905464984349753 1473834793429098738262315)
                      ·
                        rfl

theorem cell23_2870283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 2, 2].length) (baseStart_2870283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870283 prefixEnd_2870283 := by exact prefixLift 2870283
  have htrace : WordTrace (prefixWord ++ tailWord_2870283) baseStart_2870283 baseEnd_2870283 := by
    simpa [prefixWord, tailWord_2870283, baseEnd_2870283] using wordTrace_append hprefix tailTrace_2870283
  have hstable : (prefixWord ++ tailWord_2870283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870283).length < 2 ^ (prefixWord ++ tailWord_2870283).sum := by decide
  have hdescent : baseEnd_2870283 < baseStart_2870283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870339 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 4]
def baseStart_2870339 : Nat := 118140960795 + 2870339 * 2 ^ 59
def prefixEnd_2870339 : Nat := 4983230072969 + 3 ^ 40 * 2870339 * 2
def baseEnd_2870339 : Nat := 1473863548345750519162057

theorem tailTrace_2870339 : CollatzResearch.WordTrace tailWord_2870339 prefixEnd_2870339 1473863548345750519162057 := by
  unfold tailWord_2870339
  simp only [CollatzResearch.WordTrace]
  refine ⟨104689863948259492718310071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69793242632172995145540047 104689863948259492718310071)
  ·
    refine ⟨157034795922389239077465107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104689863948259492718310071 157034795922389239077465107)
    ·
      refine ⟨235552193883583858616197661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157034795922389239077465107 235552193883583858616197661)
      ·
        refine ⟨88332072706343946981074123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235552193883583858616197661 88332072706343946981074123)
        ·
          refine ⟨132498109059515920471611185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88332072706343946981074123 132498109059515920471611185)
          ·
            refine ⟨99373581794636940353708389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132498109059515920471611185 99373581794636940353708389)
            ·
              refine ⟨18632546586494426316320323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99373581794636940353708389 18632546586494426316320323)
              ·
                refine ⟨27948819879741639474480485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18632546586494426316320323 27948819879741639474480485)
                ·
                  refine ⟨5240403727451557401465091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27948819879741639474480485 5240403727451557401465091)
                  ·
                    refine ⟨7860605591177336102197637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5240403727451557401465091 7860605591177336102197637)
                    ·
                      refine ⟨1473863548345750519162057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7860605591177336102197637 1473863548345750519162057)
                      ·
                        rfl

theorem cell23_2870339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_2870339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870339 prefixEnd_2870339 := by exact prefixLift 2870339
  have htrace : WordTrace (prefixWord ++ tailWord_2870339) baseStart_2870339 baseEnd_2870339 := by
    simpa [prefixWord, tailWord_2870339, baseEnd_2870339] using wordTrace_append hprefix tailTrace_2870339
  have hstable : (prefixWord ++ tailWord_2870339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870339).length < 2 ^ (prefixWord ++ tailWord_2870339).sum := by decide
  have hdescent : baseEnd_2870339 < baseStart_2870339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870393 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2870393 : Nat := 118140960795 + 2870393 * 2 ^ 59
def prefixEnd_2870393 : Nat := 4983230072969 + 3 ^ 40 * 2870393 * 2
def baseEnd_2870393 : Nat := 1473891276301093307886809

theorem tailTrace_2870393 : CollatzResearch.WordTrace tailWord_2870393 prefixEnd_2870393 1473891276301093307886809 := by
  unfold tailWord_2870393
  simp only [CollatzResearch.WordTrace]
  refine ⟨104691833490063859940775833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69794555660042573293850555 104691833490063859940775833)
  ·
    refine ⟨78518875117547894955581875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104691833490063859940775833 78518875117547894955581875)
    ·
      refine ⟨117778312676321842433372813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78518875117547894955581875 117778312676321842433372813)
      ·
        refine ⟨44166867253620690912514805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117778312676321842433372813 44166867253620690912514805)
        ·
          refine ⟨4140643805026939773048263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44166867253620690912514805 4140643805026939773048263)
          ·
            refine ⟨6210965707540409659572395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140643805026939773048263 6210965707540409659572395)
            ·
              refine ⟨9316448561310614489358593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210965707540409659572395 9316448561310614489358593)
              ·
                refine ⟨6987336420982960867018945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9316448561310614489358593 6987336420982960867018945)
                ·
                  refine ⟨5240502315737220650264209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6987336420982960867018945 5240502315737220650264209)
                  ·
                    refine ⟨3930376736802915487698157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240502315737220650264209 3930376736802915487698157)
                    ·
                      refine ⟨1473891276301093307886809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3930376736802915487698157 1473891276301093307886809)
                      ·
                        rfl

theorem cell23_2870393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2870393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870393 prefixEnd_2870393 := by exact prefixLift 2870393
  have htrace : WordTrace (prefixWord ++ tailWord_2870393) baseStart_2870393 baseEnd_2870393 := by
    simpa [prefixWord, tailWord_2870393, baseEnd_2870393] using wordTrace_append hprefix tailTrace_2870393
  have hstable : (prefixWord ++ tailWord_2870393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870393).length < 2 ^ (prefixWord ++ tailWord_2870393).sum := by decide
  have hdescent : baseEnd_2870393 < baseStart_2870393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870416 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 1, 5, 2]
def baseStart_2870416 : Nat := 118140960795 + 2870416 * 2 ^ 59
def prefixEnd_2870416 : Nat := 4983230072969 + 3 ^ 40 * 2870416 * 2
def baseEnd_2870416 : Nat := 1473903086356146717899203

theorem tailTrace_2870416 : CollatzResearch.WordTrace tailWord_2870416 prefixEnd_2870416 1473903086356146717899203 := by
  unfold tailWord_2870416
  simp only [CollatzResearch.WordTrace]
  refine ⟨52346336184490267434431551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69795114912653689912575401 52346336184490267434431551)
  ·
    refine ⟨78519504276735401151647327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52346336184490267434431551 78519504276735401151647327)
    ·
      refine ⟨117779256415103101727470991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78519504276735401151647327 117779256415103101727470991)
      ·
        refine ⟨176668884622654652591206487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117779256415103101727470991 176668884622654652591206487)
        ·
          refine ⟨265003326933981978886809731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176668884622654652591206487 265003326933981978886809731)
          ·
            refine ⟨397504990400972968330214597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265003326933981978886809731 397504990400972968330214597)
            ·
              refine ⟨74532185700182431561915237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397504990400972968330214597 74532185700182431561915237)
              ·
                refine ⟨13974784818784205917859107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74532185700182431561915237 13974784818784205917859107)
                ·
                  refine ⟨20962177228176308876788661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13974784818784205917859107 20962177228176308876788661)
                  ·
                    refine ⟨1965204115141528957198937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20962177228176308876788661 1965204115141528957198937)
                    ·
                      refine ⟨1473903086356146717899203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965204115141528957198937 1473903086356146717899203)
                      ·
                        rfl

theorem cell23_2870416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 5, 2].length) (baseStart_2870416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870416 prefixEnd_2870416 := by exact prefixLift 2870416
  have htrace : WordTrace (prefixWord ++ tailWord_2870416) baseStart_2870416 baseEnd_2870416 := by
    simpa [prefixWord, tailWord_2870416, baseEnd_2870416] using wordTrace_append hprefix tailTrace_2870416
  have hstable : (prefixWord ++ tailWord_2870416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870416).length < 2 ^ (prefixWord ++ tailWord_2870416).sum := by decide
  have hdescent : baseEnd_2870416 < baseStart_2870416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870457 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 1, 1, 3]
def baseStart_2870457 : Nat := 118140960795 + 2870457 * 2 ^ 59
def prefixEnd_2870457 : Nat := 4983230072969 + 3 ^ 40 * 2870457 * 2
def baseEnd_2870457 : Nat := 1473924139062981057486515

theorem tailTrace_2870457 : CollatzResearch.WordTrace tailWord_2870457 prefixEnd_2870457 1473924139062981057486515 := by
  unfold tailWord_2870457
  simp only [CollatzResearch.WordTrace]
  refine ⟨104694167761831998871105625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69796111841221332580737083 104694167761831998871105625)
  ·
    refine ⟨78520625821373999153329219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104694167761831998871105625 78520625821373999153329219)
    ·
      refine ⟨117780938732060998729993829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78520625821373999153329219 117780938732060998729993829)
      ·
        refine ⟨22083926012261437261873843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117780938732060998729993829 22083926012261437261873843)
        ·
          refine ⟨33125889018392155892810765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22083926012261437261873843 33125889018392155892810765)
          ·
            refine ⟨12422208381897058459804037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33125889018392155892810765 12422208381897058459804037)
            ·
              refine ⟨2329164071605698461213257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12422208381897058459804037 2329164071605698461213257)
              ·
                refine ⟨1746873053704273845909943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329164071605698461213257 1746873053704273845909943)
                ·
                  refine ⟨2620309580556410768864915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746873053704273845909943 2620309580556410768864915)
                  ·
                    refine ⟨3930464370834616153297373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2620309580556410768864915 3930464370834616153297373)
                    ·
                      refine ⟨1473924139062981057486515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3930464370834616153297373 1473924139062981057486515)
                      ·
                        rfl

theorem cell23_2870457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_2870457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870457 prefixEnd_2870457 := by exact prefixLift 2870457
  have htrace : WordTrace (prefixWord ++ tailWord_2870457) baseStart_2870457 baseEnd_2870457 := by
    simpa [prefixWord, tailWord_2870457, baseEnd_2870457] using wordTrace_append hprefix tailTrace_2870457
  have hstable : (prefixWord ++ tailWord_2870457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870457).length < 2 ^ (prefixWord ++ tailWord_2870457).sum := by decide
  have hdescent : baseEnd_2870457 < baseStart_2870457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870459 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6]
def baseStart_2870459 : Nat := 118140960795 + 2870459 * 2 ^ 59
def prefixEnd_2870459 : Nat := 4983230072969 + 3 ^ 40 * 2870459 * 2
def baseEnd_2870459 : Nat := 1473925166024290049661505

theorem tailTrace_2870459 : CollatzResearch.WordTrace tailWord_2870459 prefixEnd_2870459 1473925166024290049661505 := by
  unfold tailWord_2870459
  simp only [CollatzResearch.WordTrace]
  refine ⟨104694240707824753212678431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69796160471883168808452287 104694240707824753212678431)
  ·
    refine ⟨157041361061737129819017647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104694240707824753212678431 157041361061737129819017647)
    ·
      refine ⟨235562041592605694728526471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157041361061737129819017647 235562041592605694728526471)
      ·
        refine ⟨353343062388908542092789707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235562041592605694728526471 353343062388908542092789707)
        ·
          refine ⟨530014593583362813139184561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353343062388908542092789707 530014593583362813139184561)
          ·
            refine ⟨397510945187522109854388421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530014593583362813139184561 397510945187522109854388421)
            ·
              refine ⟨74533302222660395597697829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397510945187522109854388421 74533302222660395597697829)
              ·
                refine ⟨13974994166748824174568343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74533302222660395597697829 13974994166748824174568343)
                ·
                  refine ⟨20962491250123236261852515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13974994166748824174568343 20962491250123236261852515)
                  ·
                    refine ⟨31443736875184854392778773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20962491250123236261852515 31443736875184854392778773)
                    ·
                      refine ⟨1473925166024290049661505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31443736875184854392778773 1473925166024290049661505)
                      ·
                        rfl

theorem cell23_2870459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_2870459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870459 prefixEnd_2870459 := by exact prefixLift 2870459
  have htrace : WordTrace (prefixWord ++ tailWord_2870459) baseStart_2870459 baseEnd_2870459 := by
    simpa [prefixWord, tailWord_2870459, baseEnd_2870459] using wordTrace_append hprefix tailTrace_2870459
  have hstable : (prefixWord ++ tailWord_2870459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870459).length < 2 ^ (prefixWord ++ tailWord_2870459).sum := by decide
  have hdescent : baseEnd_2870459 < baseStart_2870459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870484 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2870484 : Nat := 118140960795 + 2870484 * 2 ^ 59
def prefixEnd_2870484 : Nat := 4983230072969 + 3 ^ 40 * 2870484 * 2
def baseEnd_2870484 : Nat := 1473938003040652451848891

theorem tailTrace_2870484 : CollatzResearch.WordTrace tailWord_2870484 prefixEnd_2870484 1473938003040652451848891 := by
  unfold tailWord_2870484
  simp only [CollatzResearch.WordTrace]
  refine ⟨52347576266367091241169253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69796768355156121654892337 52347576266367091241169253)
  ·
    refine ⟨9815170549943829607719235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52347576266367091241169253 9815170549943829607719235)
    ·
      refine ⟨14722755824915744411578853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9815170549943829607719235 14722755824915744411578853)
      ·
        refine ⟨2760516717171702077171035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14722755824915744411578853 2760516717171702077171035)
        ·
          refine ⟨4140775075757553115756553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2760516717171702077171035 4140775075757553115756553)
          ·
            refine ⟨3105581306818164836817415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4140775075757553115756553 3105581306818164836817415)
            ·
              refine ⟨4658371960227247255226123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3105581306818164836817415 4658371960227247255226123)
              ·
                refine ⟨6987557940340870882839185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658371960227247255226123 6987557940340870882839185)
                ·
                  refine ⟨5240668455255653162129389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6987557940340870882839185 5240668455255653162129389)
                  ·
                    refine ⟨1965250670720869935798521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5240668455255653162129389 1965250670720869935798521)
                    ·
                      refine ⟨1473938003040652451848891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965250670720869935798521 1473938003040652451848891)
                      ·
                        rfl

theorem cell23_2870484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2870484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870484 prefixEnd_2870484 := by exact prefixLift 2870484
  have htrace : WordTrace (prefixWord ++ tailWord_2870484) baseStart_2870484 baseEnd_2870484 := by
    simpa [prefixWord, tailWord_2870484, baseEnd_2870484] using wordTrace_append hprefix tailTrace_2870484
  have hstable : (prefixWord ++ tailWord_2870484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870484).length < 2 ^ (prefixWord ++ tailWord_2870484).sum := by decide
  have hdescent : baseEnd_2870484 < baseStart_2870484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870497 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_2870497 : Nat := 118140960795 + 2870497 * 2 ^ 59
def prefixEnd_2870497 : Nat := 4983230072969 + 3 ^ 40 * 2870497 * 2
def baseEnd_2870497 : Nat := 1473944678289160900986331

theorem tailTrace_2870497 : CollatzResearch.WordTrace tailWord_2870497 prefixEnd_2870497 1473944678289160900986331 := by
  unfold tailWord_2870497
  simp only [CollatzResearch.WordTrace]
  refine ⟨104695626681687085702561745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69797084454458057135041163 104695626681687085702561745)
  ·
    refine ⟨78521720011265314276921309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104695626681687085702561745 78521720011265314276921309)
    ·
      refine ⟨29445645004224492853845491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78521720011265314276921309 29445645004224492853845491)
      ·
        refine ⟨44168467506336739280768237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29445645004224492853845491 44168467506336739280768237)
        ·
          refine ⟨16563175314876277230288089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44168467506336739280768237 16563175314876277230288089)
          ·
            refine ⟨12422381486157207922716067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16563175314876277230288089 12422381486157207922716067)
            ·
              refine ⟨18633572229235811884074101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12422381486157207922716067 18633572229235811884074101)
              ·
                refine ⟨1746897396490857364131947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18633572229235811884074101 1746897396490857364131947)
                ·
                  refine ⟨2620346094736286046197921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746897396490857364131947 2620346094736286046197921)
                  ·
                    refine ⟨1965259571052214534648441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620346094736286046197921 1965259571052214534648441)
                    ·
                      refine ⟨1473944678289160900986331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965259571052214534648441 1473944678289160900986331)
                      ·
                        rfl

theorem cell23_2870497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_2870497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870497 prefixEnd_2870497 := by exact prefixLift 2870497
  have htrace : WordTrace (prefixWord ++ tailWord_2870497) baseStart_2870497 baseEnd_2870497 := by
    simpa [prefixWord, tailWord_2870497, baseEnd_2870497] using wordTrace_append hprefix tailTrace_2870497
  have hstable : (prefixWord ++ tailWord_2870497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870497).length < 2 ^ (prefixWord ++ tailWord_2870497).sum := by decide
  have hdescent : baseEnd_2870497 < baseStart_2870497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870500 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_2870500 : Nat := 118140960795 + 2870500 * 2 ^ 59
def prefixEnd_2870500 : Nat := 4983230072969 + 3 ^ 40 * 2870500 * 2
def baseEnd_2870500 : Nat := 1473946218731124389248817

theorem tailTrace_2870500 : CollatzResearch.WordTrace tailWord_2870500 prefixEnd_2870500 1473946218731124389248817 := by
  unfold tailWord_2870500
  simp only [CollatzResearch.WordTrace]
  refine ⟨52347868050338108607460477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69797157400450811476613969 52347868050338108607460477)
  ·
    refine ⟨19630450518876790727797679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52347868050338108607460477 19630450518876790727797679)
    ·
      refine ⟨29445675778315186091696519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19630450518876790727797679 29445675778315186091696519)
      ·
        refine ⟨44168513667472779137544779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29445675778315186091696519 44168513667472779137544779)
        ·
          refine ⟨66252770501209168706317169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44168513667472779137544779 66252770501209168706317169)
          ·
            refine ⟨49689577875906876529737877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66252770501209168706317169 49689577875906876529737877)
            ·
              refine ⟨2329198962933134837331463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49689577875906876529737877 2329198962933134837331463)
              ·
                refine ⟨3493798444399702255997195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329198962933134837331463 3493798444399702255997195)
                ·
                  refine ⟨5240697666599553383995793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493798444399702255997195 5240697666599553383995793)
                  ·
                    refine ⟨3930523249949665037996845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240697666599553383995793 3930523249949665037996845)
                    ·
                      refine ⟨1473946218731124389248817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3930523249949665037996845 1473946218731124389248817)
                      ·
                        rfl

theorem cell23_2870500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_2870500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870500 prefixEnd_2870500 := by exact prefixLift 2870500
  have htrace : WordTrace (prefixWord ++ tailWord_2870500) baseStart_2870500 baseEnd_2870500 := by
    simpa [prefixWord, tailWord_2870500, baseEnd_2870500] using wordTrace_append hprefix tailTrace_2870500
  have hstable : (prefixWord ++ tailWord_2870500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870500).length < 2 ^ (prefixWord ++ tailWord_2870500).sum := by decide
  have hdescent : baseEnd_2870500 < baseStart_2870500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870540 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 1, 3, 2]
def baseStart_2870540 : Nat := 118140960795 + 2870540 * 2 ^ 59
def prefixEnd_2870540 : Nat := 4983230072969 + 3 ^ 40 * 2870540 * 2
def baseEnd_2870540 : Nat := 1473966757957304232748633

theorem tailTrace_2870540 : CollatzResearch.WordTrace tailWord_2870540 prefixEnd_2870540 1473966757957304232748633 := by
  unfold tailWord_2870540
  simp only [CollatzResearch.WordTrace]
  refine ⟨52348597510265652023188537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69798130013687536030918049 52348597510265652023188537)
  ·
    refine ⟨39261448132699239017391403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52348597510265652023188537 39261448132699239017391403)
    ·
      refine ⟨58892172199048858526087105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39261448132699239017391403 58892172199048858526087105)
      ·
        refine ⟨44169129149286643894565329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58892172199048858526087105 44169129149286643894565329)
        ·
          refine ⟨33126846861964982920923997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44169129149286643894565329 33126846861964982920923997)
          ·
            refine ⟨12422567573236868595346499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33126846861964982920923997 12422567573236868595346499)
            ·
              refine ⟨18633851359855302893019749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12422567573236868595346499 18633851359855302893019749)
              ·
                refine ⟨3493847129972869292441203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18633851359855302893019749 3493847129972869292441203)
                ·
                  refine ⟨5240770694959303938661805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493847129972869292441203 5240770694959303938661805)
                  ·
                    refine ⟨1965289010609738976998177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5240770694959303938661805 1965289010609738976998177)
                    ·
                      refine ⟨1473966757957304232748633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965289010609738976998177 1473966757957304232748633)
                      ·
                        rfl

theorem cell23_2870540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_2870540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870540 prefixEnd_2870540 := by exact prefixLift 2870540
  have htrace : WordTrace (prefixWord ++ tailWord_2870540) baseStart_2870540 baseEnd_2870540 := by
    simpa [prefixWord, tailWord_2870540, baseEnd_2870540] using wordTrace_append hprefix tailTrace_2870540
  have hstable : (prefixWord ++ tailWord_2870540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870540).length < 2 ^ (prefixWord ++ tailWord_2870540).sum := by decide
  have hdescent : baseEnd_2870540 < baseStart_2870540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870556 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2870556 : Nat := 118140960795 + 2870556 * 2 ^ 59
def prefixEnd_2870556 : Nat := 4983230072969 + 3 ^ 40 * 2870556 * 2
def baseEnd_2870556 : Nat := 1473974973647776170148559

theorem tailTrace_2870556 : CollatzResearch.WordTrace tailWord_2870556 prefixEnd_2870556 1473974973647776170148559 := by
  unfold tailWord_2870556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52348889294236669389479761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69798519058982225852639681 52348889294236669389479761)
  ·
    refine ⟨39261666970677502042109821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52348889294236669389479761 39261666970677502042109821)
    ·
      refine ⟨14723125114004063265791183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39261666970677502042109821 14723125114004063265791183)
      ·
        refine ⟨22084687671006094898686775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14723125114004063265791183 22084687671006094898686775)
        ·
          refine ⟨33127031506509142348030163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22084687671006094898686775 33127031506509142348030163)
          ·
            refine ⟨49690547259763713522045245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33127031506509142348030163 49690547259763713522045245)
            ·
              refine ⟨18633955222411392570766967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49690547259763713522045245 18633955222411392570766967)
              ·
                refine ⟨27950932833617088856150451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18633955222411392570766967 27950932833617088856150451)
                ·
                  refine ⟨41926399250425633284225677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27950932833617088856150451 41926399250425633284225677)
                  ·
                    refine ⟨15722399718909612481584629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41926399250425633284225677 15722399718909612481584629)
                    ·
                      refine ⟨1473974973647776170148559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15722399718909612481584629 1473974973647776170148559)
                      ·
                        rfl

theorem cell23_2870556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2870556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870556 prefixEnd_2870556 := by exact prefixLift 2870556
  have htrace : WordTrace (prefixWord ++ tailWord_2870556) baseStart_2870556 baseEnd_2870556 := by
    simpa [prefixWord, tailWord_2870556, baseEnd_2870556] using wordTrace_append hprefix tailTrace_2870556
  have hstable : (prefixWord ++ tailWord_2870556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870556).length < 2 ^ (prefixWord ++ tailWord_2870556).sum := by decide
  have hdescent : baseEnd_2870556 < baseStart_2870556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870557 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_2870557 : Nat := 118140960795 + 2870557 * 2 ^ 59
def prefixEnd_2870557 : Nat := 4983230072969 + 3 ^ 40 * 2870557 * 2
def baseEnd_2870557 : Nat := 1473975487128430666236055

theorem tailTrace_2870557 : CollatzResearch.WordTrace tailWord_2870557 prefixEnd_2870557 1473975487128430666236055 := by
  unfold tailWord_2870557
  simp only [CollatzResearch.WordTrace]
  refine ⟨104697815061469715949745925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69798543374313143966497283 104697815061469715949745925)
  ·
    refine ⟨19630840324025571740577361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104697815061469715949745925 19630840324025571740577361)
    ·
      refine ⟨14723130243019178805433021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19630840324025571740577361 14723130243019178805433021)
      ·
        refine ⟨5521173841132192052037383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14723130243019178805433021 5521173841132192052037383)
        ·
          refine ⟨8281760761698288078056075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521173841132192052037383 8281760761698288078056075)
          ·
            refine ⟨12422641142547432117084113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8281760761698288078056075 12422641142547432117084113)
            ·
              refine ⟨9316980856910574087813085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12422641142547432117084113 9316980856910574087813085)
              ·
                refine ⟨3493867821341465282929907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9316980856910574087813085 3493867821341465282929907)
                ·
                  refine ⟨5240801732012197924394861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493867821341465282929907 5240801732012197924394861)
                  ·
                    refine ⟨1965300649504574221648073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5240801732012197924394861 1965300649504574221648073)
                    ·
                      refine ⟨1473975487128430666236055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965300649504574221648073 1473975487128430666236055)
                      ·
                        rfl

theorem cell23_2870557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_2870557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870557 prefixEnd_2870557 := by exact prefixLift 2870557
  have htrace : WordTrace (prefixWord ++ tailWord_2870557) baseStart_2870557 baseEnd_2870557 := by
    simpa [prefixWord, tailWord_2870557, baseEnd_2870557] using wordTrace_append hprefix tailTrace_2870557
  have hstable : (prefixWord ++ tailWord_2870557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870557).length < 2 ^ (prefixWord ++ tailWord_2870557).sum := by decide
  have hdescent : baseEnd_2870557 < baseStart_2870557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870616 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2870616 : Nat := 118140960795 + 2870616 * 2 ^ 59
def prefixEnd_2870616 : Nat := 4983230072969 + 3 ^ 40 * 2870616 * 2
def baseEnd_2870616 : Nat := 1474005782487045935398283

theorem tailTrace_2870616 : CollatzResearch.WordTrace tailWord_2870616 prefixEnd_2870616 1474005782487045935398283 := by
  unfold tailWord_2870616
  simp only [CollatzResearch.WordTrace]
  refine ⟨52349983484127984513071851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69799977978837312684095801 52349983484127984513071851)
  ·
    refine ⟨78524975226191976769607777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52349983484127984513071851 78524975226191976769607777)
    ·
      refine ⟨58893731419643982577205833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78524975226191976769607777 58893731419643982577205833)
      ·
        refine ⟨44170298564732986932904375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58893731419643982577205833 44170298564732986932904375)
        ·
          refine ⟨66255447847099480399356563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44170298564732986932904375 66255447847099480399356563)
          ·
            refine ⟨99383171770649220599034845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66255447847099480399356563 99383171770649220599034845)
            ·
              refine ⟨37268689413993457724638067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99383171770649220599034845 37268689413993457724638067)
              ·
                refine ⟨55903034120990186586957101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37268689413993457724638067 55903034120990186586957101)
                ·
                  refine ⟨20963637795371319970108913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55903034120990186586957101 20963637795371319970108913)
                  ·
                    refine ⟨15722728346528489977581685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20963637795371319970108913 15722728346528489977581685)
                    ·
                      refine ⟨1474005782487045935398283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15722728346528489977581685 1474005782487045935398283)
                      ·
                        rfl

theorem cell23_2870616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2870616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870616 prefixEnd_2870616 := by exact prefixLift 2870616
  have htrace : WordTrace (prefixWord ++ tailWord_2870616) baseStart_2870616 baseEnd_2870616 := by
    simpa [prefixWord, tailWord_2870616, baseEnd_2870616] using wordTrace_append hprefix tailTrace_2870616
  have hstable : (prefixWord ++ tailWord_2870616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870616).length < 2 ^ (prefixWord ++ tailWord_2870616).sum := by decide
  have hdescent : baseEnd_2870616 < baseStart_2870616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870627 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 5]
def baseStart_2870627 : Nat := 118140960795 + 2870627 * 2 ^ 59
def prefixEnd_2870627 : Nat := 4983230072969 + 3 ^ 40 * 2870627 * 2
def baseEnd_2870627 : Nat := 163779047863805043595637

theorem tailTrace_2870627 : CollatzResearch.WordTrace tailWord_2870627 prefixEnd_2870627 163779047863805043595637 := by
  unfold tailWord_2870627
  simp only [CollatzResearch.WordTrace]
  refine ⟨104700368171216117904794135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69800245447477411936529423 104700368171216117904794135)
  ·
    refine ⟨157050552256824176857191203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104700368171216117904794135 157050552256824176857191203)
    ·
      refine ⟨235575828385236265285786805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157050552256824176857191203 235575828385236265285786805)
      ·
        refine ⟨22085233911115899870542513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235575828385236265285786805 22085233911115899870542513)
        ·
          refine ⟨16563925433336924902906885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22085233911115899870542513 16563925433336924902906885)
          ·
            refine ⟨3105736018750673419295041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16563925433336924902906885 3105736018750673419295041)
            ·
              refine ⟨2329302014063005064471281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3105736018750673419295041 2329302014063005064471281)
              ·
                refine ⟨1746976510547253798353461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329302014063005064471281 1746976510547253798353461)
                ·
                  refine ⟨163779047863805043595637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1746976510547253798353461 163779047863805043595637)
                  ·
                    rfl

theorem cell23_2870627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 5].length) (baseStart_2870627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870627 prefixEnd_2870627 := by exact prefixLift 2870627
  have htrace : WordTrace (prefixWord ++ tailWord_2870627) baseStart_2870627 baseEnd_2870627 := by
    simpa [prefixWord, tailWord_2870627, baseEnd_2870627] using wordTrace_append hprefix tailTrace_2870627
  have hstable : (prefixWord ++ tailWord_2870627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870627).length < 2 ^ (prefixWord ++ tailWord_2870627).sum := by decide
  have hdescent : baseEnd_2870627 < baseStart_2870627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870656 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_2870656 : Nat := 118140960795 + 2870656 * 2 ^ 59
def prefixEnd_2870656 : Nat := 4983230072969 + 3 ^ 40 * 2870656 * 2
def baseEnd_2870656 : Nat := 1474026321713225778898099

theorem tailTrace_2870656 : CollatzResearch.WordTrace tailWord_2870656 prefixEnd_2870656 1474026321713225778898099 := by
  unfold tailWord_2870656
  simp only [CollatzResearch.WordTrace]
  refine ⟨52350712944055527928799911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69800950592074037238399881 52350712944055527928799911)
  ·
    refine ⟨78526069416083291893199867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52350712944055527928799911 78526069416083291893199867)
    ·
      refine ⟨117789104124124937839799801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78526069416083291893199867 117789104124124937839799801)
      ·
        refine ⟨88341828093093703379849851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117789104124124937839799801 88341828093093703379849851)
        ·
          refine ⟨132512742139640555069774777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88341828093093703379849851 132512742139640555069774777)
          ·
            refine ⟨99384556604730416302331083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132512742139640555069774777 99384556604730416302331083)
            ·
              refine ⟨149076834907095624453496625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99384556604730416302331083 149076834907095624453496625)
              ·
                refine ⟨111807626180321718340122469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149076834907095624453496625 111807626180321718340122469)
                ·
                  refine ⟨20963929908810322188772963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111807626180321718340122469 20963929908810322188772963)
                  ·
                    refine ⟨31445894863215483283159445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20963929908810322188772963 31445894863215483283159445)
                    ·
                      refine ⟨1474026321713225778898099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31445894863215483283159445 1474026321713225778898099)
                      ·
                        rfl

theorem cell23_2870656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_2870656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870656 prefixEnd_2870656 := by exact prefixLift 2870656
  have htrace : WordTrace (prefixWord ++ tailWord_2870656) baseStart_2870656 baseEnd_2870656 := by
    simpa [prefixWord, tailWord_2870656, baseEnd_2870656] using wordTrace_append hprefix tailTrace_2870656
  have hstable : (prefixWord ++ tailWord_2870656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870656).length < 2 ^ (prefixWord ++ tailWord_2870656).sum := by decide
  have hdescent : baseEnd_2870656 < baseStart_2870656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870657 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2870657 : Nat := 118140960795 + 2870657 * 2 ^ 59
def prefixEnd_2870657 : Nat := 4983230072969 + 3 ^ 40 * 2870657 * 2
def baseEnd_2870657 : Nat := 491342278397960091661865

theorem tailTrace_2870657 : CollatzResearch.WordTrace tailWord_2870657 prefixEnd_2870657 491342278397960091661865 := by
  unfold tailWord_2870657
  simp only [CollatzResearch.WordTrace]
  refine ⟨104701462361107433028386225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69800974907404955352257483 104701462361107433028386225)
  ·
    refine ⟨78526096770830574771289669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104701462361107433028386225 78526096770830574771289669)
    ·
      refine ⟨14723643144530732769616813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78526096770830574771289669 14723643144530732769616813)
      ·
        refine ⟨5521366179199024788606305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14723643144530732769616813 5521366179199024788606305)
        ·
          refine ⟨4141024634399268591454729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5521366179199024788606305 4141024634399268591454729)
          ·
            refine ⟨3105768475799451443591047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4141024634399268591454729 3105768475799451443591047)
            ·
              refine ⟨4658652713699177165386571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3105768475799451443591047 4658652713699177165386571)
              ·
                refine ⟨6987979070548765748079857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658652713699177165386571 6987979070548765748079857)
                ·
                  refine ⟨5240984302911574311059893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6987979070548765748079857 5240984302911574311059893)
                  ·
                    refine ⟨491342278397960091661865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5240984302911574311059893 491342278397960091661865)
                    ·
                      rfl

theorem cell23_2870657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2870657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870657 prefixEnd_2870657 := by exact prefixLift 2870657
  have htrace : WordTrace (prefixWord ++ tailWord_2870657) baseStart_2870657 baseEnd_2870657 := by
    simpa [prefixWord, tailWord_2870657, baseEnd_2870657] using wordTrace_append hprefix tailTrace_2870657
  have hstable : (prefixWord ++ tailWord_2870657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870657).length < 2 ^ (prefixWord ++ tailWord_2870657).sum := by decide
  have hdescent : baseEnd_2870657 < baseStart_2870657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870660 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2870660 : Nat := 118140960795 + 2870660 * 2 ^ 59
def prefixEnd_2870660 : Nat := 4983230072969 + 3 ^ 40 * 2870660 * 2
def baseEnd_2870660 : Nat := 1474028375635843763248081

theorem tailTrace_2870660 : CollatzResearch.WordTrace tailWord_2870660 prefixEnd_2870660 1474028375635843763248081 := by
  unfold tailWord_2870660
  simp only [CollatzResearch.WordTrace]
  refine ⟨52350785890048282270372717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69801047853397709693830289 52350785890048282270372717)
  ·
    refine ⟨19631544708768105851389769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52350785890048282270372717 19631544708768105851389769)
    ·
      refine ⟨14723658531576079388542327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19631544708768105851389769 14723658531576079388542327)
      ·
        refine ⟨22085487797364119082813491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14723658531576079388542327 22085487797364119082813491)
        ·
          refine ⟨33128231696046178624220237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22085487797364119082813491 33128231696046178624220237)
          ·
            refine ⟨12423086886017316984082589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33128231696046178624220237 12423086886017316984082589)
            ·
              refine ⟨4658657582256493869030971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12423086886017316984082589 4658657582256493869030971)
              ·
                refine ⟨6987986373384740803546457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658657582256493869030971 6987986373384740803546457)
                ·
                  refine ⟨5240989780038555602659843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6987986373384740803546457 5240989780038555602659843)
                  ·
                    refine ⟨7861484670057833403989765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5240989780038555602659843 7861484670057833403989765)
                    ·
                      refine ⟨1474028375635843763248081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7861484670057833403989765 1474028375635843763248081)
                      ·
                        rfl

theorem cell23_2870660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2870660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870660 prefixEnd_2870660 := by exact prefixLift 2870660
  have htrace : WordTrace (prefixWord ++ tailWord_2870660) baseStart_2870660 baseEnd_2870660 := by
    simpa [prefixWord, tailWord_2870660, baseEnd_2870660] using wordTrace_append hprefix tailTrace_2870660
  have hstable : (prefixWord ++ tailWord_2870660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870660).length < 2 ^ (prefixWord ++ tailWord_2870660).sum := by decide
  have hdescent : baseEnd_2870660 < baseStart_2870660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870687 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 1, 4]
def baseStart_2870687 : Nat := 118140960795 + 2870687 * 2 ^ 59
def prefixEnd_2870687 : Nat := 4983230072969 + 3 ^ 40 * 2870687 * 2
def baseEnd_2870687 : Nat := 491347413204505052536819

theorem tailTrace_2870687 : CollatzResearch.WordTrace tailWord_2870687 prefixEnd_2870687 491347413204505052536819 := by
  unfold tailWord_2870687
  simp only [CollatzResearch.WordTrace]
  refine ⟨104702556550998748151978315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69801704367332498767985543 104702556550998748151978315)
  ·
    refine ⟨157053834826498122227967473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104702556550998748151978315 157053834826498122227967473)
    ·
      refine ⟨117790376119873591670975605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157053834826498122227967473 117790376119873591670975605)
      ·
        refine ⟨11042847761238149219153963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117790376119873591670975605 11042847761238149219153963)
        ·
          refine ⟨16564271641857223828730945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11042847761238149219153963 16564271641857223828730945)
          ·
            refine ⟨12423203731392917871548209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16564271641857223828730945 12423203731392917871548209)
            ·
              refine ⟨9317402798544688403661157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12423203731392917871548209 9317402798544688403661157)
              ·
                refine ⟨1747013024727129075686467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9317402798544688403661157 1747013024727129075686467)
                ·
                  refine ⟨2620519537090693613529701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747013024727129075686467 2620519537090693613529701)
                  ·
                    refine ⟨491347413204505052536819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2620519537090693613529701 491347413204505052536819)
                    ·
                      rfl

theorem cell23_2870687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 4].length) (baseStart_2870687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870687 prefixEnd_2870687 := by exact prefixLift 2870687
  have htrace : WordTrace (prefixWord ++ tailWord_2870687) baseStart_2870687 baseEnd_2870687 := by
    simpa [prefixWord, tailWord_2870687, baseEnd_2870687] using wordTrace_append hprefix tailTrace_2870687
  have hstable : (prefixWord ++ tailWord_2870687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870687).length < 2 ^ (prefixWord ++ tailWord_2870687).sum := by decide
  have hdescent : baseEnd_2870687 < baseStart_2870687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870720 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 1, 5, 2]
def baseStart_2870720 : Nat := 118140960795 + 2870720 * 2 ^ 59
def prefixEnd_2870720 : Nat := 4983230072969 + 3 ^ 40 * 2870720 * 2
def baseEnd_2870720 : Nat := 1474059184475113528497805

theorem tailTrace_2870720 : CollatzResearch.WordTrace tailWord_2870720 prefixEnd_2870720 1474059184475113528497805 := by
  unfold tailWord_2870720
  simp only [CollatzResearch.WordTrace]
  refine ⟨52351880079939597393964807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69802506773252796525286409 52351880079939597393964807)
  ·
    refine ⟨78527820119909396090947211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52351880079939597393964807 78527820119909396090947211)
    ·
      refine ⟨117791730179864094136420817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78527820119909396090947211 117791730179864094136420817)
      ·
        refine ⟨88343797634898070602315613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117791730179864094136420817 88343797634898070602315613)
        ·
          refine ⟨33128924113086776475868355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88343797634898070602315613 33128924113086776475868355)
          ·
            refine ⟨49693386169630164713802533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33128924113086776475868355 49693386169630164713802533)
            ·
              refine ⟨9317509906805655883837975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49693386169630164713802533 9317509906805655883837975)
              ·
                refine ⟨13976264860208483825756963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9317509906805655883837975 13976264860208483825756963)
                ·
                  refine ⟨20964397290312725738635445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13976264860208483825756963 20964397290312725738635445)
                  ·
                    refine ⟨1965412245966818037997073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20964397290312725738635445 1965412245966818037997073)
                    ·
                      refine ⟨1474059184475113528497805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965412245966818037997073 1474059184475113528497805)
                      ·
                        rfl

theorem cell23_2870720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_2870720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870720 prefixEnd_2870720 := by exact prefixLift 2870720
  have htrace : WordTrace (prefixWord ++ tailWord_2870720) baseStart_2870720 baseEnd_2870720 := by
    simpa [prefixWord, tailWord_2870720, baseEnd_2870720] using wordTrace_append hprefix tailTrace_2870720
  have hstable : (prefixWord ++ tailWord_2870720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870720).length < 2 ^ (prefixWord ++ tailWord_2870720).sum := by decide
  have hdescent : baseEnd_2870720 < baseStart_2870720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870730 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_2870730 : Nat := 118140960795 + 2870730 * 2 ^ 59
def prefixEnd_2870730 : Nat := 4983230072969 + 3 ^ 40 * 2870730 * 2
def baseEnd_2870730 : Nat := 491354773093886163124253

theorem tailTrace_2870730 : CollatzResearch.WordTrace tailWord_2870730 prefixEnd_2870730 491354773093886163124253 := by
  unfold tailWord_2870730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26176031222460741623948411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69802749926561977663862429 26176031222460741623948411)
  ·
    refine ⟨39264046833691112435922617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26176031222460741623948411 39264046833691112435922617)
    ·
      refine ⟨29448035125268334326941963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39264046833691112435922617 29448035125268334326941963)
      ·
        refine ⟨44172052687902501490412945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29448035125268334326941963 44172052687902501490412945)
        ·
          refine ⟨33129039515926876117809709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44172052687902501490412945 33129039515926876117809709)
          ·
            refine ⟨12423389818472578544178641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33129039515926876117809709 12423389818472578544178641)
            ·
              refine ⟨9317542363854433908133981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12423389818472578544178641 9317542363854433908133981)
              ·
                refine ⟨3494078386445412715550243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9317542363854433908133981 3494078386445412715550243)
                ·
                  refine ⟨5241117579668119073325365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494078386445412715550243 5241117579668119073325365)
                  ·
                    refine ⟨491354773093886163124253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5241117579668119073325365 491354773093886163124253)
                    ·
                      rfl

theorem cell23_2870730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_2870730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870730 prefixEnd_2870730 := by exact prefixLift 2870730
  have htrace : WordTrace (prefixWord ++ tailWord_2870730) baseStart_2870730 baseEnd_2870730 := by
    simpa [prefixWord, tailWord_2870730, baseEnd_2870730] using wordTrace_append hprefix tailTrace_2870730
  have hstable : (prefixWord ++ tailWord_2870730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870730).length < 2 ^ (prefixWord ++ tailWord_2870730).sum := by decide
  have hdescent : baseEnd_2870730 < baseStart_2870730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870767 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 3, 2, 2]
def baseStart_2870767 : Nat := 118140960795 + 2870767 * 2 ^ 59
def prefixEnd_2870767 : Nat := 4983230072969 + 3 ^ 40 * 2870767 * 2
def baseEnd_2870767 : Nat := 1474083318065874844610089

theorem tailTrace_2870767 : CollatzResearch.WordTrace tailWord_2870767 prefixEnd_2870767 1474083318065874844610089 := by
  unfold tailWord_2870767
  simp only [CollatzResearch.WordTrace]
  refine ⟨104705474390708921814890555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69803649593805947876593703 104705474390708921814890555)
  ·
    refine ⟨157058211586063382722335833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104705474390708921814890555 157058211586063382722335833)
    ·
      refine ⟨117793658689547537041751875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157058211586063382722335833 117793658689547537041751875)
      ·
        refine ⟨176690488034321305562627813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117793658689547537041751875 176690488034321305562627813)
        ·
          refine ⟨33129466506435244792992715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176690488034321305562627813 33129466506435244792992715)
          ·
            refine ⟨49694199759652867189489073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33129466506435244792992715 49694199759652867189489073)
            ·
              refine ⟨37270649819739650392116805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49694199759652867189489073 37270649819739650392116805)
              ·
                refine ⟨6988246841201184448521901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37270649819739650392116805 6988246841201184448521901)
                ·
                  refine ⟨2620592565450444168195713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6988246841201184448521901 2620592565450444168195713)
                  ·
                    refine ⟨1965444424087833126146785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620592565450444168195713 1965444424087833126146785)
                    ·
                      refine ⟨1474083318065874844610089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965444424087833126146785 1474083318065874844610089)
                      ·
                        rfl

theorem cell23_2870767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 2, 2].length) (baseStart_2870767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870767 prefixEnd_2870767 := by exact prefixLift 2870767
  have htrace : WordTrace (prefixWord ++ tailWord_2870767) baseStart_2870767 baseEnd_2870767 := by
    simpa [prefixWord, tailWord_2870767, baseEnd_2870767] using wordTrace_append hprefix tailTrace_2870767
  have hstable : (prefixWord ++ tailWord_2870767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870767).length < 2 ^ (prefixWord ++ tailWord_2870767).sum := by decide
  have hdescent : baseEnd_2870767 < baseStart_2870767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870803 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 2, 7]
def baseStart_2870803 : Nat := 118140960795 + 2870803 * 2 ^ 59
def prefixEnd_2870803 : Nat := 4983230072969 + 3 ^ 40 * 2870803 * 2
def baseEnd_2870803 : Nat := 491367267789812234586641

theorem tailTrace_2870803 : CollatzResearch.WordTrace tailWord_2870803 prefixEnd_2870803 491367267789812234586641 := by
  unfold tailWord_2870803
  simp only [CollatzResearch.WordTrace]
  refine ⟨104706787418578499963201063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69804524945718999975467375 104706787418578499963201063)
  ·
    refine ⟨157060181127867749944801595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104706787418578499963201063 157060181127867749944801595)
    ·
      refine ⟨235590271691801624917202393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157060181127867749944801595 235590271691801624917202393)
      ·
        refine ⟨176692703768851218687901795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235590271691801624917202393 176692703768851218687901795)
        ·
          refine ⟨265039055653276828031852693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176692703768851218687901795 265039055653276828031852693)
          ·
            refine ⟨12423705733747351313993095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265039055653276828031852693 12423705733747351313993095)
            ·
              refine ⟨18635558600621026970989643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12423705733747351313993095 18635558600621026970989643)
              ·
                refine ⟨27953337900931540456484465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18635558600621026970989643 27953337900931540456484465)
                ·
                  refine ⟨20965003425698655342363349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27953337900931540456484465 20965003425698655342363349)
                  ·
                    refine ⟨491367267789812234586641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20965003425698655342363349 491367267789812234586641)
                    ·
                      rfl

theorem cell23_2870803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 7].length) (baseStart_2870803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870803 prefixEnd_2870803 := by exact prefixLift 2870803
  have htrace : WordTrace (prefixWord ++ tailWord_2870803) baseStart_2870803 baseEnd_2870803 := by
    simpa [prefixWord, tailWord_2870803, baseEnd_2870803] using wordTrace_append hprefix tailTrace_2870803
  have hstable : (prefixWord ++ tailWord_2870803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870803).length < 2 ^ (prefixWord ++ tailWord_2870803).sum := by decide
  have hdescent : baseEnd_2870803 < baseStart_2870803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870817 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2870817 : Nat := 118140960795 + 2870817 * 2 ^ 59
def prefixEnd_2870817 : Nat := 4983230072969 + 3 ^ 40 * 2870817 * 2
def baseEnd_2870817 : Nat := 1474108992098599648984859

theorem tailTrace_2870817 : CollatzResearch.WordTrace tailWord_2870817 prefixEnd_2870817 1474108992098599648984859 := by
  unfold tailWord_2870817
  simp only [CollatzResearch.WordTrace]
  refine ⟨104707298040527780354210705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69804865360351853569473803 104707298040527780354210705)
  ·
    refine ⟨78530473530395835265658029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104707298040527780354210705 78530473530395835265658029)
    ·
      refine ⟨29448927573898438224621761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78530473530395835265658029 29448927573898438224621761)
      ·
        refine ⟨22086695680423828668466321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29448927573898438224621761 22086695680423828668466321)
        ·
          refine ⟨16565021760317871501349741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22086695680423828668466321 16565021760317871501349741)
          ·
            refine ⟨6211883160119201813006153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16565021760317871501349741 6211883160119201813006153)
            ·
              refine ⟨4658912370089401359754615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6211883160119201813006153 4658912370089401359754615)
              ·
                refine ⟨6988368555134102039631923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658912370089401359754615 6988368555134102039631923)
                ·
                  refine ⟨10482552832701153059447885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6988368555134102039631923 10482552832701153059447885)
                  ·
                    refine ⟨3930957312262932397292957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10482552832701153059447885 3930957312262932397292957)
                    ·
                      refine ⟨1474108992098599648984859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3930957312262932397292957 1474108992098599648984859)
                      ·
                        rfl

theorem cell23_2870817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2870817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870817 prefixEnd_2870817 := by exact prefixLift 2870817
  have htrace : WordTrace (prefixWord ++ tailWord_2870817) baseStart_2870817 baseEnd_2870817 := by
    simpa [prefixWord, tailWord_2870817, baseEnd_2870817] using wordTrace_append hprefix tailTrace_2870817
  have hstable : (prefixWord ++ tailWord_2870817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870817).length < 2 ^ (prefixWord ++ tailWord_2870817).sum := by decide
  have hdescent : baseEnd_2870817 < baseStart_2870817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870833 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_2870833 : Nat := 118140960795 + 2870833 * 2 ^ 59
def prefixEnd_2870833 : Nat := 4983230072969 + 3 ^ 40 * 2870833 * 2
def baseEnd_2870833 : Nat := 491372402596357195461595

theorem tailTrace_2870833 : CollatzResearch.WordTrace tailWord_2870833 prefixEnd_2870833 491372402596357195461595 := by
  unfold tailWord_2870833
  simp only [CollatzResearch.WordTrace]
  refine ⟨104707881608469815086793153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69805254405646543391195435 104707881608469815086793153)
  ·
    refine ⟨78530911206352361315094865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104707881608469815086793153 78530911206352361315094865)
    ·
      refine ⟨58898183404764270986321149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78530911206352361315094865 58898183404764270986321149)
      ·
        refine ⟨22086818776786601619870431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58898183404764270986321149 22086818776786601619870431)
        ·
          refine ⟨33130228165179902429805647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22086818776786601619870431 33130228165179902429805647)
          ·
            refine ⟨49695342247769853644708471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33130228165179902429805647 49695342247769853644708471)
            ·
              refine ⟨74543013371654780467062707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49695342247769853644708471 74543013371654780467062707)
              ·
                refine ⟨111814520057482170700594061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74543013371654780467062707 111814520057482170700594061)
                ·
                  refine ⟨41930445021555814012722773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111814520057482170700594061 41930445021555814012722773)
                  ·
                    refine ⟨491372402596357195461595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41930445021555814012722773 491372402596357195461595)
                    ·
                      rfl

theorem cell23_2870833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_2870833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870833 prefixEnd_2870833 := by exact prefixLift 2870833
  have htrace : WordTrace (prefixWord ++ tailWord_2870833) baseStart_2870833 baseEnd_2870833 := by
    simpa [prefixWord, tailWord_2870833, baseEnd_2870833] using wordTrace_append hprefix tailTrace_2870833
  have hstable : (prefixWord ++ tailWord_2870833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870833).length < 2 ^ (prefixWord ++ tailWord_2870833).sum := by decide
  have hdescent : baseEnd_2870833 < baseStart_2870833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870838 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_2870838 : Nat := 118140960795 + 2870838 * 2 ^ 59
def prefixEnd_2870838 : Nat := 4983230072969 + 3 ^ 40 * 2870838 * 2
def baseEnd_2870838 : Nat := 1474119775192344066822263

theorem tailTrace_2870838 : CollatzResearch.WordTrace tailWord_2870838 prefixEnd_2870838 1474119775192344066822263 := by
  unfold tailWord_2870838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6544253998340731308795323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69805375982301133960483445 6544253998340731308795323)
  ·
    refine ⟨9816380997511096963192985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6544253998340731308795323 9816380997511096963192985)
    ·
      refine ⟨7362285748133322722394739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9816380997511096963192985 7362285748133322722394739)
      ·
        refine ⟨11043428622199984083592109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7362285748133322722394739 11043428622199984083592109)
        ·
          refine ⟨4141285733324994031347041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11043428622199984083592109 4141285733324994031347041)
          ·
            refine ⟨3105964299993745523510281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4141285733324994031347041 3105964299993745523510281)
            ·
              refine ⟨2329473224995309142632711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3105964299993745523510281 2329473224995309142632711)
              ·
                refine ⟨3494209837492963713949067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329473224995309142632711 3494209837492963713949067)
                ·
                  refine ⟨5241314756239445570923601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494209837492963713949067 5241314756239445570923601)
                  ·
                    refine ⟨3930986067179584178192701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5241314756239445570923601 3930986067179584178192701)
                    ·
                      refine ⟨1474119775192344066822263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3930986067179584178192701 1474119775192344066822263)
                      ·
                        rfl

theorem cell23_2870838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_2870838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870838 prefixEnd_2870838 := by exact prefixLift 2870838
  have htrace : WordTrace (prefixWord ++ tailWord_2870838) baseStart_2870838 baseEnd_2870838 := by
    simpa [prefixWord, tailWord_2870838, baseEnd_2870838] using wordTrace_append hprefix tailTrace_2870838
  have hstable : (prefixWord ++ tailWord_2870838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870838).length < 2 ^ (prefixWord ++ tailWord_2870838).sum := by decide
  have hdescent : baseEnd_2870838 < baseStart_2870838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870873 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2870873 : Nat := 118140960795 + 2870873 * 2 ^ 59
def prefixEnd_2870873 : Nat := 4983230072969 + 3 ^ 40 * 2870873 * 2
def baseEnd_2870873 : Nat := 1474137747015251429884601

theorem tailTrace_2870873 : CollatzResearch.WordTrace tailWord_2870873 prefixEnd_2870873 1474137747015251429884601 := by
  unfold tailWord_2870873
  simp only [CollatzResearch.WordTrace]
  refine ⟨104709340528324901918249273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69806227018883267945499515 104709340528324901918249273)
  ·
    refine ⟨78532005396243676438686955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104709340528324901918249273 78532005396243676438686955)
    ·
      refine ⟨117798008094365514658030433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78532005396243676438686955 117798008094365514658030433)
      ·
        refine ⟨88348506070774135993522825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117798008094365514658030433 88348506070774135993522825)
        ·
          refine ⟨66261379553080601995142119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88348506070774135993522825 66261379553080601995142119)
          ·
            refine ⟨99392069329620902992713179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66261379553080601995142119 99392069329620902992713179)
            ·
              refine ⟨149088103994431354489069769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99392069329620902992713179 149088103994431354489069769)
              ·
                refine ⟨111816077995823515866802327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149088103994431354489069769 111816077995823515866802327)
                ·
                  refine ⟨167724116993735273800203491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111816077995823515866802327 167724116993735273800203491)
                  ·
                    refine ⟨251586175490602910700305237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167724116993735273800203491 251586175490602910700305237)
                    ·
                      refine ⟨1474137747015251429884601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 251586175490602910700305237 1474137747015251429884601)
                      ·
                        rfl

theorem cell23_2870873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2870873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870873 prefixEnd_2870873 := by exact prefixLift 2870873
  have htrace : WordTrace (prefixWord ++ tailWord_2870873) baseStart_2870873 baseEnd_2870873 := by
    simpa [prefixWord, tailWord_2870873, baseEnd_2870873] using wordTrace_append hprefix tailTrace_2870873
  have hstable : (prefixWord ++ tailWord_2870873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870873).length < 2 ^ (prefixWord ++ tailWord_2870873).sum := by decide
  have hdescent : baseEnd_2870873 < baseStart_2870873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870874 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2]
def baseStart_2870874 : Nat := 118140960795 + 2870874 * 2 ^ 59
def prefixEnd_2870874 : Nat := 4983230072969 + 3 ^ 40 * 2870874 * 2
def baseEnd_2870874 : Nat := 1474138260495905925972097

theorem tailTrace_2870874 : CollatzResearch.WordTrace tailWord_2870874 prefixEnd_2870874 1474138260495905925972097 := by
  unfold tailWord_2870874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26177344250330319772258919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69806251334214186059357117 26177344250330319772258919)
  ·
    refine ⟨39266016375495479658388379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26177344250330319772258919 39266016375495479658388379)
    ·
      refine ⟨58899024563243219487582569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39266016375495479658388379 58899024563243219487582569)
      ·
        refine ⟨44174268422432414615686927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58899024563243219487582569 44174268422432414615686927)
        ·
          refine ⟨66261402633648621923530391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44174268422432414615686927 66261402633648621923530391)
          ·
            refine ⟨99392103950472932885295587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66261402633648621923530391 99392103950472932885295587)
            ·
              refine ⟨149088155925709399327943381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99392103950472932885295587 149088155925709399327943381)
              ·
                refine ⟨3494253654508814046748673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149088155925709399327943381 3494253654508814046748673)
                ·
                  refine ⟨2620690240881610535061505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3494253654508814046748673 2620690240881610535061505)
                  ·
                    refine ⟨1965517680661207901296129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620690240881610535061505 1965517680661207901296129)
                    ·
                      refine ⟨1474138260495905925972097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965517680661207901296129 1474138260495905925972097)
                      ·
                        rfl

theorem cell23_2870874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_2870874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870874 prefixEnd_2870874 := by exact prefixLift 2870874
  have htrace : WordTrace (prefixWord ++ tailWord_2870874) baseStart_2870874 baseEnd_2870874 := by
    simpa [prefixWord, tailWord_2870874, baseEnd_2870874] using wordTrace_append hprefix tailTrace_2870874
  have hstable : (prefixWord ++ tailWord_2870874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870874).length < 2 ^ (prefixWord ++ tailWord_2870874).sum := by decide
  have hdescent : baseEnd_2870874 < baseStart_2870874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870917 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 2, 5, 2]
def baseStart_2870917 : Nat := 118140960795 + 2870917 * 2 ^ 59
def prefixEnd_2870917 : Nat := 4983230072969 + 3 ^ 40 * 2870917 * 2
def baseEnd_2870917 : Nat := 1474160340164049257734399

theorem tailTrace_2870917 : CollatzResearch.WordTrace tailWord_2870917 prefixEnd_2870917 1474160340164049257734399 := by
  unfold tailWord_2870917
  simp only [CollatzResearch.WordTrace]
  refine ⟨104710945340165497432851005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69807296893443664955234003 104710945340165497432851005)
  ·
    refine ⟨39266604502562061537319127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104710945340165497432851005 39266604502562061537319127)
    ·
      refine ⟨58899906753843092305978691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39266604502562061537319127 58899906753843092305978691)
      ·
        refine ⟨88349860130764638458968037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58899906753843092305978691 88349860130764638458968037)
        ·
          refine ⟨16565598774518369711056507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88349860130764638458968037 16565598774518369711056507)
          ·
            refine ⟨24848398161777554566584761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16565598774518369711056507 24848398161777554566584761)
            ·
              refine ⟨18636298621333165924938571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24848398161777554566584761 18636298621333165924938571)
              ·
                refine ⟨27954447931999748887407857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18636298621333165924938571 27954447931999748887407857)
                ·
                  refine ⟨20965835948999811665555893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27954447931999748887407857 20965835948999811665555893)
                  ·
                    refine ⟨1965547120218732343645865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20965835948999811665555893 1965547120218732343645865)
                    ·
                      refine ⟨1474160340164049257734399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965547120218732343645865 1474160340164049257734399)
                      ·
                        rfl

theorem cell23_2870917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_2870917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870917 prefixEnd_2870917 := by exact prefixLift 2870917
  have htrace : WordTrace (prefixWord ++ tailWord_2870917) baseStart_2870917 baseEnd_2870917 := by
    simpa [prefixWord, tailWord_2870917, baseEnd_2870917] using wordTrace_append hprefix tailTrace_2870917
  have hstable : (prefixWord ++ tailWord_2870917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870917).length < 2 ^ (prefixWord ++ tailWord_2870917).sum := by decide
  have hdescent : baseEnd_2870917 < baseStart_2870917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870947 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 4]
def baseStart_2870947 : Nat := 118140960795 + 2870947 * 2 ^ 59
def prefixEnd_2870947 : Nat := 4983230072969 + 3 ^ 40 * 2870947 * 2
def baseEnd_2870947 : Nat := 1474175744583684140359261

theorem tailTrace_2870947 : CollatzResearch.WordTrace tailWord_2870947 prefixEnd_2870947 1474175744583684140359261 := by
  unfold tailWord_2870947
  simp only [CollatzResearch.WordTrace]
  refine ⟨104712039530056812556443095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69808026353371208370962063 104712039530056812556443095)
  ·
    refine ⟨157068059295085218834664643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104712039530056812556443095 157068059295085218834664643)
    ·
      refine ⟨235602088942627828251996965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157068059295085218834664643 235602088942627828251996965)
      ·
        refine ⟨44175391676742717797249431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235602088942627828251996965 44175391676742717797249431)
        ·
          refine ⟨66263087515114076695874147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44175391676742717797249431 66263087515114076695874147)
          ·
            refine ⟨99394631272671115043811221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66263087515114076695874147 99394631272671115043811221)
            ·
              refine ⟨4659123340906458517678651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99394631272671115043811221 4659123340906458517678651)
              ·
                refine ⟨6988685011359687776517977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659123340906458517678651 6988685011359687776517977)
                ·
                  refine ⟨5241513758519765832388483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6988685011359687776517977 5241513758519765832388483)
                  ·
                    refine ⟨7862270637779648748582725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241513758519765832388483 7862270637779648748582725)
                    ·
                      refine ⟨1474175744583684140359261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7862270637779648748582725 1474175744583684140359261)
                      ·
                        rfl

theorem cell23_2870947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_2870947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2870947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2870947 prefixEnd_2870947 := by exact prefixLift 2870947
  have htrace : WordTrace (prefixWord ++ tailWord_2870947) baseStart_2870947 baseEnd_2870947 := by
    simpa [prefixWord, tailWord_2870947, baseEnd_2870947] using wordTrace_append hprefix tailTrace_2870947
  have hstable : (prefixWord ++ tailWord_2870947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870947).length < 2 ^ (prefixWord ++ tailWord_2870947).sum := by decide
  have hdescent : baseEnd_2870947 < baseStart_2870947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871031 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 1, 1, 3]
def baseStart_2871031 : Nat := 118140960795 + 2871031 * 2 ^ 59
def prefixEnd_2871031 : Nat := 4983230072969 + 3 ^ 40 * 2871031 * 2
def baseEnd_2871031 : Nat := 1474218876958661811708875

theorem tailTrace_2871031 : CollatzResearch.WordTrace tailWord_2871031 prefixEnd_2871031 1474218876958661811708875 := by
  unfold tailWord_2871031
  simp only [CollatzResearch.WordTrace]
  refine ⟨104715103261752494902500947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69810068841168329935000631 104715103261752494902500947)
  ·
    refine ⟨157072654892628742353751421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104715103261752494902500947 157072654892628742353751421)
    ·
      refine ⟨58902245584735778382656783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157072654892628742353751421 58902245584735778382656783)
      ·
        refine ⟨88353368377103667573985175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58902245584735778382656783 88353368377103667573985175)
        ·
          refine ⟨132530052565655501360977763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88353368377103667573985175 132530052565655501360977763)
          ·
            refine ⟨198795078848483252041466645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132530052565655501360977763 198795078848483252041466645)
            ·
              refine ⟨9318519321022652439443749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198795078848483252041466645 9318519321022652439443749)
              ·
                refine ⟨1747222372691747332395703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9318519321022652439443749 1747222372691747332395703)
                ·
                  refine ⟨2620833559037620998593555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747222372691747332395703 2620833559037620998593555)
                  ·
                    refine ⟨3931250338556431497890333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2620833559037620998593555 3931250338556431497890333)
                    ·
                      refine ⟨1474218876958661811708875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931250338556431497890333 1474218876958661811708875)
                      ·
                        rfl

theorem cell23_2871031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_2871031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871031 prefixEnd_2871031 := by exact prefixLift 2871031
  have htrace : WordTrace (prefixWord ++ tailWord_2871031) baseStart_2871031 baseEnd_2871031 := by
    simpa [prefixWord, tailWord_2871031, baseEnd_2871031] using wordTrace_append hprefix tailTrace_2871031
  have hstable : (prefixWord ++ tailWord_2871031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871031).length < 2 ^ (prefixWord ++ tailWord_2871031).sum := by decide
  have hdescent : baseEnd_2871031 < baseStart_2871031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871037 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_2871037 : Nat := 118140960795 + 2871037 * 2 ^ 59
def prefixEnd_2871037 : Nat := 4983230072969 + 3 ^ 40 * 2871037 * 2
def baseEnd_2871037 : Nat := 1474221957842588788233847

theorem tailTrace_2871037 : CollatzResearch.WordTrace tailWord_2871037 prefixEnd_2871037 1474221957842588788233847 := by
  unfold tailWord_2871037
  simp only [CollatzResearch.WordTrace]
  refine ⟨104715322099730757927219365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69810214733153838618146243 104715322099730757927219365)
  ·
    refine ⟨19634122893699517111353631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104715322099730757927219365 19634122893699517111353631)
    ·
      refine ⟨29451184340549275667030447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19634122893699517111353631 29451184340549275667030447)
      ·
        refine ⟨44176776510823913500545671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29451184340549275667030447 44176776510823913500545671)
        ·
          refine ⟨66265164766235870250818507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44176776510823913500545671 66265164766235870250818507)
          ·
            refine ⟨99397747149353805376227761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66265164766235870250818507 99397747149353805376227761)
            ·
              refine ⟨74548310362015354032170821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99397747149353805376227761 74548310362015354032170821)
              ·
                refine ⟨13977808192877878881032029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74548310362015354032170821 13977808192877878881032029)
                ·
                  refine ⟨5241678072329204580387011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13977808192877878881032029 5241678072329204580387011)
                  ·
                    refine ⟨7862517108493806870580517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241678072329204580387011 7862517108493806870580517)
                    ·
                      refine ⟨1474221957842588788233847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7862517108493806870580517 1474221957842588788233847)
                      ·
                        rfl

theorem cell23_2871037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_2871037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871037 prefixEnd_2871037 := by exact prefixLift 2871037
  have htrace : WordTrace (prefixWord ++ tailWord_2871037) baseStart_2871037 baseEnd_2871037 := by
    simpa [prefixWord, tailWord_2871037, baseEnd_2871037] using wordTrace_append hprefix tailTrace_2871037
  have hstable : (prefixWord ++ tailWord_2871037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871037).length < 2 ^ (prefixWord ++ tailWord_2871037).sum := by decide
  have hdescent : baseEnd_2871037 < baseStart_2871037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871054 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2871054 : Nat := 118140960795 + 2871054 * 2 ^ 59
def prefixEnd_2871054 : Nat := 4983230072969 + 3 ^ 40 * 2871054 * 2
def baseEnd_2871054 : Nat := 1474230687013715221721269

theorem tailTrace_2871054 : CollatzResearch.WordTrace tailWord_2871054 prefixEnd_2871054 1474230687013715221721269 := by
  unfold tailWord_2871054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089492767583646228823527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69810628093779446553725477 13089492767583646228823527)
  ·
    refine ⟨19634239151375469343235291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13089492767583646228823527 19634239151375469343235291)
    ·
      refine ⟨29451358727063204014852937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19634239151375469343235291 29451358727063204014852937)
      ·
        refine ⟨22088519045297403011139703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29451358727063204014852937 22088519045297403011139703)
        ·
          refine ⟨33132778567946104516709555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22088519045297403011139703 33132778567946104516709555)
          ·
            refine ⟨49699167851919156775064333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33132778567946104516709555 49699167851919156775064333)
            ·
              refine ⟨18637187944469683790649125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49699167851919156775064333 18637187944469683790649125)
              ·
                refine ⟨3494472739588065710746711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18637187944469683790649125 3494472739588065710746711)
                ·
                  refine ⟨5241709109382098566120067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494472739588065710746711 5241709109382098566120067)
                  ·
                    refine ⟨7862563664073147849180101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241709109382098566120067 7862563664073147849180101)
                    ·
                      refine ⟨1474230687013715221721269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7862563664073147849180101 1474230687013715221721269)
                      ·
                        rfl

theorem cell23_2871054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2871054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871054 prefixEnd_2871054 := by exact prefixLift 2871054
  have htrace : WordTrace (prefixWord ++ tailWord_2871054) baseStart_2871054 baseEnd_2871054 := by
    simpa [prefixWord, tailWord_2871054, baseEnd_2871054] using wordTrace_append hprefix tailTrace_2871054
  have hstable : (prefixWord ++ tailWord_2871054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871054).length < 2 ^ (prefixWord ++ tailWord_2871054).sum := by decide
  have hdescent : baseEnd_2871054 < baseStart_2871054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871074 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_2871074 : Nat := 118140960795 + 2871074 * 2 ^ 59
def prefixEnd_2871074 : Nat := 4983230072969 + 3 ^ 40 * 2871074 * 2
def baseEnd_2871074 : Nat := 1474240956626805143471177

theorem tailTrace_2871074 : CollatzResearch.WordTrace tailWord_2871074 prefixEnd_2871074 1474240956626805143471177 := by
  unfold tailWord_2871074
  simp only [CollatzResearch.WordTrace]
  refine ⟨26179167900149178311579069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69811114400397808830877517 26179167900149178311579069)
  ·
    refine ⟨9817187962555941866842151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26179167900149178311579069 9817187962555941866842151)
    ·
      refine ⟨14725781943833912800263227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9817187962555941866842151 14725781943833912800263227)
      ·
        refine ⟨22088672915750869200394841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14725781943833912800263227 22088672915750869200394841)
        ·
          refine ⟨16566504686813151900296131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22088672915750869200394841 16566504686813151900296131)
          ·
            refine ⟨24849757030219727850444197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16566504686813151900296131 24849757030219727850444197)
            ·
              refine ⟨4659329443166198971958287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24849757030219727850444197 4659329443166198971958287)
              ·
                refine ⟨6988994164749298457937431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659329443166198971958287 6988994164749298457937431)
                ·
                  refine ⟨10483491247123947686906147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6988994164749298457937431 10483491247123947686906147)
                  ·
                    refine ⟨15725236870685921530359221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10483491247123947686906147 15725236870685921530359221)
                    ·
                      refine ⟨1474240956626805143471177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15725236870685921530359221 1474240956626805143471177)
                      ·
                        rfl

theorem cell23_2871074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_2871074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871074 prefixEnd_2871074 := by exact prefixLift 2871074
  have htrace : WordTrace (prefixWord ++ tailWord_2871074) baseStart_2871074 baseEnd_2871074 := by
    simpa [prefixWord, tailWord_2871074, baseEnd_2871074] using wordTrace_append hprefix tailTrace_2871074
  have hstable : (prefixWord ++ tailWord_2871074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871074).length < 2 ^ (prefixWord ++ tailWord_2871074).sum := by decide
  have hdescent : baseEnd_2871074 < baseStart_2871074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871077 : List Nat := [1, 3, 1, 2, 3, 4, 9]
def baseStart_2871077 : Nat := 118140960795 + 2871077 * 2 ^ 59
def prefixEnd_2871077 : Nat := 4983230072969 + 3 ^ 40 * 2871077 * 2
def baseEnd_2871077 : Nat := 18200524655169983107823

theorem tailTrace_2871077 : CollatzResearch.WordTrace tailWord_2871077 prefixEnd_2871077 18200524655169983107823 := by
  unfold tailWord_2871077
  simp only [CollatzResearch.WordTrace]
  refine ⟨104716781019585844758675485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69811187346390563172450323 104716781019585844758675485)
  ·
    refine ⟨39268792882344691784503307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104716781019585844758675485 39268792882344691784503307)
    ·
      refine ⟨58903189323517037676754961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39268792882344691784503307 58903189323517037676754961)
      ·
        refine ⟨44177391992637778257566221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58903189323517037676754961 44177391992637778257566221)
        ·
          refine ⟨16566521997239166846587333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44177391992637778257566221 16566521997239166846587333)
          ·
            refine ⟨3106222874482343783735125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16566521997239166846587333 3106222874482343783735125)
            ·
              refine ⟨18200524655169983107823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3106222874482343783735125 18200524655169983107823)
              ·
                rfl

theorem cell23_2871077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 9].length) (baseStart_2871077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871077 prefixEnd_2871077 := by exact prefixLift 2871077
  have htrace : WordTrace (prefixWord ++ tailWord_2871077) baseStart_2871077 baseEnd_2871077 := by
    simpa [prefixWord, tailWord_2871077, baseEnd_2871077] using wordTrace_append hprefix tailTrace_2871077
  have hstable : (prefixWord ++ tailWord_2871077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871077).length < 2 ^ (prefixWord ++ tailWord_2871077).sum := by decide
  have hdescent : baseEnd_2871077 < baseStart_2871077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871087 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_2871087 : Nat := 118140960795 + 2871087 * 2 ^ 59
def prefixEnd_2871087 : Nat := 4983230072969 + 3 ^ 40 * 2871087 * 2
def baseEnd_2871087 : Nat := 1474247631875313592608617

theorem tailTrace_2871087 : CollatzResearch.WordTrace tailWord_2871087 prefixEnd_2871087 1474247631875313592608617 := by
  unfold tailWord_2871087
  simp only [CollatzResearch.WordTrace]
  refine ⟨104717145749549616466539515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69811430499699744311026343 104717145749549616466539515)
  ·
    refine ⟨157075718624324424699809273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104717145749549616466539515 157075718624324424699809273)
    ·
      refine ⟨117806788968243318524856955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157075718624324424699809273 117806788968243318524856955)
      ·
        refine ⟨176710183452364977787285433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117806788968243318524856955 176710183452364977787285433)
        ·
          refine ⟨132532637589273733340464075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176710183452364977787285433 132532637589273733340464075)
          ·
            refine ⟨198798956383910600010696113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132532637589273733340464075 198798956383910600010696113)
            ·
              refine ⟨149099217287932950008022085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198798956383910600010696113 149099217287932950008022085)
              ·
                refine ⟨27956103241487428126504141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149099217287932950008022085 27956103241487428126504141)
                ·
                  refine ⟨10483538715557785547439053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27956103241487428126504141 10483538715557785547439053)
                  ·
                    refine ⟨3931327018334169580289645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10483538715557785547439053 3931327018334169580289645)
                    ·
                      refine ⟨1474247631875313592608617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931327018334169580289645 1474247631875313592608617)
                      ·
                        rfl

theorem cell23_2871087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_2871087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871087 prefixEnd_2871087 := by exact prefixLift 2871087
  have htrace : WordTrace (prefixWord ++ tailWord_2871087) baseStart_2871087 baseEnd_2871087 := by
    simpa [prefixWord, tailWord_2871087, baseEnd_2871087] using wordTrace_append hprefix tailTrace_2871087
  have hstable : (prefixWord ++ tailWord_2871087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871087).length < 2 ^ (prefixWord ++ tailWord_2871087).sum := by decide
  have hdescent : baseEnd_2871087 < baseStart_2871087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871094 : List Nat := [5, 1, 2, 2, 1, 1, 1, 10]
def baseStart_2871094 : Nat := 118140960795 + 2871094 * 2 ^ 59
def prefixEnd_2871094 : Nat := 4983230072969 + 3 ^ 40 * 2871094 * 2
def baseEnd_2871094 : Nat := 54601897268144261674855

theorem tailTrace_2871094 : CollatzResearch.WordTrace tailWord_2871094 prefixEnd_2871094 54601897268144261674855 := by
  unfold tailWord_2871094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6544837566282766041377771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69811600707016171108029557 6544837566282766041377771)
  ·
    refine ⟨9817256349424149062066657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6544837566282766041377771 9817256349424149062066657)
    ·
      refine ⟨7362942262068111796549993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9817256349424149062066657 7362942262068111796549993)
      ·
        refine ⟨5522206696551083847412495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7362942262068111796549993 5522206696551083847412495)
        ·
          refine ⟨8283310044826625771118743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5522206696551083847412495 8283310044826625771118743)
          ·
            refine ⟨12424965067239938656678115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8283310044826625771118743 12424965067239938656678115)
            ·
              refine ⟨18637447600859907985017173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12424965067239938656678115 18637447600859907985017173)
              ·
                refine ⟨54601897268144261674855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18637447600859907985017173 54601897268144261674855)
                ·
                  rfl

theorem cell23_2871094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_2871094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871094 prefixEnd_2871094 := by exact prefixLift 2871094
  have htrace : WordTrace (prefixWord ++ tailWord_2871094) baseStart_2871094 baseEnd_2871094 := by
    simpa [prefixWord, tailWord_2871094, baseEnd_2871094] using wordTrace_append hprefix tailTrace_2871094
  have hstable : (prefixWord ++ tailWord_2871094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871094).length < 2 ^ (prefixWord ++ tailWord_2871094).sum := by decide
  have hdescent : baseEnd_2871094 < baseStart_2871094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871098 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_2871098 : Nat := 118140960795 + 2871098 * 2 ^ 59
def prefixEnd_2871098 : Nat := 4983230072969 + 3 ^ 40 * 2871098 * 2
def baseEnd_2871098 : Nat := 491417760054171016523689

theorem tailTrace_2871098 : CollatzResearch.WordTrace tailWord_2871098 prefixEnd_2871098 491417760054171016523689 := by
  unfold tailWord_2871098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26179386738127441336297487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69811697968339843563459965 26179386738127441336297487)
  ·
    refine ⟨39269080107191162004446231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26179386738127441336297487 39269080107191162004446231)
    ·
      refine ⟨58903620160786743006669347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39269080107191162004446231 58903620160786743006669347)
      ·
        refine ⟨88355430241180114510004021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58903620160786743006669347 88355430241180114510004021)
        ·
          refine ⟨8283321585110635735312877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88355430241180114510004021 8283321585110635735312877)
          ·
            refine ⟨3106245594416488400742329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8283321585110635735312877 3106245594416488400742329)
            ·
              refine ⟨2329684195812366300556747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106245594416488400742329 2329684195812366300556747)
              ·
                refine ⟨3494526293718549450835121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329684195812366300556747 3494526293718549450835121)
                ·
                  refine ⟨2620894720288912088126341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3494526293718549450835121 2620894720288912088126341)
                  ·
                    refine ⟨491417760054171016523689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2620894720288912088126341 491417760054171016523689)
                    ·
                      rfl

theorem cell23_2871098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_2871098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871098 prefixEnd_2871098 := by exact prefixLift 2871098
  have htrace : WordTrace (prefixWord ++ tailWord_2871098) baseStart_2871098 baseEnd_2871098 := by
    simpa [prefixWord, tailWord_2871098, baseEnd_2871098] using wordTrace_append hprefix tailTrace_2871098
  have hstable : (prefixWord ++ tailWord_2871098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871098).length < 2 ^ (prefixWord ++ tailWord_2871098).sum := by decide
  have hdescent : baseEnd_2871098 < baseStart_2871098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871137 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2871137 : Nat := 118140960795 + 2871137 * 2 ^ 59
def prefixEnd_2871137 : Nat := 4983230072969 + 3 ^ 40 * 2871137 * 2
def baseEnd_2871137 : Nat := 491424435302679465661129

theorem tailTrace_2871137 : CollatzResearch.WordTrace tailWord_2871137 prefixEnd_2871137 491424435302679465661129 := by
  unfold tailWord_2871137
  simp only [CollatzResearch.WordTrace]
  refine ⟨104718969399368475005859665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69812646266245650003906443 104718969399368475005859665)
  ·
    refine ⟨78539227049526356254394749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104718969399368475005859665 78539227049526356254394749)
    ·
      refine ⟨29452210143572383595398031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78539227049526356254394749 29452210143572383595398031)
      ·
        refine ⟨44178315215358575393097047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29452210143572383595398031 44178315215358575393097047)
        ·
          refine ⟨66267472823037863089645571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44178315215358575393097047 66267472823037863089645571)
          ·
            refine ⟨99401209234556794634468357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66267472823037863089645571 99401209234556794634468357)
            ·
              refine ⟨18637726731479398993962817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99401209234556794634468357 18637726731479398993962817)
              ·
                refine ⟨13978295048609549245472113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18637726731479398993962817 13978295048609549245472113)
                ·
                  refine ⟨10483721286457161934104085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13978295048609549245472113 10483721286457161934104085)
                  ·
                    refine ⟨491424435302679465661129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10483721286457161934104085 491424435302679465661129)
                    ·
                      rfl

theorem cell23_2871137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2871137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871137 prefixEnd_2871137 := by exact prefixLift 2871137
  have htrace : WordTrace (prefixWord ++ tailWord_2871137) baseStart_2871137 baseEnd_2871137 := by
    simpa [prefixWord, tailWord_2871137, baseEnd_2871137] using wordTrace_append hprefix tailTrace_2871137
  have hstable : (prefixWord ++ tailWord_2871137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871137).length < 2 ^ (prefixWord ++ tailWord_2871137).sum := by decide
  have hdescent : baseEnd_2871137 < baseStart_2871137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871138 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2871138 : Nat := 118140960795 + 2871138 * 2 ^ 59
def prefixEnd_2871138 : Nat := 4983230072969 + 3 ^ 40 * 2871138 * 2
def baseEnd_2871138 : Nat := 1474273819388692893070883

theorem tailTrace_2871138 : CollatzResearch.WordTrace tailWord_2871138 prefixEnd_2871138 1474273819388692893070883 := by
  unfold tailWord_2871138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26179751468091213044161517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69812670581576568117764045 26179751468091213044161517)
  ·
    refine ⟨9817406800534204891560569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26179751468091213044161517 9817406800534204891560569)
    ·
      refine ⟨7363055100400653668670427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9817406800534204891560569 7363055100400653668670427)
      ·
        refine ⟨11044582650600980503005641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363055100400653668670427 11044582650600980503005641)
        ·
          refine ⟨8283436987950735377254231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11044582650600980503005641 8283436987950735377254231)
          ·
            refine ⟨12425155481926103065881347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8283436987950735377254231 12425155481926103065881347)
            ·
              refine ⟨18637733222889154598822021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12425155481926103065881347 18637733222889154598822021)
              ·
                refine ⟨3494574979291716487279129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18637733222889154598822021 3494574979291716487279129)
                ·
                  refine ⟨2620931234468787365459347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3494574979291716487279129 2620931234468787365459347)
                  ·
                    refine ⟨3931396851703181048189021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2620931234468787365459347 3931396851703181048189021)
                    ·
                      refine ⟨1474273819388692893070883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931396851703181048189021 1474273819388692893070883)
                      ·
                        rfl

theorem cell23_2871138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2871138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871138 prefixEnd_2871138 := by exact prefixLift 2871138
  have htrace : WordTrace (prefixWord ++ tailWord_2871138) baseStart_2871138 baseEnd_2871138 := by
    simpa [prefixWord, tailWord_2871138, baseEnd_2871138] using wordTrace_append hprefix tailTrace_2871138
  have hstable : (prefixWord ++ tailWord_2871138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871138).length < 2 ^ (prefixWord ++ tailWord_2871138).sum := by decide
  have hdescent : baseEnd_2871138 < baseStart_2871138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871139 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 1, 2, 2]
def baseStart_2871139 : Nat := 118140960795 + 2871139 * 2 ^ 59
def prefixEnd_2871139 : Nat := 4983230072969 + 3 ^ 40 * 2871139 * 2
def baseEnd_2871139 : Nat := 1474274332869347389158379

theorem tailTrace_2871139 : CollatzResearch.WordTrace tailWord_2871139 prefixEnd_2871139 1474274332869347389158379 := by
  unfold tailWord_2871139
  simp only [CollatzResearch.WordTrace]
  refine ⟨104719042345361229347432471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69812694896907486231621647 104719042345361229347432471)
  ·
    refine ⟨157078563518041844021148707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104719042345361229347432471 157078563518041844021148707)
    ·
      refine ⟨235617845277062766031723061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157078563518041844021148707 235617845277062766031723061)
      ·
        refine ⟨22089172994724634315474037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235617845277062766031723061 22089172994724634315474037)
        ·
          refine ⟨2070859968255434467075691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22089172994724634315474037 2070859968255434467075691)
          ·
            refine ⟨3106289952383151700613537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070859968255434467075691 3106289952383151700613537)
            ·
              refine ⟨2329717464287363775460153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106289952383151700613537 2329717464287363775460153)
              ·
                refine ⟨1747288098215522831595115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329717464287363775460153 1747288098215522831595115)
                ·
                  refine ⟨2620932147323284247392673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747288098215522831595115 2620932147323284247392673)
                  ·
                    refine ⟨1965699110492463185544505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2620932147323284247392673 1965699110492463185544505)
                    ·
                      refine ⟨1474274332869347389158379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965699110492463185544505 1474274332869347389158379)
                      ·
                        rfl

theorem cell23_2871139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_2871139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871139 prefixEnd_2871139 := by exact prefixLift 2871139
  have htrace : WordTrace (prefixWord ++ tailWord_2871139) baseStart_2871139 baseEnd_2871139 := by
    simpa [prefixWord, tailWord_2871139, baseEnd_2871139] using wordTrace_append hprefix tailTrace_2871139
  have hstable : (prefixWord ++ tailWord_2871139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871139).length < 2 ^ (prefixWord ++ tailWord_2871139).sum := by decide
  have hdescent : baseEnd_2871139 < baseStart_2871139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871161 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 1, 4, 2]
def baseStart_2871161 : Nat := 118140960795 + 2871161 * 2 ^ 59
def prefixEnd_2871161 : Nat := 4983230072969 + 3 ^ 40 * 2871161 * 2
def baseEnd_2871161 : Nat := 1474285629443746303083277

theorem tailTrace_2871161 : CollatzResearch.WordTrace tailWord_2871161 prefixEnd_2871161 1474285629443746303083277 := by
  unfold tailWord_2871161
  simp only [CollatzResearch.WordTrace]
  refine ⟨104719844751281527104733337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69813229834187684736488891 104719844751281527104733337)
  ·
    refine ⟨78539883563461145328550003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104719844751281527104733337 78539883563461145328550003)
    ·
      refine ⟨117809825345191717992825005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78539883563461145328550003 117809825345191717992825005)
      ·
        refine ⟨44178684504446894247309377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117809825345191717992825005 44178684504446894247309377)
        ·
          refine ⟨33134013378335170685482033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44178684504446894247309377 33134013378335170685482033)
          ·
            refine ⟨24850510033751378014111525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33134013378335170685482033 24850510033751378014111525)
            ·
              refine ⟨4659470631328383377645911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24850510033751378014111525 4659470631328383377645911)
              ·
                refine ⟨6989205946992575066468867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659470631328383377645911 6989205946992575066468867)
                ·
                  refine ⟨10483808920488862599703301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989205946992575066468867 10483808920488862599703301)
                  ·
                    refine ⟨1965714172591661737444369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10483808920488862599703301 1965714172591661737444369)
                    ·
                      refine ⟨1474285629443746303083277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965714172591661737444369 1474285629443746303083277)
                      ·
                        rfl

theorem cell23_2871161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_2871161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871161 prefixEnd_2871161 := by exact prefixLift 2871161
  have htrace : WordTrace (prefixWord ++ tailWord_2871161) baseStart_2871161 baseEnd_2871161 := by
    simpa [prefixWord, tailWord_2871161, baseEnd_2871161] using wordTrace_append hprefix tailTrace_2871161
  have hstable : (prefixWord ++ tailWord_2871161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871161).length < 2 ^ (prefixWord ++ tailWord_2871161).sum := by decide
  have hdescent : baseEnd_2871161 < baseStart_2871161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871184 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 5]
def baseStart_2871184 : Nat := 118140960795 + 2871184 * 2 ^ 59
def prefixEnd_2871184 : Nat := 4983230072969 + 3 ^ 40 * 2871184 * 2
def baseEnd_2871184 : Nat := 163810826610977745899519

theorem tailTrace_2871184 : CollatzResearch.WordTrace tailWord_2871184 prefixEnd_2871184 163810826610977745899519 := by
  unfold tailWord_2871184
  simp only [CollatzResearch.WordTrace]
  refine ⟨52360341815099101016410303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69813789086798801355213737 52360341815099101016410303)
  ·
    refine ⟨78540512722648651524615455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52360341815099101016410303 78540512722648651524615455)
    ·
      refine ⟨117810769083972977286923183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78540512722648651524615455 117810769083972977286923183)
      ·
        refine ⟨176716153625959465930384775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117810769083972977286923183 176716153625959465930384775)
        ·
          refine ⟨265074230438939198895577163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176716153625959465930384775 265074230438939198895577163)
          ·
            refine ⟨397611345658408798343365745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265074230438939198895577163 397611345658408798343365745)
            ·
              refine ⟨298208509243806598757524309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397611345658408798343365745 298208509243806598757524309)
              ·
                refine ⟨1747315483850429289594869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 298208509243806598757524309 1747315483850429289594869)
                ·
                  refine ⟨163810826610977745899519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1747315483850429289594869 163810826610977745899519)
                  ·
                    rfl

theorem cell23_2871184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 5].length) (baseStart_2871184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871184 prefixEnd_2871184 := by exact prefixLift 2871184
  have htrace : WordTrace (prefixWord ++ tailWord_2871184) baseStart_2871184 baseEnd_2871184 := by
    simpa [prefixWord, tailWord_2871184, baseEnd_2871184] using wordTrace_append hprefix tailTrace_2871184
  have hstable : (prefixWord ++ tailWord_2871184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871184).length < 2 ^ (prefixWord ++ tailWord_2871184).sum := by decide
  have hdescent : baseEnd_2871184 < baseStart_2871184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871201 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 7]
def baseStart_2871201 : Nat := 118140960795 + 2871201 * 2 ^ 59
def prefixEnd_2871201 : Nat := 4983230072969 + 3 ^ 40 * 2871201 * 2
def baseEnd_2871201 : Nat := 163811796518880682953677

theorem tailTrace_2871201 : CollatzResearch.WordTrace tailWord_2871201 prefixEnd_2871201 163811796518880682953677 := by
  unfold tailWord_2871201
  simp only [CollatzResearch.WordTrace]
  refine ⟨104721303671136613936189457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69814202447424409290792971 104721303671136613936189457)
  ·
    refine ⟨78540977753352460452142093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104721303671136613936189457 78540977753352460452142093)
    ·
      refine ⟨29452866657507172669553285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78540977753352460452142093 29452866657507172669553285)
      ·
        refine ⟨5522412498282594875541241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29452866657507172669553285 5522412498282594875541241)
        ·
          refine ⟨4141809373711946156655931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522412498282594875541241 4141809373711946156655931)
          ·
            refine ⟨6212714060567919234983897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141809373711946156655931 6212714060567919234983897)
            ·
              refine ⟨4659535545425939426237923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6212714060567919234983897 4659535545425939426237923)
              ·
                refine ⟨6989303318138909139356885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659535545425939426237923 6989303318138909139356885)
                ·
                  refine ⟨163811796518880682953677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6989303318138909139356885 163811796518880682953677)
                  ·
                    rfl

theorem cell23_2871201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 7].length) (baseStart_2871201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871201 prefixEnd_2871201 := by exact prefixLift 2871201
  have htrace : WordTrace (prefixWord ++ tailWord_2871201) baseStart_2871201 baseEnd_2871201 := by
    simpa [prefixWord, tailWord_2871201, baseEnd_2871201] using wordTrace_append hprefix tailTrace_2871201
  have hstable : (prefixWord ++ tailWord_2871201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871201).length < 2 ^ (prefixWord ++ tailWord_2871201).sum := by decide
  have hdescent : baseEnd_2871201 < baseStart_2871201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871345 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 2, 3, 2]
def baseStart_2871345 : Nat := 118140960795 + 2871345 * 2 ^ 59
def prefixEnd_2871345 : Nat := 4983230072969 + 3 ^ 40 * 2871345 * 2
def baseEnd_2871345 : Nat := 1474380109884173583182431

theorem tailTrace_2871345 : CollatzResearch.WordTrace tailWord_2871345 prefixEnd_2871345 1474380109884173583182431 := by
  unfold tailWord_2871345
  simp only [CollatzResearch.WordTrace]
  refine ⟨104726555782614926529431489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69817703855076617686287659 104726555782614926529431489)
  ·
    refine ⟨78544916836961194897073617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104726555782614926529431489 78544916836961194897073617)
    ·
      refine ⟨58908687627720896172805213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78544916836961194897073617 58908687627720896172805213)
      ·
        refine ⟨22090757860395336064801955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58908687627720896172805213 22090757860395336064801955)
        ·
          refine ⟨33136136790593004097202933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22090757860395336064801955 33136136790593004097202933)
          ·
            refine ⟨3106512824118094134112775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33136136790593004097202933 3106512824118094134112775)
            ·
              refine ⟨4659769236177141201169163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106512824118094134112775 4659769236177141201169163)
              ·
                refine ⟨6989653854265711801753745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659769236177141201169163 6989653854265711801753745)
                ·
                  refine ⟨5242240390699283851315309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6989653854265711801753745 5242240390699283851315309)
                  ·
                    refine ⟨1965840146512231444243241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5242240390699283851315309 1965840146512231444243241)
                    ·
                      refine ⟨1474380109884173583182431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965840146512231444243241 1474380109884173583182431)
                      ·
                        rfl

theorem cell23_2871345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_2871345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871345 prefixEnd_2871345 := by exact prefixLift 2871345
  have htrace : WordTrace (prefixWord ++ tailWord_2871345) baseStart_2871345 baseEnd_2871345 := by
    simpa [prefixWord, tailWord_2871345, baseEnd_2871345] using wordTrace_append hprefix tailTrace_2871345
  have hstable : (prefixWord ++ tailWord_2871345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871345).length < 2 ^ (prefixWord ++ tailWord_2871345).sum := by decide
  have hdescent : baseEnd_2871345 < baseStart_2871345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871352 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 1, 1, 3]
def baseStart_2871352 : Nat := 118140960795 + 2871352 * 2 ^ 59
def prefixEnd_2871352 : Nat := 4983230072969 + 3 ^ 40 * 2871352 * 2
def baseEnd_2871352 : Nat := 1474383704248755055794899

theorem tailTrace_2871352 : CollatzResearch.WordTrace tailWord_2871352 prefixEnd_2871352 1474383704248755055794899 := by
  unfold tailWord_2871352
  simp only [CollatzResearch.WordTrace]
  refine ⟨52363405546794783362468155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69817874062393044483290873 52363405546794783362468155)
  ·
    refine ⟨78545108320192175043702233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52363405546794783362468155 78545108320192175043702233)
    ·
      refine ⟨58908831240144131282776675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78545108320192175043702233 58908831240144131282776675)
      ·
        refine ⟨88363246860216196924165013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58908831240144131282776675 88363246860216196924165013)
        ·
          refine ⟨4142027196572634230820235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88363246860216196924165013 4142027196572634230820235)
          ·
            refine ⟨6213040794858951346230353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142027196572634230820235 6213040794858951346230353)
            ·
              refine ⟨4659780596144213509672765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6213040794858951346230353 4659780596144213509672765)
              ·
                refine ⟨1747417723554080066127287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4659780596144213509672765 1747417723554080066127287)
                ·
                  refine ⟨2621126585331120099190931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747417723554080066127287 2621126585331120099190931)
                  ·
                    refine ⟨3931689877996680148786397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2621126585331120099190931 3931689877996680148786397)
                    ·
                      refine ⟨1474383704248755055794899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931689877996680148786397 1474383704248755055794899)
                      ·
                        rfl

theorem cell23_2871352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_2871352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871352 prefixEnd_2871352 := by exact prefixLift 2871352
  have htrace : WordTrace (prefixWord ++ tailWord_2871352) baseStart_2871352 baseEnd_2871352 := by
    simpa [prefixWord, tailWord_2871352, baseEnd_2871352] using wordTrace_append hprefix tailTrace_2871352
  have hstable : (prefixWord ++ tailWord_2871352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871352).length < 2 ^ (prefixWord ++ tailWord_2871352).sum := by decide
  have hdescent : baseEnd_2871352 < baseStart_2871352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871354 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_2871354 : Nat := 118140960795 + 2871354 * 2 ^ 59
def prefixEnd_2871354 : Nat := 4983230072969 + 3 ^ 40 * 2871354 * 2
def baseEnd_2871354 : Nat := 1474384731210064047969889

theorem tailTrace_2871354 : CollatzResearch.WordTrace tailWord_2871354 prefixEnd_2871354 1474384731210064047969889 := by
  unfold tailWord_2871354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26181721009895580266627279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69817922693054880711006077 26181721009895580266627279)
  ·
    refine ⟨39272581514843370399940919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26181721009895580266627279 39272581514843370399940919)
    ·
      refine ⟨58908872272265055599911379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39272581514843370399940919 58908872272265055599911379)
      ·
        refine ⟨88363308408397583399867069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58908872272265055599911379 88363308408397583399867069)
        ·
          refine ⟨33136240653149093774950151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88363308408397583399867069 33136240653149093774950151)
          ·
            refine ⟨49704360979723640662425227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33136240653149093774950151 49704360979723640662425227)
            ·
              refine ⟨74556541469585460993637841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49704360979723640662425227 74556541469585460993637841)
              ·
                refine ⟨55917406102189095745228381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74556541469585460993637841 55917406102189095745228381)
                ·
                  refine ⟨20969027288320910904460643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55917406102189095745228381 20969027288320910904460643)
                  ·
                    refine ⟨31453540932481366356690965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20969027288320910904460643 31453540932481366356690965)
                    ·
                      refine ⟨1474384731210064047969889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31453540932481366356690965 1474384731210064047969889)
                      ·
                        rfl

theorem cell23_2871354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_2871354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871354 prefixEnd_2871354 := by exact prefixLift 2871354
  have htrace : WordTrace (prefixWord ++ tailWord_2871354) baseStart_2871354 baseEnd_2871354 := by
    simpa [prefixWord, tailWord_2871354, baseEnd_2871354] using wordTrace_append hprefix tailTrace_2871354
  have hstable : (prefixWord ++ tailWord_2871354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871354).length < 2 ^ (prefixWord ++ tailWord_2871354).sum := by decide
  have hdescent : baseEnd_2871354 < baseStart_2871354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871378 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2871378 : Nat := 118140960795 + 2871378 * 2 ^ 59
def prefixEnd_2871378 : Nat := 4983230072969 + 3 ^ 40 * 2871378 * 2
def baseEnd_2871378 : Nat := 1474397054745771954069779

theorem tailTrace_2871378 : CollatzResearch.WordTrace tailWord_2871378 prefixEnd_2871378 1474397054745771954069779 := by
  unfold tailWord_2871378
  simp only [CollatzResearch.WordTrace]
  refine ⟨26181939847873843291345697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69818506260996915443588525 26181939847873843291345697)
  ·
    refine ⟨19636454885905382468509273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26181939847873843291345697 19636454885905382468509273)
    ·
      refine ⟨14727341164429036851381955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19636454885905382468509273 14727341164429036851381955)
      ·
        refine ⟨22091011746643555277072933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14727341164429036851381955 22091011746643555277072933)
        ·
          refine ⟨4142064702495666614451175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22091011746643555277072933 4142064702495666614451175)
          ·
            refine ⟨6213097053743499921676763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142064702495666614451175 6213097053743499921676763)
            ·
              refine ⟨9319645580615249882515145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213097053743499921676763 9319645580615249882515145)
              ·
                refine ⟨6989734185461437411886359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9319645580615249882515145 6989734185461437411886359)
                ·
                  refine ⟨10484601278192156117829539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989734185461437411886359 10484601278192156117829539)
                  ·
                    refine ⟨15726901917288234176744309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10484601278192156117829539 15726901917288234176744309)
                    ·
                      refine ⟨1474397054745771954069779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15726901917288234176744309 1474397054745771954069779)
                      ·
                        rfl

theorem cell23_2871378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2871378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871378 prefixEnd_2871378 := by exact prefixLift 2871378
  have htrace : WordTrace (prefixWord ++ tailWord_2871378) baseStart_2871378 baseEnd_2871378 := by
    simpa [prefixWord, tailWord_2871378, baseEnd_2871378] using wordTrace_append hprefix tailTrace_2871378
  have hstable : (prefixWord ++ tailWord_2871378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871378).length < 2 ^ (prefixWord ++ tailWord_2871378).sum := by decide
  have hdescent : baseEnd_2871378 < baseStart_2871378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871388 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2871388 : Nat := 118140960795 + 2871388 * 2 ^ 59
def prefixEnd_2871388 : Nat := 4983230072969 + 3 ^ 40 * 2871388 * 2
def baseEnd_2871388 : Nat := 1474402189552316914944733

theorem tailTrace_2871388 : CollatzResearch.WordTrace tailWord_2871388 prefixEnd_2871388 1474402189552316914944733 := by
  unfold tailWord_2871388
  simp only [CollatzResearch.WordTrace]
  refine ⟨52364062060729572436623409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69818749414306096582164545 52364062060729572436623409)
  ·
    refine ⟨39273046545547179327467557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52364062060729572436623409 39273046545547179327467557)
    ·
      refine ⟨7363696227290096123900167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39273046545547179327467557 7363696227290096123900167)
      ·
        refine ⟨11045544340935144185850251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363696227290096123900167 11045544340935144185850251)
        ·
          refine ⟨16568316511402716278775377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11045544340935144185850251 16568316511402716278775377)
          ·
            refine ⟨12426237383552037209081533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16568316511402716278775377 12426237383552037209081533)
            ·
              refine ⟨4659839018832013953405575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12426237383552037209081533 4659839018832013953405575)
              ·
                refine ⟨6989758528248020930108363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659839018832013953405575 6989758528248020930108363)
                ·
                  refine ⟨10484637792372031395162545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989758528248020930108363 10484637792372031395162545)
                  ·
                    refine ⟨7863478344279023546371909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10484637792372031395162545 7863478344279023546371909)
                    ·
                      refine ⟨1474402189552316914944733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7863478344279023546371909 1474402189552316914944733)
                      ·
                        rfl

theorem cell23_2871388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2871388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871388 prefixEnd_2871388 := by exact prefixLift 2871388
  have htrace : WordTrace (prefixWord ++ tailWord_2871388) baseStart_2871388 baseEnd_2871388 := by
    simpa [prefixWord, tailWord_2871388, baseEnd_2871388] using wordTrace_append hprefix tailTrace_2871388
  have hstable : (prefixWord ++ tailWord_2871388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871388).length < 2 ^ (prefixWord ++ tailWord_2871388).sum := by decide
  have hdescent : baseEnd_2871388 < baseStart_2871388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871391 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_2871391 : Nat := 118140960795 + 2871391 * 2 ^ 59
def prefixEnd_2871391 : Nat := 4983230072969 + 3 ^ 40 * 2871391 * 2
def baseEnd_2871391 : Nat := 1474403729994280403207219

theorem tailTrace_2871391 : CollatzResearch.WordTrace tailWord_2871391 prefixEnd_2871391 1474403729994280403207219 := by
  unfold tailWord_2871391
  simp only [CollatzResearch.WordTrace]
  refine ⟨104728233540448276385606027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69818822360298850923737351 104728233540448276385606027)
  ·
    refine ⟨157092350310672414578409041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104728233540448276385606027 157092350310672414578409041)
    ·
      refine ⟨117819262733004310933806781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157092350310672414578409041 117819262733004310933806781)
      ·
        refine ⟨44182223524876616600177543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117819262733004310933806781 44182223524876616600177543)
        ·
          refine ⟨66273335287314924900266315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44182223524876616600177543 66273335287314924900266315)
          ·
            refine ⟨99410002930972387350399473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66273335287314924900266315 99410002930972387350399473)
            ·
              refine ⟨74557502198229290512799605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99410002930972387350399473 74557502198229290512799605)
              ·
                refine ⟨6989765831083995985574963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74557502198229290512799605 6989765831083995985574963)
                ·
                  refine ⟨10484648746625993978362445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989765831083995985574963 10484648746625993978362445)
                  ·
                    refine ⟨3931743279984747741885917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10484648746625993978362445 3931743279984747741885917)
                    ·
                      refine ⟨1474403729994280403207219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931743279984747741885917 1474403729994280403207219)
                      ·
                        rfl

theorem cell23_2871391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_2871391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871391 prefixEnd_2871391 := by exact prefixLift 2871391
  have htrace : WordTrace (prefixWord ++ tailWord_2871391) baseStart_2871391 baseEnd_2871391 := by
    simpa [prefixWord, tailWord_2871391, baseEnd_2871391] using wordTrace_append hprefix tailTrace_2871391
  have hstable : (prefixWord ++ tailWord_2871391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871391).length < 2 ^ (prefixWord ++ tailWord_2871391).sum := by decide
  have hdescent : baseEnd_2871391 < baseStart_2871391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871408 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 4, 1, 3]
def baseStart_2871408 : Nat := 118140960795 + 2871408 * 2 ^ 59
def prefixEnd_2871408 : Nat := 4983230072969 + 3 ^ 40 * 2871408 * 2
def baseEnd_2871408 : Nat := 1474412459165406836694641

theorem tailTrace_2871408 : CollatzResearch.WordTrace tailWord_2871408 prefixEnd_2871408 1474412459165406836694641 := by
  unfold tailWord_2871408
  simp only [CollatzResearch.WordTrace]
  refine ⟨52364426790693344144487439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69819235720924458859316585 52364426790693344144487439)
  ·
    refine ⟨78546640186040016216731159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52364426790693344144487439 78546640186040016216731159)
    ·
      refine ⟨117819960279060024325096739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78546640186040016216731159 117819960279060024325096739)
      ·
        refine ⟨176729940418590036487645109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117819960279060024325096739 176729940418590036487645109)
        ·
          refine ⟨16568431914242815920716729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176729940418590036487645109 16568431914242815920716729)
          ·
            refine ⟨12426323935682111940537547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16568431914242815920716729 12426323935682111940537547)
            ·
              refine ⟨18639485903523167910806321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12426323935682111940537547 18639485903523167910806321)
              ·
                refine ⟨13979614427642375933104741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18639485903523167910806321 13979614427642375933104741)
                ·
                  refine ⟨2621177705182945487457139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13979614427642375933104741 2621177705182945487457139)
                  ·
                    refine ⟨3931766557774418231185709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2621177705182945487457139 3931766557774418231185709)
                    ·
                      refine ⟨1474412459165406836694641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931766557774418231185709 1474412459165406836694641)
                      ·
                        rfl

theorem cell23_2871408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_2871408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871408 prefixEnd_2871408 := by exact prefixLift 2871408
  have htrace : WordTrace (prefixWord ++ tailWord_2871408) baseStart_2871408 baseEnd_2871408 := by
    simpa [prefixWord, tailWord_2871408, baseEnd_2871408] using wordTrace_append hprefix tailTrace_2871408
  have hstable : (prefixWord ++ tailWord_2871408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871408).length < 2 ^ (prefixWord ++ tailWord_2871408).sum := by decide
  have hdescent : baseEnd_2871408 < baseStart_2871408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871446 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2871446 : Nat := 118140960795 + 2871446 * 2 ^ 59
def prefixEnd_2871446 : Nat := 4983230072969 + 3 ^ 40 * 2871446 * 2
def baseEnd_2871446 : Nat := 1474431971430277688019467

theorem tailTrace_2871446 : CollatzResearch.WordTrace tailWord_2871446 prefixEnd_2871446 1474431971430277688019467 := by
  unfold tailWord_2871446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6545639972203063798678637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69820159703499347185905461 6545639972203063798678637)
  ·
    refine ⟨2454614989576148924504489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6545639972203063798678637 2454614989576148924504489)
    ·
      refine ⟨1840961242182111693378367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2454614989576148924504489 1840961242182111693378367)
      ·
        refine ⟨2761441863273167540067551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840961242182111693378367 2761441863273167540067551)
        ·
          refine ⟨4142162794909751310101327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761441863273167540067551 4142162794909751310101327)
          ·
            refine ⟨6213244192364626965151991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142162794909751310101327 6213244192364626965151991)
            ·
              refine ⟨9319866288546940447727987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213244192364626965151991 9319866288546940447727987)
              ·
                refine ⟨13979799432820410671591981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319866288546940447727987 13979799432820410671591981)
                ·
                  refine ⟨5242424787307654001846993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13979799432820410671591981 5242424787307654001846993)
                  ·
                    refine ⟨3931818590480740501385245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5242424787307654001846993 3931818590480740501385245)
                    ·
                      refine ⟨1474431971430277688019467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931818590480740501385245 1474431971430277688019467)
                      ·
                        rfl

theorem cell23_2871446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2871446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871446 prefixEnd_2871446 := by exact prefixLift 2871446
  have htrace : WordTrace (prefixWord ++ tailWord_2871446) baseStart_2871446 baseEnd_2871446 := by
    simpa [prefixWord, tailWord_2871446, baseEnd_2871446] using wordTrace_append hprefix tailTrace_2871446
  have hstable : (prefixWord ++ tailWord_2871446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871446).length < 2 ^ (prefixWord ++ tailWord_2871446).sum := by decide
  have hdescent : baseEnd_2871446 < baseStart_2871446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871469 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_2871469 : Nat := 118140960795 + 2871469 * 2 ^ 59
def prefixEnd_2871469 : Nat := 4983230072969 + 3 ^ 40 * 2871469 * 2
def baseEnd_2871469 : Nat := 1474443781485331098031861

theorem tailTrace_2871469 : CollatzResearch.WordTrace tailWord_2871469 prefixEnd_2871469 1474443781485331098031861 := by
  unfold tailWord_2871469
  simp only [CollatzResearch.WordTrace]
  refine ⟨104731078434165695706945461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69820718956110463804630307 104731078434165695706945461)
  ·
    refine ⟨9818538603203033972526137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104731078434165695706945461 9818538603203033972526137)
    ·
      refine ⟨7363903952402275479394603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9818538603203033972526137 7363903952402275479394603)
      ·
        refine ⟨11045855928603413219091905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363903952402275479394603 11045855928603413219091905)
        ·
          refine ⟨8284391946452559914318929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11045855928603413219091905 8284391946452559914318929)
          ·
            refine ⟨6213293959839419935739197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8284391946452559914318929 6213293959839419935739197)
            ·
              refine ⟨2329985234939782475902199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6213293959839419935739197 2329985234939782475902199)
              ·
                refine ⟨3494977852409673713853299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329985234939782475902199 3494977852409673713853299)
                ·
                  refine ⟨5242466778614510570779949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494977852409673713853299 5242466778614510570779949)
                  ·
                    refine ⟨1965925041980441464042481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5242466778614510570779949 1965925041980441464042481)
                    ·
                      refine ⟨1474443781485331098031861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1965925041980441464042481 1474443781485331098031861)
                      ·
                        rfl

theorem cell23_2871469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_2871469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871469 prefixEnd_2871469 := by exact prefixLift 2871469
  have htrace : WordTrace (prefixWord ++ tailWord_2871469) baseStart_2871469 baseEnd_2871469 := by
    simpa [prefixWord, tailWord_2871469, baseEnd_2871469] using wordTrace_append hprefix tailTrace_2871469
  have hstable : (prefixWord ++ tailWord_2871469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871469).length < 2 ^ (prefixWord ++ tailWord_2871469).sum := by decide
  have hdescent : baseEnd_2871469 < baseStart_2871469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871498 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_2871498 : Nat := 118140960795 + 2871498 * 2 ^ 59
def prefixEnd_2871498 : Nat := 4983230072969 + 3 ^ 40 * 2871498 * 2
def baseEnd_2871498 : Nat := 1474458672424311484569227

theorem tailTrace_2871498 : CollatzResearch.WordTrace tailWord_2871498 prefixEnd_2871498 1474458672424311484569227 := by
  unfold tailWord_2871498
  simp only [CollatzResearch.WordTrace]
  refine ⟨26183034037765158414937787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69821424100707089106500765 26183034037765158414937787)
  ·
    refine ⟨39274551056647737622406681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26183034037765158414937787 39274551056647737622406681)
    ·
      refine ⟨29455913292485803216805011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39274551056647737622406681 29455913292485803216805011)
      ·
        refine ⟨44183869938728704825207517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29455913292485803216805011 44183869938728704825207517)
        ·
          refine ⟨16568951227023264309452819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44183869938728704825207517 16568951227023264309452819)
          ·
            refine ⟨24853426840534896464179229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16568951227023264309452819 24853426840534896464179229)
            ·
              refine ⟨9320035065200586174067211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24853426840534896464179229 9320035065200586174067211)
              ·
                refine ⟨13980052597800879261100817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9320035065200586174067211 13980052597800879261100817)
                ·
                  refine ⟨10485039448350659445825613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13980052597800879261100817 10485039448350659445825613)
                  ·
                    refine ⟨3931889793131497292184605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10485039448350659445825613 3931889793131497292184605)
                    ·
                      refine ⟨1474458672424311484569227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3931889793131497292184605 1474458672424311484569227)
                      ·
                        rfl

theorem cell23_2871498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_2871498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871498 prefixEnd_2871498 := by exact prefixLift 2871498
  have htrace : WordTrace (prefixWord ++ tailWord_2871498) baseStart_2871498 baseEnd_2871498 := by
    simpa [prefixWord, tailWord_2871498, baseEnd_2871498] using wordTrace_append hprefix tailTrace_2871498
  have hstable : (prefixWord ++ tailWord_2871498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871498).length < 2 ^ (prefixWord ++ tailWord_2871498).sum := by decide
  have hdescent : baseEnd_2871498 < baseStart_2871498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871551 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_2871551 : Nat := 118140960795 + 2871551 * 2 ^ 59
def prefixEnd_2871551 : Nat := 4983230072969 + 3 ^ 40 * 2871551 * 2
def baseEnd_2871551 : Nat := 1474485886898999777206483

theorem tailTrace_2871551 : CollatzResearch.WordTrace tailWord_2871551 prefixEnd_2871551 1474485886898999777206483 := by
  unfold tailWord_2871551
  simp only [CollatzResearch.WordTrace]
  refine ⟨104734069219868623711430507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69822712813245749140953671 104734069219868623711430507)
  ·
    refine ⟨157101103829802935567145761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104734069219868623711430507 157101103829802935567145761)
    ·
      refine ⟨117825827872352201675359321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157101103829802935567145761 117825827872352201675359321)
      ·
        refine ⟨88369370904264151256519491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117825827872352201675359321 88369370904264151256519491)
        ·
          refine ⟨132554056356396226884779237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88369370904264151256519491 132554056356396226884779237)
          ·
            refine ⟨24853885566824292540896107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132554056356396226884779237 24853885566824292540896107)
            ·
              refine ⟨37280828350236438811344161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24853885566824292540896107 37280828350236438811344161)
              ·
                refine ⟨27960621262677329108508121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37280828350236438811344161 27960621262677329108508121)
                ·
                  refine ⟨20970465947007996831381091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27960621262677329108508121 20970465947007996831381091)
                  ·
                    refine ⟨31455698920511995247071637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20970465947007996831381091 31455698920511995247071637)
                    ·
                      refine ⟨1474485886898999777206483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31455698920511995247071637 1474485886898999777206483)
                      ·
                        rfl

theorem cell23_2871551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_2871551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871551 prefixEnd_2871551 := by exact prefixLift 2871551
  have htrace : WordTrace (prefixWord ++ tailWord_2871551) baseStart_2871551 baseEnd_2871551 := by
    simpa [prefixWord, tailWord_2871551, baseEnd_2871551] using wordTrace_append hprefix tailTrace_2871551
  have hstable : (prefixWord ++ tailWord_2871551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871551).length < 2 ^ (prefixWord ++ tailWord_2871551).sum := by decide
  have hdescent : baseEnd_2871551 < baseStart_2871551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871592 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2871592 : Nat := 118140960795 + 2871592 * 2 ^ 59
def prefixEnd_2871592 : Nat := 4983230072969 + 3 ^ 40 * 2871592 * 2
def baseEnd_2871592 : Nat := 1474506939605834116793795

theorem tailTrace_2871592 : CollatzResearch.WordTrace tailWord_2871592 prefixEnd_2871592 1474506939605834116793795 := by
  unfold tailWord_2871592
  simp only [CollatzResearch.WordTrace]
  refine ⟨52367782306360043856836515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69823709741813391809115353 52367782306360043856836515)
  ·
    refine ⟨78551673459540065785254773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52367782306360043856836515 78551673459540065785254773)
    ·
      refine ⟨7364219386831881167367635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78551673459540065785254773 7364219386831881167367635)
      ·
        refine ⟨11046329080247821751051453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364219386831881167367635 11046329080247821751051453)
        ·
          refine ⟨4142373405092933156644295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11046329080247821751051453 4142373405092933156644295)
          ·
            refine ⟨6213560107639399734966443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142373405092933156644295 6213560107639399734966443)
            ·
              refine ⟨9320340161459099602449665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213560107639399734966443 9320340161459099602449665)
              ·
                refine ⟨6990255121094324701837249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9320340161459099602449665 6990255121094324701837249)
                ·
                  refine ⟨5242691340820743526377937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990255121094324701837249 5242691340820743526377937)
                  ·
                    refine ⟨3932018505615557644783453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5242691340820743526377937 3932018505615557644783453)
                    ·
                      refine ⟨1474506939605834116793795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3932018505615557644783453 1474506939605834116793795)
                      ·
                        rfl

theorem cell23_2871592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2871592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871592 prefixEnd_2871592 := by exact prefixLift 2871592
  have htrace : WordTrace (prefixWord ++ tailWord_2871592) baseStart_2871592 baseEnd_2871592 := by
    simpa [prefixWord, tailWord_2871592, baseEnd_2871592] using wordTrace_append hprefix tailTrace_2871592
  have hstable : (prefixWord ++ tailWord_2871592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871592).length < 2 ^ (prefixWord ++ tailWord_2871592).sum := by decide
  have hdescent : baseEnd_2871592 < baseStart_2871592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871615 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 4, 3, 2]
def baseStart_2871615 : Nat := 118140960795 + 2871615 * 2 ^ 59
def prefixEnd_2871615 : Nat := 4983230072969 + 3 ^ 40 * 2871615 * 2
def baseEnd_2871615 : Nat := 1474518749660887526806189

theorem tailTrace_2871615 : CollatzResearch.WordTrace tailWord_2871615 prefixEnd_2871615 1474518749660887526806189 := by
  unfold tailWord_2871615
  simp only [CollatzResearch.WordTrace]
  refine ⟨104736403491636762641760299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69824268994424508427840199 104736403491636762641760299)
  ·
    refine ⟨157104605237455143962640449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104736403491636762641760299 157104605237455143962640449)
    ·
      refine ⟨117828453928091357971980337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157104605237455143962640449 117828453928091357971980337)
      ·
        refine ⟨88371340446068518478985253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117828453928091357971980337 88371340446068518478985253)
        ·
          refine ⟨16569626333637847214809735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88371340446068518478985253 16569626333637847214809735)
          ·
            refine ⟨24854439500456770822214603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16569626333637847214809735 24854439500456770822214603)
            ·
              refine ⟨37281659250685156233321905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24854439500456770822214603 37281659250685156233321905)
              ·
                refine ⟨27961244438013867174991429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37281659250685156233321905 27961244438013867174991429)
                ·
                  refine ⟨5242733332127600095310893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27961244438013867174991429 5242733332127600095310893)
                  ·
                    refine ⟨1966024999547850035741585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5242733332127600095310893 1966024999547850035741585)
                    ·
                      refine ⟨1474518749660887526806189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966024999547850035741585 1474518749660887526806189)
                      ·
                        rfl

theorem cell23_2871615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_2871615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871615 prefixEnd_2871615 := by exact prefixLift 2871615
  have htrace : WordTrace (prefixWord ++ tailWord_2871615) baseStart_2871615 baseEnd_2871615 := by
    simpa [prefixWord, tailWord_2871615, baseEnd_2871615] using wordTrace_append hprefix tailTrace_2871615
  have hstable : (prefixWord ++ tailWord_2871615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871615).length < 2 ^ (prefixWord ++ tailWord_2871615).sum := by decide
  have hdescent : baseEnd_2871615 < baseStart_2871615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871632 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 2, 3, 2]
def baseStart_2871632 : Nat := 118140960795 + 2871632 * 2 ^ 59
def prefixEnd_2871632 : Nat := 4983230072969 + 3 ^ 40 * 2871632 * 2
def baseEnd_2871632 : Nat := 1474527478832013960293611

theorem tailTrace_2871632 : CollatzResearch.WordTrace tailWord_2871632 prefixEnd_2871632 1474527478832013960293611 := by
  unfold tailWord_2871632
  simp only [CollatzResearch.WordTrace]
  refine ⟨52368511766287587272564575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69824682355050116363419433 52368511766287587272564575)
  ·
    refine ⟨78552767649431380908846863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52368511766287587272564575 78552767649431380908846863)
    ·
      refine ⟨117829151474147071363270295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78552767649431380908846863 117829151474147071363270295)
      ·
        refine ⟨176743727211220607044905443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117829151474147071363270295 176743727211220607044905443)
        ·
          refine ⟨265115590816830910567358165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176743727211220607044905443 265115590816830910567358165)
          ·
            refine ⟨6213646659769474466422457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265115590816830910567358165 6213646659769474466422457)
            ·
              refine ⟨4660234994827105849816843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6213646659769474466422457 4660234994827105849816843)
              ·
                refine ⟨6990352492240658774725265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660234994827105849816843 6990352492240658774725265)
                ·
                  refine ⟨5242764369180494081043949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990352492240658774725265 5242764369180494081043949)
                  ·
                    refine ⟨1966036638442685280391481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5242764369180494081043949 1966036638442685280391481)
                    ·
                      refine ⟨1474527478832013960293611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966036638442685280391481 1474527478832013960293611)
                      ·
                        rfl

theorem cell23_2871632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 3, 2].length) (baseStart_2871632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871632 prefixEnd_2871632 := by exact prefixLift 2871632
  have htrace : WordTrace (prefixWord ++ tailWord_2871632) baseStart_2871632 baseEnd_2871632 := by
    simpa [prefixWord, tailWord_2871632, baseEnd_2871632] using wordTrace_append hprefix tailTrace_2871632
  have hstable : (prefixWord ++ tailWord_2871632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871632).length < 2 ^ (prefixWord ++ tailWord_2871632).sum := by decide
  have hdescent : baseEnd_2871632 < baseStart_2871632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871656 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2871656 : Nat := 118140960795 + 2871656 * 2 ^ 59
def prefixEnd_2871656 : Nat := 4983230072969 + 3 ^ 40 * 2871656 * 2
def baseEnd_2871656 : Nat := 1474539802367721866393501

theorem tailTrace_2871656 : CollatzResearch.WordTrace tailWord_2871656 prefixEnd_2871656 1474539802367721866393501 := by
  unfold tailWord_2871656
  simp only [CollatzResearch.WordTrace]
  refine ⟨52368949442244113322001411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69825265922992151096001881 52368949442244113322001411)
  ·
    refine ⟨78553424163366169983002117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52368949442244113322001411 78553424163366169983002117)
    ·
      refine ⟨14728767030631156871812897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78553424163366169983002117 14728767030631156871812897)
      ·
        refine ⟨11046575272973367653859673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14728767030631156871812897 11046575272973367653859673)
        ·
          refine ⟨8284931454730025740394755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11046575272973367653859673 8284931454730025740394755)
          ·
            refine ⟨12427397182095038610592133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8284931454730025740394755 12427397182095038610592133)
            ·
              refine ⟨2330136971642819739486025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12427397182095038610592133 2330136971642819739486025)
              ·
                refine ⟨1747602728732114804614519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330136971642819739486025 1747602728732114804614519)
                ·
                  refine ⟨2621404093098172206921779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747602728732114804614519 2621404093098172206921779)
                  ·
                    refine ⟨3932106139647258310382669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2621404093098172206921779 3932106139647258310382669)
                    ·
                      refine ⟨1474539802367721866393501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3932106139647258310382669 1474539802367721866393501)
                      ·
                        rfl

theorem cell23_2871656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2871656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871656 prefixEnd_2871656 := by exact prefixLift 2871656
  have htrace : WordTrace (prefixWord ++ tailWord_2871656) baseStart_2871656 baseEnd_2871656 := by
    simpa [prefixWord, tailWord_2871656, baseEnd_2871656] using wordTrace_append hprefix tailTrace_2871656
  have hstable : (prefixWord ++ tailWord_2871656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871656).length < 2 ^ (prefixWord ++ tailWord_2871656).sum := by decide
  have hdescent : baseEnd_2871656 < baseStart_2871656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871675 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 4]
def baseStart_2871675 : Nat := 118140960795 + 2871675 * 2 ^ 59
def prefixEnd_2871675 : Nat := 4983230072969 + 3 ^ 40 * 2871675 * 2
def baseEnd_2871675 : Nat := 1474549558500157292055913

theorem tailTrace_2871675 : CollatzResearch.WordTrace tailWord_2871675 prefixEnd_2871675 1474549558500157292055913 := by
  unfold tailWord_2871675
  simp only [CollatzResearch.WordTrace]
  refine ⟨104738591871419392888944479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69825727914279595259296319 104738591871419392888944479)
  ·
    refine ⟨157107887807129089333416719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104738591871419392888944479 157107887807129089333416719)
    ·
      refine ⟨235661831710693634000125079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157107887807129089333416719 235661831710693634000125079)
      ·
        refine ⟨353492747566040451000187619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235661831710693634000125079 353492747566040451000187619)
        ·
          refine ⟨530239121349060676500281429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353492747566040451000187619 530239121349060676500281429)
          ·
            refine ⟨6213739703309304802737673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 530239121349060676500281429 6213739703309304802737673)
            ·
              refine ⟨4660304777481978602053255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6213739703309304802737673 4660304777481978602053255)
              ·
                refine ⟨6990457166222967903079883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660304777481978602053255 6990457166222967903079883)
                ·
                  refine ⟨10485685749334451854619825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990457166222967903079883 10485685749334451854619825)
                  ·
                    refine ⟨7864264312000838890964869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10485685749334451854619825 7864264312000838890964869)
                    ·
                      refine ⟨1474549558500157292055913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7864264312000838890964869 1474549558500157292055913)
                      ·
                        rfl

theorem cell23_2871675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 4].length) (baseStart_2871675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871675 prefixEnd_2871675 := by exact prefixLift 2871675
  have htrace : WordTrace (prefixWord ++ tailWord_2871675) baseStart_2871675 baseEnd_2871675 := by
    simpa [prefixWord, tailWord_2871675, baseEnd_2871675] using wordTrace_append hprefix tailTrace_2871675
  have hstable : (prefixWord ++ tailWord_2871675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871675).length < 2 ^ (prefixWord ++ tailWord_2871675).sum := by decide
  have hdescent : baseEnd_2871675 < baseStart_2871675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871712 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 4, 1, 3]
def baseStart_2871712 : Nat := 118140960795 + 2871712 * 2 ^ 59
def prefixEnd_2871712 : Nat := 4983230072969 + 3 ^ 40 * 2871712 * 2
def baseEnd_2871712 : Nat := 1474568557284373647293243

theorem tailTrace_2871712 : CollatzResearch.WordTrace tailWord_2871712 prefixEnd_2871712 1474568557284373647293243 := by
  unfold tailWord_2871712
  simp only [CollatzResearch.WordTrace]
  refine ⟨52369970686142674104020695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69826627581523565472027593 52369970686142674104020695)
  ·
    refine ⟨78554956029214011156031043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52369970686142674104020695 78554956029214011156031043)
    ·
      refine ⟨117832434043821016734046565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78554956029214011156031043 117832434043821016734046565)
      ·
        refine ⟨22093581383216440637633731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117832434043821016734046565 22093581383216440637633731)
        ·
          refine ⟨33140372074824660956450597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22093581383216440637633731 33140372074824660956450597)
          ·
            refine ⟨6213819764029623929334487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33140372074824660956450597 6213819764029623929334487)
            ·
              refine ⟨9320729646044435894001731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213819764029623929334487 9320729646044435894001731)
              ·
                refine ⟨13981094469066653841002597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9320729646044435894001731 13981094469066653841002597)
                ·
                  refine ⟨2621455212949997595187987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13981094469066653841002597 2621455212949997595187987)
                  ·
                    refine ⟨3932182819424996392781981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2621455212949997595187987 3932182819424996392781981)
                    ·
                      refine ⟨1474568557284373647293243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3932182819424996392781981 1474568557284373647293243)
                      ·
                        rfl

theorem cell23_2871712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_2871712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871712 prefixEnd_2871712 := by exact prefixLift 2871712
  have htrace : WordTrace (prefixWord ++ tailWord_2871712) baseStart_2871712 baseEnd_2871712 := by
    simpa [prefixWord, tailWord_2871712, baseEnd_2871712] using wordTrace_append hprefix tailTrace_2871712
  have hstable : (prefixWord ++ tailWord_2871712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871712).length < 2 ^ (prefixWord ++ tailWord_2871712).sum := by decide
  have hdescent : baseEnd_2871712 < baseStart_2871712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871738 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_2871738 : Nat := 118140960795 + 2871738 * 2 ^ 59
def prefixEnd_2871738 : Nat := 4983230072969 + 3 ^ 40 * 2871738 * 2
def baseEnd_2871738 : Nat := 1474581907781390545568123

theorem tailTrace_2871738 : CollatzResearch.WordTrace tailWord_2871738 prefixEnd_2871738 1474581907781390545568123 := by
  unfold tailWord_2871738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26185222417547788662121967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69827259780127436432325245 26185222417547788662121967)
  ·
    refine ⟨39277833626321682993182951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26185222417547788662121967 39277833626321682993182951)
    ·
      refine ⟨58916750439482524489774427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39277833626321682993182951 58916750439482524489774427)
      ·
        refine ⟨88375125659223786734661641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58916750439482524489774427 88375125659223786734661641)
        ·
          refine ⟨66281344244417840050996231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88375125659223786734661641 66281344244417840050996231)
          ·
            refine ⟨99422016366626760076494347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66281344244417840050996231 99422016366626760076494347)
            ·
              refine ⟨149133024549940140114741521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99422016366626760076494347 149133024549940140114741521)
              ·
                refine ⟨111849768412455105086056141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149133024549940140114741521 111849768412455105086056141)
                ·
                  refine ⟨41943663154670664407271053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111849768412455105086056141 41943663154670664407271053)
                  ·
                    refine ⟨15728873683001499152726645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41943663154670664407271053 15728873683001499152726645)
                    ·
                      refine ⟨1474581907781390545568123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15728873683001499152726645 1474581907781390545568123)
                      ·
                        rfl

theorem cell23_2871738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_2871738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871738 prefixEnd_2871738 := by exact prefixLift 2871738
  have htrace : WordTrace (prefixWord ++ tailWord_2871738) baseStart_2871738 baseEnd_2871738 := by
    simpa [prefixWord, tailWord_2871738, baseEnd_2871738] using wordTrace_append hprefix tailTrace_2871738
  have hstable : (prefixWord ++ tailWord_2871738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871738).length < 2 ^ (prefixWord ++ tailWord_2871738).sum := by decide
  have hdescent : baseEnd_2871738 < baseStart_2871738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871768 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2871768 : Nat := 118140960795 + 2871768 * 2 ^ 59
def prefixEnd_2871768 : Nat := 4983230072969 + 3 ^ 40 * 2871768 * 2
def baseEnd_2871768 : Nat := 1474597312201025428192985

theorem tailTrace_2871768 : CollatzResearch.WordTrace tailWord_2871768 prefixEnd_2871768 1474597312201025428192985 := by
  unfold tailWord_2871768
  simp only [CollatzResearch.WordTrace]
  refine ⟨52370991930041234886039979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69827989240054979848053305 52370991930041234886039979)
  ·
    refine ⟨78556487895061852329059969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52370991930041234886039979 78556487895061852329059969)
    ·
      refine ⟨58917365921296389246794977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78556487895061852329059969 58917365921296389246794977)
      ·
        refine ⟨44188024440972291935096233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58917365921296389246794977 44188024440972291935096233)
        ·
          refine ⟨33141018330729218951322175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44188024440972291935096233 33141018330729218951322175)
          ·
            refine ⟨49711527496093828426983263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33141018330729218951322175 49711527496093828426983263)
            ·
              refine ⟨74567291244140742640474895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49711527496093828426983263 74567291244140742640474895)
              ·
                refine ⟨111850936866211113960712343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74567291244140742640474895 111850936866211113960712343)
                ·
                  refine ⟨167776405299316670941068515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111850936866211113960712343 167776405299316670941068515)
                  ·
                    refine ⟨251664607948975006411602773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167776405299316670941068515 251664607948975006411602773)
                    ·
                      refine ⟨1474597312201025428192985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 251664607948975006411602773 1474597312201025428192985)
                      ·
                        rfl

theorem cell23_2871768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2871768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871768 prefixEnd_2871768 := by exact prefixLift 2871768
  have htrace : WordTrace (prefixWord ++ tailWord_2871768) baseStart_2871768 baseEnd_2871768 := by
    simpa [prefixWord, tailWord_2871768, baseEnd_2871768] using wordTrace_append hprefix tailTrace_2871768
  have hstable : (prefixWord ++ tailWord_2871768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871768).length < 2 ^ (prefixWord ++ tailWord_2871768).sum := by decide
  have hdescent : baseEnd_2871768 < baseStart_2871768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871769 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 2, 2, 2]
def baseStart_2871769 : Nat := 118140960795 + 2871769 * 2 ^ 59
def prefixEnd_2871769 : Nat := 4983230072969 + 3 ^ 40 * 2871769 * 2
def baseEnd_2871769 : Nat := 1474597825681679924280481

theorem tailTrace_2871769 : CollatzResearch.WordTrace tailWord_2871769 prefixEnd_2871769 1474597825681679924280481 := by
  unfold tailWord_2871769
  simp only [CollatzResearch.WordTrace]
  refine ⟨104742020333078846942866361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69828013555385897961910907 104742020333078846942866361)
  ·
    refine ⟨78556515249809135207149771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104742020333078846942866361 78556515249809135207149771)
    ·
      refine ⟨117834772874713702810724657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78556515249809135207149771 117834772874713702810724657)
      ·
        refine ⟨88376079656035277108043493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117834772874713702810724657 88376079656035277108043493)
        ·
          refine ⟨16570514935506614457758155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88376079656035277108043493 16570514935506614457758155)
          ·
            refine ⟨24855772403259921686637233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16570514935506614457758155 24855772403259921686637233)
            ·
              refine ⟨18641829302444941264977925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24855772403259921686637233 18641829302444941264977925)
              ·
                refine ⟨3495342994208426487183361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18641829302444941264977925 3495342994208426487183361)
                ·
                  refine ⟨2621507245656319865387521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3495342994208426487183361 2621507245656319865387521)
                  ·
                    refine ⟨1966130434242239899040641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2621507245656319865387521 1966130434242239899040641)
                    ·
                      refine ⟨1474597825681679924280481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966130434242239899040641 1474597825681679924280481)
                      ·
                        rfl

theorem cell23_2871769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_2871769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871769 prefixEnd_2871769 := by exact prefixLift 2871769
  have htrace : WordTrace (prefixWord ++ tailWord_2871769) baseStart_2871769 baseEnd_2871769 := by
    simpa [prefixWord, tailWord_2871769, baseEnd_2871769] using wordTrace_append hprefix tailTrace_2871769
  have hstable : (prefixWord ++ tailWord_2871769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871769).length < 2 ^ (prefixWord ++ tailWord_2871769).sum := by decide
  have hdescent : baseEnd_2871769 < baseStart_2871769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871775 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 7]
def baseStart_2871775 : Nat := 118140960795 + 2871775 * 2 ^ 59
def prefixEnd_2871775 : Nat := 4983230072969 + 3 ^ 40 * 2871775 * 2
def baseEnd_2871775 : Nat := 163844545173956322311717

theorem tailTrace_2871775 : CollatzResearch.WordTrace tailWord_2871775 prefixEnd_2871775 163844545173956322311717 := by
  unfold tailWord_2871775
  simp only [CollatzResearch.WordTrace]
  refine ⟨104742239171057109967584779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69828159447371406645056519 104742239171057109967584779)
  ·
    refine ⟨157113358756585664951377169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104742239171057109967584779 157113358756585664951377169)
    ·
      refine ⟨117835019067439248713532877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157113358756585664951377169 117835019067439248713532877)
      ·
        refine ⟨44188132150289718267574829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117835019067439248713532877 44188132150289718267574829)
        ·
          refine ⟨16570549556358644350340561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44188132150289718267574829 16570549556358644350340561)
          ·
            refine ⟨12427912167268983262755421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16570549556358644350340561 12427912167268983262755421)
            ·
              refine ⟨4660467062725868723533283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12427912167268983262755421 4660467062725868723533283)
              ·
                refine ⟨6990700594088803085299925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660467062725868723533283 6990700594088803085299925)
                ·
                  refine ⟨163844545173956322311717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6990700594088803085299925 163844545173956322311717)
                  ·
                    rfl

theorem cell23_2871775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 7].length) (baseStart_2871775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871775 prefixEnd_2871775 := by exact prefixLift 2871775
  have htrace : WordTrace (prefixWord ++ tailWord_2871775) baseStart_2871775 baseEnd_2871775 := by
    simpa [prefixWord, tailWord_2871775, baseEnd_2871775] using wordTrace_append hprefix tailTrace_2871775
  have hstable : (prefixWord ++ tailWord_2871775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871775).length < 2 ^ (prefixWord ++ tailWord_2871775).sum := by decide
  have hdescent : baseEnd_2871775 < baseStart_2871775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871786 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_2871786 : Nat := 118140960795 + 2871786 * 2 ^ 59
def prefixEnd_2871786 : Nat := 4983230072969 + 3 ^ 40 * 2871786 * 2
def baseEnd_2871786 : Nat := 1474606554852806357767903

theorem tailTrace_2871786 : CollatzResearch.WordTrace tailWord_2871786 prefixEnd_2871786 1474606554852806357767903 := by
  unfold tailWord_2871786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26185660093504314711558803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69828426916011505897490141 26185660093504314711558803)
  ·
    refine ⟨39278490140256472067338205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26185660093504314711558803 39278490140256472067338205)
    ·
      refine ⟨14729433802596177025251827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39278490140256472067338205 14729433802596177025251827)
      ·
        refine ⟨22094150703894265537877741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14729433802596177025251827 22094150703894265537877741)
        ·
          refine ⟨8285306513960349576704153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22094150703894265537877741 8285306513960349576704153)
          ·
            refine ⟨6213979885470262182528115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8285306513960349576704153 6213979885470262182528115)
            ·
              refine ⟨9320969828205393273792173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213979885470262182528115 9320969828205393273792173)
              ·
                refine ⟨3495363685577022477672065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9320969828205393273792173 3495363685577022477672065)
                ·
                  refine ⟨2621522764182766858254049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3495363685577022477672065 2621522764182766858254049)
                  ·
                    refine ⟨1966142073137075143690537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2621522764182766858254049 1966142073137075143690537)
                    ·
                      refine ⟨1474606554852806357767903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966142073137075143690537 1474606554852806357767903)
                      ·
                        rfl

theorem cell23_2871786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_2871786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871786 prefixEnd_2871786 := by exact prefixLift 2871786
  have htrace : WordTrace (prefixWord ++ tailWord_2871786) baseStart_2871786 baseEnd_2871786 := by
    simpa [prefixWord, tailWord_2871786, baseEnd_2871786] using wordTrace_append hprefix tailTrace_2871786
  have hstable : (prefixWord ++ tailWord_2871786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871786).length < 2 ^ (prefixWord ++ tailWord_2871786).sum := by decide
  have hdescent : baseEnd_2871786 < baseStart_2871786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871822 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_2871822 : Nat := 118140960795 + 2871822 * 2 ^ 59
def prefixEnd_2871822 : Nat := 4983230072969 + 3 ^ 40 * 2871822 * 2
def baseEnd_2871822 : Nat := 491541680052122738972579

theorem tailTrace_2871822 : CollatzResearch.WordTrace tailWord_2871822 prefixEnd_2871822 491541680052122738972579 := by
  unfold tailWord_2871822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092994175235854624318215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69829302267924557996363813 13092994175235854624318215)
  ·
    refine ⟨19639491262853781936477323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13092994175235854624318215 19639491262853781936477323)
    ·
      refine ⟨29459236894280672904715985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19639491262853781936477323 29459236894280672904715985)
      ·
        refine ⟨22094427670710504678536989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29459236894280672904715985 22094427670710504678536989)
        ·
          refine ⟨8285410376516439254451371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22094427670710504678536989 8285410376516439254451371)
          ·
            refine ⟨12428115564774658881677057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8285410376516439254451371 12428115564774658881677057)
            ·
              refine ⟨9321086673580994161257793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12428115564774658881677057 9321086673580994161257793)
              ·
                refine ⟨6990815005185745620943345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9321086673580994161257793 6990815005185745620943345)
                ·
                  refine ⟨5243111253889309215707509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990815005185745620943345 5243111253889309215707509)
                  ·
                    refine ⟨491541680052122738972579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5243111253889309215707509 491541680052122738972579)
                    ·
                      rfl

theorem cell23_2871822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_2871822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871822 prefixEnd_2871822 := by exact prefixLift 2871822
  have htrace : WordTrace (prefixWord ++ tailWord_2871822) baseStart_2871822 baseEnd_2871822 := by
    simpa [prefixWord, tailWord_2871822, baseEnd_2871822] using wordTrace_append hprefix tailTrace_2871822
  have hstable : (prefixWord ++ tailWord_2871822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871822).length < 2 ^ (prefixWord ++ tailWord_2871822).sum := by decide
  have hdescent : baseEnd_2871822 < baseStart_2871822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871825 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2871825 : Nat := 118140960795 + 2871825 * 2 ^ 59
def prefixEnd_2871825 : Nat := 4983230072969 + 3 ^ 40 * 2871825 * 2
def baseEnd_2871825 : Nat := 1474626580598331705180223

theorem tailTrace_2871825 : CollatzResearch.WordTrace tailWord_2871825 prefixEnd_2871825 1474626580598331705180223 := by
  unfold tailWord_2871825
  simp only [CollatzResearch.WordTrace]
  refine ⟨104744062820875968506904929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69829375213917312337936619 104744062820875968506904929)
  ·
    refine ⟨78558047115656976380178697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104744062820875968506904929 78558047115656976380178697)
    ·
      refine ⟨58918535336742732285134023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78558047115656976380178697 58918535336742732285134023)
      ·
        refine ⟨88377803005114098427701035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58918535336742732285134023 88377803005114098427701035)
        ·
          refine ⟨132566704507671147641551553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88377803005114098427701035 132566704507671147641551553)
          ·
            refine ⟨99425028380753360731163665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132566704507671147641551553 99425028380753360731163665)
            ·
              refine ⟨74568771285565020548372749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99425028380753360731163665 74568771285565020548372749)
              ·
                refine ⟨27963289232086882705639781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74568771285565020548372749 27963289232086882705639781)
                ·
                  refine ⟨5243116731016290507307459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27963289232086882705639781 5243116731016290507307459)
                  ·
                    refine ⟨7864675096524435760961189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243116731016290507307459 7864675096524435760961189)
                    ·
                      refine ⟨1474626580598331705180223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7864675096524435760961189 1474626580598331705180223)
                      ·
                        rfl

theorem cell23_2871825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2871825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871825 prefixEnd_2871825 := by exact prefixLift 2871825
  have htrace : WordTrace (prefixWord ++ tailWord_2871825) baseStart_2871825 baseEnd_2871825 := by
    simpa [prefixWord, tailWord_2871825, baseEnd_2871825] using wordTrace_append hprefix tailTrace_2871825
  have hstable : (prefixWord ++ tailWord_2871825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871825).length < 2 ^ (prefixWord ++ tailWord_2871825).sum := by decide
  have hdescent : baseEnd_2871825 < baseStart_2871825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871835 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 9, 4]
def baseStart_2871835 : Nat := 118140960795 + 2871835 * 2 ^ 59
def prefixEnd_2871835 : Nat := 4983230072969 + 3 ^ 40 * 2871835 * 2
def baseEnd_2871835 : Nat := 491543905134958888685059

theorem tailTrace_2871835 : CollatzResearch.WordTrace tailWord_2871835 prefixEnd_2871835 491543905134958888685059 := by
  unfold tailWord_2871835
  simp only [CollatzResearch.WordTrace]
  refine ⟨104744427550839740214768959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69829618367226493476512639 104744427550839740214768959)
  ·
    refine ⟨157116641326259610322153439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104744427550839740214768959 157116641326259610322153439)
    ·
      refine ⟨235674961989389415483230159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157116641326259610322153439 235674961989389415483230159)
      ·
        refine ⟨353512442984084123224845239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235674961989389415483230159 353512442984084123224845239)
        ·
          refine ⟨530268664476126184837267859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353512442984084123224845239 530268664476126184837267859)
          ·
            refine ⟨795402996714189277255901789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530268664476126184837267859 795402996714189277255901789)
            ·
              refine ⟨298276123767820978970963171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795402996714189277255901789 298276123767820978970963171)
              ·
                refine ⟨447414185651731468456444757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298276123767820978970963171 447414185651731468456444757)
                ·
                  refine ⟨2621567494053114072986981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 447414185651731468456444757 2621567494053114072986981)
                  ·
                    refine ⟨491543905134958888685059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2621567494053114072986981 491543905134958888685059)
                    ·
                      rfl

theorem cell23_2871835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 4].length) (baseStart_2871835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871835 prefixEnd_2871835 := by exact prefixLift 2871835
  have htrace : WordTrace (prefixWord ++ tailWord_2871835) baseStart_2871835 baseEnd_2871835 := by
    simpa [prefixWord, tailWord_2871835, baseEnd_2871835] using wordTrace_append hprefix tailTrace_2871835
  have hstable : (prefixWord ++ tailWord_2871835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871835).length < 2 ^ (prefixWord ++ tailWord_2871835).sum := by decide
  have hdescent : baseEnd_2871835 < baseStart_2871835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871865 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 8]
def baseStart_2871865 : Nat := 118140960795 + 2871865 * 2 ^ 59
def prefixEnd_2871865 : Nat := 4983230072969 + 3 ^ 40 * 2871865 * 2
def baseEnd_2871865 : Nat := 163849679980501283186671

theorem tailTrace_2871865 : CollatzResearch.WordTrace tailWord_2871865 prefixEnd_2871865 163849679980501283186671 := by
  unfold tailWord_2871865
  simp only [CollatzResearch.WordTrace]
  refine ⟨104745521740731055338361049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69830347827154036892240699 104745521740731055338361049)
  ·
    refine ⟨78559141305548291503770787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104745521740731055338361049 78559141305548291503770787)
    ·
      refine ⟨117838711958322437255656181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78559141305548291503770787 117838711958322437255656181)
      ·
        refine ⟨11047379246092728492717767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117838711958322437255656181 11047379246092728492717767)
        ·
          refine ⟨16571068869139092739076651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11047379246092728492717767 16571068869139092739076651)
          ·
            refine ⟨24856603303708639108614977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16571068869139092739076651 24856603303708639108614977)
            ·
              refine ⟨18642452477781479331461233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24856603303708639108614977 18642452477781479331461233)
              ·
                refine ⟨13981839358336109498595925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18642452477781479331461233 13981839358336109498595925)
                ·
                  refine ⟨163849679980501283186671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13981839358336109498595925 163849679980501283186671)
                  ·
                    rfl

theorem cell23_2871865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_2871865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871865 prefixEnd_2871865 := by exact prefixLift 2871865
  have htrace : WordTrace (prefixWord ++ tailWord_2871865) baseStart_2871865 baseEnd_2871865 := by
    simpa [prefixWord, tailWord_2871865, baseEnd_2871865] using wordTrace_append hprefix tailTrace_2871865
  have hstable : (prefixWord ++ tailWord_2871865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871865).length < 2 ^ (prefixWord ++ tailWord_2871865).sum := by decide
  have hdescent : baseEnd_2871865 < baseStart_2871865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871875 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 3]
def baseStart_2871875 : Nat := 118140960795 + 2871875 * 2 ^ 59
def prefixEnd_2871875 : Nat := 4983230072969 + 3 ^ 40 * 2871875 * 2
def baseEnd_2871875 : Nat := 1474652254631056509554993

theorem tailTrace_2871875 : CollatzResearch.WordTrace tailWord_2871875 prefixEnd_2871875 1474652254631056509554993 := by
  unfold tailWord_2871875
  simp only [CollatzResearch.WordTrace]
  refine ⟨104745886470694827046225079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69830590980463218030816719 104745886470694827046225079)
  ·
    refine ⟨157118829706042240569337619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104745886470694827046225079 157118829706042240569337619)
    ·
      refine ⟨235678244559063360854006429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157118829706042240569337619 235678244559063360854006429)
      ·
        refine ⟨88379341709648760320252411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235678244559063360854006429 88379341709648760320252411)
        ·
          refine ⟨132569012564473140480378617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88379341709648760320252411 132569012564473140480378617)
          ·
            refine ⟨99426759423354855360283963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132569012564473140480378617 99426759423354855360283963)
            ·
              refine ⟨149140139135032283040425945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99426759423354855360283963 149140139135032283040425945)
              ·
                refine ⟨111855104351274212280319459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149140139135032283040425945 111855104351274212280319459)
                ·
                  refine ⟨167782656526911318420479189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111855104351274212280319459 167782656526911318420479189)
                  ·
                    refine ⟨3932406012349484025479981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167782656526911318420479189 3932406012349484025479981)
                    ·
                      refine ⟨1474652254631056509554993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3932406012349484025479981 1474652254631056509554993)
                      ·
                        rfl

theorem cell23_2871875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_2871875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871875 prefixEnd_2871875 := by exact prefixLift 2871875
  have htrace : WordTrace (prefixWord ++ tailWord_2871875) baseStart_2871875 baseEnd_2871875 := by
    simpa [prefixWord, tailWord_2871875, baseEnd_2871875] using wordTrace_append hprefix tailTrace_2871875
  have hstable : (prefixWord ++ tailWord_2871875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871875).length < 2 ^ (prefixWord ++ tailWord_2871875).sum := by decide
  have hdescent : baseEnd_2871875 < baseStart_2871875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871882 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_2871882 : Nat := 118140960795 + 2871882 * 2 ^ 59
def prefixEnd_2871882 : Nat := 4983230072969 + 3 ^ 40 * 2871882 * 2
def baseEnd_2871882 : Nat := 163850649888404220240829

theorem tailTrace_2871882 : CollatzResearch.WordTrace tailWord_2871882 prefixEnd_2871882 163850649888404220240829 := by
  unfold tailWord_2871882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26186535445417366810432475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69830761187779644827819933 26186535445417366810432475)
  ·
    refine ⟨39279803168126050215648713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26186535445417366810432475 39279803168126050215648713)
    ·
      refine ⟨29459852376094537661736535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39279803168126050215648713 29459852376094537661736535)
      ·
        refine ⟨44189778564141806492604803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29459852376094537661736535 44189778564141806492604803)
        ·
          refine ⟨66284667846212709738907205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44189778564141806492604803 66284667846212709738907205)
          ·
            refine ⟨12428375221164883076045101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66284667846212709738907205 12428375221164883076045101)
            ·
              refine ⟨4660640707936831153516913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12428375221164883076045101 4660640707936831153516913)
              ·
                refine ⟨3495480530952623365137685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4660640707936831153516913 3495480530952623365137685)
                ·
                  refine ⟨163850649888404220240829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3495480530952623365137685 163850649888404220240829)
                  ·
                    rfl

theorem cell23_2871882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_2871882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871882 prefixEnd_2871882 := by exact prefixLift 2871882
  have htrace : WordTrace (prefixWord ++ tailWord_2871882) baseStart_2871882 baseEnd_2871882 := by
    simpa [prefixWord, tailWord_2871882, baseEnd_2871882] using wordTrace_append hprefix tailTrace_2871882
  have hstable : (prefixWord ++ tailWord_2871882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871882).length < 2 ^ (prefixWord ++ tailWord_2871882).sum := by decide
  have hdescent : baseEnd_2871882 < baseStart_2871882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871943 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_2871943 : Nat := 118140960795 + 2871943 * 2 ^ 59
def prefixEnd_2871943 : Nat := 4983230072969 + 3 ^ 40 * 2871943 * 2
def baseEnd_2871943 : Nat := 1474687171315562243504681

theorem tailTrace_2871943 : CollatzResearch.WordTrace tailWord_2871943 prefixEnd_2871943 1474687171315562243504681 := by
  unfold tailWord_2871943
  simp only [CollatzResearch.WordTrace]
  refine ⟨104748366634448474659700483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69832244422965649773133655 104748366634448474659700483)
  ·
    refine ⟨157122549951672711989550725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104748366634448474659700483 157122549951672711989550725)
    ·
      refine ⟨29460478115938633498040761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157122549951672711989550725 29460478115938633498040761)
      ·
        refine ⟨22095358586953975123530571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29460478115938633498040761 22095358586953975123530571)
        ·
          refine ⟨33143037880430962685295857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22095358586953975123530571 33143037880430962685295857)
          ·
            refine ⟨24857278410323222013971893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33143037880430962685295857 24857278410323222013971893)
            ·
              refine ⟨2330369850967802063809865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24857278410323222013971893 2330369850967802063809865)
              ·
                refine ⟨1747777388225851547857399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330369850967802063809865 1747777388225851547857399)
                ·
                  refine ⟨2621666082338777321786099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747777388225851547857399 2621666082338777321786099)
                  ·
                    refine ⟨3932499123508165982679149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2621666082338777321786099 3932499123508165982679149)
                    ·
                      refine ⟨1474687171315562243504681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3932499123508165982679149 1474687171315562243504681)
                      ·
                        rfl

theorem cell23_2871943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_2871943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871943 prefixEnd_2871943 := by exact prefixLift 2871943
  have htrace : WordTrace (prefixWord ++ tailWord_2871943) baseStart_2871943 baseEnd_2871943 := by
    simpa [prefixWord, tailWord_2871943, baseEnd_2871943] using wordTrace_append hprefix tailTrace_2871943
  have hstable : (prefixWord ++ tailWord_2871943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871943).length < 2 ^ (prefixWord ++ tailWord_2871943).sum := by decide
  have hdescent : baseEnd_2871943 < baseStart_2871943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871959 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 2, 4]
def baseStart_2871959 : Nat := 118140960795 + 2871959 * 2 ^ 59
def prefixEnd_2871959 : Nat := 4983230072969 + 3 ^ 40 * 2871959 * 2
def baseEnd_2871959 : Nat := 491565129002011393634869

theorem tailTrace_2871959 : CollatzResearch.WordTrace tailWord_2871959 prefixEnd_2871959 491565129002011393634869 := by
  unfold tailWord_2871959
  simp only [CollatzResearch.WordTrace]
  refine ⟨104748950202390509392282931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69832633468260339594855287 104748950202390509392282931)
  ·
    refine ⟨157123425303585764088424397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104748950202390509392282931 157123425303585764088424397)
    ·
      refine ⟨58921284488844661533159149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157123425303585764088424397 58921284488844661533159149)
      ·
        refine ⟨22095481683316748074934681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58921284488844661533159149 22095481683316748074934681)
        ·
          refine ⟨16571611262487561056201011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22095481683316748074934681 16571611262487561056201011)
          ·
            refine ⟨24857416893731341584301517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16571611262487561056201011 24857416893731341584301517)
            ·
              refine ⟨9321531335149253094113069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24857416893731341584301517 9321531335149253094113069)
              ·
                refine ⟨3495574250680969910292401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9321531335149253094113069 3495574250680969910292401)
                ·
                  refine ⟨2621680688010727432719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3495574250680969910292401 2621680688010727432719301)
                  ·
                    refine ⟨491565129002011393634869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2621680688010727432719301 491565129002011393634869)
                    ·
                      rfl

theorem cell23_2871959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_2871959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871959 prefixEnd_2871959 := by exact prefixLift 2871959
  have htrace : WordTrace (prefixWord ++ tailWord_2871959) baseStart_2871959 baseEnd_2871959 := by
    simpa [prefixWord, tailWord_2871959, baseEnd_2871959] using wordTrace_append hprefix tailTrace_2871959
  have hstable : (prefixWord ++ tailWord_2871959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871959).length < 2 ^ (prefixWord ++ tailWord_2871959).sum := by decide
  have hdescent : baseEnd_2871959 < baseStart_2871959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871995 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_2871995 : Nat := 118140960795 + 2871995 * 2 ^ 59
def prefixEnd_2871995 : Nat := 4983230072969 + 3 ^ 40 * 2871995 * 2
def baseEnd_2871995 : Nat := 1474713872309596040054441

theorem tailTrace_2871995 : CollatzResearch.WordTrace tailWord_2871995 prefixEnd_2871995 1474713872309596040054441 := by
  unfold tailWord_2871995
  simp only [CollatzResearch.WordTrace]
  refine ⟨104750263230260087540593439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69833508820173391693728959 104750263230260087540593439)
  ·
    refine ⟨157125394845390131310890159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104750263230260087540593439 157125394845390131310890159)
    ·
      refine ⟨235688092268085196966335239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157125394845390131310890159 235688092268085196966335239)
      ·
        refine ⟨353532138402127795449502859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235688092268085196966335239 353532138402127795449502859)
        ·
          refine ⟨530298207603191693174254289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353532138402127795449502859 530298207603191693174254289)
          ·
            refine ⟨397723655702393769880690717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530298207603191693174254289 397723655702393769880690717)
            ·
              refine ⟨149146370888397663705259019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397723655702393769880690717 149146370888397663705259019)
              ·
                refine ⟨223719556332596495557888529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149146370888397663705259019 223719556332596495557888529)
                ·
                  refine ⟨167789667249447371668416397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223719556332596495557888529 167789667249447371668416397)
                  ·
                    refine ⟨62921125218542764375656149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167789667249447371668416397 62921125218542764375656149)
                    ·
                      refine ⟨1474713872309596040054441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62921125218542764375656149 1474713872309596040054441)
                      ·
                        rfl

theorem cell23_2871995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_2871995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2871995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2871995 prefixEnd_2871995 := by exact prefixLift 2871995
  have htrace : WordTrace (prefixWord ++ tailWord_2871995) baseStart_2871995 baseEnd_2871995 := by
    simpa [prefixWord, tailWord_2871995, baseEnd_2871995] using wordTrace_append hprefix tailTrace_2871995
  have hstable : (prefixWord ++ tailWord_2871995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871995).length < 2 ^ (prefixWord ++ tailWord_2871995).sum := by decide
  have hdescent : baseEnd_2871995 < baseStart_2871995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872000 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 1, 2, 2]
def baseStart_2872000 : Nat := 118140960795 + 2872000 * 2 ^ 59
def prefixEnd_2872000 : Nat := 4983230072969 + 3 ^ 40 * 2872000 * 2
def baseEnd_2872000 : Nat := 1474716439712868520491919

theorem tailTrace_2872000 : CollatzResearch.WordTrace tailWord_2872000 prefixEnd_2872000 1474716439712868520491919 := by
  unfold tailWord_2872000
  simp only [CollatzResearch.WordTrace]
  refine ⟨52375222797620986697262727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69833630396827982263016969 52375222797620986697262727)
  ·
    refine ⟨78562834196431480045894091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52375222797620986697262727 78562834196431480045894091)
    ·
      refine ⟨117844251294647220068841137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78562834196431480045894091 117844251294647220068841137)
      ·
        refine ⟨88383188470985415051630853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117844251294647220068841137 88383188470985415051630853)
        ·
          refine ⟨16571847838309765322180785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88383188470985415051630853 16571847838309765322180785)
          ·
            refine ⟨12428885878732323991635589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16571847838309765322180785 12428885878732323991635589)
            ·
              refine ⟨2330416102262310748431673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12428885878732323991635589 2330416102262310748431673)
              ·
                refine ⟨1747812076696733061323755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330416102262310748431673 1747812076696733061323755)
                ·
                  refine ⟨2621718115045099591985633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747812076696733061323755 2621718115045099591985633)
                  ·
                    refine ⟨1966288586283824693989225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2621718115045099591985633 1966288586283824693989225)
                    ·
                      refine ⟨1474716439712868520491919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966288586283824693989225 1474716439712868520491919)
                      ·
                        rfl

theorem cell23_2872000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_2872000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872000 prefixEnd_2872000 := by exact prefixLift 2872000
  have htrace : WordTrace (prefixWord ++ tailWord_2872000) baseStart_2872000 baseEnd_2872000 := by
    simpa [prefixWord, tailWord_2872000, baseEnd_2872000] using wordTrace_append hprefix tailTrace_2872000
  have hstable : (prefixWord ++ tailWord_2872000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872000).length < 2 ^ (prefixWord ++ tailWord_2872000).sum := by decide
  have hdescent : baseEnd_2872000 < baseStart_2872000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872013 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2872013 : Nat := 118140960795 + 2872013 * 2 ^ 59
def prefixEnd_2872013 : Nat := 4983230072969 + 3 ^ 40 * 2872013 * 2
def baseEnd_2872013 : Nat := 1474723114961376969629359

theorem tailTrace_2872013 : CollatzResearch.WordTrace tailWord_2872013 prefixEnd_2872013 1474723114961376969629359 := by
  unfold tailWord_2872013
  simp only [CollatzResearch.WordTrace]
  refine ⟨104750919744194876614748693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69833946496129917743165795 104750919744194876614748693)
  ·
    refine ⟨4910199363009134841316345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104750919744194876614748693 4910199363009134841316345)
    ·
      refine ⟨3682649522256851130987259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4910199363009134841316345 3682649522256851130987259)
      ·
        refine ⟨5523974283385276696480889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682649522256851130987259 5523974283385276696480889)
        ·
          refine ⟨4142980712538957522360667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5523974283385276696480889 4142980712538957522360667)
          ·
            refine ⟨6214471068808436283541001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142980712538957522360667 6214471068808436283541001)
            ·
              refine ⟨4660853301606327212655751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6214471068808436283541001 4660853301606327212655751)
              ·
                refine ⟨6991279952409490818983627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660853301606327212655751 6991279952409490818983627)
                ·
                  refine ⟨10486919928614236228475441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6991279952409490818983627 10486919928614236228475441)
                  ·
                    refine ⟨7865189946460677171356581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10486919928614236228475441 7865189946460677171356581)
                    ·
                      refine ⟨1474723114961376969629359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7865189946460677171356581 1474723114961376969629359)
                      ·
                        rfl

theorem cell23_2872013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2872013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872013 prefixEnd_2872013 := by exact prefixLift 2872013
  have htrace : WordTrace (prefixWord ++ tailWord_2872013) baseStart_2872013 baseEnd_2872013 := by
    simpa [prefixWord, tailWord_2872013, baseEnd_2872013] using wordTrace_append hprefix tailTrace_2872013
  have hstable : (prefixWord ++ tailWord_2872013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872013).length < 2 ^ (prefixWord ++ tailWord_2872013).sum := by decide
  have hdescent : baseEnd_2872013 < baseStart_2872013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872026 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2]
def baseStart_2872026 : Nat := 118140960795 + 2872026 * 2 ^ 59
def prefixEnd_2872026 : Nat := 4983230072969 + 3 ^ 40 * 2872026 * 2
def baseEnd_2872026 : Nat := 1474729790209885418766799

theorem tailTrace_2872026 : CollatzResearch.WordTrace tailWord_2872026 prefixEnd_2872026 1474729790209885418766799 := by
  unfold tailWord_2872026
  simp only [CollatzResearch.WordTrace]
  refine ⟨26187848473286944958742983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69834262595431853223314621 26187848473286944958742983)
  ·
    refine ⟨39281772709930417438114475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26187848473286944958742983 39281772709930417438114475)
    ·
      refine ⟨58922659064895626157171713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39281772709930417438114475 58922659064895626157171713)
      ·
        refine ⟨44191994298671719617878785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58922659064895626157171713 44191994298671719617878785)
        ·
          refine ⟨33143995724003789713409089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44191994298671719617878785 33143995724003789713409089)
          ·
            refine ⟨24857996793002842285056817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33143995724003789713409089 24857996793002842285056817)
            ·
              refine ⟨18643497594752131713792613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24857996793002842285056817 18643497594752131713792613)
              ·
                refine ⟨3495655799016024696336115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18643497594752131713792613 3495655799016024696336115)
                ·
                  refine ⟨5243483698524037044504173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3495655799016024696336115 5243483698524037044504173)
                  ·
                    refine ⟨1966306386946513891689065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5243483698524037044504173 1966306386946513891689065)
                    ·
                      refine ⟨1474729790209885418766799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966306386946513891689065 1474729790209885418766799)
                      ·
                        rfl

theorem cell23_2872026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_2872026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872026 prefixEnd_2872026 := by exact prefixLift 2872026
  have htrace : WordTrace (prefixWord ++ tailWord_2872026) baseStart_2872026 baseEnd_2872026 := by
    simpa [prefixWord, tailWord_2872026, baseEnd_2872026] using wordTrace_append hprefix tailTrace_2872026
  have hstable : (prefixWord ++ tailWord_2872026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872026).length < 2 ^ (prefixWord ++ tailWord_2872026).sum := by decide
  have hdescent : baseEnd_2872026 < baseStart_2872026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872042 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2872042 : Nat := 118140960795 + 2872042 * 2 ^ 59
def prefixEnd_2872042 : Nat := 4983230072969 + 3 ^ 40 * 2872042 * 2
def baseEnd_2872042 : Nat := 1474738005900357356166725

theorem tailTrace_2872042 : CollatzResearch.WordTrace tailWord_2872042 prefixEnd_2872042 1474738005900357356166725 := by
  unfold tailWord_2872042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26187994365272453641888595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69834651640726543045036253 26187994365272453641888595)
  ·
    refine ⟨39281991547908680462832893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26187994365272453641888595 39281991547908680462832893)
    ·
      refine ⟨14730746830465755173562335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39281991547908680462832893 14730746830465755173562335)
      ·
        refine ⟨22096120245698632760343503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14730746830465755173562335 22096120245698632760343503)
        ·
          refine ⟨33144180368547949140515255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22096120245698632760343503 33144180368547949140515255)
          ·
            refine ⟨49716270552821923710772883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33144180368547949140515255 49716270552821923710772883)
            ·
              refine ⟨74574405829232885566159325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49716270552821923710772883 74574405829232885566159325)
              ·
                refine ⟨27965402185962332087309747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74574405829232885566159325 27965402185962332087309747)
                ·
                  refine ⟨41948103278943498130964621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27965402185962332087309747 41948103278943498130964621)
                  ·
                    refine ⟨15730538729603811799111733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41948103278943498130964621 15730538729603811799111733)
                    ·
                      refine ⟨1474738005900357356166725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15730538729603811799111733 1474738005900357356166725)
                      ·
                        rfl

theorem cell23_2872042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2872042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872042 prefixEnd_2872042 := by exact prefixLift 2872042
  have htrace : WordTrace (prefixWord ++ tailWord_2872042) baseStart_2872042 baseEnd_2872042 := by
    simpa [prefixWord, tailWord_2872042, baseEnd_2872042] using wordTrace_append hprefix tailTrace_2872042
  have hstable : (prefixWord ++ tailWord_2872042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872042).length < 2 ^ (prefixWord ++ tailWord_2872042).sum := by decide
  have hdescent : baseEnd_2872042 < baseStart_2872042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872056 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 4, 2, 2]
def baseStart_2872056 : Nat := 118140960795 + 2872056 * 2 ^ 59
def prefixEnd_2872056 : Nat := 4983230072969 + 3 ^ 40 * 2872056 * 2
def baseEnd_2872056 : Nat := 1474745194629520301391661

theorem tailTrace_2872056 : CollatzResearch.WordTrace tailWord_2872056 prefixEnd_2872056 1474745194629520301391661 := by
  unfold tailWord_2872056
  simp only [CollatzResearch.WordTrace]
  refine ⟨52376244041519547479282011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69834992055359396639042681 52376244041519547479282011)
  ·
    refine ⟨78564366062279321218923017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52376244041519547479282011 78564366062279321218923017)
    ·
      refine ⟨58923274546709490914192263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78564366062279321218923017 58923274546709490914192263)
      ·
        refine ⟨88384911820064236371288395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58923274546709490914192263 88384911820064236371288395)
        ·
          refine ⟨132577367730096354556932593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88384911820064236371288395 132577367730096354556932593)
          ·
            refine ⟨99433025797572265917699445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132577367730096354556932593 99433025797572265917699445)
            ·
              refine ⟨9321846168522399929784323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99433025797572265917699445 9321846168522399929784323)
              ·
                refine ⟨13982769252783599894676485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321846168522399929784323 13982769252783599894676485)
                ·
                  refine ⟨2621769234896924980251841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13982769252783599894676485 2621769234896924980251841)
                  ·
                    refine ⟨1966326926172693735188881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2621769234896924980251841 1966326926172693735188881)
                    ·
                      refine ⟨1474745194629520301391661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966326926172693735188881 1474745194629520301391661)
                      ·
                        rfl

theorem cell23_2872056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_2872056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872056 prefixEnd_2872056 := by exact prefixLift 2872056
  have htrace : WordTrace (prefixWord ++ tailWord_2872056) baseStart_2872056 baseEnd_2872056 := by
    simpa [prefixWord, tailWord_2872056, baseEnd_2872056] using wordTrace_append hprefix tailTrace_2872056
  have hstable : (prefixWord ++ tailWord_2872056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872056).length < 2 ^ (prefixWord ++ tailWord_2872056).sum := by decide
  have hdescent : baseEnd_2872056 < baseStart_2872056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872096 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 5]
def baseStart_2872096 : Nat := 118140960795 + 2872096 * 2 ^ 59
def prefixEnd_2872096 : Nat := 4983230072969 + 3 ^ 40 * 2872096 * 2
def baseEnd_2872096 : Nat := 163862859317300016099053

theorem tailTrace_2872096 : CollatzResearch.WordTrace tailWord_2872096 prefixEnd_2872096 163862859317300016099053 := by
  unfold tailWord_2872096
  simp only [CollatzResearch.WordTrace]
  refine ⟨52376973501447090895010071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69835964668596121193346761 52376973501447090895010071)
  ·
    refine ⟨78565460252170636342515107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52376973501447090895010071 78565460252170636342515107)
    ·
      refine ⟨117848190378255954513772661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78565460252170636342515107 117848190378255954513772661)
      ·
        refine ⟨11048267847961495735666187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117848190378255954513772661 11048267847961495735666187)
        ·
          refine ⟨16572401771942243603499281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11048267847961495735666187 16572401771942243603499281)
          ·
            refine ⟨12429301328956682702624461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16572401771942243603499281 12429301328956682702624461)
            ·
              refine ⟨4660987998358756013484173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12429301328956682702624461 4660987998358756013484173)
              ·
                refine ⟨1747870499384533505056565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4660987998358756013484173 1747870499384533505056565)
                ·
                  refine ⟨163862859317300016099053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1747870499384533505056565 163862859317300016099053)
                  ·
                    rfl

theorem cell23_2872096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 5].length) (baseStart_2872096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872096 prefixEnd_2872096 := by exact prefixLift 2872096
  have htrace : WordTrace (prefixWord ++ tailWord_2872096) baseStart_2872096 baseEnd_2872096 := by
    simpa [prefixWord, tailWord_2872096, baseEnd_2872096] using wordTrace_append hprefix tailTrace_2872096
  have hstable : (prefixWord ++ tailWord_2872096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872096).length < 2 ^ (prefixWord ++ tailWord_2872096).sum := by decide
  have hdescent : baseEnd_2872096 < baseStart_2872096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872099 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 7, 2]
def baseStart_2872099 : Nat := 118140960795 + 2872099 * 2 ^ 59
def prefixEnd_2872099 : Nat := 4983230072969 + 3 ^ 40 * 2872099 * 2
def baseEnd_2872099 : Nat := 1474767274297663633153963

theorem tailTrace_2872099 : CollatzResearch.WordTrace tailWord_2872099 prefixEnd_2872099 1474767274297663633153963 := by
  unfold tailWord_2872099
  simp only [CollatzResearch.WordTrace]
  refine ⟨104754056421883313302379351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69836037614588875534919567 104754056421883313302379351)
  ·
    refine ⟨157131084632824969953569027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104754056421883313302379351 157131084632824969953569027)
    ·
      refine ⟨235696626949237454930353541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157131084632824969953569027 235696626949237454930353541)
      ·
        refine ⟨44193117552982022799441289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235696626949237454930353541 44193117552982022799441289)
        ·
          refine ⟨33144838164736517099580967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44193117552982022799441289 33144838164736517099580967)
          ·
            refine ⟨49717257247104775649371451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33144838164736517099580967 49717257247104775649371451)
            ·
              refine ⟨74575885870657163474057177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49717257247104775649371451 74575885870657163474057177)
              ·
                refine ⟨55931914402992872605542883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74575885870657163474057177 55931914402992872605542883)
                ·
                  refine ⟨83897871604489308908314325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55931914402992872605542883 83897871604489308908314325)
                  ·
                    refine ⟨1966356365730218177538617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83897871604489308908314325 1966356365730218177538617)
                    ·
                      refine ⟨1474767274297663633153963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966356365730218177538617 1474767274297663633153963)
                      ·
                        rfl

theorem cell23_2872099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_2872099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872099 prefixEnd_2872099 := by exact prefixLift 2872099
  have htrace : WordTrace (prefixWord ++ tailWord_2872099) baseStart_2872099 baseEnd_2872099 := by
    simpa [prefixWord, tailWord_2872099, baseEnd_2872099] using wordTrace_append hprefix tailTrace_2872099
  have hstable : (prefixWord ++ tailWord_2872099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872099).length < 2 ^ (prefixWord ++ tailWord_2872099).sum := by decide
  have hdescent : baseEnd_2872099 < baseStart_2872099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872146 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2872146 : Nat := 118140960795 + 2872146 * 2 ^ 59
def prefixEnd_2872146 : Nat := 4983230072969 + 3 ^ 40 * 2872146 * 2
def baseEnd_2872146 : Nat := 1474791407888424949266247

theorem tailTrace_2872146 : CollatzResearch.WordTrace tailWord_2872146 prefixEnd_2872146 1474791407888424949266247 := by
  unfold tailWord_2872146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26188942663178260082335073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69837180435142026886226861 26188942663178260082335073)
  ·
    refine ⟨19641706997383695061751305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26188942663178260082335073 19641706997383695061751305)
    ·
      refine ⟨14731280248037771296313479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19641706997383695061751305 14731280248037771296313479)
      ·
        refine ⟨22096920372056656944470219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14731280248037771296313479 22096920372056656944470219)
        ·
          refine ⟨33145380558084985416705329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22096920372056656944470219 33145380558084985416705329)
          ·
            refine ⟨24859035418563739062528997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33145380558084985416705329 24859035418563739062528997)
            ·
              refine ⟨4661069140980701074224187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24859035418563739062528997 4661069140980701074224187)
              ·
                refine ⟨6991603711471051611336281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661069140980701074224187 6991603711471051611336281)
                ·
                  refine ⟨5243702783603288708502211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6991603711471051611336281 5243702783603288708502211)
                  ·
                    refine ⟨7865554175404933062753317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243702783603288708502211 7865554175404933062753317)
                    ·
                      refine ⟨1474791407888424949266247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7865554175404933062753317 1474791407888424949266247)
                      ·
                        rfl

theorem cell23_2872146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2872146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872146 prefixEnd_2872146 := by exact prefixLift 2872146
  have htrace : WordTrace (prefixWord ++ tailWord_2872146) baseStart_2872146 baseEnd_2872146 := by
    simpa [prefixWord, tailWord_2872146, baseEnd_2872146] using wordTrace_append hprefix tailTrace_2872146
  have hstable : (prefixWord ++ tailWord_2872146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872146).length < 2 ^ (prefixWord ++ tailWord_2872146).sum := by decide
  have hdescent : baseEnd_2872146 < baseStart_2872146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872152 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 10]
def baseStart_2872152 : Nat := 118140960795 + 2872152 * 2 ^ 59
def prefixEnd_2872152 : Nat := 4983230072969 + 3 ^ 40 * 2872152 * 2
def baseEnd_2872152 : Nat := 163866054308039102865691

theorem tailTrace_2872152 : CollatzResearch.WordTrace tailWord_2872152 prefixEnd_2872152 163866054308039102865691 := by
  unfold tailWord_2872152
  simp only [CollatzResearch.WordTrace]
  refine ⟨52377994745345651677029355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69837326327127535569372473 52377994745345651677029355)
  ·
    refine ⟨78566992118018477515544033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52377994745345651677029355 78566992118018477515544033)
    ·
      refine ⟨58925244088513858136658025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78566992118018477515544033 58925244088513858136658025)
      ·
        refine ⟨44193933066385393602493519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58925244088513858136658025 44193933066385393602493519)
        ·
          refine ⟨66290899599578090403740279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44193933066385393602493519 66290899599578090403740279)
          ·
            refine ⟨99436349399367135605610419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66290899599578090403740279 99436349399367135605610419)
            ·
              refine ⟨149154524099050703408415629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99436349399367135605610419 149154524099050703408415629)
              ·
                refine ⟨55932946537144013778155861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149154524099050703408415629 55932946537144013778155861)
                ·
                  refine ⟨163866054308039102865691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 55932946537144013778155861 163866054308039102865691)
                  ·
                    rfl

theorem cell23_2872152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_2872152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872152 prefixEnd_2872152 := by exact prefixLift 2872152
  have htrace : WordTrace (prefixWord ++ tailWord_2872152) baseStart_2872152 baseEnd_2872152 := by
    simpa [prefixWord, tailWord_2872152, baseEnd_2872152] using wordTrace_append hprefix tailTrace_2872152
  have hstable : (prefixWord ++ tailWord_2872152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872152).length < 2 ^ (prefixWord ++ tailWord_2872152).sum := by decide
  have hdescent : baseEnd_2872152 < baseStart_2872152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872190 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2872190 : Nat := 118140960795 + 2872190 * 2 ^ 59
def prefixEnd_2872190 : Nat := 4983230072969 + 3 ^ 40 * 2872190 * 2
def baseEnd_2872190 : Nat := 491604667012407592372015

theorem tailTrace_2872190 : CollatzResearch.WordTrace tailWord_2872190 prefixEnd_2872190 491604667012407592372015 := by
  unfold tailWord_2872190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094671933069204480492753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69838250309702423895961349 13094671933069204480492753)
  ·
    refine ⟨9821003949801903360369565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13094671933069204480492753 9821003949801903360369565)
    ·
      refine ⟨3682876481175713760138587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9821003949801903360369565 3682876481175713760138587)
      ·
        refine ⟨5524314721763570640207881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682876481175713760138587 5524314721763570640207881)
        ·
          refine ⟨4143236041322677980155911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5524314721763570640207881 4143236041322677980155911)
          ·
            refine ⟨6214854061984016970233867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143236041322677980155911 6214854061984016970233867)
            ·
              refine ⟨9322281092976025455350801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214854061984016970233867 9322281092976025455350801)
              ·
                refine ⟨6991710819732019091513101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9322281092976025455350801 6991710819732019091513101)
                ·
                  refine ⟨2621891557399507159317413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6991710819732019091513101 2621891557399507159317413)
                  ·
                    refine ⟨491604667012407592372015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2621891557399507159317413 491604667012407592372015)
                    ·
                      rfl

theorem cell23_2872190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2872190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872190 prefixEnd_2872190 := by exact prefixLift 2872190
  have htrace : WordTrace (prefixWord ++ tailWord_2872190) baseStart_2872190 baseEnd_2872190 := by
    simpa [prefixWord, tailWord_2872190, baseEnd_2872190] using wordTrace_append hprefix tailTrace_2872190
  have hstable : (prefixWord ++ tailWord_2872190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872190).length < 2 ^ (prefixWord ++ tailWord_2872190).sum := by decide
  have hdescent : baseEnd_2872190 < baseStart_2872190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872220 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 6]
def baseStart_2872220 : Nat := 118140960795 + 2872220 * 2 ^ 59
def prefixEnd_2872220 : Nat := 4983230072969 + 3 ^ 40 * 2872220 * 2
def baseEnd_2872220 : Nat := 163869933939650851082323

theorem tailTrace_2872220 : CollatzResearch.WordTrace tailWord_2872220 prefixEnd_2872220 163869933939650851082323 := by
  unfold tailWord_2872220
  simp only [CollatzResearch.WordTrace]
  refine ⟨52379234827222475483767057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69838979769629967311689409 52379234827222475483767057)
  ·
    refine ⟨39284426120416856612825293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52379234827222475483767057 39284426120416856612825293)
    ·
      refine ⟨14731659795156321229809485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39284426120416856612825293 14731659795156321229809485)
      ·
        refine ⟨5524372423183620461178557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14731659795156321229809485 5524372423183620461178557)
        ·
          refine ⟨2071639658693857672941959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5524372423183620461178557 2071639658693857672941959)
          ·
            refine ⟨3107459488040786509412939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071639658693857672941959 3107459488040786509412939)
            ·
              refine ⟨4661189232061179764119409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107459488040786509412939 4661189232061179764119409)
              ·
                refine ⟨3495891924045884823089557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4661189232061179764119409 3495891924045884823089557)
                ·
                  refine ⟨163869933939650851082323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3495891924045884823089557 163869933939650851082323)
                  ·
                    rfl

theorem cell23_2872220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_2872220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872220 prefixEnd_2872220 := by exact prefixLift 2872220
  have htrace : WordTrace (prefixWord ++ tailWord_2872220) baseStart_2872220 baseEnd_2872220 := by
    simpa [prefixWord, tailWord_2872220, baseEnd_2872220] using wordTrace_append hprefix tailTrace_2872220
  have hstable : (prefixWord ++ tailWord_2872220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872220).length < 2 ^ (prefixWord ++ tailWord_2872220).sum := by decide
  have hdescent : baseEnd_2872220 < baseStart_2872220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872239 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_2872239 : Nat := 118140960795 + 2872239 * 2 ^ 59
def prefixEnd_2872239 : Nat := 4983230072969 + 3 ^ 40 * 2872239 * 2
def baseEnd_2872239 : Nat := 1474839161589293085403319

theorem tailTrace_2872239 : CollatzResearch.WordTrace tailWord_2872239 prefixEnd_2872239 1474839161589293085403319 := by
  unfold tailWord_2872239
  simp only [CollatzResearch.WordTrace]
  refine ⟨104759162641376117212475771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69839441760917411474983847 104759162641376117212475771)
  ·
    refine ⟨157138743962064175818713657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104759162641376117212475771 157138743962064175818713657)
    ·
      refine ⟨117854057971548131864035243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157138743962064175818713657 117854057971548131864035243)
      ·
        refine ⟨176781086957322197796052865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117854057971548131864035243 176781086957322197796052865)
        ·
          refine ⟨132585815217991648347039649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176781086957322197796052865 132585815217991648347039649)
          ·
            refine ⟨99439361413493736260279737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132585815217991648347039649 99439361413493736260279737)
            ·
              refine ⟨74579521060120302195209803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99439361413493736260279737 74579521060120302195209803)
              ·
                refine ⟨111869281590180453292814705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74579521060120302195209803 111869281590180453292814705)
                ·
                  refine ⟨83901961192635339969611029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111869281590180453292814705 83901961192635339969611029)
                  ·
                    refine ⟨3932904430904781561075517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83901961192635339969611029 3932904430904781561075517)
                    ·
                      refine ⟨1474839161589293085403319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3932904430904781561075517 1474839161589293085403319)
                      ·
                        rfl

theorem cell23_2872239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_2872239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872239 prefixEnd_2872239 := by exact prefixLift 2872239
  have htrace : WordTrace (prefixWord ++ tailWord_2872239) baseStart_2872239 baseEnd_2872239 := by
    simpa [prefixWord, tailWord_2872239, baseEnd_2872239] using wordTrace_append hprefix tailTrace_2872239
  have hstable : (prefixWord ++ tailWord_2872239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872239).length < 2 ^ (prefixWord ++ tailWord_2872239).sum := by decide
  have hdescent : baseEnd_2872239 < baseStart_2872239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872264 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_2872264 : Nat := 118140960795 + 2872264 * 2 ^ 59
def prefixEnd_2872264 : Nat := 4983230072969 + 3 ^ 40 * 2872264 * 2
def baseEnd_2872264 : Nat := 1474851998605655487590705

theorem tailTrace_2872264 : CollatzResearch.WordTrace tailWord_2872264 prefixEnd_2872264 1474851998605655487590705 := by
  unfold tailWord_2872264
  simp only [CollatzResearch.WordTrace]
  refine ⟨52380037233142773241067923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69840049644190364321423897 52380037233142773241067923)
  ·
    refine ⟨78570055849714159861601885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52380037233142773241067923 78570055849714159861601885)
    ·
      refine ⟨29463770943642809948100707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78570055849714159861601885 29463770943642809948100707)
      ·
        refine ⟨44195656415464214922151061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29463770943642809948100707 44195656415464214922151061)
        ·
          refine ⟨2071671394474885074475831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44195656415464214922151061 2071671394474885074475831)
          ·
            refine ⟨3107507091712327611713747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071671394474885074475831 3107507091712327611713747)
            ·
              refine ⟨4661260637568491417570621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107507091712327611713747 4661260637568491417570621)
              ·
                refine ⟨1747972739088184281588983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4661260637568491417570621 1747972739088184281588983)
                ·
                  refine ⟨2621959108632276422383475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747972739088184281588983 2621959108632276422383475)
                  ·
                    refine ⟨3932938662948414633575213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2621959108632276422383475 3932938662948414633575213)
                    ·
                      refine ⟨1474851998605655487590705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3932938662948414633575213 1474851998605655487590705)
                      ·
                        rfl

theorem cell23_2872264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_2872264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872264 prefixEnd_2872264 := by exact prefixLift 2872264
  have htrace : WordTrace (prefixWord ++ tailWord_2872264) baseStart_2872264 baseEnd_2872264 := by
    simpa [prefixWord, tailWord_2872264, baseEnd_2872264] using wordTrace_append hprefix tailTrace_2872264
  have hstable : (prefixWord ++ tailWord_2872264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872264).length < 2 ^ (prefixWord ++ tailWord_2872264).sum := by decide
  have hdescent : baseEnd_2872264 < baseStart_2872264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872276 : List Nat := [2, 4, 1, 2, 1, 4, 9]
def baseStart_2872276 : Nat := 118140960795 + 2872276 * 2 ^ 59
def prefixEnd_2872276 : Nat := 4983230072969 + 3 ^ 40 * 2872276 * 2
def baseEnd_2872276 : Nat := 18208125436709993094329

theorem tailTrace_2872276 : CollatzResearch.WordTrace tailWord_2872276 prefixEnd_2872276 18208125436709993094329 := by
  unfold tailWord_2872276
  simp only [CollatzResearch.WordTrace]
  refine ⟨52380256071121036265786341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69840341428161381687715121 52380256071121036265786341)
  ·
    refine ⟨9821298013335194299834939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52380256071121036265786341 9821298013335194299834939)
    ·
      refine ⟨14731947020002791449752409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9821298013335194299834939 14731947020002791449752409)
      ·
        refine ⟨11048960265002093587314307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14731947020002791449752409 11048960265002093587314307)
        ·
          refine ⟨16573440397503140380971461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11048960265002093587314307 16573440397503140380971461)
          ·
            refine ⟨3107520074531838821432149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16573440397503140380971461 3107520074531838821432149)
            ·
              refine ⟨18208125436709993094329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3107520074531838821432149 18208125436709993094329)
              ·
                rfl

theorem cell23_2872276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 9].length) (baseStart_2872276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872276 prefixEnd_2872276 := by exact prefixLift 2872276
  have htrace : WordTrace (prefixWord ++ tailWord_2872276) baseStart_2872276 baseEnd_2872276 := by
    simpa [prefixWord, tailWord_2872276, baseEnd_2872276] using wordTrace_append hprefix tailTrace_2872276
  have hstable : (prefixWord ++ tailWord_2872276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872276).length < 2 ^ (prefixWord ++ tailWord_2872276).sum := by decide
  have hdescent : baseEnd_2872276 < baseStart_2872276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872287 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 3, 2, 2]
def baseStart_2872287 : Nat := 118140960795 + 2872287 * 2 ^ 59
def prefixEnd_2872287 : Nat := 4983230072969 + 3 ^ 40 * 2872287 * 2
def baseEnd_2872287 : Nat := 1474863808660708897603099

theorem tailTrace_2872287 : CollatzResearch.WordTrace tailWord_2872287 prefixEnd_2872287 1474863808660708897603099 := by
  unfold tailWord_2872287
  simp only [CollatzResearch.WordTrace]
  refine ⟨104760913345202221410223115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69840608896801480940148743 104760913345202221410223115)
  ·
    refine ⟨157141370017803332115334673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104760913345202221410223115 157141370017803332115334673)
    ·
      refine ⟨117856027513352499086501005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157141370017803332115334673 117856027513352499086501005)
      ·
        refine ⟨44196010317507187157437877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117856027513352499086501005 44196010317507187157437877)
        ·
          refine ⟨4143375967266298796009801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44196010317507187157437877 4143375967266298796009801)
          ·
            refine ⟨3107531975449724097007351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4143375967266298796009801 3107531975449724097007351)
            ·
              refine ⟨4661297963174586145511027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107531975449724097007351 4661297963174586145511027)
              ·
                refine ⟨6991946944761879218266541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661297963174586145511027 6991946944761879218266541)
                ·
                  refine ⟨2621980104285704706849953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6991946944761879218266541 2621980104285704706849953)
                  ·
                    refine ⟨1966485078214278530137465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2621980104285704706849953 1966485078214278530137465)
                    ·
                      refine ⟨1474863808660708897603099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966485078214278530137465 1474863808660708897603099)
                      ·
                        rfl

theorem cell23_2872287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_2872287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872287 prefixEnd_2872287 := by exact prefixLift 2872287
  have htrace : WordTrace (prefixWord ++ tailWord_2872287) baseStart_2872287 baseEnd_2872287 := by
    simpa [prefixWord, tailWord_2872287, baseEnd_2872287] using wordTrace_append hprefix tailTrace_2872287
  have hstable : (prefixWord ++ tailWord_2872287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872287).length < 2 ^ (prefixWord ++ tailWord_2872287).sum := by decide
  have hdescent : baseEnd_2872287 < baseStart_2872287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872289 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2872289 : Nat := 118140960795 + 2872289 * 2 ^ 59
def prefixEnd_2872289 : Nat := 4983230072969 + 3 ^ 40 * 2872289 * 2
def baseEnd_2872289 : Nat := 491621611874005963259363

theorem tailTrace_2872289 : CollatzResearch.WordTrace tailWord_2872289 prefixEnd_2872289 491621611874005963259363 := by
  unfold tailWord_2872289
  simp only [CollatzResearch.WordTrace]
  refine ⟨104760986291194975751795921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69840657527463317167863947 104760986291194975751795921)
  ·
    refine ⟨78570739718396231813846941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104760986291194975751795921 78570739718396231813846941)
    ·
      refine ⟨29464027394398586930192603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78570739718396231813846941 29464027394398586930192603)
      ·
        refine ⟨44196041091597880395288905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29464027394398586930192603 44196041091597880395288905)
        ·
          refine ⟨33147030818698410296466679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44196041091597880395288905 33147030818698410296466679)
          ·
            refine ⟨49720546228047615444700019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33147030818698410296466679 49720546228047615444700019)
            ·
              refine ⟨74580819342071423167050029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49720546228047615444700019 74580819342071423167050029)
              ·
                refine ⟨27967807253276783687643761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74580819342071423167050029 27967807253276783687643761)
                ·
                  refine ⟨20975855439957587765732821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27967807253276783687643761 20975855439957587765732821)
                  ·
                    refine ⟨491621611874005963259363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20975855439957587765732821 491621611874005963259363)
                    ·
                      rfl

theorem cell23_2872289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2872289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872289 prefixEnd_2872289 := by exact prefixLift 2872289
  have htrace : WordTrace (prefixWord ++ tailWord_2872289) baseStart_2872289 baseEnd_2872289 := by
    simpa [prefixWord, tailWord_2872289, baseEnd_2872289] using wordTrace_append hprefix tailTrace_2872289
  have hstable : (prefixWord ++ tailWord_2872289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872289).length < 2 ^ (prefixWord ++ tailWord_2872289).sum := by decide
  have hdescent : baseEnd_2872289 < baseStart_2872289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872293 : List Nat := [1, 3, 1, 6, 1, 1, 2, 8]
def baseStart_2872293 : Nat := 118140960795 + 2872293 * 2 ^ 59
def prefixEnd_2872293 : Nat := 4983230072969 + 3 ^ 40 * 2872293 * 2
def baseEnd_2872293 : Nat := 54624699612764291634373

theorem tailTrace_2872293 : CollatzResearch.WordTrace tailWord_2872293 prefixEnd_2872293 54624699612764291634373 := by
  unfold tailWord_2872293
  simp only [CollatzResearch.WordTrace]
  refine ⟨104761132183180484434941533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69840754788786989623294355 104761132183180484434941533)
  ·
    refine ⟨39285424568692681663103075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104761132183180484434941533 39285424568692681663103075)
    ·
      refine ⟨58928136853039022494654613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39285424568692681663103075 58928136853039022494654613)
      ·
        refine ⟨2762256414986204179436935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58928136853039022494654613 2762256414986204179436935)
        ·
          refine ⟨4143384622479306269155403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762256414986204179436935 4143384622479306269155403)
          ·
            refine ⟨6215076933718959403733105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143384622479306269155403 6215076933718959403733105)
            ·
              refine ⟨4661307700289219552799829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6215076933718959403733105 4661307700289219552799829)
              ·
                refine ⟨54624699612764291634373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4661307700289219552799829 54624699612764291634373)
                ·
                  rfl

theorem cell23_2872293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 8].length) (baseStart_2872293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872293 prefixEnd_2872293 := by exact prefixLift 2872293
  have htrace : WordTrace (prefixWord ++ tailWord_2872293) baseStart_2872293 baseEnd_2872293 := by
    simpa [prefixWord, tailWord_2872293, baseEnd_2872293] using wordTrace_append hprefix tailTrace_2872293
  have hstable : (prefixWord ++ tailWord_2872293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872293).length < 2 ^ (prefixWord ++ tailWord_2872293).sum := by decide
  have hdescent : baseEnd_2872293 < baseStart_2872293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872313 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 3, 3, 2]
def baseStart_2872313 : Nat := 118140960795 + 2872313 * 2 ^ 59
def prefixEnd_2872313 : Nat := 4983230072969 + 3 ^ 40 * 2872313 * 2
def baseEnd_2872313 : Nat := 1474877159157725795877979

theorem tailTrace_2872313 : CollatzResearch.WordTrace tailWord_2872313 prefixEnd_2872313 1474877159157725795877979 := by
  unfold tailWord_2872313
  simp only [CollatzResearch.WordTrace]
  refine ⟨104761861643108027850669593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69841241095405351900446395 104761861643108027850669593)
  ·
    refine ⟨78571396232331020888002195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104761861643108027850669593 78571396232331020888002195)
    ·
      refine ⟨117857094348496531332003293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78571396232331020888002195 117857094348496531332003293)
      ·
        refine ⟨44196410380686199249501235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117857094348496531332003293 44196410380686199249501235)
        ·
          refine ⟨66294615571029298874251853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44196410380686199249501235 66294615571029298874251853)
          ·
            refine ⟨24860480839135987077844445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66294615571029298874251853 24860480839135987077844445)
            ·
              refine ⟨9322680314675995154191667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24860480839135987077844445 9322680314675995154191667)
              ·
                refine ⟨13984020472013992731287501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9322680314675995154191667 13984020472013992731287501)
                ·
                  refine ⟨5244007677005247274232813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13984020472013992731287501 5244007677005247274232813)
                  ·
                    refine ⟨1966502878876967727837305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5244007677005247274232813 1966502878876967727837305)
                    ·
                      refine ⟨1474877159157725795877979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966502878876967727837305 1474877159157725795877979)
                      ·
                        rfl

theorem cell23_2872313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_2872313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872313 prefixEnd_2872313 := by exact prefixLift 2872313
  have htrace : WordTrace (prefixWord ++ tailWord_2872313) baseStart_2872313 baseEnd_2872313 := by
    simpa [prefixWord, tailWord_2872313, baseEnd_2872313] using wordTrace_append hprefix tailTrace_2872313
  have hstable : (prefixWord ++ tailWord_2872313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872313).length < 2 ^ (prefixWord ++ tailWord_2872313).sum := by decide
  have hdescent : baseEnd_2872313 < baseStart_2872313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872319 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 6, 6]
def baseStart_2872319 : Nat := 118140960795 + 2872319 * 2 ^ 59
def prefixEnd_2872319 : Nat := 4983230072969 + 3 ^ 40 * 2872319 * 2
def baseEnd_2872319 : Nat := 491626746680550924134317

theorem tailTrace_2872319 : CollatzResearch.WordTrace tailWord_2872319 prefixEnd_2872319 491626746680550924134317 := by
  unfold tailWord_2872319
  simp only [CollatzResearch.WordTrace]
  refine ⟨104762080481086290875388011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69841386987390860583592007 104762080481086290875388011)
  ·
    refine ⟨157143120721629436313082017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104762080481086290875388011 157143120721629436313082017)
    ·
      refine ⟨117857340541222077234811513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157143120721629436313082017 117857340541222077234811513)
      ·
        refine ⟨88393005405916557926108635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117857340541222077234811513 88393005405916557926108635)
        ·
          refine ⟨132589508108874836889162953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88393005405916557926108635 132589508108874836889162953)
          ·
            refine ⟨99442131081656127666872215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132589508108874836889162953 99442131081656127666872215)
            ·
              refine ⟨149163196622484191500308323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99442131081656127666872215 149163196622484191500308323)
              ·
                refine ⟨223744794933726287250462485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149163196622484191500308323 223744794933726287250462485)
                ·
                  refine ⟨10488037262518419714865429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223744794933726287250462485 10488037262518419714865429)
                  ·
                    refine ⟨491626746680550924134317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10488037262518419714865429 491626746680550924134317)
                    ·
                      rfl

theorem cell23_2872319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_2872319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872319 prefixEnd_2872319 := by exact prefixLift 2872319
  have htrace : WordTrace (prefixWord ++ tailWord_2872319) baseStart_2872319 baseEnd_2872319 := by
    simpa [prefixWord, tailWord_2872319, baseEnd_2872319] using wordTrace_append hprefix tailTrace_2872319
  have hstable : (prefixWord ++ tailWord_2872319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872319).length < 2 ^ (prefixWord ++ tailWord_2872319).sum := by decide
  have hdescent : baseEnd_2872319 < baseStart_2872319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872338 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2872338 : Nat := 118140960795 + 2872338 * 2 ^ 59
def prefixEnd_2872338 : Nat := 4983230072969 + 3 ^ 40 * 2872338 * 2
def baseEnd_2872338 : Nat := 1474889996174088198065365

theorem tailTrace_2872338 : CollatzResearch.WordTrace tailWord_2872338 prefixEnd_2872338 1474889996174088198065365 := by
  unfold tailWord_2872338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26190693367004364280082417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69841848978678304746886445 26190693367004364280082417)
  ·
    refine ⟨19643020025253273210061813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26190693367004364280082417 19643020025253273210061813)
    ·
      refine ⟨1841533127367494363443295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19643020025253273210061813 1841533127367494363443295)
      ·
        refine ⟨2762299691051241545164943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841533127367494363443295 2762299691051241545164943)
        ·
          refine ⟨4143449536576862317747415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762299691051241545164943 4143449536576862317747415)
          ·
            refine ⟨6215174304865293476621123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143449536576862317747415 6215174304865293476621123)
            ·
              refine ⟨9322761457297940214931685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215174304865293476621123 9322761457297940214931685)
              ·
                refine ⟨1748017773243363790299691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9322761457297940214931685 1748017773243363790299691)
                ·
                  refine ⟨2622026659865045685449537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748017773243363790299691 2622026659865045685449537)
                  ·
                    refine ⟨1966519994898784264087153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2622026659865045685449537 1966519994898784264087153)
                    ·
                      refine ⟨1474889996174088198065365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966519994898784264087153 1474889996174088198065365)
                      ·
                        rfl

theorem cell23_2872338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2872338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872338 prefixEnd_2872338 := by exact prefixLift 2872338
  have htrace : WordTrace (prefixWord ++ tailWord_2872338) baseStart_2872338 baseEnd_2872338 := by
    simpa [prefixWord, tailWord_2872338, baseEnd_2872338] using wordTrace_append hprefix tailTrace_2872338
  have hstable : (prefixWord ++ tailWord_2872338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872338).length < 2 ^ (prefixWord ++ tailWord_2872338).sum := by decide
  have hdescent : baseEnd_2872338 < baseStart_2872338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872339 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_2872339 : Nat := 118140960795 + 2872339 * 2 ^ 59
def prefixEnd_2872339 : Nat := 4983230072969 + 3 ^ 40 * 2872339 * 2
def baseEnd_2872339 : Nat := 1474890509654742694152859

theorem tailTrace_2872339 : CollatzResearch.WordTrace tailWord_2872339 prefixEnd_2872339 1474890509654742694152859 := by
  unfold tailWord_2872339
  simp only [CollatzResearch.WordTrace]
  refine ⟨104762809941013834291116071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69841873294009222860744047 104762809941013834291116071)
  ·
    refine ⟨157144214911520751436674107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104762809941013834291116071 157144214911520751436674107)
    ·
      refine ⟨235716322367281127155011161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157144214911520751436674107 235716322367281127155011161)
      ·
        refine ⟨176787241775460845366258371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235716322367281127155011161 176787241775460845366258371)
        ·
          refine ⟨265180862663191268049387557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176787241775460845366258371 265180862663191268049387557)
          ·
            refine ⟨49721411749348362759260167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265180862663191268049387557 49721411749348362759260167)
            ·
              refine ⟨74582117624022544138890251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49721411749348362759260167 74582117624022544138890251)
              ·
                refine ⟨111873176436033816208335377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74582117624022544138890251 111873176436033816208335377)
                ·
                  refine ⟨83904882327025362156251533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111873176436033816208335377 83904882327025362156251533)
                  ·
                    refine ⟨31464330872634510808594325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83904882327025362156251533 31464330872634510808594325)
                    ·
                      refine ⟨1474890509654742694152859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31464330872634510808594325 1474890509654742694152859)
                      ·
                        rfl

theorem cell23_2872339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_2872339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872339 prefixEnd_2872339 := by exact prefixLift 2872339
  have htrace : WordTrace (prefixWord ++ tailWord_2872339) baseStart_2872339 baseEnd_2872339 := by
    simpa [prefixWord, tailWord_2872339, baseEnd_2872339] using wordTrace_append hprefix tailTrace_2872339
  have hstable : (prefixWord ++ tailWord_2872339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872339).length < 2 ^ (prefixWord ++ tailWord_2872339).sum := by decide
  have hdescent : baseEnd_2872339 < baseStart_2872339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872346 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_2872346 : Nat := 118140960795 + 2872346 * 2 ^ 59
def prefixEnd_2872346 : Nat := 4983230072969 + 3 ^ 40 * 2872346 * 2
def baseEnd_2872346 : Nat := 1474894104019324166765327

theorem tailTrace_2872346 : CollatzResearch.WordTrace tailWord_2872346 prefixEnd_2872346 1474894104019324166765327 := by
  unfold tailWord_2872346
  simp only [CollatzResearch.WordTrace]
  refine ⟨26190766312997118621655223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69842043501325649657747261 26190766312997118621655223)
  ·
    refine ⟨39286149469495677932482835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26190766312997118621655223 39286149469495677932482835)
    ·
      refine ⟨58929224204243516898724253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39286149469495677932482835 58929224204243516898724253)
      ·
        refine ⟨22098459076591318837021595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58929224204243516898724253 22098459076591318837021595)
        ·
          refine ⟨33147688614886978255532393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22098459076591318837021595 33147688614886978255532393)
          ·
            refine ⟨24860766461165233691649295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33147688614886978255532393 24860766461165233691649295)
            ·
              refine ⟨37291149691747850537473943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24860766461165233691649295 37291149691747850537473943)
              ·
                refine ⟨55936724537621775806210915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37291149691747850537473943 55936724537621775806210915)
                ·
                  refine ⟨83905086806432663709316373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55936724537621775806210915 83905086806432663709316373)
                  ·
                    refine ⟨3933050944051531111374205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83905086806432663709316373 3933050944051531111374205)
                    ·
                      refine ⟨1474894104019324166765327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933050944051531111374205 1474894104019324166765327)
                      ·
                        rfl

theorem cell23_2872346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_2872346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872346 prefixEnd_2872346 := by exact prefixLift 2872346
  have htrace : WordTrace (prefixWord ++ tailWord_2872346) baseStart_2872346 baseEnd_2872346 := by
    simpa [prefixWord, tailWord_2872346, baseEnd_2872346] using wordTrace_append hprefix tailTrace_2872346
  have hstable : (prefixWord ++ tailWord_2872346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872346).length < 2 ^ (prefixWord ++ tailWord_2872346).sum := by decide
  have hdescent : baseEnd_2872346 < baseStart_2872346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872390 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2872390 : Nat := 118140960795 + 2872390 * 2 ^ 59
def prefixEnd_2872390 : Nat := 4983230072969 + 3 ^ 40 * 2872390 * 2
def baseEnd_2872390 : Nat := 1474916697168121994615125

theorem tailTrace_2872390 : CollatzResearch.WordTrace tailWord_2872390 prefixEnd_2872390 1474916697168121994615125 := by
  unfold tailWord_2872390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273895939494658437538207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69843113375886046667481749 3273895939494658437538207)
  ·
    refine ⟨4910843909241987656307311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273895939494658437538207 4910843909241987656307311)
    ·
      refine ⟨7366265863862981484460967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4910843909241987656307311 7366265863862981484460967)
      ·
        refine ⟨11049398795794472226691451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7366265863862981484460967 11049398795794472226691451)
        ·
          refine ⟨16574098193691708340037177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11049398795794472226691451 16574098193691708340037177)
          ·
            refine ⟨12430573645268781255027883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16574098193691708340037177 12430573645268781255027883)
            ·
              refine ⟨18645860467903171882541825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12430573645268781255027883 18645860467903171882541825)
              ·
                refine ⟨13984395350927378911906369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18645860467903171882541825 13984395350927378911906369)
                ·
                  refine ⟨10488296513195534183929777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13984395350927378911906369 10488296513195534183929777)
                  ·
                    refine ⟨7866222384896650637947333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10488296513195534183929777 7866222384896650637947333)
                    ·
                      refine ⟨1474916697168121994615125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7866222384896650637947333 1474916697168121994615125)
                      ·
                        rfl

theorem cell23_2872390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2872390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872390 prefixEnd_2872390 := by exact prefixLift 2872390
  have htrace : WordTrace (prefixWord ++ tailWord_2872390) baseStart_2872390 baseEnd_2872390 := by
    simpa [prefixWord, tailWord_2872390, baseEnd_2872390] using wordTrace_append hprefix tailTrace_2872390
  have hstable : (prefixWord ++ tailWord_2872390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872390).length < 2 ^ (prefixWord ++ tailWord_2872390).sum := by decide
  have hdescent : baseEnd_2872390 < baseStart_2872390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872396 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_2872396 : Nat := 118140960795 + 2872396 * 2 ^ 59
def prefixEnd_2872396 : Nat := 4983230072969 + 3 ^ 40 * 2872396 * 2
def baseEnd_2872396 : Nat := 491639926017349657046699

theorem tailTrace_2872396 : CollatzResearch.WordTrace tailWord_2872396 prefixEnd_2872396 491639926017349657046699 := by
  unfold tailWord_2872396
  simp only [CollatzResearch.WordTrace]
  refine ⟨52382444450903666512970521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69843259267871555350627361 52382444450903666512970521)
  ·
    refine ⟨39286833338177749884727891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52382444450903666512970521 39286833338177749884727891)
    ·
      refine ⟨58930250007266624827091837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39286833338177749884727891 58930250007266624827091837)
      ·
        refine ⟨22098843752724984310159439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58930250007266624827091837 22098843752724984310159439)
        ·
          refine ⟨33148265629087476465239159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22098843752724984310159439 33148265629087476465239159)
          ·
            refine ⟨49722398443631214697858739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33148265629087476465239159 49722398443631214697858739)
            ·
              refine ⟨74583597665446822046788109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49722398443631214697858739 74583597665446822046788109)
              ·
                refine ⟨27968849124542558267545541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74583597665446822046788109 27968849124542558267545541)
                ·
                  refine ⟨5244159210851729675164789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27968849124542558267545541 5244159210851729675164789)
                  ·
                    refine ⟨491639926017349657046699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5244159210851729675164789 491639926017349657046699)
                    ·
                      rfl

theorem cell23_2872396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_2872396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872396 prefixEnd_2872396 := by exact prefixLift 2872396
  have htrace : WordTrace (prefixWord ++ tailWord_2872396) baseStart_2872396 baseEnd_2872396 := by
    simpa [prefixWord, tailWord_2872396, baseEnd_2872396] using wordTrace_append hprefix tailTrace_2872396
  have hstable : (prefixWord ++ tailWord_2872396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872396).length < 2 ^ (prefixWord ++ tailWord_2872396).sum := by decide
  have hdescent : baseEnd_2872396 < baseStart_2872396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872416 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2872416 : Nat := 118140960795 + 2872416 * 2 ^ 59
def prefixEnd_2872416 : Nat := 4983230072969 + 3 ^ 40 * 2872416 * 2
def baseEnd_2872416 : Nat := 1474930047665138892890005

theorem tailTrace_2872416 : CollatzResearch.WordTrace tailWord_2872416 prefixEnd_2872416 1474930047665138892890005 := by
  unfold tailWord_2872416
  simp only [CollatzResearch.WordTrace]
  refine ⟨52382809180867438220834551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69843745574489917627779401 52382809180867438220834551)
  ·
    refine ⟨78574213771301157331251827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52382809180867438220834551 78574213771301157331251827)
    ·
      refine ⟨117861320656951735996877741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78574213771301157331251827 117861320656951735996877741)
      ·
        refine ⟨44197995246356900998829153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117861320656951735996877741 44197995246356900998829153)
        ·
          refine ⟨33148496434767675749121865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44197995246356900998829153 33148496434767675749121865)
          ·
            refine ⟨24861372326075756811841399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33148496434767675749121865 24861372326075756811841399)
            ·
              refine ⟨37292058489113635217762099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24861372326075756811841399 37292058489113635217762099)
              ·
                refine ⟨55938087733670452826643149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37292058489113635217762099 55938087733670452826643149)
                ·
                  refine ⟨20976782900126419809991181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55938087733670452826643149 20976782900126419809991181)
                  ·
                    refine ⟨7866293587547407428746693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20976782900126419809991181 7866293587547407428746693)
                    ·
                      refine ⟨1474930047665138892890005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7866293587547407428746693 1474930047665138892890005)
                      ·
                        rfl

theorem cell23_2872416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2872416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872416 prefixEnd_2872416 := by exact prefixLift 2872416
  have htrace : WordTrace (prefixWord ++ tailWord_2872416) baseStart_2872416 baseEnd_2872416 := by
    simpa [prefixWord, tailWord_2872416, baseEnd_2872416] using wordTrace_append hprefix tailTrace_2872416
  have hstable : (prefixWord ++ tailWord_2872416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872416).length < 2 ^ (prefixWord ++ tailWord_2872416).sum := by decide
  have hdescent : baseEnd_2872416 < baseStart_2872416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872433 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 4, 4, 2]
def baseStart_2872433 : Nat := 118140960795 + 2872433 * 2 ^ 59
def prefixEnd_2872433 : Nat := 4983230072969 + 3 ^ 40 * 2872433 * 2
def baseEnd_2872433 : Nat := 1474938776836265326377427

theorem tailTrace_2872433 : CollatzResearch.WordTrace tailWord_2872433 prefixEnd_2872433 1474938776836265326377427 := by
  unfold tailWord_2872433
  simp only [CollatzResearch.WordTrace]
  refine ⟨104766238402673288345037953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69844158935115525563358635 104766238402673288345037953)
  ·
    refine ⟨78574678802004966258778465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104766238402673288345037953 78574678802004966258778465)
    ·
      refine ⟨58931009101503724694083849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78574678802004966258778465 58931009101503724694083849)
      ·
        refine ⟨44198256826127793520562887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58931009101503724694083849 44198256826127793520562887)
        ·
          refine ⟨66297385239191690280844331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44198256826127793520562887 66297385239191690280844331)
          ·
            refine ⟨99446077858787535421266497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66297385239191690280844331 99446077858787535421266497)
            ·
              refine ⟨74584558394090651565949873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99446077858787535421266497 74584558394090651565949873)
              ·
                refine ⟨55938418795567988674462405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74584558394090651565949873 55938418795567988674462405)
                ·
                  refine ⟨10488453524168997876461701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55938418795567988674462405 10488453524168997876461701)
                  ·
                    refine ⟨1966585035781687101836569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10488453524168997876461701 1966585035781687101836569)
                    ·
                      refine ⟨1474938776836265326377427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966585035781687101836569 1474938776836265326377427)
                      ·
                        rfl

theorem cell23_2872433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_2872433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872433 prefixEnd_2872433 := by exact prefixLift 2872433
  have htrace : WordTrace (prefixWord ++ tailWord_2872433) baseStart_2872433 baseEnd_2872433 := by
    simpa [prefixWord, tailWord_2872433, baseEnd_2872433] using wordTrace_append hprefix tailTrace_2872433
  have hstable : (prefixWord ++ tailWord_2872433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872433).length < 2 ^ (prefixWord ++ tailWord_2872433).sum := by decide
  have hdescent : baseEnd_2872433 < baseStart_2872433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872460 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_2872460 : Nat := 118140960795 + 2872460 * 2 ^ 59
def prefixEnd_2872460 : Nat := 4983230072969 + 3 ^ 40 * 2872460 * 2
def baseEnd_2872460 : Nat := 491650880271312240246601

theorem tailTrace_2872460 : CollatzResearch.WordTrace tailWord_2872460 prefixEnd_2872460 491650880271312240246601 := by
  unfold tailWord_2872460
  simp only [CollatzResearch.WordTrace]
  refine ⟨52383611586787735978135417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69844815449050314637513889 52383611586787735978135417)
  ·
    refine ⟨39287708690090801983601563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52383611586787735978135417 39287708690090801983601563)
    ·
      refine ⟨58931563035136202975402345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39287708690090801983601563 58931563035136202975402345)
      ·
        refine ⟨44198672276352152231551759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58931563035136202975402345 44198672276352152231551759)
        ·
          refine ⟨66298008414528228347327639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44198672276352152231551759 66298008414528228347327639)
          ·
            refine ⟨99447012621792342520991459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66298008414528228347327639 99447012621792342520991459)
            ·
              refine ⟨149170518932688513781487189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99447012621792342520991459 149170518932688513781487189)
              ·
                refine ⟨1748092018742443520876803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 149170518932688513781487189 1748092018742443520876803)
                ·
                  refine ⟨2622138028113665281315205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748092018742443520876803 2622138028113665281315205)
                  ·
                    refine ⟨491650880271312240246601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622138028113665281315205 491650880271312240246601)
                    ·
                      rfl

theorem cell23_2872460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_2872460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872460 prefixEnd_2872460 := by exact prefixLift 2872460
  have htrace : WordTrace (prefixWord ++ tailWord_2872460) baseStart_2872460 baseEnd_2872460 := by
    simpa [prefixWord, tailWord_2872460, baseEnd_2872460] using wordTrace_append hprefix tailTrace_2872460
  have hstable : (prefixWord ++ tailWord_2872460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872460).length < 2 ^ (prefixWord ++ tailWord_2872460).sum := by decide
  have hdescent : baseEnd_2872460 < baseStart_2872460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872487 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2872487 : Nat := 118140960795 + 2872487 * 2 ^ 59
def prefixEnd_2872487 : Nat := 4983230072969 + 3 ^ 40 * 2872487 * 2
def baseEnd_2872487 : Nat := 1474966504791608115102179

theorem tailTrace_2872487 : CollatzResearch.WordTrace tailWord_2872487 prefixEnd_2872487 1474966504791608115102179 := by
  unfold tailWord_2872487
  simp only [CollatzResearch.WordTrace]
  refine ⟨104768207944477655567503715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69845471962985103711669143 104768207944477655567503715)
  ·
    refine ⟨157152311916716483351255573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104768207944477655567503715 157152311916716483351255573)
    ·
      refine ⟨7366514621096085157090105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157152311916716483351255573 7366514621096085157090105)
      ·
        refine ⟨5524885965822063867817579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7366514621096085157090105 5524885965822063867817579)
        ·
          refine ⟨8287328948733095801726369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524885965822063867817579 8287328948733095801726369)
          ·
            refine ⟨6215496711549821851294777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8287328948733095801726369 6215496711549821851294777)
            ·
              refine ⟨4661622533662366388471083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6215496711549821851294777 4661622533662366388471083)
              ·
                refine ⟨6992433800493549582706625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661622533662366388471083 6992433800493549582706625)
                ·
                  refine ⟨5244325350370162187029969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6992433800493549582706625 5244325350370162187029969)
                  ·
                    refine ⟨3933244012777621640272477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5244325350370162187029969 3933244012777621640272477)
                    ·
                      refine ⟨1474966504791608115102179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933244012777621640272477 1474966504791608115102179)
                      ·
                        rfl

theorem cell23_2872487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2872487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872487 prefixEnd_2872487 := by exact prefixLift 2872487
  have htrace : WordTrace (prefixWord ++ tailWord_2872487) baseStart_2872487 baseEnd_2872487 := by
    simpa [prefixWord, tailWord_2872487, baseEnd_2872487] using wordTrace_append hprefix tailTrace_2872487
  have hstable : (prefixWord ++ tailWord_2872487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872487).length < 2 ^ (prefixWord ++ tailWord_2872487).sum := by decide
  have hdescent : baseEnd_2872487 < baseStart_2872487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872551 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2872551 : Nat := 118140960795 + 2872551 * 2 ^ 59
def prefixEnd_2872551 : Nat := 4983230072969 + 3 ^ 40 * 2872551 * 2
def baseEnd_2872551 : Nat := 1474999367553495864701885

theorem tailTrace_2872551 : CollatzResearch.WordTrace tailWord_2872551 prefixEnd_2872551 1474999367553495864701885 := by
  unfold tailWord_2872551
  simp only [CollatzResearch.WordTrace]
  refine ⟨104770542216245794497833507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69847028144163862998555671 104770542216245794497833507)
  ·
    refine ⟨157155813324368691746750261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104770542216245794497833507 157155813324368691746750261)
    ·
      refine ⟨14733357499159564851257837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157155813324368691746750261 14733357499159564851257837)
      ·
        refine ⟨5525009062184836819221689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14733357499159564851257837 5525009062184836819221689)
        ·
          refine ⟨4143756796638627614416267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5525009062184836819221689 4143756796638627614416267)
          ·
            refine ⟨6215635194957941421624401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143756796638627614416267 6215635194957941421624401)
            ·
              refine ⟨4661726396218456066218301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6215635194957941421624401 4661726396218456066218301)
              ·
                refine ⟨1748147398581921024831863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4661726396218456066218301 1748147398581921024831863)
                ·
                  refine ⟨2622221097872881537247795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748147398581921024831863 2622221097872881537247795)
                  ·
                    refine ⟨3933331646809322305871693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2622221097872881537247795 3933331646809322305871693)
                    ·
                      refine ⟨1474999367553495864701885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933331646809322305871693 1474999367553495864701885)
                      ·
                        rfl

theorem cell23_2872551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2872551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872551 prefixEnd_2872551 := by exact prefixLift 2872551
  have htrace : WordTrace (prefixWord ++ tailWord_2872551) baseStart_2872551 baseEnd_2872551 := by
    simpa [prefixWord, tailWord_2872551, baseEnd_2872551] using wordTrace_append hprefix tailTrace_2872551
  have hstable : (prefixWord ++ tailWord_2872551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872551).length < 2 ^ (prefixWord ++ tailWord_2872551).sum := by decide
  have hdescent : baseEnd_2872551 < baseStart_2872551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872557 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2872557 : Nat := 118140960795 + 2872557 * 2 ^ 59
def prefixEnd_2872557 : Nat := 4983230072969 + 3 ^ 40 * 2872557 * 2
def baseEnd_2872557 : Nat := 1475002448437422841226857

theorem tailTrace_2872557 : CollatzResearch.WordTrace tailWord_2872557 prefixEnd_2872557 1475002448437422841226857 := by
  unfold tailWord_2872557
  simp only [CollatzResearch.WordTrace]
  refine ⟨104770761054224057522551925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69847174036149371681701283 104770761054224057522551925)
  ·
    refine ⟨9822258848833505392739243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104770761054224057522551925 9822258848833505392739243)
    ·
      refine ⟨14733388273250258089108865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9822258848833505392739243 14733388273250258089108865)
      ·
        refine ⟨11050041204937693566831649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14733388273250258089108865 11050041204937693566831649)
        ·
          refine ⟨8287530903703270175123737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11050041204937693566831649 8287530903703270175123737)
          ·
            refine ⟨6215648177777452631342803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8287530903703270175123737 6215648177777452631342803)
            ·
              refine ⟨9323472266666178947014205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215648177777452631342803 9323472266666178947014205)
              ·
                refine ⟨3496302099999817105130327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9323472266666178947014205 3496302099999817105130327)
                ·
                  refine ⟨5244453149999725657695491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496302099999817105130327 5244453149999725657695491)
                  ·
                    refine ⟨7866679724999588486543237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5244453149999725657695491 7866679724999588486543237)
                    ·
                      refine ⟨1475002448437422841226857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7866679724999588486543237 1475002448437422841226857)
                      ·
                        rfl

theorem cell23_2872557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2872557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872557 prefixEnd_2872557 := by exact prefixLift 2872557
  have htrace : WordTrace (prefixWord ++ tailWord_2872557) baseStart_2872557 baseEnd_2872557 := by
    simpa [prefixWord, tailWord_2872557, baseEnd_2872557] using wordTrace_append hprefix tailTrace_2872557
  have hstable : (prefixWord ++ tailWord_2872557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872557).length < 2 ^ (prefixWord ++ tailWord_2872557).sum := by decide
  have hdescent : baseEnd_2872557 < baseStart_2872557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872573 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_2872573 : Nat := 118140960795 + 2872573 * 2 ^ 59
def prefixEnd_2872573 : Nat := 4983230072969 + 3 ^ 40 * 2872573 * 2
def baseEnd_2872573 : Nat := 1475010664127894778626783

theorem tailTrace_2872573 : CollatzResearch.WordTrace tailWord_2872573 prefixEnd_2872573 1475010664127894778626783 := by
  unfold tailWord_2872573
  simp only [CollatzResearch.WordTrace]
  refine ⟨104771344622166092255134373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69847563081444061503422915 104771344622166092255134373)
  ·
    refine ⟨19644627116656142297837695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104771344622166092255134373 19644627116656142297837695)
    ·
      refine ⟨29466940674984213446756543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19644627116656142297837695 29466940674984213446756543)
      ·
        refine ⟨44200411012476320170134815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29466940674984213446756543 44200411012476320170134815)
        ·
          refine ⟨66300616518714480255202223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44200411012476320170134815 66300616518714480255202223)
          ·
            refine ⟨99450924778071720382803335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66300616518714480255202223 99450924778071720382803335)
            ·
              refine ⟨149176387167107580574205003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99450924778071720382803335 149176387167107580574205003)
              ·
                refine ⟨223764580750661370861307505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149176387167107580574205003 223764580750661370861307505)
                ·
                  refine ⟨167823435562996028145980629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223764580750661370861307505 167823435562996028145980629)
                  ·
                    refine ⟨3933361771007719409671421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167823435562996028145980629 3933361771007719409671421)
                    ·
                      refine ⟨1475010664127894778626783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933361771007719409671421 1475010664127894778626783)
                      ·
                        rfl

theorem cell23_2872573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_2872573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872573 prefixEnd_2872573 := by exact prefixLift 2872573
  have htrace : WordTrace (prefixWord ++ tailWord_2872573) baseStart_2872573 baseEnd_2872573 := by
    simpa [prefixWord, tailWord_2872573, baseEnd_2872573] using wordTrace_append hprefix tailTrace_2872573
  have hstable : (prefixWord ++ tailWord_2872573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872573).length < 2 ^ (prefixWord ++ tailWord_2872573).sum := by decide
  have hdescent : baseEnd_2872573 < baseStart_2872573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872574 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2872574 : Nat := 118140960795 + 2872574 * 2 ^ 59
def prefixEnd_2872574 : Nat := 4983230072969 + 3 ^ 40 * 2872574 * 2
def baseEnd_2872574 : Nat := 1475011177608549274714279

theorem tailTrace_2872574 : CollatzResearch.WordTrace tailWord_2872574 prefixEnd_2872574 1475011177608549274714279 := by
  unfold tailWord_2872574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096422636895308678240097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69847587396774979617280517 13096422636895308678240097)
  ·
    refine ⟨9822316977671481508680073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13096422636895308678240097 9822316977671481508680073)
    ·
      refine ⟨7366737733253611131510055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9822316977671481508680073 7366737733253611131510055)
      ·
        refine ⟨11050106599880416697265083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7366737733253611131510055 11050106599880416697265083)
        ·
          refine ⟨16575159899820625045897625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050106599880416697265083 16575159899820625045897625)
          ·
            refine ⟨12431369924865468784423219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16575159899820625045897625 12431369924865468784423219)
            ·
              refine ⟨18647054887298203176634829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431369924865468784423219 18647054887298203176634829)
              ·
                refine ⟨6992645582736826191238061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18647054887298203176634829 6992645582736826191238061)
                ·
                  refine ⟨2622242093526309821714273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6992645582736826191238061 2622242093526309821714273)
                  ·
                    refine ⟨1966681570144732366285705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2622242093526309821714273 1966681570144732366285705)
                    ·
                      refine ⟨1475011177608549274714279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966681570144732366285705 1475011177608549274714279)
                      ·
                        rfl

theorem cell23_2872574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2872574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872574 prefixEnd_2872574 := by exact prefixLift 2872574
  have htrace : WordTrace (prefixWord ++ tailWord_2872574) baseStart_2872574 baseEnd_2872574 := by
    simpa [prefixWord, tailWord_2872574, baseEnd_2872574] using wordTrace_append hprefix tailTrace_2872574
  have hstable : (prefixWord ++ tailWord_2872574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872574).length < 2 ^ (prefixWord ++ tailWord_2872574).sum := by decide
  have hdescent : baseEnd_2872574 < baseStart_2872574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872584 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 2, 4]
def baseStart_2872584 : Nat := 118140960795 + 2872584 * 2 ^ 59
def prefixEnd_2872584 : Nat := 4983230072969 + 3 ^ 40 * 2872584 * 2
def baseEnd_2872584 : Nat := 491672104138364745196411

theorem tailTrace_2872584 : CollatzResearch.WordTrace tailWord_2872584 prefixEnd_2872584 491672104138364745196411 := by
  unfold tailWord_2872584
  simp only [CollatzResearch.WordTrace]
  refine ⟨52385872912563120566892403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69847830550084160755856537 52385872912563120566892403)
  ·
    refine ⟨78578809368844680850338605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52385872912563120566892403 78578809368844680850338605)
    ·
      refine ⟨29467053513316755318876977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78578809368844680850338605 29467053513316755318876977)
      ·
        refine ⟨22100290134987566489157733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29467053513316755318876977 22100290134987566489157733)
        ·
          refine ⟨4143804400310168716717075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22100290134987566489157733 4143804400310168716717075)
          ·
            refine ⟨6215706600465253075075613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143804400310168716717075 6215706600465253075075613)
            ·
              refine ⟨2330889975174469903153355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6215706600465253075075613 2330889975174469903153355)
              ·
                refine ⟨3496334962761704854730033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330889975174469903153355 3496334962761704854730033)
                ·
                  refine ⟨2622251222071278641047525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3496334962761704854730033 2622251222071278641047525)
                  ·
                    refine ⟨491672104138364745196411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622251222071278641047525 491672104138364745196411)
                    ·
                      rfl

theorem cell23_2872584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_2872584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872584 prefixEnd_2872584 := by exact prefixLift 2872584
  have htrace : WordTrace (prefixWord ++ tailWord_2872584) baseStart_2872584 baseEnd_2872584 := by
    simpa [prefixWord, tailWord_2872584, baseEnd_2872584] using wordTrace_append hprefix tailTrace_2872584
  have hstable : (prefixWord ++ tailWord_2872584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872584).length < 2 ^ (prefixWord ++ tailWord_2872584).sum := by decide
  have hdescent : baseEnd_2872584 < baseStart_2872584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872608 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 1, 2, 2]
def baseStart_2872608 : Nat := 118140960795 + 2872608 * 2 ^ 59
def prefixEnd_2872608 : Nat := 4983230072969 + 3 ^ 40 * 2872608 * 2
def baseEnd_2872608 : Nat := 1475028635950802141689123

theorem tailTrace_2872608 : CollatzResearch.WordTrace tailWord_2872608 prefixEnd_2872608 1475028635950802141689123 := by
  unfold tailWord_2872608
  simp only [CollatzResearch.WordTrace]
  refine ⟨52386310588519646616329239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69848414118026195488438985 52386310588519646616329239)
  ·
    refine ⟨78579465882779469924493859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52386310588519646616329239 78579465882779469924493859)
    ·
      refine ⟨117869198824169204886740789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78579465882779469924493859 117869198824169204886740789)
      ·
        refine ⟨11050237389765862958131949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117869198824169204886740789 11050237389765862958131949)
        ·
          refine ⟨4143839021162198609299481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11050237389765862958131949 4143839021162198609299481)
          ·
            refine ⟨3107879265871648956974611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4143839021162198609299481 3107879265871648956974611)
            ·
              refine ⟨4661818898807473435461917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107879265871648956974611 4661818898807473435461917)
              ·
                refine ⟨1748182087052802538298219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4661818898807473435461917 1748182087052802538298219)
                ·
                  refine ⟨2622273130579203807447329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748182087052802538298219 2622273130579203807447329)
                  ·
                    refine ⟨1966704847934402855585497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2622273130579203807447329 1966704847934402855585497)
                    ·
                      refine ⟨1475028635950802141689123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966704847934402855585497 1475028635950802141689123)
                      ·
                        rfl

theorem cell23_2872608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_2872608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872608 prefixEnd_2872608 := by exact prefixLift 2872608
  have htrace : WordTrace (prefixWord ++ tailWord_2872608) baseStart_2872608 baseEnd_2872608 := by
    simpa [prefixWord, tailWord_2872608, baseEnd_2872608] using wordTrace_append hprefix tailTrace_2872608
  have hstable : (prefixWord ++ tailWord_2872608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872608).length < 2 ^ (prefixWord ++ tailWord_2872608).sum := by decide
  have hdescent : baseEnd_2872608 < baseStart_2872608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872641 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2872641 : Nat := 118140960795 + 2872641 * 2 ^ 59
def prefixEnd_2872641 : Nat := 4983230072969 + 3 ^ 40 * 2872641 * 2
def baseEnd_2872641 : Nat := 1475045580812400512576471

theorem tailTrace_2872641 : CollatzResearch.WordTrace tailWord_2872641 prefixEnd_2872641 1475045580812400512576471 := by
  unfold tailWord_2872641
  simp only [CollatzResearch.WordTrace]
  refine ⟨104773824785919739868609777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69849216523946493245739851 104773824785919739868609777)
  ·
    refine ⟨78580368589439804901457333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104773824785919739868609777 78580368589439804901457333)
    ·
      refine ⟨7366909555259981709511625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78580368589439804901457333 7366909555259981709511625)
      ·
        refine ⟨5525182166444986282133719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7366909555259981709511625 5525182166444986282133719)
        ·
          refine ⟨8287773249667479423200579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525182166444986282133719 8287773249667479423200579)
          ·
            refine ⟨12431659874501219134800869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287773249667479423200579 12431659874501219134800869)
            ·
              refine ⟨2330936226468978587775163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12431659874501219134800869 2330936226468978587775163)
              ·
                refine ⟨3496404339703467881662745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330936226468978587775163 3496404339703467881662745)
                ·
                  refine ⟨2622303254777600911247059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3496404339703467881662745 2622303254777600911247059)
                  ·
                    refine ⟨3933454882166401366870589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2622303254777600911247059 3933454882166401366870589)
                    ·
                      refine ⟨1475045580812400512576471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933454882166401366870589 1475045580812400512576471)
                      ·
                        rfl

theorem cell23_2872641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2872641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872641 prefixEnd_2872641 := by exact prefixLift 2872641
  have htrace : WordTrace (prefixWord ++ tailWord_2872641) baseStart_2872641 baseEnd_2872641 := by
    simpa [prefixWord, tailWord_2872641, baseEnd_2872641] using wordTrace_append hprefix tailTrace_2872641
  have hstable : (prefixWord ++ tailWord_2872641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872641).length < 2 ^ (prefixWord ++ tailWord_2872641).sum := by decide
  have hdescent : baseEnd_2872641 < baseStart_2872641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872643 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4]
def baseStart_2872643 : Nat := 118140960795 + 2872643 * 2 ^ 59
def prefixEnd_2872643 : Nat := 4983230072969 + 3 ^ 40 * 2872643 * 2
def baseEnd_2872643 : Nat := 1475046607773709504751461

theorem tailTrace_2872643 : CollatzResearch.WordTrace tailWord_2872643 prefixEnd_2872643 1475046607773709504751461 := by
  unfold tailWord_2872643
  simp only [CollatzResearch.WordTrace]
  refine ⟨104773897731912494210182583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69849265154608329473455055 104773897731912494210182583)
  ·
    refine ⟨157160846597868741315273875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104773897731912494210182583 157160846597868741315273875)
    ·
      refine ⟨235741269896803111972910813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157160846597868741315273875 235741269896803111972910813)
      ·
        refine ⟨88402976211301166989841555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235741269896803111972910813 88402976211301166989841555)
        ·
          refine ⟨132604464316951750484762333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88402976211301166989841555 132604464316951750484762333)
          ·
            refine ⟨49726674118856906431785875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132604464316951750484762333 49726674118856906431785875)
            ·
              refine ⟨74590011178285359647678813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49726674118856906431785875 74590011178285359647678813)
              ·
                refine ⟨27971254191857009867879555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74590011178285359647678813 27971254191857009867879555)
                ·
                  refine ⟨41956881287785514801819333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27971254191857009867879555 41956881287785514801819333)
                  ·
                    refine ⟨7866915241459784025341125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41956881287785514801819333 7866915241459784025341125)
                    ·
                      refine ⟨1475046607773709504751461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7866915241459784025341125 1475046607773709504751461)
                      ·
                        rfl

theorem cell23_2872643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_2872643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872643 prefixEnd_2872643 := by exact prefixLift 2872643
  have htrace : WordTrace (prefixWord ++ tailWord_2872643) baseStart_2872643 baseEnd_2872643 := by
    simpa [prefixWord, tailWord_2872643, baseEnd_2872643] using wordTrace_append hprefix tailTrace_2872643
  have hstable : (prefixWord ++ tailWord_2872643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872643).length < 2 ^ (prefixWord ++ tailWord_2872643).sum := by decide
  have hdescent : baseEnd_2872643 < baseStart_2872643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872757 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2872757 : Nat := 118140960795 + 2872757 * 2 ^ 59
def prefixEnd_2872757 : Nat := 4983230072969 + 3 ^ 40 * 2872757 * 2
def baseEnd_2872757 : Nat := 1475105144568322058725937

theorem tailTrace_2872757 : CollatzResearch.WordTrace tailWord_2872757 prefixEnd_2872757 1475105144568322058725937 := by
  unfold tailWord_2872757
  simp only [CollatzResearch.WordTrace]
  refine ⟨104778055653499491679832525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69852037102332994453221683 104778055653499491679832525)
  ·
    refine ⟨39291770870062309379937197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104778055653499491679832525 39291770870062309379937197)
    ·
      refine ⟨14734414076273366017476449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39291770870062309379937197 14734414076273366017476449)
      ·
        refine ⟨11050810557205024513107337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14734414076273366017476449 11050810557205024513107337)
        ·
          refine ⟨8288107917903768384830503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11050810557205024513107337 8288107917903768384830503)
          ·
            refine ⟨12432161876855652577245755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8288107917903768384830503 12432161876855652577245755)
            ·
              refine ⟨18648242815283478865868633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12432161876855652577245755 18648242815283478865868633)
              ·
                refine ⟨13986182111462609149401475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18648242815283478865868633 13986182111462609149401475)
                ·
                  refine ⟨20979273167193913724102213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13986182111462609149401475 20979273167193913724102213)
                  ·
                    refine ⟨3933613718848858823269165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20979273167193913724102213 3933613718848858823269165)
                    ·
                      refine ⟨1475105144568322058725937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933613718848858823269165 1475105144568322058725937)
                      ·
                        rfl

theorem cell23_2872757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2872757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872757 prefixEnd_2872757 := by exact prefixLift 2872757
  have htrace : WordTrace (prefixWord ++ tailWord_2872757) baseStart_2872757 baseEnd_2872757 := by
    simpa [prefixWord, tailWord_2872757, baseEnd_2872757] using wordTrace_append hprefix tailTrace_2872757
  have hstable : (prefixWord ++ tailWord_2872757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872757).length < 2 ^ (prefixWord ++ tailWord_2872757).sum := by decide
  have hdescent : baseEnd_2872757 < baseStart_2872757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872760 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 6]
def baseStart_2872760 : Nat := 118140960795 + 2872760 * 2 ^ 59
def prefixEnd_2872760 : Nat := 4983230072969 + 3 ^ 40 * 2872760 * 2
def baseEnd_2872760 : Nat := 163900742778920616332047

theorem tailTrace_2872760 : CollatzResearch.WordTrace tailWord_2872760 prefixEnd_2872760 163900742778920616332047 := by
  unfold tailWord_2872760
  simp only [CollatzResearch.WordTrace]
  refine ⟨52389082536244311596095867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69852110048325748794794489 52389082536244311596095867)
  ·
    refine ⟨78583623804366467394143801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52389082536244311596095867 78583623804366467394143801)
    ·
      refine ⟨58937717853274850545607851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78583623804366467394143801 58937717853274850545607851)
      ·
        refine ⟨88406576779912275818411777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58937717853274850545607851 88406576779912275818411777)
        ·
          refine ⟨66304932584934206863808833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88406576779912275818411777 66304932584934206863808833)
          ·
            refine ⟨49728699438700655147856625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66304932584934206863808833 49728699438700655147856625)
            ·
              refine ⟨37296524579025491360892469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49728699438700655147856625 37296524579025491360892469)
              ·
                refine ⟨3496549179283639815083669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37296524579025491360892469 3496549179283639815083669)
                ·
                  refine ⟨163900742778920616332047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3496549179283639815083669 163900742778920616332047)
                  ·
                    rfl

theorem cell23_2872760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 6].length) (baseStart_2872760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872760 prefixEnd_2872760 := by exact prefixLift 2872760
  have htrace : WordTrace (prefixWord ++ tailWord_2872760) baseStart_2872760 baseEnd_2872760 := by
    simpa [prefixWord, tailWord_2872760, baseEnd_2872760] using wordTrace_append hprefix tailTrace_2872760
  have hstable : (prefixWord ++ tailWord_2872760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872760).length < 2 ^ (prefixWord ++ tailWord_2872760).sum := by decide
  have hdescent : baseEnd_2872760 < baseStart_2872760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872814 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_2872814 : Nat := 118140960795 + 2872814 * 2 ^ 59
def prefixEnd_2872814 : Nat := 4983230072969 + 3 ^ 40 * 2872814 * 2
def baseEnd_2872814 : Nat := 1475134412965628335713175

theorem tailTrace_2872814 : CollatzResearch.WordTrace tailWord_2872814 prefixEnd_2872814 1475134412965628335713175 := by
  unfold tailWord_2872814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097516826786623801832187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69853423076195326943104997 13097516826786623801832187)
  ·
    refine ⟨19646275240179935702748281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13097516826786623801832187 19646275240179935702748281)
    ·
      refine ⟨14734706430134951777061211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19646275240179935702748281 14734706430134951777061211)
      ·
        refine ⟨22102059645202427665591817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14734706430134951777061211 22102059645202427665591817)
        ·
          refine ⟨16576544733901820749193863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22102059645202427665591817 16576544733901820749193863)
          ·
            refine ⟨24864817100852731123790795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16576544733901820749193863 24864817100852731123790795)
            ·
              refine ⟨37297225651279096685686193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24864817100852731123790795 37297225651279096685686193)
              ·
                refine ⟨27972919238459322514264645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37297225651279096685686193 27972919238459322514264645)
                ·
                  refine ⟨5244922357211122971424621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27972919238459322514264645 5244922357211122971424621)
                  ·
                    refine ⟨1966845883954171114284233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5244922357211122971424621 1966845883954171114284233)
                    ·
                      refine ⟨1475134412965628335713175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966845883954171114284233 1475134412965628335713175)
                      ·
                        rfl

theorem cell23_2872814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_2872814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872814 prefixEnd_2872814 := by exact prefixLift 2872814
  have htrace : WordTrace (prefixWord ++ tailWord_2872814) baseStart_2872814 baseEnd_2872814 := by
    simpa [prefixWord, tailWord_2872814, baseEnd_2872814] using wordTrace_append hprefix tailTrace_2872814
  have hstable : (prefixWord ++ tailWord_2872814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872814).length < 2 ^ (prefixWord ++ tailWord_2872814).sum := by decide
  have hdescent : baseEnd_2872814 < baseStart_2872814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872824 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 1, 5]
def baseStart_2872824 : Nat := 118140960795 + 2872824 * 2 ^ 59
def prefixEnd_2872824 : Nat := 4983230072969 + 3 ^ 40 * 2872824 * 2
def baseEnd_2872824 : Nat := 491713182590724432196043

theorem tailTrace_2872824 : CollatzResearch.WordTrace tailWord_2872824 prefixEnd_2872824 491713182590724432196043 := by
  unfold tailWord_2872824
  simp only [CollatzResearch.WordTrace]
  refine ⟨52390249672128381061260763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69853666229504508081681017 52390249672128381061260763)
  ·
    refine ⟨78585374508192571591891145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52390249672128381061260763 78585374508192571591891145)
    ·
      refine ⟨58939030881144428693918359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78585374508192571591891145 58939030881144428693918359)
      ·
        refine ⟨88408546321716643040877539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58939030881144428693918359 88408546321716643040877539)
        ·
          refine ⟨132612819482574964561316309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88408546321716643040877539 132612819482574964561316309)
          ·
            refine ⟨3108112956622850731905851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 132612819482574964561316309 3108112956622850731905851)
            ·
              refine ⟨4662169434934276097858777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108112956622850731905851 4662169434934276097858777)
              ·
                refine ⟨3496627076200707073394083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662169434934276097858777 3496627076200707073394083)
                ·
                  refine ⟨5244940614301060610091125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496627076200707073394083 5244940614301060610091125)
                  ·
                    refine ⟨491713182590724432196043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5244940614301060610091125 491713182590724432196043)
                    ·
                      rfl

theorem cell23_2872824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_2872824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872824 prefixEnd_2872824 := by exact prefixLift 2872824
  have htrace : WordTrace (prefixWord ++ tailWord_2872824) baseStart_2872824 baseEnd_2872824 := by
    simpa [prefixWord, tailWord_2872824, baseEnd_2872824] using wordTrace_append hprefix tailTrace_2872824
  have hstable : (prefixWord ++ tailWord_2872824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872824).length < 2 ^ (prefixWord ++ tailWord_2872824).sum := by decide
  have hdescent : baseEnd_2872824 < baseStart_2872824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872861 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_2872861 : Nat := 118140960795 + 2872861 * 2 ^ 59
def prefixEnd_2872861 : Nat := 4983230072969 + 3 ^ 40 * 2872861 * 2
def baseEnd_2872861 : Nat := 1475158546556389651825459

theorem tailTrace_2872861 : CollatzResearch.WordTrace tailWord_2872861 prefixEnd_2872861 1475158546556389651825459 := by
  unfold tailWord_2872861
  simp only [CollatzResearch.WordTrace]
  refine ⟨104781848845122717441618437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69854565896748478294412291 104781848845122717441618437)
  ·
    refine ⟨19646596658460509520303457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104781848845122717441618437 19646596658460509520303457)
    ·
      refine ⟨14734947493845382140227593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19646596658460509520303457 14734947493845382140227593)
      ·
        refine ⟨11051210620384036605170695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14734947493845382140227593 11051210620384036605170695)
        ·
          refine ⟨16576815930576054907756043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051210620384036605170695 16576815930576054907756043)
          ·
            refine ⟨24865223895864082361634065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16576815930576054907756043 24865223895864082361634065)
            ·
              refine ⟨18648917921898061771225549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24865223895864082361634065 18648917921898061771225549)
              ·
                refine ⟨6993344220711773164209581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18648917921898061771225549 6993344220711773164209581)
                ·
                  refine ⟨2622504082766914936578593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6993344220711773164209581 2622504082766914936578593)
                  ·
                    refine ⟨1966878062075186202433945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2622504082766914936578593 1966878062075186202433945)
                    ·
                      refine ⟨1475158546556389651825459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966878062075186202433945 1475158546556389651825459)
                      ·
                        rfl

theorem cell23_2872861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_2872861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872861 prefixEnd_2872861 := by exact prefixLift 2872861
  have htrace : WordTrace (prefixWord ++ tailWord_2872861) baseStart_2872861 baseEnd_2872861 := by
    simpa [prefixWord, tailWord_2872861, baseEnd_2872861] using wordTrace_append hprefix tailTrace_2872861
  have hstable : (prefixWord ++ tailWord_2872861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872861).length < 2 ^ (prefixWord ++ tailWord_2872861).sum := by decide
  have hdescent : baseEnd_2872861 < baseStart_2872861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872864 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2872864 : Nat := 118140960795 + 2872864 * 2 ^ 59
def prefixEnd_2872864 : Nat := 4983230072969 + 3 ^ 40 * 2872864 * 2
def baseEnd_2872864 : Nat := 1475160086998353140087945

theorem tailTrace_2872864 : CollatzResearch.WordTrace tailWord_2872864 prefixEnd_2872864 1475160086998353140087945 := by
  unfold tailWord_2872864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52390979132055924476988823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69854638842741232635985097 52390979132055924476988823)
  ·
    refine ⟨78586468698083886715483235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52390979132055924476988823 78586468698083886715483235)
    ·
      refine ⟨117879703047125830073224853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78586468698083886715483235 117879703047125830073224853)
      ·
        refine ⟨5525611080334023284682415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117879703047125830073224853 5525611080334023284682415)
        ·
          refine ⟨8288416620501034927023623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525611080334023284682415 8288416620501034927023623)
          ·
            refine ⟨12432624930751552390535435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8288416620501034927023623 12432624930751552390535435)
            ·
              refine ⟨18648937396127328585803153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12432624930751552390535435 18648937396127328585803153)
              ·
                refine ⟨13986703047095496439352365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18648937396127328585803153 13986703047095496439352365)
                ·
                  refine ⟨5245013642660811164757137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13986703047095496439352365 5245013642660811164757137)
                  ·
                    refine ⟨3933760231995608373567853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5245013642660811164757137 3933760231995608373567853)
                    ·
                      refine ⟨1475160086998353140087945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933760231995608373567853 1475160086998353140087945)
                      ·
                        rfl

theorem cell23_2872864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2872864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872864 prefixEnd_2872864 := by exact prefixLift 2872864
  have htrace : WordTrace (prefixWord ++ tailWord_2872864) baseStart_2872864 baseEnd_2872864 := by
    simpa [prefixWord, tailWord_2872864, baseEnd_2872864] using wordTrace_append hprefix tailTrace_2872864
  have hstable : (prefixWord ++ tailWord_2872864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872864).length < 2 ^ (prefixWord ++ tailWord_2872864).sum := by decide
  have hdescent : baseEnd_2872864 < baseStart_2872864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872874 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2872874 : Nat := 118140960795 + 2872874 * 2 ^ 59
def prefixEnd_2872874 : Nat := 4983230072969 + 3 ^ 40 * 2872874 * 2
def baseEnd_2872874 : Nat := 1475165221804898100962899

theorem tailTrace_2872874 : CollatzResearch.WordTrace tailWord_2872874 prefixEnd_2872874 1475165221804898100962899 := by
  unfold tailWord_2872874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26195580748518905165460419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69854881996050413774561117 26195580748518905165460419)
  ·
    refine ⟨39293371122778357748190629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26195580748518905165460419 39293371122778357748190629)
    ·
      refine ⟨7367507085520942077785743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39293371122778357748190629 7367507085520942077785743)
      ·
        refine ⟨11051260628281413116678615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367507085520942077785743 11051260628281413116678615)
        ·
          refine ⟨16576890942422119675017923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051260628281413116678615 16576890942422119675017923)
          ·
            refine ⟨24865336413633179512526885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16576890942422119675017923 24865336413633179512526885)
            ·
              refine ⟨4662250577556221158598791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24865336413633179512526885 4662250577556221158598791)
              ·
                refine ⟨6993375866334331737898187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662250577556221158598791 6993375866334331737898187)
                ·
                  refine ⟨10490063799501497606847281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6993375866334331737898187 10490063799501497606847281)
                  ·
                    refine ⟨7867547849626123205135461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10490063799501497606847281 7867547849626123205135461)
                    ·
                      refine ⟨1475165221804898100962899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7867547849626123205135461 1475165221804898100962899)
                      ·
                        rfl

theorem cell23_2872874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2872874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872874 prefixEnd_2872874 := by exact prefixLift 2872874
  have htrace : WordTrace (prefixWord ++ tailWord_2872874) baseStart_2872874 baseEnd_2872874 := by
    simpa [prefixWord, tailWord_2872874, baseEnd_2872874] using wordTrace_append hprefix tailTrace_2872874
  have hstable : (prefixWord ++ tailWord_2872874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872874).length < 2 ^ (prefixWord ++ tailWord_2872874).sum := by decide
  have hdescent : baseEnd_2872874 < baseStart_2872874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872878 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_2872878 : Nat := 118140960795 + 2872878 * 2 ^ 59
def prefixEnd_2872878 : Nat := 4983230072969 + 3 ^ 40 * 2872878 * 2
def baseEnd_2872878 : Nat := 1475167275727516085312881

theorem tailTrace_2872878 : CollatzResearch.WordTrace tailWord_2872878 prefixEnd_2872878 1475167275727516085312881 := by
  unfold tailWord_2872878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097808610757641168123411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69854979257374086229991525 13097808610757641168123411)
  ·
    refine ⟨19646712916136461752185117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13097808610757641168123411 19646712916136461752185117)
    ·
      refine ⟨7367517343551173157069419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19646712916136461752185117 7367517343551173157069419)
      ·
        refine ⟨11051276015326759735604129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367517343551173157069419 11051276015326759735604129)
        ·
          refine ⟨8288457011495069801703097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11051276015326759735604129 8288457011495069801703097)
          ·
            refine ⟨6216342758621302351277323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8288457011495069801703097 6216342758621302351277323)
            ·
              refine ⟨9324514137931953526915985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216342758621302351277323 9324514137931953526915985)
              ·
                refine ⟨6993385603448965145186989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9324514137931953526915985 6993385603448965145186989)
                ·
                  refine ⟨2622519601293361929445121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6993385603448965145186989 2622519601293361929445121)
                  ·
                    refine ⟨1966889700970021447083841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2622519601293361929445121 1966889700970021447083841)
                    ·
                      refine ⟨1475167275727516085312881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966889700970021447083841 1475167275727516085312881)
                      ·
                        rfl

theorem cell23_2872878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_2872878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872878 prefixEnd_2872878 := by exact prefixLift 2872878
  have htrace : WordTrace (prefixWord ++ tailWord_2872878) baseStart_2872878 baseEnd_2872878 := by
    simpa [prefixWord, tailWord_2872878, baseEnd_2872878] using wordTrace_append hprefix tailTrace_2872878
  have hstable : (prefixWord ++ tailWord_2872878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872878).length < 2 ^ (prefixWord ++ tailWord_2872878).sum := by decide
  have hdescent : baseEnd_2872878 < baseStart_2872878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872880 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_2872880 : Nat := 118140960795 + 2872880 * 2 ^ 59
def prefixEnd_2872880 : Nat := 4983230072969 + 3 ^ 40 * 2872880 * 2
def baseEnd_2872880 : Nat := 491722767562941692495957

theorem tailTrace_2872880 : CollatzResearch.WordTrace tailWord_2872880 prefixEnd_2872880 491722767562941692495957 := by
  unfold tailWord_2872880
  simp only [CollatzResearch.WordTrace]
  refine ⟨52391270916026941843280047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69855027888035922457706729 52391270916026941843280047)
  ·
    refine ⟨78586906374040412764920071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52391270916026941843280047 78586906374040412764920071)
    ·
      refine ⟨117880359561060619147380107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78586906374040412764920071 117880359561060619147380107)
      ·
        refine ⟨176820539341590928721070161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117880359561060619147380107 176820539341590928721070161)
        ·
          refine ⟨132615404506193196540802621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176820539341590928721070161 132615404506193196540802621)
          ·
            refine ⟨49730776689822448702800983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132615404506193196540802621 49730776689822448702800983)
            ·
              refine ⟨74596165034733673054201475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49730776689822448702800983 74596165034733673054201475)
              ·
                refine ⟨111894247552100509581302213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74596165034733673054201475 111894247552100509581302213)
                ·
                  refine ⟨20980171416018845546494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111894247552100509581302213 20980171416018845546494165)
                  ·
                    refine ⟨491722767562941692495957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20980171416018845546494165 491722767562941692495957)
                    ·
                      rfl

theorem cell23_2872880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_2872880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872880 prefixEnd_2872880 := by exact prefixLift 2872880
  have htrace : WordTrace (prefixWord ++ tailWord_2872880) baseStart_2872880 baseEnd_2872880 := by
    simpa [prefixWord, tailWord_2872880, baseEnd_2872880] using wordTrace_append hprefix tailTrace_2872880
  have hstable : (prefixWord ++ tailWord_2872880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872880).length < 2 ^ (prefixWord ++ tailWord_2872880).sum := by decide
  have hdescent : baseEnd_2872880 < baseStart_2872880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872925 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2872925 : Nat := 118140960795 + 2872925 * 2 ^ 59
def prefixEnd_2872925 : Nat := 4983230072969 + 3 ^ 40 * 2872925 * 2
def baseEnd_2872925 : Nat := 1475191409318277401425165

theorem tailTrace_2872925 : CollatzResearch.WordTrace tailWord_2872925 prefixEnd_2872925 1475191409318277401425165 := by
  unfold tailWord_2872925
  simp only [CollatzResearch.WordTrace]
  refine ⟨104784183116890856371948229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69856122077927237581298819 104784183116890856371948229)
  ·
    refine ⟨19647034334417035569740293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104784183116890856371948229 19647034334417035569740293)
    ·
      refine ⟨3683818937703194169326305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19647034334417035569740293 3683818937703194169326305)
      ·
        refine ⟨2762864203277395626994729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3683818937703194169326305 2762864203277395626994729)
        ·
          refine ⟨2072148152458046720246047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2762864203277395626994729 2072148152458046720246047)
          ·
            refine ⟨3108222228687070080369071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072148152458046720246047 3108222228687070080369071)
            ·
              refine ⟨4662333343030605120553607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108222228687070080369071 4662333343030605120553607)
              ·
                refine ⟨6993500014545907680830411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662333343030605120553607 6993500014545907680830411)
                ·
                  refine ⟨10490250021818861521245617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6993500014545907680830411 10490250021818861521245617)
                  ·
                    refine ⟨7867687516364146140934213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10490250021818861521245617 7867687516364146140934213)
                    ·
                      refine ⟨1475191409318277401425165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7867687516364146140934213 1475191409318277401425165)
                      ·
                        rfl

theorem cell23_2872925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2872925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872925 prefixEnd_2872925 := by exact prefixLift 2872925
  have htrace : WordTrace (prefixWord ++ tailWord_2872925) baseStart_2872925 baseEnd_2872925 := by
    simpa [prefixWord, tailWord_2872925, baseEnd_2872925] using wordTrace_append hprefix tailTrace_2872925
  have hstable : (prefixWord ++ tailWord_2872925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872925).length < 2 ^ (prefixWord ++ tailWord_2872925).sum := by decide
  have hdescent : baseEnd_2872925 < baseStart_2872925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872937 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_2872937 : Nat := 118140960795 + 2872937 * 2 ^ 59
def prefixEnd_2872937 : Nat := 4983230072969 + 3 ^ 40 * 2872937 * 2
def baseEnd_2872937 : Nat := 1475197571086131354475109

theorem tailTrace_2872937 : CollatzResearch.WordTrace tailWord_2872937 prefixEnd_2872937 1475197571086131354475109 := by
  unfold tailWord_2872937
  simp only [CollatzResearch.WordTrace]
  refine ⟨104784620792847382421385065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69856413861898254947590043 104784620792847382421385065)
  ·
    refine ⟨78588465594635536816038799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104784620792847382421385065 78588465594635536816038799)
    ·
      refine ⟨117882698391953305224058199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78588465594635536816038799 117882698391953305224058199)
      ·
        refine ⟨176824047587929957836087299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117882698391953305224058199 176824047587929957836087299)
        ·
          refine ⟨265236071381894936754130949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176824047587929957836087299 265236071381894936754130949)
          ·
            refine ⟨49731763384105300641399553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265236071381894936754130949 49731763384105300641399553)
            ·
              refine ⟨37298822538078975481049665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49731763384105300641399553 37298822538078975481049665)
              ·
                refine ⟨27974116903559231610787249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37298822538078975481049665 27974116903559231610787249)
                ·
                  refine ⟨20980587677669423708090437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27974116903559231610787249 20980587677669423708090437)
                  ·
                    refine ⟨3933860189563016945266957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20980587677669423708090437 3933860189563016945266957)
                    ·
                      refine ⟨1475197571086131354475109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3933860189563016945266957 1475197571086131354475109)
                      ·
                        rfl

theorem cell23_2872937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_2872937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872937 prefixEnd_2872937 := by exact prefixLift 2872937
  have htrace : WordTrace (prefixWord ++ tailWord_2872937) baseStart_2872937 baseEnd_2872937 := by
    simpa [prefixWord, tailWord_2872937, baseEnd_2872937] using wordTrace_append hprefix tailTrace_2872937
  have hstable : (prefixWord ++ tailWord_2872937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872937).length < 2 ^ (prefixWord ++ tailWord_2872937).sum := by decide
  have hdescent : baseEnd_2872937 < baseStart_2872937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872938 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_2872938 : Nat := 118140960795 + 2872938 * 2 ^ 59
def prefixEnd_2872938 : Nat := 4983230072969 + 3 ^ 40 * 2872938 * 2
def baseEnd_2872938 : Nat := 1475198084566785850562605

theorem tailTrace_2872938 : CollatzResearch.WordTrace tailWord_2872938 prefixEnd_2872938 1475198084566785850562605 := by
  unfold tailWord_2872938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26196164316460939898042867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69856438177229173061447645 26196164316460939898042867)
  ·
    refine ⟨39294246474691409847064301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26196164316460939898042867 39294246474691409847064301)
    ·
      refine ⟨14735342428009278692649113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39294246474691409847064301 14735342428009278692649113)
      ·
        refine ⟨11051506821006959019486835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14735342428009278692649113 11051506821006959019486835)
        ·
          refine ⟨16577260231510438529230253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051506821006959019486835 16577260231510438529230253)
          ·
            refine ⟨6216472586816414448461345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16577260231510438529230253 6216472586816414448461345)
            ·
              refine ⟨4662354440112310836346009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6216472586816414448461345 4662354440112310836346009)
              ·
                refine ⟨3496765830084233127259507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662354440112310836346009 3496765830084233127259507)
                ·
                  refine ⟨5245148745126349690889261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496765830084233127259507 5245148745126349690889261)
                  ·
                    refine ⟨1966930779422381134083473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5245148745126349690889261 1966930779422381134083473)
                    ·
                      refine ⟨1475198084566785850562605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1966930779422381134083473 1475198084566785850562605)
                      ·
                        rfl

theorem cell23_2872938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_2872938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872938 prefixEnd_2872938 := by exact prefixLift 2872938
  have htrace : WordTrace (prefixWord ++ tailWord_2872938) baseStart_2872938 baseEnd_2872938 := by
    simpa [prefixWord, tailWord_2872938, baseEnd_2872938] using wordTrace_append hprefix tailTrace_2872938
  have hstable : (prefixWord ++ tailWord_2872938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872938).length < 2 ^ (prefixWord ++ tailWord_2872938).sum := by decide
  have hdescent : baseEnd_2872938 < baseStart_2872938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872974 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_2872974 : Nat := 118140960795 + 2872974 * 2 ^ 59
def prefixEnd_2872974 : Nat := 4983230072969 + 3 ^ 40 * 2872974 * 2
def baseEnd_2872974 : Nat := 163912952207816412190271

theorem tailTrace_2872974 : CollatzResearch.WordTrace tailWord_2872974 prefixEnd_2872974 163912952207816412190271 := by
  unfold tailWord_2872974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13098246286714167217560247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69857313529142225160321317 13098246286714167217560247)
  ·
    refine ⟨19647369430071250826340371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13098246286714167217560247 19647369430071250826340371)
    ·
      refine ⟨29471054145106876239510557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19647369430071250826340371 29471054145106876239510557)
      ·
        refine ⟨11051645304415078589816459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29471054145106876239510557 11051645304415078589816459)
        ·
          refine ⟨16577467956622617884724689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051645304415078589816459 16577467956622617884724689)
          ·
            refine ⟨12433100967466963413543517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16577467956622617884724689 12433100967466963413543517)
            ·
              refine ⟨4662412862800111280078819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12433100967466963413543517 4662412862800111280078819)
              ·
                refine ⟨6993619294200166920118229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662412862800111280078819 6993619294200166920118229)
                ·
                  refine ⟨163912952207816412190271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6993619294200166920118229 163912952207816412190271)
                  ·
                    rfl

theorem cell23_2872974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_2872974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2872974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2872974 prefixEnd_2872974 := by exact prefixLift 2872974
  have htrace : WordTrace (prefixWord ++ tailWord_2872974) baseStart_2872974 baseEnd_2872974 := by
    simpa [prefixWord, tailWord_2872974, baseEnd_2872974] using wordTrace_append hprefix tailTrace_2872974
  have hstable : (prefixWord ++ tailWord_2872974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872974).length < 2 ^ (prefixWord ++ tailWord_2872974).sum := by decide
  have hdescent : baseEnd_2872974 < baseStart_2872974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873024 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_2873024 : Nat := 118140960795 + 2873024 * 2 ^ 59
def prefixEnd_2873024 : Nat := 4983230072969 + 3 ^ 40 * 2873024 * 2
def baseEnd_2873024 : Nat := 1475242243903072514087209

theorem tailTrace_2873024 : CollatzResearch.WordTrace tailWord_2873024 prefixEnd_2873024 1475242243903072514087209 := by
  unfold tailWord_2873024
  simp only [CollatzResearch.WordTrace]
  refine ⟨52393896971766098139901063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69858529295688130853201417 52393896971766098139901063)
  ·
    refine ⟨78590845457649147209851595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52393896971766098139901063 78590845457649147209851595)
    ·
      refine ⟨117886268186473720814777393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78590845457649147209851595 117886268186473720814777393)
      ·
        refine ⟨88414701139855290611083045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117886268186473720814777393 88414701139855290611083045)
        ·
          refine ⟨16577756463722866989578071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88414701139855290611083045 16577756463722866989578071)
          ·
            refine ⟨24866634695584300484367107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16577756463722866989578071 24866634695584300484367107)
            ·
              refine ⟨37299952043376450726550661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24866634695584300484367107 37299952043376450726550661)
              ·
                refine ⟨6993741008133084511228249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37299952043376450726550661 6993741008133084511228249)
                ·
                  refine ⟨5245305756099813383421187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6993741008133084511228249 5245305756099813383421187)
                  ·
                    refine ⟨7867958634149720075131781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245305756099813383421187 7867958634149720075131781)
                    ·
                      refine ⟨1475242243903072514087209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7867958634149720075131781 1475242243903072514087209)
                      ·
                        rfl

theorem cell23_2873024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_2873024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873024 prefixEnd_2873024 := by exact prefixLift 2873024
  have htrace : WordTrace (prefixWord ++ tailWord_2873024) baseStart_2873024 baseEnd_2873024 := by
    simpa [prefixWord, tailWord_2873024, baseEnd_2873024] using wordTrace_append hprefix tailTrace_2873024
  have hstable : (prefixWord ++ tailWord_2873024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873024).length < 2 ^ (prefixWord ++ tailWord_2873024).sum := by decide
  have hdescent : baseEnd_2873024 < baseStart_2873024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873041 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 2, 4, 2]
def baseStart_2873041 : Nat := 118140960795 + 2873041 * 2 ^ 59
def prefixEnd_2873041 : Nat := 4983230072969 + 3 ^ 40 * 2873041 * 2
def baseEnd_2873041 : Nat := 1475250973074198947574631

theorem tailTrace_2873041 : CollatzResearch.WordTrace tailWord_2873041 prefixEnd_2873041 1475250973074198947574631 := by
  unfold tailWord_2873041
  simp only [CollatzResearch.WordTrace]
  refine ⟨104788413984470608183170977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69858942656313738788780651 104788413984470608183170977)
  ·
    refine ⟨78591310488352956137378233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104788413984470608183170977 78591310488352956137378233)
    ·
      refine ⟨58943482866264717103033675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78591310488352956137378233 58943482866264717103033675)
      ·
        refine ⟨88415224299397075654550513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58943482866264717103033675 88415224299397075654550513)
        ·
          refine ⟨66311418224547806740912885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88415224299397075654550513 66311418224547806740912885)
          ·
            refine ⟨6216695458551356881960583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66311418224547806740912885 6216695458551356881960583)
            ·
              refine ⟨9325043187827035322940875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216695458551356881960583 9325043187827035322940875)
              ·
                refine ⟨13987564781740552984411313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9325043187827035322940875 13987564781740552984411313)
                ·
                  refine ⟨10490673586305414738308485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13987564781740552984411313 10490673586305414738308485)
                  ·
                    refine ⟨1967001297432265263432841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10490673586305414738308485 1967001297432265263432841)
                    ·
                      refine ⟨1475250973074198947574631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967001297432265263432841 1475250973074198947574631)
                      ·
                        rfl

theorem cell23_2873041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_2873041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873041 prefixEnd_2873041 := by exact prefixLift 2873041
  have htrace : WordTrace (prefixWord ++ tailWord_2873041) baseStart_2873041 baseEnd_2873041 := by
    simpa [prefixWord, tailWord_2873041, baseEnd_2873041] using wordTrace_append hprefix tailTrace_2873041
  have hstable : (prefixWord ++ tailWord_2873041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873041).length < 2 ^ (prefixWord ++ tailWord_2873041).sum := by decide
  have hdescent : baseEnd_2873041 < baseStart_2873041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873091 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 3]
def baseStart_2873091 : Nat := 118140960795 + 2873091 * 2 ^ 59
def prefixEnd_2873091 : Nat := 4983230072969 + 3 ^ 40 * 2873091 * 2
def baseEnd_2873091 : Nat := 1475276647106923751949401

theorem tailTrace_2873091 : CollatzResearch.WordTrace tailWord_2873091 prefixEnd_2873091 1475276647106923751949401 := by
  unfold tailWord_2873091
  simp only [CollatzResearch.WordTrace]
  refine ⟨104790237634289466722491127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69860158422859644481660751 104790237634289466722491127)
  ·
    refine ⟨157185356451434200083736691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104790237634289466722491127 157185356451434200083736691)
    ·
      refine ⟨235778034677151300125605037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157185356451434200083736691 235778034677151300125605037)
      ·
        refine ⟨88416763003931737547101889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235778034677151300125605037 88416763003931737547101889)
        ·
          refine ⟨66312572252948803160326417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88416763003931737547101889 66312572252948803160326417)
          ·
            refine ⟨49734429189711602370244813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66312572252948803160326417 49734429189711602370244813)
            ·
              refine ⟨18650410946141850888841805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49734429189711602370244813 18650410946141850888841805)
              ·
                refine ⟨6993904104803194083315677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18650410946141850888841805 6993904104803194083315677)
                ·
                  refine ⟨2622714039301197781243379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6993904104803194083315677 2622714039301197781243379)
                  ·
                    refine ⟨3934071058951796671865069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2622714039301197781243379 3934071058951796671865069)
                    ·
                      refine ⟨1475276647106923751949401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934071058951796671865069 1475276647106923751949401)
                      ·
                        rfl

theorem cell23_2873091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_2873091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873091 prefixEnd_2873091 := by exact prefixLift 2873091
  have htrace : WordTrace (prefixWord ++ tailWord_2873091) baseStart_2873091 baseEnd_2873091 := by
    simpa [prefixWord, tailWord_2873091, baseEnd_2873091] using wordTrace_append hprefix tailTrace_2873091
  have hstable : (prefixWord ++ tailWord_2873091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873091).length < 2 ^ (prefixWord ++ tailWord_2873091).sum := by decide
  have hdescent : baseEnd_2873091 < baseStart_2873091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873111 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 1, 5]
def baseStart_2873111 : Nat := 118140960795 + 2873111 * 2 ^ 59
def prefixEnd_2873111 : Nat := 4983230072969 + 3 ^ 40 * 2873111 * 2
def baseEnd_2873111 : Nat := 491762305573337891233103

theorem tailTrace_2873111 : CollatzResearch.WordTrace tailWord_2873111 prefixEnd_2873111 491762305573337891233103 := by
  unfold tailWord_2873111
  simp only [CollatzResearch.WordTrace]
  refine ⟨104790967094217010138219187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69860644729478006758812791 104790967094217010138219187)
  ·
    refine ⟨157186450641325515207328781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104790967094217010138219187 157186450641325515207328781)
    ·
      refine ⟨58944918990497068202748293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157186450641325515207328781 58944918990497068202748293)
      ·
        refine ⟨11052172310718200288015305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58944918990497068202748293 11052172310718200288015305)
        ·
          refine ⟨8289129233038650216011479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11052172310718200288015305 8289129233038650216011479)
          ·
            refine ⟨12433693849557975324017219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289129233038650216011479 12433693849557975324017219)
            ·
              refine ⟨18650540774336962986025829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12433693849557975324017219 18650540774336962986025829)
              ·
                refine ⟨3496976395188180559879843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18650540774336962986025829 3496976395188180559879843)
                ·
                  refine ⟨5245464592782270839819765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496976395188180559879843 5245464592782270839819765)
                  ·
                    refine ⟨491762305573337891233103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5245464592782270839819765 491762305573337891233103)
                    ·
                      rfl

theorem cell23_2873111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_2873111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873111 prefixEnd_2873111 := by exact prefixLift 2873111
  have htrace : WordTrace (prefixWord ++ tailWord_2873111) baseStart_2873111 baseEnd_2873111 := by
    simpa [prefixWord, tailWord_2873111, baseEnd_2873111] using wordTrace_append hprefix tailTrace_2873111
  have hstable : (prefixWord ++ tailWord_2873111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873111).length < 2 ^ (prefixWord ++ tailWord_2873111).sum := by decide
  have hdescent : baseEnd_2873111 < baseStart_2873111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873125 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 1, 1, 3]
def baseStart_2873125 : Nat := 118140960795 + 2873125 * 2 ^ 59
def prefixEnd_2873125 : Nat := 4983230072969 + 3 ^ 40 * 2873125 * 2
def baseEnd_2873125 : Nat := 1475294105449176618924245

theorem tailTrace_2873125 : CollatzResearch.WordTrace tailWord_2873125 prefixEnd_2873125 1475294105449176618924245 := by
  unfold tailWord_2873125
  simp only [CollatzResearch.WordTrace]
  refine ⟨104791477716166290529228829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69860985144110860352819219 104791477716166290529228829)
  ·
    refine ⟨39296804143562358948460811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104791477716166290529228829 39296804143562358948460811)
    ·
      refine ⟨58945206215343538422691217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39296804143562358948460811 58945206215343538422691217)
      ·
        refine ⟨44208904661507653817018413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58945206215343538422691217 44208904661507653817018413)
        ·
          refine ⟨16578339248065370181381905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44208904661507653817018413 16578339248065370181381905)
          ·
            refine ⟨12433754436049027636036429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16578339248065370181381905 12433754436049027636036429)
            ·
              refine ⟨4662657913518385363513661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12433754436049027636036429 4662657913518385363513661)
              ·
                refine ⟨1748496717569394511317623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4662657913518385363513661 1748496717569394511317623)
                ·
                  refine ⟨2622745076354091766976435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748496717569394511317623 2622745076354091766976435)
                  ·
                    refine ⟨3934117614531137650464653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2622745076354091766976435 3934117614531137650464653)
                    ·
                      refine ⟨1475294105449176618924245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934117614531137650464653 1475294105449176618924245)
                      ·
                        rfl

theorem cell23_2873125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_2873125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873125 prefixEnd_2873125 := by exact prefixLift 2873125
  have htrace : WordTrace (prefixWord ++ tailWord_2873125) baseStart_2873125 baseEnd_2873125 := by
    simpa [prefixWord, tailWord_2873125, baseEnd_2873125] using wordTrace_append hprefix tailTrace_2873125
  have hstable : (prefixWord ++ tailWord_2873125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873125).length < 2 ^ (prefixWord ++ tailWord_2873125).sum := by decide
  have hdescent : baseEnd_2873125 < baseStart_2873125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873142 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2873142 : Nat := 118140960795 + 2873142 * 2 ^ 59
def prefixEnd_2873142 : Nat := 4983230072969 + 3 ^ 40 * 2873142 * 2
def baseEnd_2873142 : Nat := 1475302834620303052411667

theorem tailTrace_2873142 : CollatzResearch.WordTrace tailWord_2873142 prefixEnd_2873142 1475302834620303052411667 := by
  unfold tailWord_2873142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549506109819043902037355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69861398504736468288398453 6549506109819043902037355)
  ·
    refine ⟨9824259164728565853056033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6549506109819043902037355 9824259164728565853056033)
    ·
      refine ⟨7368194373546424389792025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9824259164728565853056033 7368194373546424389792025)
      ·
        refine ⟨5526145780159818292344019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7368194373546424389792025 5526145780159818292344019)
        ·
          refine ⟨8289218670239727438516029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526145780159818292344019 8289218670239727438516029)
          ·
            refine ⟨3108457001339897789443511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8289218670239727438516029 3108457001339897789443511)
            ·
              refine ⟨4662685502009846684165267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108457001339897789443511 4662685502009846684165267)
              ·
                refine ⟨6994028253014770026247901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662685502009846684165267 6994028253014770026247901)
                ·
                  refine ⟨2622760594880538759842963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6994028253014770026247901 2622760594880538759842963)
                  ·
                    refine ⟨3934140892320808139764445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2622760594880538759842963 3934140892320808139764445)
                    ·
                      refine ⟨1475302834620303052411667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934140892320808139764445 1475302834620303052411667)
                      ·
                        rfl

theorem cell23_2873142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2873142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873142 prefixEnd_2873142 := by exact prefixLift 2873142
  have htrace : WordTrace (prefixWord ++ tailWord_2873142) baseStart_2873142 baseEnd_2873142 := by
    simpa [prefixWord, tailWord_2873142, baseEnd_2873142] using wordTrace_append hprefix tailTrace_2873142
  have hstable : (prefixWord ++ tailWord_2873142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873142).length < 2 ^ (prefixWord ++ tailWord_2873142).sum := by decide
  have hdescent : baseEnd_2873142 < baseStart_2873142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873144 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_2873144 : Nat := 118140960795 + 2873144 * 2 ^ 59
def prefixEnd_2873144 : Nat := 4983230072969 + 3 ^ 40 * 2873144 * 2
def baseEnd_2873144 : Nat := 1475303861581612044586657

theorem tailTrace_2873144 : CollatzResearch.WordTrace tailWord_2873144 prefixEnd_2873144 1475303861581612044586657 := by
  unfold tailWord_2873144
  simp only [CollatzResearch.WordTrace]
  refine ⟨52396085351548728387085243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69861447135398304516113657 52396085351548728387085243)
  ·
    refine ⟨78594128027323092580627865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52396085351548728387085243 78594128027323092580627865)
    ·
      refine ⟨58945596020492319435470899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78594128027323092580627865 58945596020492319435470899)
      ·
        refine ⟨88418394030738479153206349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58945596020492319435470899 88418394030738479153206349)
        ·
          refine ⟨33156897761526929682452381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88418394030738479153206349 33156897761526929682452381)
          ·
            refine ⟨12433836660572598630919643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33156897761526929682452381 12433836660572598630919643)
            ·
              refine ⟨18650754990858897946379465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12433836660572598630919643 18650754990858897946379465)
              ·
                refine ⟨13988066243144173459784599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18650754990858897946379465 13988066243144173459784599)
                ·
                  refine ⟨20982099364716260189676899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13988066243144173459784599 20982099364716260189676899)
                  ·
                    refine ⟨31473149047074390284515349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20982099364716260189676899 31473149047074390284515349)
                    ·
                      refine ⟨1475303861581612044586657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31473149047074390284515349 1475303861581612044586657)
                      ·
                        rfl

theorem cell23_2873144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_2873144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873144 prefixEnd_2873144 := by exact prefixLift 2873144
  have htrace : WordTrace (prefixWord ++ tailWord_2873144) baseStart_2873144 baseEnd_2873144 := by
    simpa [prefixWord, tailWord_2873144, baseEnd_2873144] using wordTrace_append hprefix tailTrace_2873144
  have hstable : (prefixWord ++ tailWord_2873144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873144).length < 2 ^ (prefixWord ++ tailWord_2873144).sum := by decide
  have hdescent : baseEnd_2873144 < baseStart_2873144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873165 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2873165 : Nat := 118140960795 + 2873165 * 2 ^ 59
def prefixEnd_2873165 : Nat := 4983230072969 + 3 ^ 40 * 2873165 * 2
def baseEnd_2873165 : Nat := 1475314644675356462424061

theorem tailTrace_2873165 : CollatzResearch.WordTrace tailWord_2873165 prefixEnd_2873165 1475314644675356462424061 := by
  unfold tailWord_2873165
  simp only [CollatzResearch.WordTrace]
  refine ⟨104792936636021377360684949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69861957757347584907123299 104792936636021377360684949)
  ·
    refine ⟨4912168904813502063782107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104792936636021377360684949 4912168904813502063782107)
    ·
      refine ⟨7368253357220253095673161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4912168904813502063782107 7368253357220253095673161)
      ·
        refine ⟨5526190017915189821754871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7368253357220253095673161 5526190017915189821754871)
        ·
          refine ⟨8289285026872784732632307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526190017915189821754871 8289285026872784732632307)
          ·
            refine ⟨12433927540309177098948461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289285026872784732632307 12433927540309177098948461)
            ·
              refine ⟨4662722827615941412105673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12433927540309177098948461 4662722827615941412105673)
              ·
                refine ⟨3497042120711956059079255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662722827615941412105673 3497042120711956059079255)
                ·
                  refine ⟨5245563181067934088618883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497042120711956059079255 5245563181067934088618883)
                  ·
                    refine ⟨7868344771601901132928325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245563181067934088618883 7868344771601901132928325)
                    ·
                      refine ⟨1475314644675356462424061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7868344771601901132928325 1475314644675356462424061)
                      ·
                        rfl

theorem cell23_2873165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2873165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873165 prefixEnd_2873165 := by exact prefixLift 2873165
  have htrace : WordTrace (prefixWord ++ tailWord_2873165) baseStart_2873165 baseEnd_2873165 := by
    simpa [prefixWord, tailWord_2873165, baseEnd_2873165] using wordTrace_append hprefix tailTrace_2873165
  have hstable : (prefixWord ++ tailWord_2873165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873165).length < 2 ^ (prefixWord ++ tailWord_2873165).sum := by decide
  have hdescent : baseEnd_2873165 < baseStart_2873165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873242 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2]
def baseStart_2873242 : Nat := 118140960795 + 2873242 * 2 ^ 59
def prefixEnd_2873242 : Nat := 4983230072969 + 3 ^ 40 * 2873242 * 2
def baseEnd_2873242 : Nat := 1475354182685752661161207

theorem tailTrace_2873242 : CollatzResearch.WordTrace tailWord_2873242 prefixEnd_2873242 1475354182685752661161207 := by
  unfold tailWord_2873242
  simp only [CollatzResearch.WordTrace]
  refine ⟨26198936264185604877809495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69863830037828279674158653 26198936264185604877809495)
  ·
    refine ⟨39298404396278407316714243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26198936264185604877809495 39298404396278407316714243)
    ·
      refine ⟨58947606594417610975071365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39298404396278407316714243 58947606594417610975071365)
      ·
        refine ⟨11052676236453302057825881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58947606594417610975071365 11052676236453302057825881)
        ·
          refine ⟨8289507177339976543369411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11052676236453302057825881 8289507177339976543369411)
          ·
            refine ⟨12434260766009964815054117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289507177339976543369411 12434260766009964815054117)
            ·
              refine ⟨2331423893626868402822647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12434260766009964815054117 2331423893626868402822647)
              ·
                refine ⟨3497135840440302604233971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331423893626868402822647 3497135840440302604233971)
                ·
                  refine ⟨5245703760660453906350957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497135840440302604233971 5245703760660453906350957)
                  ·
                    refine ⟨1967138910247670214881609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5245703760660453906350957 1967138910247670214881609)
                    ·
                      refine ⟨1475354182685752661161207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967138910247670214881609 1475354182685752661161207)
                      ·
                        rfl

theorem cell23_2873242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_2873242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873242 prefixEnd_2873242 := by exact prefixLift 2873242
  have htrace : WordTrace (prefixWord ++ tailWord_2873242) baseStart_2873242 baseEnd_2873242 := by
    simpa [prefixWord, tailWord_2873242, baseEnd_2873242] using wordTrace_append hprefix tailTrace_2873242
  have hstable : (prefixWord ++ tailWord_2873242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873242).length < 2 ^ (prefixWord ++ tailWord_2873242).sum := by decide
  have hdescent : baseEnd_2873242 < baseStart_2873242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873249 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2873249 : Nat := 118140960795 + 2873249 * 2 ^ 59
def prefixEnd_2873249 : Nat := 4983230072969 + 3 ^ 40 * 2873249 * 2
def baseEnd_2873249 : Nat := 1475357777050334133773675

theorem tailTrace_2873249 : CollatzResearch.WordTrace tailWord_2873249 prefixEnd_2873249 1475357777050334133773675 := by
  unfold tailWord_2873249
  simp only [CollatzResearch.WordTrace]
  refine ⟨104796000367717059706742801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69864000245144706471161867 104796000367717059706742801)
  ·
    refine ⟨78597000275787794780057101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104796000367717059706742801 78597000275787794780057101)
    ·
      refine ⟨29473875103420423042521413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78597000275787794780057101 29473875103420423042521413)
      ·
        refine ⟨5526351581891329320472765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29473875103420423042521413 5526351581891329320472765)
        ·
          refine ⟨2072381843209248495177287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5526351581891329320472765 2072381843209248495177287)
          ·
            refine ⟨3108572764813872742765931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072381843209248495177287 3108572764813872742765931)
            ·
              refine ⟨4662859147220809114148897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108572764813872742765931 4662859147220809114148897)
              ·
                refine ⟨3497144360415606835611673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662859147220809114148897 3497144360415606835611673)
                ·
                  refine ⟨2622858270311705126708755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3497144360415606835611673 2622858270311705126708755)
                  ·
                    refine ⟨3934287405467557690063133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2622858270311705126708755 3934287405467557690063133)
                    ·
                      refine ⟨1475357777050334133773675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934287405467557690063133 1475357777050334133773675)
                      ·
                        rfl

theorem cell23_2873249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2873249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873249 prefixEnd_2873249 := by exact prefixLift 2873249
  have htrace : WordTrace (prefixWord ++ tailWord_2873249) baseStart_2873249 baseEnd_2873249 := by
    simpa [prefixWord, tailWord_2873249, baseEnd_2873249] using wordTrace_append hprefix tailTrace_2873249
  have hstable : (prefixWord ++ tailWord_2873249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873249).length < 2 ^ (prefixWord ++ tailWord_2873249).sum := by decide
  have hdescent : baseEnd_2873249 < baseStart_2873249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873272 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 2, 2, 2]
def baseStart_2873272 : Nat := 118140960795 + 2873272 * 2 ^ 59
def prefixEnd_2873272 : Nat := 4983230072969 + 3 ^ 40 * 2873272 * 2
def baseEnd_2873272 : Nat := 1475369587105387543786069

theorem tailTrace_2873272 : CollatzResearch.WordTrace tailWord_2873272 prefixEnd_2873272 1475369587105387543786069 := by
  unfold tailWord_2873272
  simp only [CollatzResearch.WordTrace]
  refine ⟨52398419623316867317415035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69864559497755823089886713 52398419623316867317415035)
  ·
    refine ⟨78597629434975300976122553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52398419623316867317415035 78597629434975300976122553)
    ·
      refine ⟨58948222076231475732091915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78597629434975300976122553 58948222076231475732091915)
      ·
        refine ⟨88422333114347213598137873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58948222076231475732091915 88422333114347213598137873)
        ·
          refine ⟨66316749835760410198603405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88422333114347213598137873 66316749835760410198603405)
          ·
            refine ⟨24868781188410153824476277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66316749835760410198603405 24868781188410153824476277)
            ·
              refine ⟨2331448236413451921044651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24868781188410153824476277 2331448236413451921044651)
              ·
                refine ⟨3497172354620177881566977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331448236413451921044651 3497172354620177881566977)
                ·
                  refine ⟨2622879265965133411175233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3497172354620177881566977 2622879265965133411175233)
                  ·
                    refine ⟨1967159449473850058381425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2622879265965133411175233 1967159449473850058381425)
                    ·
                      refine ⟨1475369587105387543786069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967159449473850058381425 1475369587105387543786069)
                      ·
                        rfl

theorem cell23_2873272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_2873272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873272 prefixEnd_2873272 := by exact prefixLift 2873272
  have htrace : WordTrace (prefixWord ++ tailWord_2873272) baseStart_2873272 baseEnd_2873272 := by
    simpa [prefixWord, tailWord_2873272, baseEnd_2873272] using wordTrace_append hprefix tailTrace_2873272
  have hstable : (prefixWord ++ tailWord_2873272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873272).length < 2 ^ (prefixWord ++ tailWord_2873272).sum := by decide
  have hdescent : baseEnd_2873272 < baseStart_2873272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873291 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 2, 5]
def baseStart_2873291 : Nat := 118140960795 + 2873291 * 2 ^ 59
def prefixEnd_2873291 : Nat := 4983230072969 + 3 ^ 40 * 2873291 * 2
def baseEnd_2873291 : Nat := 491793114412607656482827

theorem tailTrace_2873291 : CollatzResearch.WordTrace tailWord_2873291 prefixEnd_2873291 491793114412607656482827 := by
  unfold tailWord_2873291
  simp only [CollatzResearch.WordTrace]
  refine ⟨104797532233564900879771727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69865021489043267253181151 104797532233564900879771727)
  ·
    refine ⟨157196298350347351319657591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104797532233564900879771727 157196298350347351319657591)
    ·
      refine ⟨235794447525521026979486387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157196298350347351319657591 235794447525521026979486387)
      ·
        refine ⟨353691671288281540469229581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235794447525521026979486387 353691671288281540469229581)
        ·
          refine ⟨132634376733105577675961093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353691671288281540469229581 132634376733105577675961093)
          ·
            refine ⟨24868945637457295814242705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132634376733105577675961093 24868945637457295814242705)
            ·
              refine ⟨18651709228092971860682029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24868945637457295814242705 18651709228092971860682029)
              ·
                refine ⟨6994390960534864447755761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18651709228092971860682029 6994390960534864447755761)
                ·
                  refine ⟨5245793220401148335816821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6994390960534864447755761 5245793220401148335816821)
                  ·
                    refine ⟨491793114412607656482827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5245793220401148335816821 491793114412607656482827)
                    ·
                      rfl

theorem cell23_2873291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 5].length) (baseStart_2873291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873291 prefixEnd_2873291 := by exact prefixLift 2873291
  have htrace : WordTrace (prefixWord ++ tailWord_2873291) baseStart_2873291 baseEnd_2873291 := by
    simpa [prefixWord, tailWord_2873291, baseEnd_2873291] using wordTrace_append hprefix tailTrace_2873291
  have hstable : (prefixWord ++ tailWord_2873291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873291).length < 2 ^ (prefixWord ++ tailWord_2873291).sum := by decide
  have hdescent : baseEnd_2873291 < baseStart_2873291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873328 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 2, 4, 2]
def baseStart_2873328 : Nat := 118140960795 + 2873328 * 2 ^ 59
def prefixEnd_2873328 : Nat := 4983230072969 + 3 ^ 40 * 2873328 * 2
def baseEnd_2873328 : Nat := 1475398342022039324685811

theorem tailTrace_2873328 : CollatzResearch.WordTrace tailWord_2873328 prefixEnd_2873328 1475398342022039324685811 := by
  unfold tailWord_2873328
  simp only [CollatzResearch.WordTrace]
  refine ⟨52399440867215428099434319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69865921156287237465912425 52399440867215428099434319)
  ·
    refine ⟨78599161300823142149151479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52399440867215428099434319 78599161300823142149151479)
    ·
      refine ⟨117898741951234713223727219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78599161300823142149151479 117898741951234713223727219)
      ·
        refine ⟨176848112926852069835590829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117898741951234713223727219 176848112926852069835590829)
        ·
          refine ⟨66318042347569526188346561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176848112926852069835590829 66318042347569526188346561)
          ·
            refine ⟨49738531760677144641259921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66318042347569526188346561 49738531760677144641259921)
            ·
              refine ⟨37303898820507858480944941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49738531760677144641259921 37303898820507858480944941)
              ·
                refine ⟨13988962057690446930354353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37303898820507858480944941 13988962057690446930354353)
                ·
                  refine ⟨10491721543267835197765765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13988962057690446930354353 10491721543267835197765765)
                  ·
                    refine ⟨1967197789362719099581081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10491721543267835197765765 1967197789362719099581081)
                    ·
                      refine ⟨1475398342022039324685811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967197789362719099581081 1475398342022039324685811)
                      ·
                        rfl

theorem cell23_2873328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 4, 2].length) (baseStart_2873328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873328 prefixEnd_2873328 := by exact prefixLift 2873328
  have htrace : WordTrace (prefixWord ++ tailWord_2873328) baseStart_2873328 baseEnd_2873328 := by
    simpa [prefixWord, tailWord_2873328, baseEnd_2873328] using wordTrace_append hprefix tailTrace_2873328
  have hstable : (prefixWord ++ tailWord_2873328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873328).length < 2 ^ (prefixWord ++ tailWord_2873328).sum := by decide
  have hdescent : baseEnd_2873328 < baseStart_2873328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873331 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 3]
def baseStart_2873331 : Nat := 118140960795 + 2873331 * 2 ^ 59
def prefixEnd_2873331 : Nat := 4983230072969 + 3 ^ 40 * 2873331 * 2
def baseEnd_2873331 : Nat := 1475399882464002812948297

theorem tailTrace_2873331 : CollatzResearch.WordTrace tailWord_2873331 prefixEnd_2873331 1475399882464002812948297 := by
  unfold tailWord_2873331
  simp only [CollatzResearch.WordTrace]
  refine ⟨104798991153419987711227847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69865994102279991807485231 104798991153419987711227847)
  ·
    refine ⟨157198486730129981566841771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104798991153419987711227847 157198486730129981566841771)
    ·
      refine ⟨235797730095194972350262657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157198486730129981566841771 235797730095194972350262657)
      ·
        refine ⟨176848297571396229262696993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235797730095194972350262657 176848297571396229262696993)
        ·
          refine ⟨132636223178547171947022745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176848297571396229262696993 132636223178547171947022745)
          ·
            refine ⟨99477167383910378960267059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132636223178547171947022745 99477167383910378960267059)
            ·
              refine ⟨149215751075865568440400589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99477167383910378960267059 149215751075865568440400589)
              ·
                refine ⟨55955906653449588165150221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149215751075865568440400589 55955906653449588165150221)
                ·
                  refine ⟨20983464995043595561931333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55955906653449588165150221 20983464995043595561931333)
                  ·
                    refine ⟨3934399686570674167862125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20983464995043595561931333 3934399686570674167862125)
                    ·
                      refine ⟨1475399882464002812948297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934399686570674167862125 1475399882464002812948297)
                      ·
                        rfl

theorem cell23_2873331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_2873331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873331 prefixEnd_2873331 := by exact prefixLift 2873331
  have htrace : WordTrace (prefixWord ++ tailWord_2873331) baseStart_2873331 baseEnd_2873331 := by
    simpa [prefixWord, tailWord_2873331, baseEnd_2873331] using wordTrace_append hprefix tailTrace_2873331
  have hstable : (prefixWord ++ tailWord_2873331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873331).length < 2 ^ (prefixWord ++ tailWord_2873331).sum := by decide
  have hdescent : baseEnd_2873331 < baseStart_2873331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873341 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_2873341 : Nat := 118140960795 + 2873341 * 2 ^ 59
def prefixEnd_2873341 : Nat := 4983230072969 + 3 ^ 40 * 2873341 * 2
def baseEnd_2873341 : Nat := 1475405017270547773823251

theorem tailTrace_2873341 : CollatzResearch.WordTrace tailWord_2873341 prefixEnd_2873341 1475405017270547773823251 := by
  unfold tailWord_2873341
  simp only [CollatzResearch.WordTrace]
  refine ⟨104799355883383759419091877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69866237255589172946061251 104799355883383759419091877)
  ·
    refine ⟨19649879228134454891079727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104799355883383759419091877 19649879228134454891079727)
    ·
      refine ⟨29474818842201682336619591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19649879228134454891079727 29474818842201682336619591)
      ·
        refine ⟨44212228263302523504929387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29474818842201682336619591 44212228263302523504929387)
        ·
          refine ⟨66318342394953785257394081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44212228263302523504929387 66318342394953785257394081)
          ·
            refine ⟨49738756796215338943045561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66318342394953785257394081 49738756796215338943045561)
            ·
              refine ⟨37304067597161504207284171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49738756796215338943045561 37304067597161504207284171)
              ·
                refine ⟨55956101395742256310926257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37304067597161504207284171 55956101395742256310926257)
                ·
                  refine ⟨41967076046806692233194693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55956101395742256310926257 41967076046806692233194693)
                  ·
                    refine ⟨7868826758776254793724005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41967076046806692233194693 7868826758776254793724005)
                    ·
                      refine ⟨1475405017270547773823251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7868826758776254793724005 1475405017270547773823251)
                      ·
                        rfl

theorem cell23_2873341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_2873341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873341 prefixEnd_2873341 := by exact prefixLift 2873341
  have htrace : WordTrace (prefixWord ++ tailWord_2873341) baseStart_2873341 baseEnd_2873341 := by
    simpa [prefixWord, tailWord_2873341, baseEnd_2873341] using wordTrace_append hprefix tailTrace_2873341
  have hstable : (prefixWord ++ tailWord_2873341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873341).length < 2 ^ (prefixWord ++ tailWord_2873341).sum := by decide
  have hdescent : baseEnd_2873341 < baseStart_2873341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873355 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 1, 4]
def baseStart_2873355 : Nat := 118140960795 + 2873355 * 2 ^ 59
def prefixEnd_2873355 : Nat := 4983230072969 + 3 ^ 40 * 2873355 * 2
def baseEnd_2873355 : Nat := 491804068666570239682729

theorem tailTrace_2873355 : CollatzResearch.WordTrace tailWord_2873355 prefixEnd_2873355 491804068666570239682729 := by
  unfold tailWord_2873355
  simp only [CollatzResearch.WordTrace]
  refine ⟨104799866505333039810101519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69866577670222026540067679 104799866505333039810101519)
  ·
    refine ⟨157199799757999559715152279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104799866505333039810101519 157199799757999559715152279)
    ·
      refine ⟨235799699636999339572728419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157199799757999559715152279 235799699636999339572728419)
      ·
        refine ⟨353699549455499009359092629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235799699636999339572728419 353699549455499009359092629)
        ·
          refine ⟨16579666380726516063707467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 353699549455499009359092629 16579666380726516063707467)
          ·
            refine ⟨24869499571089774095561201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16579666380726516063707467 24869499571089774095561201)
            ·
              refine ⟨18652124678317330571670901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24869499571089774095561201 18652124678317330571670901)
              ·
                refine ⟨1748636688592249741094147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18652124678317330571670901 1748636688592249741094147)
                ·
                  refine ⟨2622955032888374611641221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748636688592249741094147 2622955032888374611641221)
                  ·
                    refine ⟨491804068666570239682729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622955032888374611641221 491804068666570239682729)
                    ·
                      rfl

theorem cell23_2873355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 4].length) (baseStart_2873355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873355 prefixEnd_2873355 := by exact prefixLift 2873355
  have htrace : WordTrace (prefixWord ++ tailWord_2873355) baseStart_2873355 baseEnd_2873355 := by
    simpa [prefixWord, tailWord_2873355, baseEnd_2873355] using wordTrace_append hprefix tailTrace_2873355
  have hstable : (prefixWord ++ tailWord_2873355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873355).length < 2 ^ (prefixWord ++ tailWord_2873355).sum := by decide
  have hdescent : baseEnd_2873355 < baseStart_2873355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873368 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 6]
def baseStart_2873368 : Nat := 118140960795 + 2873368 * 2 ^ 59
def prefixEnd_2873368 : Nat := 4983230072969 + 3 ^ 40 * 2873368 * 2
def baseEnd_2873368 : Nat := 163935431249802129798403

theorem tailTrace_2873368 : CollatzResearch.WordTrace tailWord_2873368 prefixEnd_2873368 163935431249802129798403 := by
  unfold tailWord_2873368
  simp only [CollatzResearch.WordTrace]
  refine ⟨52400170327142971515162379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69866893769523962020216505 52400170327142971515162379)
  ·
    refine ⟨78600255490714457272743569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52400170327142971515162379 78600255490714457272743569)
    ·
      refine ⟨58950191618035842954557677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78600255490714457272743569 58950191618035842954557677)
      ·
        refine ⟨22106321856763441107959129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58950191618035842954557677 22106321856763441107959129)
        ·
          refine ⟨16579741392572580830969347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22106321856763441107959129 16579741392572580830969347)
          ·
            refine ⟨24869612088858871246454021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16579741392572580830969347 24869612088858871246454021)
            ·
              refine ⟨4663052266661038358710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24869612088858871246454021 4663052266661038358710129)
              ·
                refine ⟨3497289199995778769032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4663052266661038358710129 3497289199995778769032597)
                ·
                  refine ⟨163935431249802129798403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3497289199995778769032597 163935431249802129798403)
                  ·
                    rfl

theorem cell23_2873368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 6].length) (baseStart_2873368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873368 prefixEnd_2873368 := by exact prefixLift 2873368
  have htrace : WordTrace (prefixWord ++ tailWord_2873368) baseStart_2873368 baseEnd_2873368 := by
    simpa [prefixWord, tailWord_2873368, baseEnd_2873368] using wordTrace_append hprefix tailTrace_2873368
  have hstable : (prefixWord ++ tailWord_2873368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873368).length < 2 ^ (prefixWord ++ tailWord_2873368).sum := by decide
  have hdescent : baseEnd_2873368 < baseStart_2873368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873372 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2873372 : Nat := 118140960795 + 2873372 * 2 ^ 59
def prefixEnd_2873372 : Nat := 4983230072969 + 3 ^ 40 * 2873372 * 2
def baseEnd_2873372 : Nat := 491806978390279050845203

theorem tailTrace_2873372 : CollatzResearch.WordTrace tailWord_2873372 prefixEnd_2873372 491806978390279050845203 := by
  unfold tailWord_2873372
  simp only [CollatzResearch.WordTrace]
  refine ⟨52400243273135725856735185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69866991030847634475646913 52400243273135725856735185)
  ·
    refine ⟨39300182454851794392551389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52400243273135725856735185 39300182454851794392551389)
    ·
      refine ⟨14737568420569422897206771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39300182454851794392551389 14737568420569422897206771)
      ·
        refine ⟨22106352630854134345810157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14737568420569422897206771 22106352630854134345810157)
        ·
          refine ⟨8289882236570300379678809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22106352630854134345810157 8289882236570300379678809)
          ·
            refine ⟨6217411677427725284759107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8289882236570300379678809 6217411677427725284759107)
            ·
              refine ⟨9326117516141587927138661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6217411677427725284759107 9326117516141587927138661)
              ·
                refine ⟨1748647034276547736338499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9326117516141587927138661 1748647034276547736338499)
                ·
                  refine ⟨2622970551414821604507749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748647034276547736338499 2622970551414821604507749)
                  ·
                    refine ⟨491806978390279050845203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622970551414821604507749 491806978390279050845203)
                    ·
                      rfl

theorem cell23_2873372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2873372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873372 prefixEnd_2873372 := by exact prefixLift 2873372
  have htrace : WordTrace (prefixWord ++ tailWord_2873372) baseStart_2873372 baseEnd_2873372 := by
    simpa [prefixWord, tailWord_2873372, baseEnd_2873372] using wordTrace_append hprefix tailTrace_2873372
  have hstable : (prefixWord ++ tailWord_2873372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873372).length < 2 ^ (prefixWord ++ tailWord_2873372).sum := by decide
  have hdescent : baseEnd_2873372 < baseStart_2873372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873405 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_2873405 : Nat := 118140960795 + 2873405 * 2 ^ 59
def prefixEnd_2873405 : Nat := 4983230072969 + 3 ^ 40 * 2873405 * 2
def baseEnd_2873405 : Nat := 1475437880032435523422957

theorem tailTrace_2873405 : CollatzResearch.WordTrace tailWord_2873405 prefixEnd_2873405 1475437880032435523422957 := by
  unfold tailWord_2873405
  simp only [CollatzResearch.WordTrace]
  refine ⟨104801690155151898349421669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69867793436767932232947779 104801690155151898349421669)
  ·
    refine ⟨19650316904090980940516563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104801690155151898349421669 19650316904090980940516563)
    ·
      refine ⟨29475475356136471410774845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19650316904090980940516563 29475475356136471410774845)
      ·
        refine ⟨11053303258551176779040567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29475475356136471410774845 11053303258551176779040567)
        ·
          refine ⟨16579954887826765168560851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11053303258551176779040567 16579954887826765168560851)
          ·
            refine ⟨24869932331740147752841277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16579954887826765168560851 24869932331740147752841277)
            ·
              refine ⟨9326224624402555407315479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24869932331740147752841277 9326224624402555407315479)
              ·
                refine ⟨13989336936603833110973219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9326224624402555407315479 13989336936603833110973219)
                ·
                  refine ⟨20984005404905749666459829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13989336936603833110973219 20984005404905749666459829)
                  ·
                    refine ⟨1967250506709914031230609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20984005404905749666459829 1967250506709914031230609)
                    ·
                      refine ⟨1475437880032435523422957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967250506709914031230609 1475437880032435523422957)
                      ·
                        rfl

theorem cell23_2873405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_2873405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873405 prefixEnd_2873405 := by exact prefixLift 2873405
  have htrace : WordTrace (prefixWord ++ tailWord_2873405) baseStart_2873405 baseEnd_2873405 := by
    simpa [prefixWord, tailWord_2873405, baseEnd_2873405] using wordTrace_append hprefix tailTrace_2873405
  have hstable : (prefixWord ++ tailWord_2873405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873405).length < 2 ^ (prefixWord ++ tailWord_2873405).sum := by decide
  have hdescent : baseEnd_2873405 < baseStart_2873405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873411 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 3, 6]
def baseStart_2873411 : Nat := 118140960795 + 2873411 * 2 ^ 59
def prefixEnd_2873411 : Nat := 4983230072969 + 3 ^ 40 * 2873411 * 2
def baseEnd_2873411 : Nat := 491813653638787499982643

theorem tailTrace_2873411 : CollatzResearch.WordTrace tailWord_2873411 prefixEnd_2873411 491813653638787499982643 := by
  unfold tailWord_2873411
  simp only [CollatzResearch.WordTrace]
  refine ⟨104801908993130161374140087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69867939328753440916093391 104801908993130161374140087)
  ·
    refine ⟨157202863489695242061210131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104801908993130161374140087 157202863489695242061210131)
    ·
      refine ⟨235804295234542863091815197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157202863489695242061210131 235804295234542863091815197)
      ·
        refine ⟨88426610712953573659430699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235804295234542863091815197 88426610712953573659430699)
        ·
          refine ⟨132639916069430360489146049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88426610712953573659430699 132639916069430360489146049)
          ·
            refine ⟨99479937052072770366859537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132639916069430360489146049 99479937052072770366859537)
            ·
              refine ⟨74609952789054577775144653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99479937052072770366859537 74609952789054577775144653)
              ·
                refine ⟨27978732295895466665679245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74609952789054577775144653 27978732295895466665679245)
                ·
                  refine ⟨10492024610960799999629717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27978732295895466665679245 10492024610960799999629717)
                  ·
                    refine ⟨491813653638787499982643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10492024610960799999629717 491813653638787499982643)
                    ·
                      rfl

theorem cell23_2873411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 6].length) (baseStart_2873411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873411 prefixEnd_2873411 := by exact prefixLift 2873411
  have htrace : WordTrace (prefixWord ++ tailWord_2873411) baseStart_2873411 baseEnd_2873411 := by
    simpa [prefixWord, tailWord_2873411, baseEnd_2873411] using wordTrace_append hprefix tailTrace_2873411
  have hstable : (prefixWord ++ tailWord_2873411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873411).length < 2 ^ (prefixWord ++ tailWord_2873411).sum := by decide
  have hdescent : baseEnd_2873411 < baseStart_2873411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873441 : List Nat := [1, 2, 3, 1, 1, 2, 1, 12]
def baseStart_2873441 : Nat := 118140960795 + 2873441 * 2 ^ 59
def prefixEnd_2873441 : Nat := 4983230072969 + 3 ^ 40 * 2873441 * 2
def baseEnd_2873441 : Nat := 54646532049481384539733

theorem tailTrace_2873441 : CollatzResearch.WordTrace tailWord_2873441 prefixEnd_2873441 54646532049481384539733 := by
  unfold tailWord_2873441
  simp only [CollatzResearch.WordTrace]
  refine ⟨104803003183021476497732177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69868668788680984331821451 104803003183021476497732177)
  ·
    refine ⟨78602252387266107373299133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104803003183021476497732177 78602252387266107373299133)
    ·
      refine ⟨29475844645224790264987175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78602252387266107373299133 29475844645224790264987175)
      ·
        refine ⟨44213766967837185397480763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29475844645224790264987175 44213766967837185397480763)
        ·
          refine ⟨66320650451755778096221145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44213766967837185397480763 66320650451755778096221145)
          ·
            refine ⟨49740487838816833572165859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66320650451755778096221145 49740487838816833572165859)
            ·
              refine ⟨74610731758225250358248789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49740487838816833572165859 74610731758225250358248789)
              ·
                refine ⟨54646532049481384539733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 74610731758225250358248789 54646532049481384539733)
                ·
                  rfl

theorem cell23_2873441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 12].length) (baseStart_2873441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873441 prefixEnd_2873441 := by exact prefixLift 2873441
  have htrace : WordTrace (prefixWord ++ tailWord_2873441) baseStart_2873441 baseEnd_2873441 := by
    simpa [prefixWord, tailWord_2873441, baseEnd_2873441] using wordTrace_append hprefix tailTrace_2873441
  have hstable : (prefixWord ++ tailWord_2873441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873441).length < 2 ^ (prefixWord ++ tailWord_2873441).sum := by decide
  have hdescent : baseEnd_2873441 < baseStart_2873441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873445 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_2873445 : Nat := 118140960795 + 2873445 * 2 ^ 59
def prefixEnd_2873445 : Nat := 4983230072969 + 3 ^ 40 * 2873445 * 2
def baseEnd_2873445 : Nat := 491819473086205122307591

theorem tailTrace_2873445 : CollatzResearch.WordTrace tailWord_2873445 prefixEnd_2873445 491819473086205122307591 := by
  unfold tailWord_2873445
  simp only [CollatzResearch.WordTrace]
  refine ⟨104803149075006985180877789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69868766050004656787251859 104803149075006985180877789)
  ·
    refine ⟨39301180903127619442829171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104803149075006985180877789 39301180903127619442829171)
    ·
      refine ⟨58951771354691429164243757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39301180903127619442829171 58951771354691429164243757)
      ·
        refine ⟨22106914258009285936591409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58951771354691429164243757 22106914258009285936591409)
        ·
          refine ⟨16580185693506964452443557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22106914258009285936591409 16580185693506964452443557)
          ·
            refine ⟨3108784817532555834833167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16580185693506964452443557 3108784817532555834833167)
            ·
              refine ⟨4663177226298833752249751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108784817532555834833167 4663177226298833752249751)
              ·
                refine ⟨6994765839448250628374627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663177226298833752249751 6994765839448250628374627)
                ·
                  refine ⟨10492148759172375942561941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6994765839448250628374627 10492148759172375942561941)
                  ·
                    refine ⟨491819473086205122307591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10492148759172375942561941 491819473086205122307591)
                    ·
                      rfl

theorem cell23_2873445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_2873445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873445 prefixEnd_2873445 := by exact prefixLift 2873445
  have htrace : WordTrace (prefixWord ++ tailWord_2873445) baseStart_2873445 baseEnd_2873445 := by
    simpa [prefixWord, tailWord_2873445, baseEnd_2873445] using wordTrace_append hprefix tailTrace_2873445
  have hstable : (prefixWord ++ tailWord_2873445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873445).length < 2 ^ (prefixWord ++ tailWord_2873445).sum := by decide
  have hdescent : baseEnd_2873445 < baseStart_2873445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873452 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 3, 2, 2]
def baseStart_2873452 : Nat := 118140960795 + 2873452 * 2 ^ 59
def prefixEnd_2873452 : Nat := 4983230072969 + 3 ^ 40 * 2873452 * 2
def baseEnd_2873452 : Nat := 1475462013623196839535241

theorem tailTrace_2873452 : CollatzResearch.WordTrace tailWord_2873452 prefixEnd_2873452 1475462013623196839535241 := by
  unfold tailWord_2873452
  simp only [CollatzResearch.WordTrace]
  refine ⟨52401702192990812688191305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69868936257321083584255073 52401702192990812688191305)
  ·
    refine ⟨39301276644743109516143479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52401702192990812688191305 39301276644743109516143479)
    ·
      refine ⟨58951914967114664274215219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39301276644743109516143479 58951914967114664274215219)
      ·
        refine ⟨88427872450671996411322829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58951914967114664274215219 88427872450671996411322829)
        ·
          refine ⟨33160452169001998654246061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88427872450671996411322829 33160452169001998654246061)
          ·
            refine ⟨12435169563375749495342273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33160452169001998654246061 12435169563375749495342273)
            ·
              refine ⟨9326377172531812121506705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12435169563375749495342273 9326377172531812121506705)
              ·
                refine ⟨6994782879398859091130029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9326377172531812121506705 6994782879398859091130029)
                ·
                  refine ⟨2623043579774572159173761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6994782879398859091130029 2623043579774572159173761)
                  ·
                    refine ⟨1967282684830929119380321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2623043579774572159173761 1967282684830929119380321)
                    ·
                      refine ⟨1475462013623196839535241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967282684830929119380321 1475462013623196839535241)
                      ·
                        rfl

theorem cell23_2873452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_2873452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873452 prefixEnd_2873452 := by exact prefixLift 2873452
  have htrace : WordTrace (prefixWord ++ tailWord_2873452) baseStart_2873452 baseEnd_2873452 := by
    simpa [prefixWord, tailWord_2873452, baseEnd_2873452] using wordTrace_append hprefix tailTrace_2873452
  have hstable : (prefixWord ++ tailWord_2873452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873452).length < 2 ^ (prefixWord ++ tailWord_2873452).sum := by decide
  have hdescent : baseEnd_2873452 < baseStart_2873452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873455 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 3]
def baseStart_2873455 : Nat := 118140960795 + 2873455 * 2 ^ 59
def prefixEnd_2873455 : Nat := 4983230072969 + 3 ^ 40 * 2873455 * 2
def baseEnd_2873455 : Nat := 1475463554065160327797727

theorem tailTrace_2873455 : CollatzResearch.WordTrace tailWord_2873455 prefixEnd_2873455 1475463554065160327797727 := by
  unfold tailWord_2873455
  simp only [CollatzResearch.WordTrace]
  refine ⟨104803513804970756888741819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69869009203313837925827879 104803513804970756888741819)
  ·
    refine ⟨157205270707456135333112729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104803513804970756888741819 157205270707456135333112729)
    ·
      refine ⟨117903953030592101499834547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157205270707456135333112729 117903953030592101499834547)
      ·
        refine ⟨176855929545888152249751821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117903953030592101499834547 176855929545888152249751821)
        ·
          refine ⟨66320973579708057093656933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176855929545888152249751821 66320973579708057093656933)
          ·
            refine ⟨12435182546195260705060675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66320973579708057093656933 12435182546195260705060675)
            ·
              refine ⟨18652773819292891057591013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435182546195260705060675 18652773819292891057591013)
              ·
                refine ⟨3497395091117417073298315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18652773819292891057591013 3497395091117417073298315)
                ·
                  refine ⟨5246092636676125609947473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497395091117417073298315 5246092636676125609947473)
                  ·
                    refine ⟨3934569477507094207460605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5246092636676125609947473 3934569477507094207460605)
                    ·
                      refine ⟨1475463554065160327797727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934569477507094207460605 1475463554065160327797727)
                      ·
                        rfl

theorem cell23_2873455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_2873455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873455 prefixEnd_2873455 := by exact prefixLift 2873455
  have htrace : WordTrace (prefixWord ++ tailWord_2873455) baseStart_2873455 baseEnd_2873455 := by
    simpa [prefixWord, tailWord_2873455, baseEnd_2873455] using wordTrace_append hprefix tailTrace_2873455
  have hstable : (prefixWord ++ tailWord_2873455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873455).length < 2 ^ (prefixWord ++ tailWord_2873455).sum := by decide
  have hdescent : baseEnd_2873455 < baseStart_2873455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873458 : List Nat := [3, 2, 1, 2, 2, 3, 1, 9]
def baseStart_2873458 : Nat := 118140960795 + 2873458 * 2 ^ 59
def prefixEnd_2873458 : Nat := 4983230072969 + 3 ^ 40 * 2873458 * 2
def baseEnd_2873458 : Nat := 54646855352115696891119

theorem tailTrace_2873458 : CollatzResearch.WordTrace tailWord_2873458 prefixEnd_2873458 54646855352115696891119 := by
  unfold tailWord_2873458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26200905805989972100275257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69869082149306592267400685 26200905805989972100275257)
  ·
    refine ⟨19650679354492479075206443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26200905805989972100275257 19650679354492479075206443)
    ·
      refine ⟨29476019031738718612809665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19650679354492479075206443 29476019031738718612809665)
      ·
        refine ⟨22107014273804038959607249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29476019031738718612809665 22107014273804038959607249)
        ·
          refine ⟨16580260705353029219705437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22107014273804038959607249 16580260705353029219705437)
          ·
            refine ⟨6217597764507385957389539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16580260705353029219705437 6217597764507385957389539)
            ·
              refine ⟨9326396646761078936084309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6217597764507385957389539 9326396646761078936084309)
              ·
                refine ⟨54646855352115696891119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9326396646761078936084309 54646855352115696891119)
                ·
                  rfl

theorem cell23_2873458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_2873458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873458 prefixEnd_2873458 := by exact prefixLift 2873458
  have htrace : WordTrace (prefixWord ++ tailWord_2873458) baseStart_2873458 baseEnd_2873458 := by
    simpa [prefixWord, tailWord_2873458, baseEnd_2873458] using wordTrace_append hprefix tailTrace_2873458
  have hstable : (prefixWord ++ tailWord_2873458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873458).length < 2 ^ (prefixWord ++ tailWord_2873458).sum := by decide
  have hdescent : baseEnd_2873458 < baseStart_2873458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873486 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2873486 : Nat := 118140960795 + 2873486 * 2 ^ 59
def prefixEnd_2873486 : Nat := 4983230072969 + 3 ^ 40 * 2873486 * 2
def baseEnd_2873486 : Nat := 1475479471965449706510085

theorem tailTrace_2873486 : CollatzResearch.WordTrace tailWord_2873486 prefixEnd_2873486 1475479471965449706510085 := by
  unfold tailWord_2873486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13100580558482306147890039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69869762978572299455413541 13100580558482306147890039)
  ·
    refine ⟨19650870837723459221835059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13100580558482306147890039 19650870837723459221835059)
    ·
      refine ⟨29476306256585188832752589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19650870837723459221835059 29476306256585188832752589)
      ·
        refine ⟨11053614846219445812282221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29476306256585188832752589 11053614846219445812282221)
        ·
          refine ⟨4145105567332292179605833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11053614846219445812282221 4145105567332292179605833)
          ·
            refine ⟨3108829175499219134704375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145105567332292179605833 3108829175499219134704375)
            ·
              refine ⟨4663243763248828702056563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108829175499219134704375 4663243763248828702056563)
              ·
                refine ⟨6994865644873243053084845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663243763248828702056563 6994865644873243053084845)
                ·
                  refine ⟨2623074616827466144906817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6994865644873243053084845 2623074616827466144906817)
                  ·
                    refine ⟨1967305962620599608680113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2623074616827466144906817 1967305962620599608680113)
                    ·
                      refine ⟨1475479471965449706510085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967305962620599608680113 1475479471965449706510085)
                      ·
                        rfl

theorem cell23_2873486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2873486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873486 prefixEnd_2873486 := by exact prefixLift 2873486
  have htrace : WordTrace (prefixWord ++ tailWord_2873486) baseStart_2873486 baseEnd_2873486 := by
    simpa [prefixWord, tailWord_2873486, baseEnd_2873486] using wordTrace_append hprefix tailTrace_2873486
  have hstable : (prefixWord ++ tailWord_2873486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873486).length < 2 ^ (prefixWord ++ tailWord_2873486).sum := by decide
  have hdescent : baseEnd_2873486 < baseStart_2873486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873492 : List Nat := [2, 4, 2, 3, 1, 1, 2, 8]
def baseStart_2873492 : Nat := 118140960795 + 2873492 * 2 ^ 59
def prefixEnd_2873492 : Nat := 4983230072969 + 3 ^ 40 * 2873492 * 2
def baseEnd_2873492 : Nat := 54647501957384321593891

theorem tailTrace_2873492 : CollatzResearch.WordTrace tailWord_2873492 prefixEnd_2873492 54647501957384321593891 := by
  unfold tailWord_2873492
  simp only [CollatzResearch.WordTrace]
  refine ⟨52402431652918356103919365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69869908870557808138559153 52402431652918356103919365)
  ·
    refine ⟨9825455934922191769484881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52402431652918356103919365 9825455934922191769484881)
    ·
      refine ⟨7369091951191643827113661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9825455934922191769484881 7369091951191643827113661)
      ·
        refine ⟨2763409481696866435167623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7369091951191643827113661 2763409481696866435167623)
        ·
          refine ⟨4145114222545299652751435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763409481696866435167623 4145114222545299652751435)
          ·
            refine ⟨6217671333817949479127153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145114222545299652751435 6217671333817949479127153)
            ·
              refine ⟨4663253500363462109345365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6217671333817949479127153 4663253500363462109345365)
              ·
                refine ⟨54647501957384321593891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4663253500363462109345365 54647501957384321593891)
                ·
                  rfl

theorem cell23_2873492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 8].length) (baseStart_2873492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873492 prefixEnd_2873492 := by exact prefixLift 2873492
  have htrace : WordTrace (prefixWord ++ tailWord_2873492) baseStart_2873492 baseEnd_2873492 := by
    simpa [prefixWord, tailWord_2873492, baseEnd_2873492] using wordTrace_append hprefix tailTrace_2873492
  have hstable : (prefixWord ++ tailWord_2873492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873492).length < 2 ^ (prefixWord ++ tailWord_2873492).sum := by decide
  have hdescent : baseEnd_2873492 < baseStart_2873492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873496 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 2, 4]
def baseStart_2873496 : Nat := 118140960795 + 2873496 * 2 ^ 59
def prefixEnd_2873496 : Nat := 4983230072969 + 3 ^ 40 * 2873496 * 2
def baseEnd_2873496 : Nat := 491828202257331555795013

theorem tailTrace_2873496 : CollatzResearch.WordTrace tailWord_2873496 prefixEnd_2873496 491828202257331555795013 := by
  unfold tailWord_2873496
  simp only [CollatzResearch.WordTrace]
  refine ⟨52402504598911110445492171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69870006131881480593989561 52402504598911110445492171)
  ·
    refine ⟨78603756898366665668238257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52402504598911110445492171 78603756898366665668238257)
    ·
      refine ⟨58952817673774999251178693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78603756898366665668238257 58952817673774999251178693)
      ·
        refine ⟨11053653313832812359596005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58952817673774999251178693 11053653313832812359596005)
        ·
          refine ⟨2072559996343652317424251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11053653313832812359596005 2072559996343652317424251)
          ·
            refine ⟨3108839994515478476136377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072559996343652317424251 3108839994515478476136377)
            ·
              refine ⟨2331629995886608857102283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108839994515478476136377 2331629995886608857102283)
              ·
                refine ⟨3497444993829913285653425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331629995886608857102283 3497444993829913285653425)
                ·
                  refine ⟨2623083745372434964240069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3497444993829913285653425 2623083745372434964240069)
                  ·
                    refine ⟨491828202257331555795013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2623083745372434964240069 491828202257331555795013)
                    ·
                      rfl

theorem cell23_2873496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_2873496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873496 prefixEnd_2873496 := by exact prefixLift 2873496
  have htrace : WordTrace (prefixWord ++ tailWord_2873496) baseStart_2873496 baseEnd_2873496 := by
    simpa [prefixWord, tailWord_2873496, baseEnd_2873496] using wordTrace_append hprefix tailTrace_2873496
  have hstable : (prefixWord ++ tailWord_2873496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873496).length < 2 ^ (prefixWord ++ tailWord_2873496).sum := by decide
  have hdescent : baseEnd_2873496 < baseStart_2873496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873528 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_2873528 : Nat := 118140960795 + 2873528 * 2 ^ 59
def prefixEnd_2873528 : Nat := 4983230072969 + 3 ^ 40 * 2873528 * 2
def baseEnd_2873528 : Nat := 1475501038152938542184891

theorem tailTrace_2873528 : CollatzResearch.WordTrace tailWord_2873528 prefixEnd_2873528 1475501038152938542184891 := by
  unfold tailWord_2873528
  simp only [CollatzResearch.WordTrace]
  refine ⟨52403088166853145178074619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69870784222470860237432825 52403088166853145178074619)
  ·
    refine ⟨78604632250279717767111929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52403088166853145178074619 78604632250279717767111929)
    ·
      refine ⟨58953474187709788325333947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78604632250279717767111929 58953474187709788325333947)
      ·
        refine ⟨88430211281564682488000921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58953474187709788325333947 88430211281564682488000921)
        ·
          refine ⟨66322658461173511866000691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88430211281564682488000921 66322658461173511866000691)
          ·
            refine ⟨99483987691760267799001037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66322658461173511866000691 99483987691760267799001037)
            ·
              refine ⟨37306495384410100424625389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99483987691760267799001037 37306495384410100424625389)
              ·
                refine ⟨13989935769153787659234521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37306495384410100424625389 13989935769153787659234521)
                ·
                  refine ⟨10492451826865340744425891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13989935769153787659234521 10492451826865340744425891)
                  ·
                    refine ⟨15738677740298011116638837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10492451826865340744425891 15738677740298011116638837)
                    ·
                      refine ⟨1475501038152938542184891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15738677740298011116638837 1475501038152938542184891)
                      ·
                        rfl

theorem cell23_2873528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_2873528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873528 prefixEnd_2873528 := by exact prefixLift 2873528
  have htrace : WordTrace (prefixWord ++ tailWord_2873528) baseStart_2873528 baseEnd_2873528 := by
    simpa [prefixWord, tailWord_2873528, baseEnd_2873528] using wordTrace_append hprefix tailTrace_2873528
  have hstable : (prefixWord ++ tailWord_2873528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873528).length < 2 ^ (prefixWord ++ tailWord_2873528).sum := by decide
  have hdescent : baseEnd_2873528 < baseStart_2873528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873529 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 1, 3, 2]
def baseStart_2873529 : Nat := 118140960795 + 2873529 * 2 ^ 59
def prefixEnd_2873529 : Nat := 4983230072969 + 3 ^ 40 * 2873529 * 2
def baseEnd_2873529 : Nat := 1475501551633593038272387

theorem tailTrace_2873529 : CollatzResearch.WordTrace tailWord_2873529 prefixEnd_2873529 1475501551633593038272387 := by
  unfold tailWord_2873529
  simp only [CollatzResearch.WordTrace]
  refine ⟨104806212806702667526935641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69870808537801778351290427 104806212806702667526935641)
  ·
    refine ⟨78604659605027000645201731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104806212806702667526935641 78604659605027000645201731)
    ·
      refine ⟨117906989407540500967802597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78604659605027000645201731 117906989407540500967802597)
      ·
        refine ⟨22107560513913843931462987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117906989407540500967802597 22107560513913843931462987)
        ·
          refine ⟨33161340770870765897194481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22107560513913843931462987 33161340770870765897194481)
          ·
            refine ⟨24871005578153074422895861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33161340770870765897194481 24871005578153074422895861)
            ·
              refine ⟨2331656772951850727146487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24871005578153074422895861 2331656772951850727146487)
              ·
                refine ⟨3497485159427776090719731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331656772951850727146487 3497485159427776090719731)
                ·
                  refine ⟨5246227739141664136079597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497485159427776090719731 5246227739141664136079597)
                  ·
                    refine ⟨1967335402178124051029849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5246227739141664136079597 1967335402178124051029849)
                    ·
                      refine ⟨1475501551633593038272387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967335402178124051029849 1475501551633593038272387)
                      ·
                        rfl

theorem cell23_2873529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_2873529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873529 prefixEnd_2873529 := by exact prefixLift 2873529
  have htrace : WordTrace (prefixWord ++ tailWord_2873529) baseStart_2873529 baseEnd_2873529 := by
    simpa [prefixWord, tailWord_2873529, baseEnd_2873529] using wordTrace_append hprefix tailTrace_2873529
  have hstable : (prefixWord ++ tailWord_2873529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873529).length < 2 ^ (prefixWord ++ tailWord_2873529).sum := by decide
  have hdescent : baseEnd_2873529 < baseStart_2873529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873537 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2873537 : Nat := 118140960795 + 2873537 * 2 ^ 59
def prefixEnd_2873537 : Nat := 4983230072969 + 3 ^ 40 * 2873537 * 2
def baseEnd_2873537 : Nat := 1475505659478829006972351

theorem tailTrace_2873537 : CollatzResearch.WordTrace tailWord_2873537 prefixEnd_2873537 1475505659478829006972351 := by
  unfold tailWord_2873537
  simp only [CollatzResearch.WordTrace]
  refine ⟨104806504590673684893226865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69871003060449123262151243 104806504590673684893226865)
  ·
    refine ⟨78604878443005263669920149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104806504590673684893226865 78604878443005263669920149)
    ·
      refine ⟨3684603677015871734527507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78604878443005263669920149 3684603677015871734527507)
      ·
        refine ⟨5526905515523807601791261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684603677015871734527507 5526905515523807601791261)
        ·
          refine ⟨2072589568321427850671723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5526905515523807601791261 2072589568321427850671723)
          ·
            refine ⟨3108884352482141776007585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072589568321427850671723 3108884352482141776007585)
            ·
              refine ⟨2331663264361606332005689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108884352482141776007585 2331663264361606332005689)
              ·
                refine ⟨1748747448271204749004267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331663264361606332005689 1748747448271204749004267)
                ·
                  refine ⟨2623121172406807123506401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748747448271204749004267 2623121172406807123506401)
                  ·
                    refine ⟨1967340879305105342629801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2623121172406807123506401 1967340879305105342629801)
                    ·
                      refine ⟨1475505659478829006972351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967340879305105342629801 1475505659478829006972351)
                      ·
                        rfl

theorem cell23_2873537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2873537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873537 prefixEnd_2873537 := by exact prefixLift 2873537
  have htrace : WordTrace (prefixWord ++ tailWord_2873537) baseStart_2873537 baseEnd_2873537 := by
    simpa [prefixWord, tailWord_2873537, baseEnd_2873537] using wordTrace_append hprefix tailTrace_2873537
  have hstable : (prefixWord ++ tailWord_2873537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873537).length < 2 ^ (prefixWord ++ tailWord_2873537).sum := by decide
  have hdescent : baseEnd_2873537 < baseStart_2873537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873565 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 9]
def baseStart_2873565 : Nat := 118140960795 + 2873565 * 2 ^ 59
def prefixEnd_2873565 : Nat := 4983230072969 + 3 ^ 40 * 2873565 * 2
def baseEnd_2873565 : Nat := 163946670770794988602469

theorem tailTrace_2873565 : CollatzResearch.WordTrace tailWord_2873565 prefixEnd_2873565 163946670770794988602469 := by
  unfold tailWord_2873565
  simp only [CollatzResearch.WordTrace]
  refine ⟨104807525834572245675246149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69871683889714830450164099 104807525834572245675246149)
  ·
    refine ⟨19651411093982296064108653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104807525834572245675246149 19651411093982296064108653)
    ·
      refine ⟨7369279160243361024040745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19651411093982296064108653 7369279160243361024040745)
      ·
        refine ⟨5526959370182520768030559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7369279160243361024040745 5526959370182520768030559)
        ·
          refine ⟨8290439055273781152045839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526959370182520768030559 8290439055273781152045839)
          ·
            refine ⟨12435658582910671728068759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8290439055273781152045839 12435658582910671728068759)
            ·
              refine ⟨18653487874366007592103139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435658582910671728068759 18653487874366007592103139)
              ·
                refine ⟨27980231811549011388154709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18653487874366007592103139 27980231811549011388154709)
                ·
                  refine ⟨163946670770794988602469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27980231811549011388154709 163946670770794988602469)
                  ·
                    rfl

theorem cell23_2873565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_2873565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873565 prefixEnd_2873565 := by exact prefixLift 2873565
  have htrace : WordTrace (prefixWord ++ tailWord_2873565) baseStart_2873565 baseEnd_2873565 := by
    simpa [prefixWord, tailWord_2873565, baseEnd_2873565] using wordTrace_append hprefix tailTrace_2873565
  have hstable : (prefixWord ++ tailWord_2873565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873565).length < 2 ^ (prefixWord ++ tailWord_2873565).sum := by decide
  have hdescent : baseEnd_2873565 < baseStart_2873565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873635 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 3]
def baseStart_2873635 : Nat := 118140960795 + 2873635 * 2 ^ 59
def prefixEnd_2873635 : Nat := 4983230072969 + 3 ^ 40 * 2873635 * 2
def baseEnd_2873635 : Nat := 1475555980582969623546899

theorem tailTrace_2873635 : CollatzResearch.WordTrace tailWord_2873635 prefixEnd_2873635 1475555980582969623546899 := by
  unfold tailWord_2873635
  simp only [CollatzResearch.WordTrace]
  refine ⟨104810078944318647630294359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69873385962879098420196239 104810078944318647630294359)
  ·
    refine ⟨157215118416477971445441539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104810078944318647630294359 157215118416477971445441539)
    ·
      refine ⟨235822677624716957168162309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157215118416477971445441539 235822677624716957168162309)
      ·
        refine ⟨44216752054634429469030433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235822677624716957168162309 44216752054634429469030433)
        ·
          refine ⟨33162564040975822101772825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44216752054634429469030433 33162564040975822101772825)
          ·
            refine ⟨24871923030731866576329619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33162564040975822101772825 24871923030731866576329619)
            ·
              refine ⟨37307884546097799864494429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24871923030731866576329619 37307884546097799864494429)
              ·
                refine ⟨13990456704786674949185411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37307884546097799864494429 13990456704786674949185411)
                ·
                  refine ⟨20985685057180012423778117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13990456704786674949185411 20985685057180012423778117)
                  ·
                    refine ⟨3934815948221252329458397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20985685057180012423778117 3934815948221252329458397)
                    ·
                      refine ⟨1475555980582969623546899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934815948221252329458397 1475555980582969623546899)
                      ·
                        rfl

theorem cell23_2873635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_2873635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873635 prefixEnd_2873635 := by exact prefixLift 2873635
  have htrace : WordTrace (prefixWord ++ tailWord_2873635) baseStart_2873635 baseEnd_2873635 := by
    simpa [prefixWord, tailWord_2873635, baseEnd_2873635] using wordTrace_append hprefix tailTrace_2873635
  have hstable : (prefixWord ++ tailWord_2873635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873635).length < 2 ^ (prefixWord ++ tailWord_2873635).sum := by decide
  have hdescent : baseEnd_2873635 < baseStart_2873635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873672 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 6]
def baseStart_2873672 : Nat := 118140960795 + 2873672 * 2 ^ 59
def prefixEnd_2873672 : Nat := 4983230072969 + 3 ^ 40 * 2873672 * 2
def baseEnd_2873672 : Nat := 163952775485242886531581

theorem tailTrace_2873672 : CollatzResearch.WordTrace tailWord_2873672 prefixEnd_2873672 163952775485242886531581 := by
  unfold tailWord_2873672
  simp only [CollatzResearch.WordTrace]
  refine ⟨52405714222592301474695635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69874285630123068632927513 52405714222592301474695635)
  ·
    refine ⟨78608571333888452212043453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52405714222592301474695635 78608571333888452212043453)
    ·
      refine ⟨29478214250208169579516295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78608571333888452212043453 29478214250208169579516295)
      ·
        refine ⟨44217321375312254369274443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29478214250208169579516295 44217321375312254369274443)
        ·
          refine ⟨66325982062968381553911665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44217321375312254369274443 66325982062968381553911665)
          ·
            refine ⟨49744486547226286165433749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66325982062968381553911665 49744486547226286165433749)
            ·
              refine ⟨2331772806901232164004707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49744486547226286165433749 2331772806901232164004707)
              ·
                refine ⟨3497659210351848246007061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331772806901232164004707 3497659210351848246007061)
                ·
                  refine ⟨163952775485242886531581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3497659210351848246007061 163952775485242886531581)
                  ·
                    rfl

theorem cell23_2873672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 6].length) (baseStart_2873672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873672 prefixEnd_2873672 := by exact prefixLift 2873672
  have htrace : WordTrace (prefixWord ++ tailWord_2873672) baseStart_2873672 baseEnd_2873672 := by
    simpa [prefixWord, tailWord_2873672, baseEnd_2873672] using wordTrace_append hprefix tailTrace_2873672
  have hstable : (prefixWord ++ tailWord_2873672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873672).length < 2 ^ (prefixWord ++ tailWord_2873672).sum := by decide
  have hdescent : baseEnd_2873672 < baseStart_2873672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873709 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_2873709 : Nat := 118140960795 + 2873709 * 2 ^ 59
def prefixEnd_2873709 : Nat := 4983230072969 + 3 ^ 40 * 2873709 * 2
def baseEnd_2873709 : Nat := 1475593978151402334021559

theorem tailTrace_2873709 : CollatzResearch.WordTrace tailWord_2873709 prefixEnd_2873709 1475593978151402334021559 := by
  unfold tailWord_2873709
  simp only [CollatzResearch.WordTrace]
  refine ⟨104812777946050558268488181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69875185297367038845658787 104812777946050558268488181)
  ·
    refine ⟨9826197932442239837670767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104812777946050558268488181 9826197932442239837670767)
    ·
      refine ⟨14739296898663359756506151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826197932442239837670767 14739296898663359756506151)
      ·
        refine ⟨22108945347995039634759227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14739296898663359756506151 22108945347995039634759227)
        ·
          refine ⟨33163418021992559452138841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22108945347995039634759227 33163418021992559452138841)
          ·
            refine ⟨24872563516494419589104131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33163418021992559452138841 24872563516494419589104131)
            ·
              refine ⟨37308845274741629383656197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24872563516494419589104131 37308845274741629383656197)
              ·
                refine ⟨6995408489014055509435537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37308845274741629383656197 6995408489014055509435537)
                ·
                  refine ⟨5246556366760541632076653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6995408489014055509435537 5246556366760541632076653)
                  ·
                    refine ⟨1967458637535203112028745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5246556366760541632076653 1967458637535203112028745)
                    ·
                      refine ⟨1475593978151402334021559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967458637535203112028745 1475593978151402334021559)
                      ·
                        rfl

theorem cell23_2873709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_2873709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873709 prefixEnd_2873709 := by exact prefixLift 2873709
  have htrace : WordTrace (prefixWord ++ tailWord_2873709) baseStart_2873709 baseEnd_2873709 := by
    simpa [prefixWord, tailWord_2873709, baseEnd_2873709] using wordTrace_append hprefix tailTrace_2873709
  have hstable : (prefixWord ++ tailWord_2873709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873709).length < 2 ^ (prefixWord ++ tailWord_2873709).sum := by decide
  have hdescent : baseEnd_2873709 < baseStart_2873709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873732 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2873732 : Nat := 118140960795 + 2873732 * 2 ^ 59
def prefixEnd_2873732 : Nat := 4983230072969 + 3 ^ 40 * 2873732 * 2
def baseEnd_2873732 : Nat := 491868596068818581344651

theorem tailTrace_2873732 : CollatzResearch.WordTrace tailWord_2873732 prefixEnd_2873732 491868596068818581344651 := by
  unfold tailWord_2873732
  simp only [CollatzResearch.WordTrace]
  refine ⟨52406808412483616598287725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69875744549978155464383633 52406808412483616598287725)
  ·
    refine ⟨19652553154681356224357897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52406808412483616598287725 19652553154681356224357897)
    ·
      refine ⟨14739414866011017168268423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19652553154681356224357897 14739414866011017168268423)
      ·
        refine ⟨22109122299016525752402635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14739414866011017168268423 22109122299016525752402635)
        ·
          refine ⟨33163683448524788628603953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22109122299016525752402635 33163683448524788628603953)
          ·
            refine ⟨24872762586393591471452965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33163683448524788628603953 24872762586393591471452965)
            ·
              refine ⟨4663642984948798400897431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24872762586393591471452965 4663642984948798400897431)
              ·
                refine ⟨6995464477423197601346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663642984948798400897431 6995464477423197601346147)
                ·
                  refine ⟨10493196716134796402019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6995464477423197601346147 10493196716134796402019221)
                  ·
                    refine ⟨491868596068818581344651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10493196716134796402019221 491868596068818581344651)
                    ·
                      rfl

theorem cell23_2873732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2873732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873732 prefixEnd_2873732 := by exact prefixLift 2873732
  have htrace : WordTrace (prefixWord ++ tailWord_2873732) baseStart_2873732 baseEnd_2873732 := by
    simpa [prefixWord, tailWord_2873732, baseEnd_2873732] using wordTrace_append hprefix tailTrace_2873732
  have hstable : (prefixWord ++ tailWord_2873732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873732).length < 2 ^ (prefixWord ++ tailWord_2873732).sum := by decide
  have hdescent : baseEnd_2873732 < baseStart_2873732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873739 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 5, 2, 2]
def baseStart_2873739 : Nat := 118140960795 + 2873739 * 2 ^ 59
def prefixEnd_2873739 : Nat := 4983230072969 + 3 ^ 40 * 2873739 * 2
def baseEnd_2873739 : Nat := 1475609382571037216646421

theorem tailTrace_2873739 : CollatzResearch.WordTrace tailWord_2873739 prefixEnd_2873739 1475609382571037216646421 := by
  unfold tailWord_2873739
  simp only [CollatzResearch.WordTrace]
  refine ⟨104813872135941873392080271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69875914757294582261386847 104813872135941873392080271)
  ·
    refine ⟨157220808203912810088120407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104813872135941873392080271 157220808203912810088120407)
    ·
      refine ⟨235831212305869215132180611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157220808203912810088120407 235831212305869215132180611)
      ·
        refine ⟨353746818458803822698270917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235831212305869215132180611 353746818458803822698270917)
        ·
          refine ⟨66327528461025716755925797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353746818458803822698270917 66327528461025716755925797)
          ·
            refine ⟨12436411586442321891736087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66327528461025716755925797 12436411586442321891736087)
            ·
              refine ⟨18654617379663482837604131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12436411586442321891736087 18654617379663482837604131)
              ·
                refine ⟨27981926069495224256406197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18654617379663482837604131 27981926069495224256406197)
                ·
                  refine ⟨2623305569015177274038081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27981926069495224256406197 2623305569015177274038081)
                  ·
                    refine ⟨1967479176761382955528561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2623305569015177274038081 1967479176761382955528561)
                    ·
                      refine ⟨1475609382571037216646421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967479176761382955528561 1475609382571037216646421)
                      ·
                        rfl

theorem cell23_2873739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 2, 2].length) (baseStart_2873739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873739 prefixEnd_2873739 := by exact prefixLift 2873739
  have htrace : WordTrace (prefixWord ++ tailWord_2873739) baseStart_2873739 baseEnd_2873739 := by
    simpa [prefixWord, tailWord_2873739, baseEnd_2873739] using wordTrace_append hprefix tailTrace_2873739
  have hstable : (prefixWord ++ tailWord_2873739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873739).length < 2 ^ (prefixWord ++ tailWord_2873739).sum := by decide
  have hdescent : baseEnd_2873739 < baseStart_2873739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873759 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2873759 : Nat := 118140960795 + 2873759 * 2 ^ 59
def prefixEnd_2873759 : Nat := 4983230072969 + 3 ^ 40 * 2873759 * 2
def baseEnd_2873759 : Nat := 1475619652184127138396329

theorem tailTrace_2873759 : CollatzResearch.WordTrace tailWord_2873759 prefixEnd_2873759 1475619652184127138396329 := by
  unfold tailWord_2873759
  simp only [CollatzResearch.WordTrace]
  refine ⟨104814601595869416807808331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69876401063912944538538887 104814601595869416807808331)
  ·
    refine ⟨157221902393804125211712497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104814601595869416807808331 157221902393804125211712497)
    ·
      refine ⟨117916426795353093908784373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157221902393804125211712497 117916426795353093908784373)
      ·
        refine ⟨11054665012064352553948535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117916426795353093908784373 11054665012064352553948535)
        ·
          refine ⟨16581997518096528830922803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11054665012064352553948535 16581997518096528830922803)
          ·
            refine ⟨24872996277144793246384205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16581997518096528830922803 24872996277144793246384205)
            ·
              refine ⟨9327373603929297467394077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24872996277144793246384205 9327373603929297467394077)
              ·
                refine ⟨3497765101473486550272779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9327373603929297467394077 3497765101473486550272779)
                ·
                  refine ⟨5246647652210229825409169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497765101473486550272779 5246647652210229825409169)
                  ·
                    refine ⟨3934985739157672369056877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5246647652210229825409169 3934985739157672369056877)
                    ·
                      refine ⟨1475619652184127138396329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3934985739157672369056877 1475619652184127138396329)
                      ·
                        rfl

theorem cell23_2873759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2873759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873759 prefixEnd_2873759 := by exact prefixLift 2873759
  have htrace : WordTrace (prefixWord ++ tailWord_2873759) baseStart_2873759 baseEnd_2873759 := by
    simpa [prefixWord, tailWord_2873759, baseEnd_2873759] using wordTrace_append hprefix tailTrace_2873759
  have hstable : (prefixWord ++ tailWord_2873759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873759).length < 2 ^ (prefixWord ++ tailWord_2873759).sum := by decide
  have hdescent : baseEnd_2873759 < baseStart_2873759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873789 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2873789 : Nat := 118140960795 + 2873789 * 2 ^ 59
def prefixEnd_2873789 : Nat := 4983230072969 + 3 ^ 40 * 2873789 * 2
def baseEnd_2873789 : Nat := 1475635056603762021021191

theorem tailTrace_2873789 : CollatzResearch.WordTrace tailWord_2873789 prefixEnd_2873789 1475635056603762021021191 := by
  unfold tailWord_2873789
  simp only [CollatzResearch.WordTrace]
  refine ⟨104815695785760731931400421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69877130523840487954266947 104815695785760731931400421)
  ·
    refine ⟨19652942959830137237137579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104815695785760731931400421 19652942959830137237137579)
    ·
      refine ⟨29479414439745205855706369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19652942959830137237137579 29479414439745205855706369)
      ·
        refine ⟨22109560829808904391779777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29479414439745205855706369 22109560829808904391779777)
        ·
          refine ⟨16582170622356678293834833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22109560829808904391779777 16582170622356678293834833)
          ·
            refine ⟨12436627966767508720376125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16582170622356678293834833 12436627966767508720376125)
            ·
              refine ⟨4663735487537815770141047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12436627966767508720376125 4663735487537815770141047)
              ·
                refine ⟨6995603231306723655211571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663735487537815770141047 6995603231306723655211571)
                ·
                  refine ⟨10493404846960085482817357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6995603231306723655211571 10493404846960085482817357)
                  ·
                    refine ⟨3935026817610032056056509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10493404846960085482817357 3935026817610032056056509)
                    ·
                      refine ⟨1475635056603762021021191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935026817610032056056509 1475635056603762021021191)
                      ·
                        rfl

theorem cell23_2873789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2873789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873789 prefixEnd_2873789 := by exact prefixLift 2873789
  have htrace : WordTrace (prefixWord ++ tailWord_2873789) baseStart_2873789 baseEnd_2873789 := by
    simpa [prefixWord, tailWord_2873789, baseEnd_2873789] using wordTrace_append hprefix tailTrace_2873789
  have hstable : (prefixWord ++ tailWord_2873789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873789).length < 2 ^ (prefixWord ++ tailWord_2873789).sum := by decide
  have hdescent : baseEnd_2873789 < baseStart_2873789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873796 : List Nat := [2, 3, 3, 2, 2, 2, 2, 7]
def baseStart_2873796 : Nat := 118140960795 + 2873796 * 2 ^ 59
def prefixEnd_2873796 : Nat := 4983230072969 + 3 ^ 40 * 2873796 * 2
def baseEnd_2873796 : Nat := 54653283369197907171617

theorem tailTrace_2873796 : CollatzResearch.WordTrace tailWord_2873796 prefixEnd_2873796 54653283369197907171617 := by
  unfold tailWord_2873796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52407975548367686063452621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69877300731156914751270161 52407975548367686063452621)
  ·
    refine ⟨19652990830637882273794733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52407975548367686063452621 19652990830637882273794733)
    ·
      refine ⟨7369871561489205852673025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19652990830637882273794733 7369871561489205852673025)
      ·
        refine ⟨5527403671116904389504769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7369871561489205852673025 5527403671116904389504769)
        ·
          refine ⟨4145552753337678292128577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5527403671116904389504769 4145552753337678292128577)
          ·
            refine ⟨3109164565003258719096433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145552753337678292128577 3109164565003258719096433)
            ·
              refine ⟨2331873423752444039322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109164565003258719096433 2331873423752444039322325)
              ·
                refine ⟨54653283369197907171617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2331873423752444039322325 54653283369197907171617)
                ·
                  rfl

theorem cell23_2873796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 7].length) (baseStart_2873796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873796 prefixEnd_2873796 := by exact prefixLift 2873796
  have htrace : WordTrace (prefixWord ++ tailWord_2873796) baseStart_2873796 baseEnd_2873796 := by
    simpa [prefixWord, tailWord_2873796, baseEnd_2873796] using wordTrace_append hprefix tailTrace_2873796
  have hstable : (prefixWord ++ tailWord_2873796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873796).length < 2 ^ (prefixWord ++ tailWord_2873796).sum := by decide
  have hdescent : baseEnd_2873796 < baseStart_2873796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873846 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_2873846 : Nat := 118140960795 + 2873846 * 2 ^ 59
def prefixEnd_2873846 : Nat := 4983230072969 + 3 ^ 40 * 2873846 * 2
def baseEnd_2873846 : Nat := 1475664325001068298008429

theorem tailTrace_2873846 : CollatzResearch.WordTrace tailWord_2873846 prefixEnd_2873846 1475664325001068298008429 := by
  unfold tailWord_2873846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551110921659639416639087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69878516497702820444150261 6551110921659639416639087)
  ·
    refine ⟨9826666382489459124958631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6551110921659639416639087 9826666382489459124958631)
    ·
      refine ⟨14739999573734188687437947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826666382489459124958631 14739999573734188687437947)
      ·
        refine ⟨22109999360601283031156921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14739999573734188687437947 22109999360601283031156921)
        ·
          refine ⟨16582499520450962273367691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22109999360601283031156921 16582499520450962273367691)
          ·
            refine ⟨24873749280676443410051537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582499520450962273367691 24873749280676443410051537)
            ·
              refine ⟨18655311960507332557538653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24873749280676443410051537 18655311960507332557538653)
              ·
                refine ⟨6995741985190249709076995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18655311960507332557538653 6995741985190249709076995)
                ·
                  refine ⟨10493612977785374563615493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6995741985190249709076995 10493612977785374563615493)
                  ·
                    refine ⟨1967552433334757730677905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10493612977785374563615493 1967552433334757730677905)
                    ·
                      refine ⟨1475664325001068298008429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967552433334757730677905 1475664325001068298008429)
                      ·
                        rfl

theorem cell23_2873846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_2873846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873846 prefixEnd_2873846 := by exact prefixLift 2873846
  have htrace : WordTrace (prefixWord ++ tailWord_2873846) baseStart_2873846 baseEnd_2873846 := by
    simpa [prefixWord, tailWord_2873846, baseEnd_2873846] using wordTrace_append hprefix tailTrace_2873846
  have hstable : (prefixWord ++ tailWord_2873846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873846).length < 2 ^ (prefixWord ++ tailWord_2873846).sum := by decide
  have hdescent : baseEnd_2873846 < baseStart_2873846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873889 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2873889 : Nat := 118140960795 + 2873889 * 2 ^ 59
def prefixEnd_2873889 : Nat := 4983230072969 + 3 ^ 40 * 2873889 * 2
def baseEnd_2873889 : Nat := 1475686404669211629770731

theorem tailTrace_2873889 : CollatzResearch.WordTrace tailWord_2873889 prefixEnd_2873889 1475686404669211629770731 := by
  unfold tailWord_2873889
  simp only [CollatzResearch.WordTrace]
  refine ⟨104819343085398449010040721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69879562056932299340027147 104819343085398449010040721)
  ·
    refine ⟨78614507314048836757530541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104819343085398449010040721 78614507314048836757530541)
    ·
      refine ⟨29480440242768313784073953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78614507314048836757530541 29480440242768313784073953)
      ·
        refine ⟨22110330182076235338055465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29480440242768313784073953 22110330182076235338055465)
        ·
          refine ⟨16582747636557176503541599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22110330182076235338055465 16582747636557176503541599)
          ·
            refine ⟨24874121454835764755312399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582747636557176503541599 24874121454835764755312399)
            ·
              refine ⟨37311182182253647132968599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24874121454835764755312399 37311182182253647132968599)
              ·
                refine ⟨55966773273380470699452899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37311182182253647132968599 55966773273380470699452899)
                ·
                  refine ⟨83950159910070706049179349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55966773273380470699452899 83950159910070706049179349)
                  ·
                    refine ⟨1967581872892282173027641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83950159910070706049179349 1967581872892282173027641)
                    ·
                      refine ⟨1475686404669211629770731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967581872892282173027641 1475686404669211629770731)
                      ·
                        rfl

theorem cell23_2873889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2873889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873889 prefixEnd_2873889 := by exact prefixLift 2873889
  have htrace : WordTrace (prefixWord ++ tailWord_2873889) baseStart_2873889 baseEnd_2873889 := by
    simpa [prefixWord, tailWord_2873889, baseEnd_2873889] using wordTrace_append hprefix tailTrace_2873889
  have hstable : (prefixWord ++ tailWord_2873889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873889).length < 2 ^ (prefixWord ++ tailWord_2873889).sum := by decide
  have hdescent : baseEnd_2873889 < baseStart_2873889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873896 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2873896 : Nat := 118140960795 + 2873896 * 2 ^ 59
def prefixEnd_2873896 : Nat := 4983230072969 + 3 ^ 40 * 2873896 * 2
def baseEnd_2873896 : Nat := 1475689999033793102383199

theorem tailTrace_2873896 : CollatzResearch.WordTrace tailWord_2873896 prefixEnd_2873896 1475689999033793102383199 := by
  unfold tailWord_2873896
  simp only [CollatzResearch.WordTrace]
  refine ⟨52409799198186544602772771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69879732264248726137030361 52409799198186544602772771)
  ·
    refine ⟨78614698797279816904159157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52409799198186544602772771 78614698797279816904159157)
    ·
      refine ⟨7370128012244982834764921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78614698797279816904159157 7370128012244982834764921)
      ·
        refine ⟨5527596009183737126073691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7370128012244982834764921 5527596009183737126073691)
        ·
          refine ⟨8291394013775605689110537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527596009183737126073691 8291394013775605689110537)
          ·
            refine ⟨6218545510331704266832903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8291394013775605689110537 6218545510331704266832903)
            ·
              refine ⟨9327818265497556400249355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218545510331704266832903 9327818265497556400249355)
              ·
                refine ⟨13991727398246334600374033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9327818265497556400249355 13991727398246334600374033)
                ·
                  refine ⟨10493795548684750950280525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13991727398246334600374033 10493795548684750950280525)
                  ·
                    refine ⟨3935173330756781606355197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10493795548684750950280525 3935173330756781606355197)
                    ·
                      refine ⟨1475689999033793102383199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935173330756781606355197 1475689999033793102383199)
                      ·
                        rfl

theorem cell23_2873896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2873896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873896 prefixEnd_2873896 := by exact prefixLift 2873896
  have htrace : WordTrace (prefixWord ++ tailWord_2873896) baseStart_2873896 baseEnd_2873896 := by
    simpa [prefixWord, tailWord_2873896, baseEnd_2873896] using wordTrace_append hprefix tailTrace_2873896
  have hstable : (prefixWord ++ tailWord_2873896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873896).length < 2 ^ (prefixWord ++ tailWord_2873896).sum := by decide
  have hdescent : baseEnd_2873896 < baseStart_2873896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873916 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_2873916 : Nat := 118140960795 + 2873916 * 2 ^ 59
def prefixEnd_2873916 : Nat := 4983230072969 + 3 ^ 40 * 2873916 * 2
def baseEnd_2873916 : Nat := 491900089548961008044369

theorem tailTrace_2873916 : CollatzResearch.WordTrace tailWord_2873916 prefixEnd_2873916 491900089548961008044369 := by
  unfold tailWord_2873916
  simp only [CollatzResearch.WordTrace]
  refine ⟨52410163928150316310636801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69880218570867088414182401 52410163928150316310636801)
  ·
    refine ⟨39307622946112737232977601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52410163928150316310636801 39307622946112737232977601)
    ·
      refine ⟨29480717209584552924733201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39307622946112737232977601 29480717209584552924733201)
      ·
        refine ⟨22110537907188414693549901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29480717209584552924733201 22110537907188414693549901)
        ·
          refine ⟨8291451715195655510081213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22110537907188414693549901 8291451715195655510081213)
          ·
            refine ⟨3109294393198370816280455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8291451715195655510081213 3109294393198370816280455)
            ·
              refine ⟨4663941589797556224420683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109294393198370816280455 4663941589797556224420683)
              ·
                refine ⟨6995912384696334336631025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663941589797556224420683 6995912384696334336631025)
                ·
                  refine ⟨5246934288522250752473269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6995912384696334336631025 5246934288522250752473269)
                  ·
                    refine ⟨491900089548961008044369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5246934288522250752473269 491900089548961008044369)
                    ·
                      rfl

theorem cell23_2873916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_2873916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873916 prefixEnd_2873916 := by exact prefixLift 2873916
  have htrace : WordTrace (prefixWord ++ tailWord_2873916) baseStart_2873916 baseEnd_2873916 := by
    simpa [prefixWord, tailWord_2873916, baseEnd_2873916] using wordTrace_append hprefix tailTrace_2873916
  have hstable : (prefixWord ++ tailWord_2873916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873916).length < 2 ^ (prefixWord ++ tailWord_2873916).sum := by decide
  have hdescent : baseEnd_2873916 < baseStart_2873916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873919 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 6, 2]
def baseStart_2873919 : Nat := 118140960795 + 2873919 * 2 ^ 59
def prefixEnd_2873919 : Nat := 4983230072969 + 3 ^ 40 * 2873919 * 2
def baseEnd_2873919 : Nat := 1475701809088846512395593

theorem tailTrace_2873919 : CollatzResearch.WordTrace tailWord_2873919 prefixEnd_2873919 1475701809088846512395593 := by
  unfold tailWord_2873919
  simp only [CollatzResearch.WordTrace]
  refine ⟨104820437275289764133632811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69880291516859842755755207 104820437275289764133632811)
  ·
    refine ⟨157230655912934646200449217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104820437275289764133632811 157230655912934646200449217)
    ·
      refine ⟨117922991934700984650336913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157230655912934646200449217 117922991934700984650336913)
      ·
        refine ⟨88442243951025738487752685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117922991934700984650336913 88442243951025738487752685)
        ·
          refine ⟨33165841481634651932907257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88442243951025738487752685 33165841481634651932907257)
          ·
            refine ⟨24874381111225988949680443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33165841481634651932907257 24874381111225988949680443)
            ·
              refine ⟨37311571666838983424520665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24874381111225988949680443 37311571666838983424520665)
              ·
                refine ⟨27983678750129237568390499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37311571666838983424520665 27983678750129237568390499)
                ·
                  refine ⟨41975518125193856352585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27983678750129237568390499 41975518125193856352585749)
                  ·
                    refine ⟨1967602412118462016527457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41975518125193856352585749 1967602412118462016527457)
                    ·
                      refine ⟨1475701809088846512395593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967602412118462016527457 1475701809088846512395593)
                      ·
                        rfl

theorem cell23_2873919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_2873919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873919 prefixEnd_2873919 := by exact prefixLift 2873919
  have htrace : WordTrace (prefixWord ++ tailWord_2873919) baseStart_2873919 baseEnd_2873919 := by
    simpa [prefixWord, tailWord_2873919, baseEnd_2873919] using wordTrace_append hprefix tailTrace_2873919
  have hstable : (prefixWord ++ tailWord_2873919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873919).length < 2 ^ (prefixWord ++ tailWord_2873919).sum := by decide
  have hdescent : baseEnd_2873919 < baseStart_2873919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873932 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2873932 : Nat := 118140960795 + 2873932 * 2 ^ 59
def prefixEnd_2873932 : Nat := 4983230072969 + 3 ^ 40 * 2873932 * 2
def baseEnd_2873932 : Nat := 1475708484337354961533033

theorem tailTrace_2873932 : CollatzResearch.WordTrace tailWord_2873932 prefixEnd_2873932 1475708484337354961533033 := by
  unfold tailWord_2873932
  simp only [CollatzResearch.WordTrace]
  refine ⟨52410455712121333676928025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69880607616161778235904033 52410455712121333676928025)
  ·
    refine ⟨39307841784091000257696019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52410455712121333676928025 39307841784091000257696019)
    ·
      refine ⟨58961762676136500386544029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39307841784091000257696019 58961762676136500386544029)
      ·
        refine ⟨22110661003551187644954011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58961762676136500386544029 22110661003551187644954011)
        ·
          refine ⟨33165991505326781467431017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22110661003551187644954011 33165991505326781467431017)
          ·
            refine ⟨24874493628995086100573263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33165991505326781467431017 24874493628995086100573263)
            ·
              refine ⟨37311740443492629150859895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24874493628995086100573263 37311740443492629150859895)
              ·
                refine ⟨55967610665238943726289843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37311740443492629150859895 55967610665238943726289843)
                ·
                  refine ⟨83951415997858415589434765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55967610665238943726289843 83951415997858415589434765)
                  ·
                    refine ⟨31481780999196905846038037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83951415997858415589434765 31481780999196905846038037)
                    ·
                      refine ⟨1475708484337354961533033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31481780999196905846038037 1475708484337354961533033)
                      ·
                        rfl

theorem cell23_2873932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2873932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2873932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2873932 prefixEnd_2873932 := by exact prefixLift 2873932
  have htrace : WordTrace (prefixWord ++ tailWord_2873932) baseStart_2873932 baseEnd_2873932 := by
    simpa [prefixWord, tailWord_2873932, baseEnd_2873932] using wordTrace_append hprefix tailTrace_2873932
  have hstable : (prefixWord ++ tailWord_2873932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873932).length < 2 ^ (prefixWord ++ tailWord_2873932).sum := by decide
  have hdescent : baseEnd_2873932 < baseStart_2873932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874009 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2874009 : Nat := 118140960795 + 2874009 * 2 ^ 59
def prefixEnd_2874009 : Nat := 4983230072969 + 3 ^ 40 * 2874009 * 2
def baseEnd_2874009 : Nat := 1475748022347751160270179

theorem tailTrace_2874009 : CollatzResearch.WordTrace tailWord_2874009 prefixEnd_2874009 1475748022347751160270179 := by
  unfold tailWord_2874009
  simp only [CollatzResearch.WordTrace]
  refine ⟨104823719844963709504409081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69882479896642473002939387 104823719844963709504409081)
  ·
    refine ⟨78617789883722782128306811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104823719844963709504409081 78617789883722782128306811)
    ·
      refine ⟨117926684825584173192460217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78617789883722782128306811 117926684825584173192460217)
      ·
        refine ⟨88445013619188129894345163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117926684825584173192460217 88445013619188129894345163)
        ·
          refine ⟨132667520428782194841517745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88445013619188129894345163 132667520428782194841517745)
          ·
            refine ⟨99500640321586646131138309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132667520428782194841517745 99500640321586646131138309)
            ·
              refine ⟨18656370060297496149588433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99500640321586646131138309 18656370060297496149588433)
              ·
                refine ⟨13992277545223122112191325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18656370060297496149588433 13992277545223122112191325)
                ·
                  refine ⟨5247104079458670792071747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13992277545223122112191325 5247104079458670792071747)
                  ·
                    refine ⟨7870656119188006188107621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5247104079458670792071747 7870656119188006188107621)
                    ·
                      refine ⟨1475748022347751160270179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7870656119188006188107621 1475748022347751160270179)
                      ·
                        rfl

theorem cell23_2874009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2874009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874009 prefixEnd_2874009 := by exact prefixLift 2874009
  have htrace : WordTrace (prefixWord ++ tailWord_2874009) baseStart_2874009 baseEnd_2874009 := by
    simpa [prefixWord, tailWord_2874009, baseEnd_2874009] using wordTrace_append hprefix tailTrace_2874009
  have hstable : (prefixWord ++ tailWord_2874009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874009).length < 2 ^ (prefixWord ++ tailWord_2874009).sum := by decide
  have hdescent : baseEnd_2874009 < baseStart_2874009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874010 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_2874010 : Nat := 118140960795 + 2874010 * 2 ^ 59
def prefixEnd_2874010 : Nat := 4983230072969 + 3 ^ 40 * 2874010 * 2
def baseEnd_2874010 : Nat := 163972059536489517373075

theorem tailTrace_2874010 : CollatzResearch.WordTrace tailWord_2874010 prefixEnd_2874010 163972059536489517373075 := by
  unfold tailWord_2874010
  simp only [CollatzResearch.WordTrace]
  refine ⟨26205939079490021668798871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69882504211973391116796989 26205939079490021668798871)
  ·
    refine ⟨39308908619235032503198307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26205939079490021668798871 39308908619235032503198307)
    ·
      refine ⟨58963362928852548754797461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39308908619235032503198307 58963362928852548754797461)
      ·
        refine ⟨2763907637289963222881131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58963362928852548754797461 2763907637289963222881131)
        ·
          refine ⟨4145861455934944834321697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763907637289963222881131 4145861455934944834321697)
          ·
            refine ⟨3109396091951208625741273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145861455934944834321697 3109396091951208625741273)
            ·
              refine ⟨2332047068963406469305955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109396091951208625741273 2332047068963406469305955)
              ·
                refine ⟨3498070603445109703958933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332047068963406469305955 3498070603445109703958933)
                ·
                  refine ⟨163972059536489517373075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3498070603445109703958933 163972059536489517373075)
                  ·
                    rfl

theorem cell23_2874010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_2874010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874010 prefixEnd_2874010 := by exact prefixLift 2874010
  have htrace : WordTrace (prefixWord ++ tailWord_2874010) baseStart_2874010 baseEnd_2874010 := by
    simpa [prefixWord, tailWord_2874010, baseEnd_2874010] using wordTrace_append hprefix tailTrace_2874010
  have hstable : (prefixWord ++ tailWord_2874010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874010).length < 2 ^ (prefixWord ++ tailWord_2874010).sum := by decide
  have hdescent : baseEnd_2874010 < baseStart_2874010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874019 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 6, 4]
def baseStart_2874019 : Nat := 118140960795 + 2874019 * 2 ^ 59
def prefixEnd_2874019 : Nat := 4983230072969 + 3 ^ 40 * 2874019 * 2
def baseEnd_2874019 : Nat := 491917719051432040381711

theorem tailTrace_2874019 : CollatzResearch.WordTrace tailWord_2874019 prefixEnd_2874019 491917719051432040381711 := by
  unfold tailWord_2874019
  simp only [CollatzResearch.WordTrace]
  refine ⟨104824084574927481212273111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69882723049951654141515407 104824084574927481212273111)
  ·
    refine ⟨157236126862391221818409667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104824084574927481212273111 157236126862391221818409667)
    ·
      refine ⟨235854190293586832727614501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157236126862391221818409667 235854190293586832727614501)
      ·
        refine ⟨44222660680047531136427719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235854190293586832727614501 44222660680047531136427719)
        ·
          refine ⟨66333991020071296704641579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44222660680047531136427719 66333991020071296704641579)
          ·
            refine ⟨99500986530106945056962369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66333991020071296704641579 99500986530106945056962369)
            ·
              refine ⟨74625739897580208792721777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99500986530106945056962369 74625739897580208792721777)
              ·
                refine ⟨55969304923185156594541333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74625739897580208792721777 55969304923185156594541333)
                ·
                  refine ⟨2623561168274304215369125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55969304923185156594541333 2623561168274304215369125)
                  ·
                    refine ⟨491917719051432040381711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2623561168274304215369125 491917719051432040381711)
                    ·
                      rfl

theorem cell23_2874019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 4].length) (baseStart_2874019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874019 prefixEnd_2874019 := by exact prefixLift 2874019
  have htrace : WordTrace (prefixWord ++ tailWord_2874019) baseStart_2874019 baseEnd_2874019 := by
    simpa [prefixWord, tailWord_2874019, baseEnd_2874019] using wordTrace_append hprefix tailTrace_2874019
  have hstable : (prefixWord ++ tailWord_2874019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874019).length < 2 ^ (prefixWord ++ tailWord_2874019).sum := by decide
  have hdescent : baseEnd_2874019 < baseStart_2874019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874023 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2874023 : Nat := 118140960795 + 2874023 * 2 ^ 59
def prefixEnd_2874023 : Nat := 4983230072969 + 3 ^ 40 * 2874023 * 2
def baseEnd_2874023 : Nat := 491918403692304701831705

theorem tailTrace_2874023 : CollatzResearch.WordTrace tailWord_2874023 prefixEnd_2874023 491918403692304701831705 := by
  unfold tailWord_2874023
  simp only [CollatzResearch.WordTrace]
  refine ⟨104824230466912989895418723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69882820311275326596945815 104824230466912989895418723)
  ·
    refine ⟨157236345700369484843128085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104824230466912989895418723 157236345700369484843128085)
    ·
      refine ⟨7370453704704819602021629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157236345700369484843128085 7370453704704819602021629)
      ·
        refine ⟨2763920139264307350758111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7370453704704819602021629 2763920139264307350758111)
        ·
          refine ⟨4145880208896461026137167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763920139264307350758111 4145880208896461026137167)
          ·
            refine ⟨6218820313344691539205751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145880208896461026137167 6218820313344691539205751)
            ·
              refine ⟨9328230470017037308808627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218820313344691539205751 9328230470017037308808627)
              ·
                refine ⟨13992345705025555963212941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9328230470017037308808627 13992345705025555963212941)
                ·
                  refine ⟨5247129639384583486204853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13992345705025555963212941 5247129639384583486204853)
                  ·
                    refine ⟨491918403692304701831705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5247129639384583486204853 491918403692304701831705)
                    ·
                      rfl

theorem cell23_2874023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2874023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874023 prefixEnd_2874023 := by exact prefixLift 2874023
  have htrace : WordTrace (prefixWord ++ tailWord_2874023) baseStart_2874023 baseEnd_2874023 := by
    simpa [prefixWord, tailWord_2874023, baseEnd_2874023] using wordTrace_append hprefix tailTrace_2874023
  have hstable : (prefixWord ++ tailWord_2874023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874023).length < 2 ^ (prefixWord ++ tailWord_2874023).sum := by decide
  have hdescent : baseEnd_2874023 < baseStart_2874023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874030 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2874030 : Nat := 118140960795 + 2874030 * 2 ^ 59
def prefixEnd_2874030 : Nat := 4983230072969 + 3 ^ 40 * 2874030 * 2
def baseEnd_2874030 : Nat := 1475758805441495578107583

theorem tailTrace_2874030 : CollatzResearch.WordTrace tailWord_2874030 prefixEnd_2874030 1475758805441495578107583 := by
  unfold tailWord_2874030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103060722235953761365443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69882990518591753393949029 13103060722235953761365443)
  ·
    refine ⟨19654591083353930642048165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13103060722235953761365443 19654591083353930642048165)
    ·
      refine ⟨3685235828128861995384031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19654591083353930642048165 3685235828128861995384031)
      ·
        refine ⟨5527853742193292993076047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685235828128861995384031 5527853742193292993076047)
        ·
          refine ⟨8291780613289939489614071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527853742193292993076047 8291780613289939489614071)
          ·
            refine ⟨12437670919934909234421107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8291780613289939489614071 12437670919934909234421107)
            ·
              refine ⟨18656506379902363851631661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12437670919934909234421107 18656506379902363851631661)
              ·
                refine ⟨6996189892463386444361873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18656506379902363851631661 6996189892463386444361873)
                ·
                  refine ⟨5247142419347539833271405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6996189892463386444361873 5247142419347539833271405)
                  ·
                    refine ⟨1967678407255327437476777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5247142419347539833271405 1967678407255327437476777)
                    ·
                      refine ⟨1475758805441495578107583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967678407255327437476777 1475758805441495578107583)
                      ·
                        rfl

theorem cell23_2874030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2874030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874030 prefixEnd_2874030 := by exact prefixLift 2874030
  have htrace : WordTrace (prefixWord ++ tailWord_2874030) baseStart_2874030 baseEnd_2874030 := by
    simpa [prefixWord, tailWord_2874030, baseEnd_2874030] using wordTrace_append hprefix tailTrace_2874030
  have hstable : (prefixWord ++ tailWord_2874030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874030).length < 2 ^ (prefixWord ++ tailWord_2874030).sum := by decide
  have hdescent : baseEnd_2874030 < baseStart_2874030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874093 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2874093 : Nat := 118140960795 + 2874093 * 2 ^ 59
def prefixEnd_2874093 : Nat := 4983230072969 + 3 ^ 40 * 2874093 * 2
def baseEnd_2874093 : Nat := 1475791154722728831619793

theorem tailTrace_2874093 : CollatzResearch.WordTrace tailWord_2874093 prefixEnd_2874093 1475791154722728831619793 := by
  unfold tailWord_2874093
  simp only [CollatzResearch.WordTrace]
  refine ⟨104826783576659391850466933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69884522384439594566977955 104826783576659391850466933)
  ·
    refine ⟨9827510960311817985981275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104826783576659391850466933 9827510960311817985981275)
    ·
      refine ⟨14741266440467726978971913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9827510960311817985981275 14741266440467726978971913)
      ·
        refine ⟨11055949830350795234228935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14741266440467726978971913 11055949830350795234228935)
        ·
          refine ⟨16583924745526192851343403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055949830350795234228935 16583924745526192851343403)
          ·
            refine ⟨24875887118289289277015105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16583924745526192851343403 24875887118289289277015105)
            ·
              refine ⟨18656915338716966957761329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24875887118289289277015105 18656915338716966957761329)
              ·
                refine ⟨13992686504037725218320997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18656915338716966957761329 13992686504037725218320997)
                ·
                  refine ⟨2623628719507073478435187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13992686504037725218320997 2623628719507073478435187)
                  ·
                    refine ⟨3935443079260610217652781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2623628719507073478435187 3935443079260610217652781)
                    ·
                      refine ⟨1475791154722728831619793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935443079260610217652781 1475791154722728831619793)
                      ·
                        rfl

theorem cell23_2874093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2874093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874093 prefixEnd_2874093 := by exact prefixLift 2874093
  have htrace : WordTrace (prefixWord ++ tailWord_2874093) baseStart_2874093 baseEnd_2874093 := by
    simpa [prefixWord, tailWord_2874093, baseEnd_2874093] using wordTrace_append hprefix tailTrace_2874093
  have hstable : (prefixWord ++ tailWord_2874093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874093).length < 2 ^ (prefixWord ++ tailWord_2874093).sum := by decide
  have hdescent : baseEnd_2874093 < baseStart_2874093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874109 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2874109 : Nat := 118140960795 + 2874109 * 2 ^ 59
def prefixEnd_2874109 : Nat := 4983230072969 + 3 ^ 40 * 2874109 * 2
def baseEnd_2874109 : Nat := 491933123471066923006573

theorem tailTrace_2874109 : CollatzResearch.WordTrace tailWord_2874109 prefixEnd_2874109 491933123471066923006573 := by
  unfold tailWord_2874109
  simp only [CollatzResearch.WordTrace]
  refine ⟨104827367144601426583049381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69884911429734284388699587 104827367144601426583049381)
  ·
    refine ⟨19655131339612767484321759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104827367144601426583049381 19655131339612767484321759)
    ·
      refine ⟨29482697009419151226482639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19655131339612767484321759 29482697009419151226482639)
      ·
        refine ⟨44224045514128726839723959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29482697009419151226482639 44224045514128726839723959)
        ·
          refine ⟨66336068271193090259585939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44224045514128726839723959 66336068271193090259585939)
          ·
            refine ⟨99504102406789635389378909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66336068271193090259585939 99504102406789635389378909)
            ·
              refine ⟨37314038402546113271017091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99504102406789635389378909 37314038402546113271017091)
              ·
                refine ⟨55971057603819169906525637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37314038402546113271017091 55971057603819169906525637)
                ·
                  refine ⟨10494573300716094357473557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55971057603819169906525637 10494573300716094357473557)
                  ·
                    refine ⟨491933123471066923006573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10494573300716094357473557 491933123471066923006573)
                    ·
                      rfl

theorem cell23_2874109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2874109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874109 prefixEnd_2874109 := by exact prefixLift 2874109
  have htrace : WordTrace (prefixWord ++ tailWord_2874109) baseStart_2874109 baseEnd_2874109 := by
    simpa [prefixWord, tailWord_2874109, baseEnd_2874109] using wordTrace_append hprefix tailTrace_2874109
  have hstable : (prefixWord ++ tailWord_2874109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874109).length < 2 ^ (prefixWord ++ tailWord_2874109).sum := by decide
  have hdescent : baseEnd_2874109 < baseStart_2874109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874110 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2874110 : Nat := 118140960795 + 2874110 * 2 ^ 59
def prefixEnd_2874110 : Nat := 4983230072969 + 3 ^ 40 * 2874110 * 2
def baseEnd_2874110 : Nat := 1475799883893855265107215

theorem tailTrace_2874110 : CollatzResearch.WordTrace tailWord_2874110 prefixEnd_2874110 1475799883893855265107215 := by
  unfold tailWord_2874110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103425452199725469229473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69884935745065202502557189 13103425452199725469229473)
  ·
    refine ⟨9827569089149794101922105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13103425452199725469229473 9827569089149794101922105)
    ·
      refine ⟨7370676816862345576441579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9827569089149794101922105 7370676816862345576441579)
      ·
        refine ⟨11056015225293518364662369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370676816862345576441579 11056015225293518364662369)
        ·
          refine ⟨8292011418970138773496777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11056015225293518364662369 8292011418970138773496777)
          ·
            refine ⟨6219008564227604080122583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8292011418970138773496777 6219008564227604080122583)
            ·
              refine ⟨9328512846341406120183875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219008564227604080122583 9328512846341406120183875)
              ·
                refine ⟨13992769269512109180275813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9328512846341406120183875 13992769269512109180275813)
                ·
                  refine ⟨2623644238033520471301715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13992769269512109180275813 2623644238033520471301715)
                  ·
                    refine ⟨3935466357050280706952573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2623644238033520471301715 3935466357050280706952573)
                    ·
                      refine ⟨1475799883893855265107215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935466357050280706952573 1475799883893855265107215)
                      ·
                        rfl

theorem cell23_2874110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2874110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874110 prefixEnd_2874110 := by exact prefixLift 2874110
  have htrace : WordTrace (prefixWord ++ tailWord_2874110) baseStart_2874110 baseEnd_2874110 := by
    simpa [prefixWord, tailWord_2874110, baseEnd_2874110] using wordTrace_append hprefix tailTrace_2874110
  have hstable : (prefixWord ++ tailWord_2874110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874110).length < 2 ^ (prefixWord ++ tailWord_2874110).sum := by decide
  have hdescent : baseEnd_2874110 < baseStart_2874110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874250 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_2874250 : Nat := 118140960795 + 2874250 * 2 ^ 59
def prefixEnd_2874250 : Nat := 4983230072969 + 3 ^ 40 * 2874250 * 2
def baseEnd_2874250 : Nat := 491957257061828239118857

theorem tailTrace_2874250 : CollatzResearch.WordTrace tailWord_2874250 prefixEnd_2874250 491957257061828239118857 := by
  unfold tailWord_2874250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26208127459272651915983051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69888339891393738442621469 26208127459272651915983051)
  ·
    refine ⟨39312191188908977873974577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26208127459272651915983051 39312191188908977873974577)
    ·
      refine ⟨29484143391681733405480933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39312191188908977873974577 29484143391681733405480933)
      ·
        refine ⟨5528276885940325013527675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29484143391681733405480933 5528276885940325013527675)
        ·
          refine ⟨8292415328910487520291513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528276885940325013527675 8292415328910487520291513)
          ·
            refine ⟨6219311496682865640218635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8292415328910487520291513 6219311496682865640218635)
            ·
              refine ⟨9328967245024298460327953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219311496682865640218635 9328967245024298460327953)
              ·
                refine ⟨6996725433768223845245965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9328967245024298460327953 6996725433768223845245965)
                ·
                  refine ⟨2623772037663083941967237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6996725433768223845245965 2623772037663083941967237)
                  ·
                    refine ⟨491957257061828239118857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2623772037663083941967237 491957257061828239118857)
                    ·
                      rfl

theorem cell23_2874250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_2874250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874250 prefixEnd_2874250 := by exact prefixLift 2874250
  have htrace : WordTrace (prefixWord ++ tailWord_2874250) baseStart_2874250 baseEnd_2874250 := by
    simpa [prefixWord, tailWord_2874250, baseEnd_2874250] using wordTrace_append hprefix tailTrace_2874250
  have hstable : (prefixWord ++ tailWord_2874250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874250).length < 2 ^ (prefixWord ++ tailWord_2874250).sum := by decide
  have hdescent : baseEnd_2874250 < baseStart_2874250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874324 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_2874324 : Nat := 118140960795 + 2874324 * 2 ^ 59
def prefixEnd_2874324 : Nat := 4983230072969 + 3 ^ 40 * 2874324 * 2
def baseEnd_2874324 : Nat := 1475909768753917427831231

theorem tailTrace_2874324 : CollatzResearch.WordTrace tailWord_2874324 prefixEnd_2874324 1475909768753917427831231 := by
  unfold tailWord_2874324
  simp only [CollatzResearch.WordTrace]
  refine ⟨52417604419411259151063013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69890139225881678868084017 52417604419411259151063013)
  ·
    refine ⟨9828300828639611090824315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52417604419411259151063013 9828300828639611090824315)
    ·
      refine ⟨14742451242959416636236473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9828300828639611090824315 14742451242959416636236473)
      ·
        refine ⟨11056838432219562477177355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14742451242959416636236473 11056838432219562477177355)
        ·
          refine ⟨16585257648329343715766033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11056838432219562477177355 16585257648329343715766033)
          ·
            refine ⟨12438943236247007786824525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16585257648329343715766033 12438943236247007786824525)
            ·
              refine ⟨4664603713592627920059197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12438943236247007786824525 4664603713592627920059197)
              ·
                refine ⟨1749226392597235470022199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4664603713592627920059197 1749226392597235470022199)
                ·
                  refine ⟨2623839588895853205033299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749226392597235470022199 2623839588895853205033299)
                  ·
                    refine ⟨3935759383343779807549949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2623839588895853205033299 3935759383343779807549949)
                    ·
                      refine ⟨1475909768753917427831231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935759383343779807549949 1475909768753917427831231)
                      ·
                        rfl

theorem cell23_2874324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_2874324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874324 prefixEnd_2874324 := by exact prefixLift 2874324
  have htrace : WordTrace (prefixWord ++ tailWord_2874324) baseStart_2874324 baseEnd_2874324 := by
    simpa [prefixWord, tailWord_2874324, baseEnd_2874324] using wordTrace_append hprefix tailTrace_2874324
  have hstable : (prefixWord ++ tailWord_2874324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874324).length < 2 ^ (prefixWord ++ tailWord_2874324).sum := by decide
  have hdescent : baseEnd_2874324 < baseStart_2874324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874330 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_2874330 : Nat := 118140960795 + 2874330 * 2 ^ 59
def prefixEnd_2874330 : Nat := 4983230072969 + 3 ^ 40 * 2874330 * 2
def baseEnd_2874330 : Nat := 1475912849637844404356203

theorem tailTrace_2874330 : CollatzResearch.WordTrace tailWord_2874330 prefixEnd_2874330 1475912849637844404356203 := by
  unfold tailWord_2874330
  simp only [CollatzResearch.WordTrace]
  refine ⟨26208856919200195331711111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69890285117867187551229629 26208856919200195331711111)
  ·
    refine ⟨39313285378800292997566667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26208856919200195331711111 39313285378800292997566667)
    ·
      refine ⟨58969928068200439496350001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39313285378800292997566667 58969928068200439496350001)
      ·
        refine ⟨44227446051150329622262501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58969928068200439496350001 44227446051150329622262501)
        ·
          refine ⟨8292646134590686804174219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44227446051150329622262501 8292646134590686804174219)
          ·
            refine ⟨12438969201886030206261329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292646134590686804174219 12438969201886030206261329)
            ·
              refine ⟨9329226901414522654695997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12438969201886030206261329 9329226901414522654695997)
              ·
                refine ⟨3498460088030445995510999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9329226901414522654695997 3498460088030445995510999)
                ·
                  refine ⟨5247690132045668993266499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498460088030445995510999 5247690132045668993266499)
                  ·
                    refine ⟨7871535198068503489899749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5247690132045668993266499 7871535198068503489899749)
                    ·
                      refine ⟨1475912849637844404356203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7871535198068503489899749 1475912849637844404356203)
                      ·
                        rfl

theorem cell23_2874330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_2874330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874330 prefixEnd_2874330 := by exact prefixLift 2874330
  have htrace : WordTrace (prefixWord ++ tailWord_2874330) baseStart_2874330 baseEnd_2874330 := by
    simpa [prefixWord, tailWord_2874330, baseEnd_2874330] using wordTrace_append hprefix tailTrace_2874330
  have hstable : (prefixWord ++ tailWord_2874330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874330).length < 2 ^ (prefixWord ++ tailWord_2874330).sum := by decide
  have hdescent : baseEnd_2874330 < baseStart_2874330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874341 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2874341 : Nat := 118140960795 + 2874341 * 2 ^ 59
def prefixEnd_2874341 : Nat := 4983230072969 + 3 ^ 40 * 2874341 * 2
def baseEnd_2874341 : Nat := 1475918497925043861318653

theorem tailTrace_2874341 : CollatzResearch.WordTrace tailWord_2874341 prefixEnd_2874341 1475918497925043861318653 := by
  unfold tailWord_2874341
  simp only [CollatzResearch.WordTrace]
  refine ⟨104835828879760930205494877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69890552586507286803663251 104835828879760930205494877)
  ·
    refine ⟨39313435829910348827060579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104835828879760930205494877 39313435829910348827060579)
    ·
      refine ⟨58970153744865523240590869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39313435829910348827060579 58970153744865523240590869)
      ·
        refine ⟨2764225956790571401902697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58970153744865523240590869 2764225956790571401902697)
        ·
          refine ⟨2073169467592928551427023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764225956790571401902697 2073169467592928551427023)
          ·
            refine ⟨3109754201389392827140535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073169467592928551427023 3109754201389392827140535)
            ·
              refine ⟨4664631302084089240710803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109754201389392827140535 4664631302084089240710803)
              ·
                refine ⟨6996946953126133861066205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4664631302084089240710803 6996946953126133861066205)
                ·
                  refine ⟨2623855107422300197899827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6996946953126133861066205 2623855107422300197899827)
                  ·
                    refine ⟨3935782661133450296849741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2623855107422300197899827 3935782661133450296849741)
                    ·
                      refine ⟨1475918497925043861318653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935782661133450296849741 1475918497925043861318653)
                      ·
                        rfl

theorem cell23_2874341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2874341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874341 prefixEnd_2874341 := by exact prefixLift 2874341
  have htrace : WordTrace (prefixWord ++ tailWord_2874341) baseStart_2874341 baseEnd_2874341 := by
    simpa [prefixWord, tailWord_2874341, baseEnd_2874341] using wordTrace_append hprefix tailTrace_2874341
  have hstable : (prefixWord ++ tailWord_2874341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874341).length < 2 ^ (prefixWord ++ tailWord_2874341).sum := by decide
  have hdescent : baseEnd_2874341 < baseStart_2874341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874343 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2874343 : Nat := 118140960795 + 2874343 * 2 ^ 59
def prefixEnd_2874343 : Nat := 4983230072969 + 3 ^ 40 * 2874343 * 2
def baseEnd_2874343 : Nat := 1475919524886352853493643

theorem tailTrace_2874343 : CollatzResearch.WordTrace tailWord_2874343 prefixEnd_2874343 1475919524886352853493643 := by
  unfold tailWord_2874343
  simp only [CollatzResearch.WordTrace]
  refine ⟨104835901825753684547067683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69890601217169123031378455 104835901825753684547067683)
  ·
    refine ⟨157253852738630526820601525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104835901825753684547067683 157253852738630526820601525)
    ·
      refine ⟨14742548694246611889431393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157253852738630526820601525 14742548694246611889431393)
      ·
        refine ⟨11056911520684958917073545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14742548694246611889431393 11056911520684958917073545)
        ·
          refine ⟨8292683640513719187805159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11056911520684958917073545 8292683640513719187805159)
          ·
            refine ⟨12439025460770578781707739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292683640513719187805159 12439025460770578781707739)
            ·
              refine ⟨18658538191155868172561609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439025460770578781707739 18658538191155868172561609)
              ·
                refine ⟨13993903643366901129421207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18658538191155868172561609 13993903643366901129421207)
                ·
                  refine ⟨20990855465050351694131811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13993903643366901129421207 20990855465050351694131811)
                  ·
                    refine ⟨31486283197575527541197717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20990855465050351694131811 31486283197575527541197717)
                    ·
                      refine ⟨1475919524886352853493643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31486283197575527541197717 1475919524886352853493643)
                      ·
                        rfl

theorem cell23_2874343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2874343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874343 prefixEnd_2874343 := by exact prefixLift 2874343
  have htrace : WordTrace (prefixWord ++ tailWord_2874343) baseStart_2874343 baseEnd_2874343 := by
    simpa [prefixWord, tailWord_2874343, baseEnd_2874343] using wordTrace_append hprefix tailTrace_2874343
  have hstable : (prefixWord ++ tailWord_2874343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874343).length < 2 ^ (prefixWord ++ tailWord_2874343).sum := by decide
  have hdescent : baseEnd_2874343 < baseStart_2874343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874353 : List Nat := [1, 2, 2, 2, 4, 2, 2, 8]
def baseStart_2874353 : Nat := 118140960795 + 2874353 * 2 ^ 59
def prefixEnd_2874353 : Nat := 4983230072969 + 3 ^ 40 * 2874353 * 2
def baseEnd_2874353 : Nat := 54663876284922141272911

theorem tailTrace_2874353 : CollatzResearch.WordTrace tailWord_2874353 prefixEnd_2874353 54663876284922141272911 := by
  unfold tailWord_2874353
  simp only [CollatzResearch.WordTrace]
  refine ⟨104836266555717456254931713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69890844370478304169954475 104836266555717456254931713)
  ·
    refine ⟨78627199916788092191198785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104836266555717456254931713 78627199916788092191198785)
    ·
      refine ⟨58970399937591069143399089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78627199916788092191198785 58970399937591069143399089)
      ·
        refine ⟨44227799953193301857549317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58970399937591069143399089 44227799953193301857549317)
        ·
          refine ⟨8292712491223744098290497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44227799953193301857549317 8292712491223744098290497)
          ·
            refine ⟨6219534368417808073717873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8292712491223744098290497 6219534368417808073717873)
            ·
              refine ⟨4664650776313356055288405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219534368417808073717873 4664650776313356055288405)
              ·
                refine ⟨54663876284922141272911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4664650776313356055288405 54663876284922141272911)
                ·
                  rfl

theorem cell23_2874353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 8].length) (baseStart_2874353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874353 prefixEnd_2874353 := by exact prefixLift 2874353
  have htrace : WordTrace (prefixWord ++ tailWord_2874353) baseStart_2874353 baseEnd_2874353 := by
    simpa [prefixWord, tailWord_2874353, baseEnd_2874353] using wordTrace_append hprefix tailTrace_2874353
  have hstable : (prefixWord ++ tailWord_2874353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874353).length < 2 ^ (prefixWord ++ tailWord_2874353).sum := by decide
  have hdescent : baseEnd_2874353 < baseStart_2874353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874363 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 3]
def baseStart_2874363 : Nat := 118140960795 + 2874363 * 2 ^ 59
def prefixEnd_2874363 : Nat := 4983230072969 + 3 ^ 40 * 2874363 * 2
def baseEnd_2874363 : Nat := 1475929794499442775243551

theorem tailTrace_2874363 : CollatzResearch.WordTrace tailWord_2874363 prefixEnd_2874363 1475929794499442775243551 := by
  unfold tailWord_2874363
  simp only [CollatzResearch.WordTrace]
  refine ⟨104836631285681227962795743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69891087523787485308530495 104836631285681227962795743)
  ·
    refine ⟨157254946928521841944193615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104836631285681227962795743 157254946928521841944193615)
    ·
      refine ⟨235882420392782762916290423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157254946928521841944193615 235882420392782762916290423)
      ·
        refine ⟨353823630589174144374435635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235882420392782762916290423 353823630589174144374435635)
        ·
          refine ⟨530735445883761216561653453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353823630589174144374435635 530735445883761216561653453)
          ·
            refine ⟨199025792206410456210620045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530735445883761216561653453 199025792206410456210620045)
            ·
              refine ⟨74634672077403921078982517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199025792206410456210620045 74634672077403921078982517)
              ·
                refine ⟨6997000507256617601154611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74634672077403921078982517 6997000507256617601154611)
                ·
                  refine ⟨10495500760884926401731917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6997000507256617601154611 10495500760884926401731917)
                  ·
                    refine ⟨3935812785331847400649469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10495500760884926401731917 3935812785331847400649469)
                    ·
                      refine ⟨1475929794499442775243551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935812785331847400649469 1475929794499442775243551)
                      ·
                        rfl

theorem cell23_2874363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 3].length) (baseStart_2874363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874363 prefixEnd_2874363 := by exact prefixLift 2874363
  have htrace : WordTrace (prefixWord ++ tailWord_2874363) baseStart_2874363 baseEnd_2874363 := by
    simpa [prefixWord, tailWord_2874363, baseEnd_2874363] using wordTrace_append hprefix tailTrace_2874363
  have hstable : (prefixWord ++ tailWord_2874363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874363).length < 2 ^ (prefixWord ++ tailWord_2874363).sum := by decide
  have hdescent : baseEnd_2874363 < baseStart_2874363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874380 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_2874380 : Nat := 118140960795 + 2874380 * 2 ^ 59
def prefixEnd_2874380 : Nat := 4983230072969 + 3 ^ 40 * 2874380 * 2
def baseEnd_2874380 : Nat := 1475938523670569208730973

theorem tailTrace_2874380 : CollatzResearch.WordTrace tailWord_2874380 prefixEnd_2874380 1475938523670569208730973 := by
  unfold tailWord_2874380
  simp only [CollatzResearch.WordTrace]
  refine ⟨52418625663309819933082297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69891500884413093244109729 52418625663309819933082297)
  ·
    refine ⟨39313969247482364949811723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52418625663309819933082297 39313969247482364949811723)
    ·
      refine ⟨58970953871223547424717585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39313969247482364949811723 58970953871223547424717585)
      ·
        refine ⟨44228215403417660568538189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58970953871223547424717585 44228215403417660568538189)
        ·
          refine ⟨16585580776281622713201821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44228215403417660568538189 16585580776281622713201821)
          ·
            refine ⟨6219592791105608517450683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16585580776281622713201821 6219592791105608517450683)
            ·
              refine ⟨9329389186658412776176025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219592791105608517450683 9329389186658412776176025)
              ·
                refine ⟨6997041889993809582132019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9329389186658412776176025 6997041889993809582132019)
                ·
                  refine ⟨10495562834990714373198029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6997041889993809582132019 10495562834990714373198029)
                  ·
                    refine ⟨3935836063121517889949261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10495562834990714373198029 3935836063121517889949261)
                    ·
                      refine ⟨1475938523670569208730973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935836063121517889949261 1475938523670569208730973)
                      ·
                        rfl

theorem cell23_2874380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_2874380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874380 prefixEnd_2874380 := by exact prefixLift 2874380
  have htrace : WordTrace (prefixWord ++ tailWord_2874380) baseStart_2874380 baseEnd_2874380 := by
    simpa [prefixWord, tailWord_2874380, baseEnd_2874380] using wordTrace_append hprefix tailTrace_2874380
  have hstable : (prefixWord ++ tailWord_2874380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874380).length < 2 ^ (prefixWord ++ tailWord_2874380).sum := by decide
  have hdescent : baseEnd_2874380 < baseStart_2874380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874403 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4]
def baseStart_2874403 : Nat := 118140960795 + 2874403 * 2 ^ 59
def prefixEnd_2874403 : Nat := 4983230072969 + 3 ^ 40 * 2874403 * 2
def baseEnd_2874403 : Nat := 1475950333725622618743367

theorem tailTrace_2874403 : CollatzResearch.WordTrace tailWord_2874403 prefixEnd_2874403 1475950333725622618743367 := by
  unfold tailWord_2874403
  simp only [CollatzResearch.WordTrace]
  refine ⟨104838090205536314794251863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69892060137024209862834575 104838090205536314794251863)
  ·
    refine ⟨157257135308304472191377795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104838090205536314794251863 157257135308304472191377795)
    ·
      refine ⟨235885702962456708287066693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157257135308304472191377795 235885702962456708287066693)
      ·
        refine ⟨44228569305460632803825005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235885702962456708287066693 44228569305460632803825005)
        ·
          refine ⟨16585713489547737301434377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44228569305460632803825005 16585713489547737301434377)
          ·
            refine ⟨12439285117160802976075783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16585713489547737301434377 12439285117160802976075783)
            ·
              refine ⟨18658927675741204464113675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439285117160802976075783 18658927675741204464113675)
              ·
                refine ⟨27988391513611806696170513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18658927675741204464113675 27988391513611806696170513)
                ·
                  refine ⟨20991293635208855022127885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27988391513611806696170513 20991293635208855022127885)
                  ·
                    refine ⟨7871735113203320633297957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20991293635208855022127885 7871735113203320633297957)
                    ·
                      refine ⟨1475950333725622618743367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7871735113203320633297957 1475950333725622618743367)
                      ·
                        rfl

theorem cell23_2874403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_2874403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874403 prefixEnd_2874403 := by exact prefixLift 2874403
  have htrace : WordTrace (prefixWord ++ tailWord_2874403) baseStart_2874403 baseEnd_2874403 := by
    simpa [prefixWord, tailWord_2874403, baseEnd_2874403] using wordTrace_append hprefix tailTrace_2874403
  have hstable : (prefixWord ++ tailWord_2874403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874403).length < 2 ^ (prefixWord ++ tailWord_2874403).sum := by decide
  have hdescent : baseEnd_2874403 < baseStart_2874403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874423 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_2874423 : Nat := 118140960795 + 2874423 * 2 ^ 59
def prefixEnd_2874423 : Nat := 4983230072969 + 3 ^ 40 * 2874423 * 2
def baseEnd_2874423 : Nat := 1475960603338712540493275

theorem tailTrace_2874423 : CollatzResearch.WordTrace tailWord_2874423 prefixEnd_2874423 1475960603338712540493275 := by
  unfold tailWord_2874423
  simp only [CollatzResearch.WordTrace]
  refine ⟨104838819665463858209979923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69892546443642572139986615 104838819665463858209979923)
  ·
    refine ⟨157258229498195787314969885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104838819665463858209979923 157258229498195787314969885)
    ·
      refine ⟨58971836061823420243113707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157258229498195787314969885 58971836061823420243113707)
      ·
        refine ⟨88457754092735130364670561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58971836061823420243113707 88457754092735130364670561)
        ·
          refine ⟨66343315569551347773502921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88457754092735130364670561 66343315569551347773502921)
          ·
            refine ⟨49757486677163510830127191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66343315569551347773502921 49757486677163510830127191)
            ·
              refine ⟨74636230015745266245190787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49757486677163510830127191 74636230015745266245190787)
              ·
                refine ⟨111954345023617899367786181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74636230015745266245190787 111954345023617899367786181)
                ·
                  refine ⟨20991439691928356131459909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111954345023617899367786181 20991439691928356131459909)
                  ·
                    refine ⟨3935894942236566774648733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20991439691928356131459909 3935894942236566774648733)
                    ·
                      refine ⟨1475960603338712540493275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3935894942236566774648733 1475960603338712540493275)
                      ·
                        rfl

theorem cell23_2874423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_2874423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874423 prefixEnd_2874423 := by exact prefixLift 2874423
  have htrace : WordTrace (prefixWord ++ tailWord_2874423) baseStart_2874423 baseEnd_2874423 := by
    simpa [prefixWord, tailWord_2874423, baseEnd_2874423] using wordTrace_append hprefix tailTrace_2874423
  have hstable : (prefixWord ++ tailWord_2874423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874423).length < 2 ^ (prefixWord ++ tailWord_2874423).sum := by decide
  have hdescent : baseEnd_2874423 < baseStart_2874423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874450 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2874450 : Nat := 118140960795 + 2874450 * 2 ^ 59
def prefixEnd_2874450 : Nat := 4983230072969 + 3 ^ 40 * 2874450 * 2
def baseEnd_2874450 : Nat := 1475974467316383934855651

theorem tailTrace_2874450 : CollatzResearch.WordTrace tailWord_2874450 prefixEnd_2874450 1475974467316383934855651 := by
  unfold tailWord_2874450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26209951109091510455303201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69893202957577361214141869 26209951109091510455303201)
  ·
    refine ⟨19657463331818632841477401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26209951109091510455303201 19657463331818632841477401)
    ·
      refine ⟨14743097498863974631108051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19657463331818632841477401 14743097498863974631108051)
      ·
        refine ⟨22114646248295961946662077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14743097498863974631108051 22114646248295961946662077)
        ·
          refine ⟨8292992343110985729998279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22114646248295961946662077 8292992343110985729998279)
          ·
            refine ⟨12439488514666478594997419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292992343110985729998279 12439488514666478594997419)
            ·
              refine ⟨18659232771999717892496129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439488514666478594997419 18659232771999717892496129)
              ·
                refine ⟨13994424578999788419372097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18659232771999717892496129 13994424578999788419372097)
                ·
                  refine ⟨10495818434249841314529073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13994424578999788419372097 10495818434249841314529073)
                  ·
                    refine ⟨7871863825687380985896805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10495818434249841314529073 7871863825687380985896805)
                    ·
                      refine ⟨1475974467316383934855651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7871863825687380985896805 1475974467316383934855651)
                      ·
                        rfl

theorem cell23_2874450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2874450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874450 prefixEnd_2874450 := by exact prefixLift 2874450
  have htrace : WordTrace (prefixWord ++ tailWord_2874450) baseStart_2874450 baseEnd_2874450 := by
    simpa [prefixWord, tailWord_2874450, baseEnd_2874450] using wordTrace_append hprefix tailTrace_2874450
  have hstable : (prefixWord ++ tailWord_2874450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874450).length < 2 ^ (prefixWord ++ tailWord_2874450).sum := by decide
  have hdescent : baseEnd_2874450 < baseStart_2874450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874460 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 7]
def baseStart_2874460 : Nat := 118140960795 + 2874460 * 2 ^ 59
def prefixEnd_2874460 : Nat := 4983230072969 + 3 ^ 40 * 2874460 * 2
def baseEnd_2874460 : Nat := 163997733569214321747845

theorem tailTrace_2874460 : CollatzResearch.WordTrace tailWord_2874460 prefixEnd_2874460 163997733569214321747845 := by
  unfold tailWord_2874460
  simp only [CollatzResearch.WordTrace]
  refine ⟨52420084583164906764538417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69893446110886542352717889 52420084583164906764538417)
  ·
    refine ⟨39315063437373680073403813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52420084583164906764538417 39315063437373680073403813)
    ·
      refine ⟨7371574394507565013763215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39315063437373680073403813 7371574394507565013763215)
      ·
        refine ⟨11057361591761347520644823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371574394507565013763215 11057361591761347520644823)
        ·
          refine ⟨16586042387642021280967235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11057361591761347520644823 16586042387642021280967235)
          ·
            refine ⟨24879063581463031921450853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16586042387642021280967235 24879063581463031921450853)
            ·
              refine ⟨4664824421524318485272035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24879063581463031921450853 4664824421524318485272035)
              ·
                refine ⟨6997236632286477727908053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4664824421524318485272035 6997236632286477727908053)
                ·
                  refine ⟨163997733569214321747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6997236632286477727908053 163997733569214321747845)
                  ·
                    rfl

theorem cell23_2874460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_2874460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874460 prefixEnd_2874460 := by exact prefixLift 2874460
  have htrace : WordTrace (prefixWord ++ tailWord_2874460) baseStart_2874460 baseEnd_2874460 := by
    simpa [prefixWord, tailWord_2874460, baseEnd_2874460] using wordTrace_append hprefix tailTrace_2874460
  have hstable : (prefixWord ++ tailWord_2874460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874460).length < 2 ^ (prefixWord ++ tailWord_2874460).sum := by decide
  have hdescent : baseEnd_2874460 < baseStart_2874460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874471 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_2874471 : Nat := 118140960795 + 2874471 * 2 ^ 59
def prefixEnd_2874471 : Nat := 4983230072969 + 3 ^ 40 * 2874471 * 2
def baseEnd_2874471 : Nat := 1475985250410128352693055

theorem tailTrace_2874471 : CollatzResearch.WordTrace tailWord_2874471 prefixEnd_2874471 1475985250410128352693055 := by
  unfold tailWord_2874471
  simp only [CollatzResearch.WordTrace]
  refine ⟨104840570369289962407727267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69893713579526641605151511 104840570369289962407727267)
  ·
    refine ⟨157260855553934943611590901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104840570369289962407727267 157260855553934943611590901)
    ·
      refine ⟨14743205208181400963586647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157260855553934943611590901 14743205208181400963586647)
      ·
        refine ⟨22114807812272101445379971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14743205208181400963586647 22114807812272101445379971)
        ·
          refine ⟨33172211718408152168069957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22114807812272101445379971 33172211718408152168069957)
          ·
            refine ⟨6219789697201528531513117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33172211718408152168069957 6219789697201528531513117)
            ·
              refine ⟨2332421136450573199317419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6219789697201528531513117 2332421136450573199317419)
              ·
                refine ⟨3498631704675859798976129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332421136450573199317419 3498631704675859798976129)
                ·
                  refine ⟨2623973778506894849232097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3498631704675859798976129 2623973778506894849232097)
                  ·
                    refine ⟨1967980333880171136924073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2623973778506894849232097 1967980333880171136924073)
                    ·
                      refine ⟨1475985250410128352693055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1967980333880171136924073 1475985250410128352693055)
                      ·
                        rfl

theorem cell23_2874471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_2874471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874471 prefixEnd_2874471 := by exact prefixLift 2874471
  have htrace : WordTrace (prefixWord ++ tailWord_2874471) baseStart_2874471 baseEnd_2874471 := by
    simpa [prefixWord, tailWord_2874471, baseEnd_2874471] using wordTrace_append hprefix tailTrace_2874471
  have hstable : (prefixWord ++ tailWord_2874471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874471).length < 2 ^ (prefixWord ++ tailWord_2874471).sum := by decide
  have hdescent : baseEnd_2874471 < baseStart_2874471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874473 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_2874473 : Nat := 118140960795 + 2874473 * 2 ^ 59
def prefixEnd_2874473 : Nat := 4983230072969 + 3 ^ 40 * 2874473 * 2
def baseEnd_2874473 : Nat := 491995425790479114956015

theorem tailTrace_2874473 : CollatzResearch.WordTrace tailWord_2874473 prefixEnd_2874473 491995425790479114956015 := by
  unfold tailWord_2874473
  simp only [CollatzResearch.WordTrace]
  refine ⟨104840643315282716749300073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69893762210188477832866715 104840643315282716749300073)
  ·
    refine ⟨78630482486462037561975055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104840643315282716749300073 78630482486462037561975055)
    ·
      refine ⟨117945723729693056342962583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78630482486462037561975055 117945723729693056342962583)
      ·
        refine ⟨176918585594539584514443875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117945723729693056342962583 176918585594539584514443875)
        ·
          refine ⟨265377878391809376771665813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176918585594539584514443875 265377878391809376771665813)
          ·
            refine ⟨12439588049616064536171835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265377878391809376771665813 12439588049616064536171835)
            ·
              refine ⟨18659382074424096804257753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439588049616064536171835 18659382074424096804257753)
              ·
                refine ⟨13994536555818072603193315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18659382074424096804257753 13994536555818072603193315)
                ·
                  refine ⟨20991804833727108904789973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13994536555818072603193315 20991804833727108904789973)
                  ·
                    refine ⟨491995425790479114956015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20991804833727108904789973 491995425790479114956015)
                    ·
                      rfl

theorem cell23_2874473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_2874473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874473 prefixEnd_2874473 := by exact prefixLift 2874473
  have htrace : WordTrace (prefixWord ++ tailWord_2874473) baseStart_2874473 baseEnd_2874473 := by
    simpa [prefixWord, tailWord_2874473, baseEnd_2874473] using wordTrace_append hprefix tailTrace_2874473
  have hstable : (prefixWord ++ tailWord_2874473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874473).length < 2 ^ (prefixWord ++ tailWord_2874473).sum := by decide
  have hdescent : baseEnd_2874473 < baseStart_2874473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874523 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4]
def baseStart_2874523 : Nat := 118140960795 + 2874523 * 2 ^ 59
def prefixEnd_2874523 : Nat := 4983230072969 + 3 ^ 40 * 2874523 * 2
def baseEnd_2874523 : Nat := 1476011951404162149242815

theorem tailTrace_2874523 : CollatzResearch.WordTrace tailWord_2874523 prefixEnd_2874523 1476011951404162149242815 := by
  unfold tailWord_2874523
  simp only [CollatzResearch.WordTrace]
  refine ⟨104842466965101575288620223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69894977976734383525746815 104842466965101575288620223)
  ·
    refine ⟨157263700447652362932930335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104842466965101575288620223 157263700447652362932930335)
    ·
      refine ⟨235895550671478544399395503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157263700447652362932930335 235895550671478544399395503)
      ·
        refine ⟨353843326007217816599093255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235895550671478544399395503 353843326007217816599093255)
        ·
          refine ⟨530764989010826724898639883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353843326007217816599093255 530764989010826724898639883)
          ·
            refine ⟨796147483516240087347959825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530764989010826724898639883 796147483516240087347959825)
            ·
              refine ⟨597110612637180065510969869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796147483516240087347959825 597110612637180065510969869)
              ·
                refine ⟨223916479738942524566613701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597110612637180065510969869 223916479738942524566613701)
                ·
                  refine ⟨41984339951051723356240069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223916479738942524566613701 41984339951051723356240069)
                  ·
                    refine ⟨7872063740822198129295013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41984339951051723356240069 7872063740822198129295013)
                    ·
                      refine ⟨1476011951404162149242815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7872063740822198129295013 1476011951404162149242815)
                      ·
                        rfl

theorem cell23_2874523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_2874523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874523 prefixEnd_2874523 := by exact prefixLift 2874523
  have htrace : WordTrace (prefixWord ++ tailWord_2874523) baseStart_2874523 baseEnd_2874523 := by
    simpa [prefixWord, tailWord_2874523, baseEnd_2874523] using wordTrace_append hprefix tailTrace_2874523
  have hstable : (prefixWord ++ tailWord_2874523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874523).length < 2 ^ (prefixWord ++ tailWord_2874523).sum := by decide
  have hdescent : baseEnd_2874523 < baseStart_2874523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874577 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_2874577 : Nat := 118140960795 + 2874577 * 2 ^ 59
def prefixEnd_2874577 : Nat := 4983230072969 + 3 ^ 40 * 2874577 * 2
def baseEnd_2874577 : Nat := 1476039679359504937967567

theorem tailTrace_2874577 : CollatzResearch.WordTrace tailWord_2874577 prefixEnd_2874577 1476039679359504937967567 := by
  unfold tailWord_2874577
  simp only [CollatzResearch.WordTrace]
  refine ⟨104844436506905942511085985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69896291004603961674057323 104844436506905942511085985)
  ·
    refine ⟨78633327380179456883314489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104844436506905942511085985 78633327380179456883314489)
    ·
      refine ⟨58974995535134592662485867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78633327380179456883314489 58974995535134592662485867)
      ·
        refine ⟨88462493302701888993728801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58974995535134592662485867 88462493302701888993728801)
        ·
          refine ⟨66346869977026416745296601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88462493302701888993728801 66346869977026416745296601)
          ·
            refine ⟨49760152482769812558972451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66346869977026416745296601 49760152482769812558972451)
            ·
              refine ⟨74640228724154718838458677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49760152482769812558972451 74640228724154718838458677)
              ·
                refine ⟨6997521442889504891105501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74640228724154718838458677 6997521442889504891105501)
                ·
                  refine ⟨2624070541083564334164563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6997521442889504891105501 2624070541083564334164563)
                  ·
                    refine ⟨3936105811625346501246845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2624070541083564334164563 3936105811625346501246845)
                    ·
                      refine ⟨1476039679359504937967567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3936105811625346501246845 1476039679359504937967567)
                      ·
                        rfl

theorem cell23_2874577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_2874577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874577 prefixEnd_2874577 := by exact prefixLift 2874577
  have htrace : WordTrace (prefixWord ++ tailWord_2874577) baseStart_2874577 baseEnd_2874577 := by
    simpa [prefixWord, tailWord_2874577, baseEnd_2874577] using wordTrace_append hprefix tailTrace_2874577
  have hstable : (prefixWord ++ tailWord_2874577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874577).length < 2 ^ (prefixWord ++ tailWord_2874577).sum := by decide
  have hdescent : baseEnd_2874577 < baseStart_2874577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874604 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 2, 3, 2]
def baseStart_2874604 : Nat := 118140960795 + 2874604 * 2 ^ 59
def prefixEnd_2874604 : Nat := 4983230072969 + 3 ^ 40 * 2874604 * 2
def baseEnd_2874604 : Nat := 1476053543337176332329943

theorem tailTrace_2874604 : CollatzResearch.WordTrace tailWord_2874604 prefixEnd_2874604 1476053543337176332329943 := by
  unfold tailWord_2874604
  simp only [CollatzResearch.WordTrace]
  refine ⟨52422710638904063061159433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69896947518538750748212577 52422710638904063061159433)
  ·
    refine ⟨39317032979178047295869575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52422710638904063061159433 39317032979178047295869575)
    ·
      refine ⟨58975549468767070943804363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39317032979178047295869575 58975549468767070943804363)
      ·
        refine ⟨88463324203150606415706545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58975549468767070943804363 88463324203150606415706545)
        ·
          refine ⟨66347493152362954811779909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88463324203150606415706545 66347493152362954811779909)
          ·
            refine ⟨12440154966068054027208733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66347493152362954811779909 12440154966068054027208733)
            ·
              refine ⟨4665058112275520260203275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12440154966068054027208733 4665058112275520260203275)
              ·
                refine ⟨6997587168413280390304913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665058112275520260203275 6997587168413280390304913)
                ·
                  refine ⟨5248190376309960292728685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6997587168413280390304913 5248190376309960292728685)
                  ·
                    refine ⟨1968071391116235109773257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5248190376309960292728685 1968071391116235109773257)
                    ·
                      refine ⟨1476053543337176332329943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968071391116235109773257 1476053543337176332329943)
                      ·
                        rfl

theorem cell23_2874604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_2874604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874604 prefixEnd_2874604 := by exact prefixLift 2874604
  have htrace : WordTrace (prefixWord ++ tailWord_2874604) baseStart_2874604 baseEnd_2874604 := by
    simpa [prefixWord, tailWord_2874604, baseEnd_2874604] using wordTrace_append hprefix tailTrace_2874604
  have hstable : (prefixWord ++ tailWord_2874604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874604).length < 2 ^ (prefixWord ++ tailWord_2874604).sum := by decide
  have hdescent : baseEnd_2874604 < baseStart_2874604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874611 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 1, 1, 3]
def baseStart_2874611 : Nat := 118140960795 + 2874611 * 2 ^ 59
def prefixEnd_2874611 : Nat := 4983230072969 + 3 ^ 40 * 2874611 * 2
def baseEnd_2874611 : Nat := 1476057137701757804942411

theorem tailTrace_2874611 : CollatzResearch.WordTrace tailWord_2874611 prefixEnd_2874611 1476057137701757804942411 := by
  unfold tailWord_2874611
  simp only [CollatzResearch.WordTrace]
  refine ⟨104845676588782766317823687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69897117725855177545215791 104845676588782766317823687)
  ·
    refine ⟨157268514883174149476735531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104845676588782766317823687 157268514883174149476735531)
    ·
      refine ⟨235902772324761224215103297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157268514883174149476735531 235902772324761224215103297)
      ·
        refine ⟨176927079243570918161327473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235902772324761224215103297 176927079243570918161327473)
        ·
          refine ⟨132695309432678188620995605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176927079243570918161327473 132695309432678188620995605)
          ·
            refine ⟨6220092629656790091609169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132695309432678188620995605 6220092629656790091609169)
            ·
              refine ⟨4665069472242592568706877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220092629656790091609169 4665069472242592568706877)
              ·
                refine ⟨1749401052090972213265079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665069472242592568706877 1749401052090972213265079)
                ·
                  refine ⟨2624101578136458319897619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749401052090972213265079 2624101578136458319897619)
                  ·
                    refine ⟨3936152367204687479846429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2624101578136458319897619 3936152367204687479846429)
                    ·
                      refine ⟨1476057137701757804942411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3936152367204687479846429 1476057137701757804942411)
                      ·
                        rfl

theorem cell23_2874611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 1, 3].length) (baseStart_2874611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874611 prefixEnd_2874611 := by exact prefixLift 2874611
  have htrace : WordTrace (prefixWord ++ tailWord_2874611) baseStart_2874611 baseEnd_2874611 := by
    simpa [prefixWord, tailWord_2874611, baseEnd_2874611] using wordTrace_append hprefix tailTrace_2874611
  have hstable : (prefixWord ++ tailWord_2874611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874611).length < 2 ^ (prefixWord ++ tailWord_2874611).sum := by decide
  have hdescent : baseEnd_2874611 < baseStart_2874611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874617 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2874617 : Nat := 118140960795 + 2874617 * 2 ^ 59
def prefixEnd_2874617 : Nat := 4983230072969 + 3 ^ 40 * 2874617 * 2
def baseEnd_2874617 : Nat := 1476060218585684781467383

theorem tailTrace_2874617 : CollatzResearch.WordTrace tailWord_2874617 prefixEnd_2874617 1476060218585684781467383 := by
  unfold tailWord_2874617
  simp only [CollatzResearch.WordTrace]
  refine ⟨104845895426761029342542105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69897263617840686228361403 104845895426761029342542105)
  ·
    refine ⟨78634421570070772006906579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104845895426761029342542105 78634421570070772006906579)
    ·
      refine ⟨117951632355106158010359869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78634421570070772006906579 117951632355106158010359869)
      ·
        refine ⟨44231862133164809253884951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117951632355106158010359869 44231862133164809253884951)
        ·
          refine ⟨66347793199747213880827427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44231862133164809253884951 66347793199747213880827427)
          ·
            refine ⟨99521689799620820821241141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66347793199747213880827427 99521689799620820821241141)
            ·
              refine ⟨9330158418714451951991357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99521689799620820821241141 9330158418714451951991357)
              ·
                refine ⟨3498809407017919481996759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9330158418714451951991357 3498809407017919481996759)
                ·
                  refine ⟨5248214110526879222995139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498809407017919481996759 5248214110526879222995139)
                  ·
                    refine ⟨7872321165790318834492709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5248214110526879222995139 7872321165790318834492709)
                    ·
                      refine ⟨1476060218585684781467383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7872321165790318834492709 1476060218585684781467383)
                      ·
                        rfl

theorem cell23_2874617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2874617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874617 prefixEnd_2874617 := by exact prefixLift 2874617
  have htrace : WordTrace (prefixWord ++ tailWord_2874617) baseStart_2874617 baseEnd_2874617 := by
    simpa [prefixWord, tailWord_2874617, baseEnd_2874617] using wordTrace_append hprefix tailTrace_2874617
  have hstable : (prefixWord ++ tailWord_2874617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874617).length < 2 ^ (prefixWord ++ tailWord_2874617).sum := by decide
  have hdescent : baseEnd_2874617 < baseStart_2874617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874627 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 4, 4]
def baseStart_2874627 : Nat := 118140960795 + 2874627 * 2 ^ 59
def prefixEnd_2874627 : Nat := 4983230072969 + 3 ^ 40 * 2874627 * 2
def baseEnd_2874627 : Nat := 492021784464076580780779

theorem tailTrace_2874627 : CollatzResearch.WordTrace tailWord_2874627 prefixEnd_2874627 492021784464076580780779 := by
  unfold tailWord_2874627
  simp only [CollatzResearch.WordTrace]
  refine ⟨104846260156724801050406135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69897506771149867366937423 104846260156724801050406135)
  ·
    refine ⟨157269390235087201575609203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104846260156724801050406135 157269390235087201575609203)
    ·
      refine ⟨235904085352630802363413805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157269390235087201575609203 235904085352630802363413805)
      ·
        refine ⟨88464032007236550886280177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235904085352630802363413805 88464032007236550886280177)
        ·
          refine ⟨66348024005427413164710133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88464032007236550886280177 66348024005427413164710133)
          ·
            refine ⟨6220127250508819984191575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66348024005427413164710133 6220127250508819984191575)
            ·
              refine ⟨9330190875763229976287363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220127250508819984191575 9330190875763229976287363)
              ·
                refine ⟨13995286313644844964431045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330190875763229976287363 13995286313644844964431045)
                ·
                  refine ⟨2624116183808408430830821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13995286313644844964431045 2624116183808408430830821)
                  ·
                    refine ⟨492021784464076580780779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624116183808408430830821 492021784464076580780779)
                    ·
                      rfl

theorem cell23_2874627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 4].length) (baseStart_2874627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874627 prefixEnd_2874627 := by exact prefixLift 2874627
  have htrace : WordTrace (prefixWord ++ tailWord_2874627) baseStart_2874627 baseEnd_2874627 := by
    simpa [prefixWord, tailWord_2874627, baseEnd_2874627] using wordTrace_append hprefix tailTrace_2874627
  have hstable : (prefixWord ++ tailWord_2874627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874627).length < 2 ^ (prefixWord ++ tailWord_2874627).sum := by decide
  have hdescent : baseEnd_2874627 < baseStart_2874627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874680 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_2874680 : Nat := 118140960795 + 2874680 * 2 ^ 59
def prefixEnd_2874680 : Nat := 4983230072969 + 3 ^ 40 * 2874680 * 2
def baseEnd_2874680 : Nat := 1476092567866918034979593

theorem tailTrace_2874680 : CollatzResearch.WordTrace tailWord_2874680 prefixEnd_2874680 1476092567866918034979593 := by
  unfold tailWord_2874680
  simp only [CollatzResearch.WordTrace]
  refine ⟨52424096612766395551042747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69898795483688527401390329 52424096612766395551042747)
  ·
    refine ⟨78636144919149593326564121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52424096612766395551042747 78636144919149593326564121)
    ·
      refine ⟨58977108689362194994923091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78636144919149593326564121 58977108689362194994923091)
      ·
        refine ⟨88465663034043292492384637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58977108689362194994923091 88465663034043292492384637)
        ·
          refine ⟨33174623637766234684644239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88465663034043292492384637 33174623637766234684644239)
          ·
            refine ⟨49761935456649352026966359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33174623637766234684644239 49761935456649352026966359)
            ·
              refine ⟨74642903184974028040449539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49761935456649352026966359 74642903184974028040449539)
              ·
                refine ⟨111964354777461042060674309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74642903184974028040449539 111964354777461042060674309)
                ·
                  refine ⟨20993316520773945386376433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111964354777461042060674309 20993316520773945386376433)
                  ·
                    refine ⟨15744987390580459039782325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20993316520773945386376433 15744987390580459039782325)
                    ·
                      refine ⟨1476092567866918034979593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15744987390580459039782325 1476092567866918034979593)
                      ·
                        rfl

theorem cell23_2874680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_2874680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874680 prefixEnd_2874680 := by exact prefixLift 2874680
  have htrace : WordTrace (prefixWord ++ tailWord_2874680) baseStart_2874680 baseEnd_2874680 := by
    simpa [prefixWord, tailWord_2874680, baseEnd_2874680] using wordTrace_append hprefix tailTrace_2874680
  have hstable : (prefixWord ++ tailWord_2874680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874680).length < 2 ^ (prefixWord ++ tailWord_2874680).sum := by decide
  have hdescent : baseEnd_2874680 < baseStart_2874680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874684 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2874684 : Nat := 118140960795 + 2874684 * 2 ^ 59
def prefixEnd_2874684 : Nat := 4983230072969 + 3 ^ 40 * 2874684 * 2
def baseEnd_2874684 : Nat := 1476094621789536019329575

theorem tailTrace_2874684 : CollatzResearch.WordTrace tailWord_2874684 prefixEnd_2874684 1476094621789536019329575 := by
  unfold tailWord_2874684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52424169558759149892615553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69898892745012199856820737 52424169558759149892615553)
  ·
    refine ⟨39318127169069362419461665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52424169558759149892615553 39318127169069362419461665)
    ·
      refine ⟨29488595376802021814596249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39318127169069362419461665 29488595376802021814596249)
      ·
        refine ⟨22116446532601516360947187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29488595376802021814596249 22116446532601516360947187)
        ·
          refine ⟨33174669798902274541420781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22116446532601516360947187 33174669798902274541420781)
          ·
            refine ⟨12440501174588352953032793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33174669798902274541420781 12440501174588352953032793)
            ·
              refine ⟨9330375880941264714774595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12440501174588352953032793 9330375880941264714774595)
              ·
                refine ⟨13995563821411897072161893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330375880941264714774595 13995563821411897072161893)
                ·
                  refine ⟨2624168216514730701030355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13995563821411897072161893 2624168216514730701030355)
                  ·
                    refine ⟨3936252324772096051545533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2624168216514730701030355 3936252324772096051545533)
                    ·
                      refine ⟨1476094621789536019329575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3936252324772096051545533 1476094621789536019329575)
                      ·
                        rfl

theorem cell23_2874684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2874684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874684 prefixEnd_2874684 := by exact prefixLift 2874684
  have htrace : WordTrace (prefixWord ++ tailWord_2874684) baseStart_2874684 baseEnd_2874684 := by
    simpa [prefixWord, tailWord_2874684, baseEnd_2874684] using wordTrace_append hprefix tailTrace_2874684
  have hstable : (prefixWord ++ tailWord_2874684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874684).length < 2 ^ (prefixWord ++ tailWord_2874684).sum := by decide
  have hdescent : baseEnd_2874684 < baseStart_2874684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874685 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2874685 : Nat := 118140960795 + 2874685 * 2 ^ 59
def prefixEnd_2874685 : Nat := 4983230072969 + 3 ^ 40 * 2874685 * 2
def baseEnd_2874685 : Nat := 1476095135270190515417071

theorem tailTrace_2874685 : CollatzResearch.WordTrace tailWord_2874685 prefixEnd_2874685 1476095135270190515417071 := by
  unfold tailWord_2874685
  simp only [CollatzResearch.WordTrace]
  refine ⟨104848375590514676956017509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69898917060343117970678339 104848375590514676956017509)
  ·
    refine ⟨19659070423221501929253283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104848375590514676956017509 19659070423221501929253283)
    ·
      refine ⟨29488605634832252893879925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19659070423221501929253283 29488605634832252893879925)
      ·
        refine ⟨2764556778265523708801243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29488605634832252893879925 2764556778265523708801243)
        ·
          refine ⟨4146835167398285563201865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764556778265523708801243 4146835167398285563201865)
          ·
            refine ⟨3110126375548714172401399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146835167398285563201865 3110126375548714172401399)
            ·
              refine ⟨4665189563323071258602099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110126375548714172401399 4665189563323071258602099)
              ·
                refine ⟨6997784344984606887903149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665189563323071258602099 6997784344984606887903149)
                ·
                  refine ⟨2624169129369227582963681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6997784344984606887903149 2624169129369227582963681)
                  ·
                    refine ⟨1968126847026920687222761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624169129369227582963681 1968126847026920687222761)
                    ·
                      refine ⟨1476095135270190515417071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968126847026920687222761 1476095135270190515417071)
                      ·
                        rfl

theorem cell23_2874685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2874685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874685 prefixEnd_2874685 := by exact prefixLift 2874685
  have htrace : WordTrace (prefixWord ++ tailWord_2874685) baseStart_2874685 baseEnd_2874685 := by
    simpa [prefixWord, tailWord_2874685, baseEnd_2874685] using wordTrace_append hprefix tailTrace_2874685
  have hstable : (prefixWord ++ tailWord_2874685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874685).length < 2 ^ (prefixWord ++ tailWord_2874685).sum := by decide
  have hdescent : baseEnd_2874685 < baseStart_2874685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874711 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 1, 3, 2]
def baseStart_2874711 : Nat := 118140960795 + 2874711 * 2 ^ 59
def prefixEnd_2874711 : Nat := 4983230072969 + 3 ^ 40 * 2874711 * 2
def baseEnd_2874711 : Nat := 1476108485767207413691951

theorem tailTrace_2874711 : CollatzResearch.WordTrace tailWord_2874711 prefixEnd_2874711 1476108485767207413691951 := by
  unfold tailWord_2874711
  simp only [CollatzResearch.WordTrace]
  refine ⟨104849323888420483396463987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69899549258946988930975991 104849323888420483396463987)
  ·
    refine ⟨157273985832630725094695981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104849323888420483396463987 157273985832630725094695981)
    ·
      refine ⟨58977744687236521910510993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157273985832630725094695981 58977744687236521910510993)
      ·
        refine ⟨44233308515427391432883245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58977744687236521910510993 44233308515427391432883245)
        ·
          refine ⟨16587490693285271787331217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44233308515427391432883245 16587490693285271787331217)
          ·
            refine ⟨12440618019963953840498413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16587490693285271787331217 12440618019963953840498413)
            ·
              refine ⟨4665231757486482690186905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12440618019963953840498413 4665231757486482690186905)
              ·
                refine ⟨3498923818114862017640179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4665231757486482690186905 3498923818114862017640179)
                ·
                  refine ⟨5248385727172293026460269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498923818114862017640179 5248385727172293026460269)
                  ·
                    refine ⟨1968144647689609884922601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5248385727172293026460269 1968144647689609884922601)
                    ·
                      refine ⟨1476108485767207413691951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968144647689609884922601 1476108485767207413691951)
                      ·
                        rfl

theorem cell23_2874711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_2874711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874711 prefixEnd_2874711 := by exact prefixLift 2874711
  have htrace : WordTrace (prefixWord ++ tailWord_2874711) baseStart_2874711 baseEnd_2874711 := by
    simpa [prefixWord, tailWord_2874711, baseEnd_2874711] using wordTrace_append hprefix tailTrace_2874711
  have hstable : (prefixWord ++ tailWord_2874711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874711).length < 2 ^ (prefixWord ++ tailWord_2874711).sum := by decide
  have hdescent : baseEnd_2874711 < baseStart_2874711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874724 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_2874724 : Nat := 118140960795 + 2874724 * 2 ^ 59
def prefixEnd_2874724 : Nat := 4983230072969 + 3 ^ 40 * 2874724 * 2
def baseEnd_2874724 : Nat := 1476115161015715862829391

theorem tailTrace_2874724 : CollatzResearch.WordTrace tailWord_2874724 prefixEnd_2874724 1476115161015715862829391 := by
  unfold tailWord_2874724
  simp only [CollatzResearch.WordTrace]
  refine ⟨52424899018686693308343613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69899865358248924411124817 52424899018686693308343613)
  ·
    refine ⟨19659337132007509990628855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52424899018686693308343613 19659337132007509990628855)
    ·
      refine ⟨29489005698011264985943283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19659337132007509990628855 29489005698011264985943283)
      ·
        refine ⟨44233508547016897478914925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29489005698011264985943283 44233508547016897478914925)
        ·
          refine ⟨16587565705131336554593097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44233508547016897478914925 16587565705131336554593097)
          ·
            refine ⟨12440674278848502415944823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16587565705131336554593097 12440674278848502415944823)
            ·
              refine ⟨18661011418272753623917235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12440674278848502415944823 18661011418272753623917235)
              ·
                refine ⟨27991517127409130435875853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18661011418272753623917235 27991517127409130435875853)
                ·
                  refine ⟨10496818922778423913453445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27991517127409130435875853 10496818922778423913453445)
                  ·
                    refine ⟨1968153548020954483772521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10496818922778423913453445 1968153548020954483772521)
                    ·
                      refine ⟨1476115161015715862829391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968153548020954483772521 1476115161015715862829391)
                      ·
                        rfl

theorem cell23_2874724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_2874724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874724 prefixEnd_2874724 := by exact prefixLift 2874724
  have htrace : WordTrace (prefixWord ++ tailWord_2874724) baseStart_2874724 baseEnd_2874724 := by
    simpa [prefixWord, tailWord_2874724, baseEnd_2874724] using wordTrace_append hprefix tailTrace_2874724
  have hstable : (prefixWord ++ tailWord_2874724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874724).length < 2 ^ (prefixWord ++ tailWord_2874724).sum := by decide
  have hdescent : baseEnd_2874724 < baseStart_2874724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874757 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_2874757 : Nat := 118140960795 + 2874757 * 2 ^ 59
def prefixEnd_2874757 : Nat := 4983230072969 + 3 ^ 40 * 2874757 * 2
def baseEnd_2874757 : Nat := 1476132105877314233716739

theorem tailTrace_2874757 : CollatzResearch.WordTrace tailWord_2874757 prefixEnd_2874757 1476132105877314233716739 := by
  unfold tailWord_2874757
  simp only [CollatzResearch.WordTrace]
  refine ⟨104851001646253833252638525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69900667764169222168425683 104851001646253833252638525)
  ·
    refine ⟨39319125617345187469739447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104851001646253833252638525 39319125617345187469739447)
    ·
      refine ⟨58978688426017781204609171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39319125617345187469739447 58978688426017781204609171)
      ·
        refine ⟨88468032639026671806913757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58978688426017781204609171 88468032639026671806913757)
        ·
          refine ⟨33175512239635001927592659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88468032639026671806913757 33175512239635001927592659)
          ·
            refine ⟨49763268359452502891388989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33175512239635001927592659 49763268359452502891388989)
            ·
              refine ⟨18661225634794688584270871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49763268359452502891388989 18661225634794688584270871)
              ·
                refine ⟨27991838452192032876406307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18661225634794688584270871 27991838452192032876406307)
                ·
                  refine ⟨41987757678288049314609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27991838452192032876406307 41987757678288049314609461)
                  ·
                    refine ⟨3936352282339504623244637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41987757678288049314609461 3936352282339504623244637)
                    ·
                      refine ⟨1476132105877314233716739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3936352282339504623244637 1476132105877314233716739)
                      ·
                        rfl

theorem cell23_2874757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_2874757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874757 prefixEnd_2874757 := by exact prefixLift 2874757
  have htrace : WordTrace (prefixWord ++ tailWord_2874757) baseStart_2874757 baseEnd_2874757 := by
    simpa [prefixWord, tailWord_2874757, baseEnd_2874757] using wordTrace_append hprefix tailTrace_2874757
  have hstable : (prefixWord ++ tailWord_2874757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874757).length < 2 ^ (prefixWord ++ tailWord_2874757).sum := by decide
  have hdescent : baseEnd_2874757 < baseStart_2874757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874777 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_2874777 : Nat := 118140960795 + 2874777 * 2 ^ 59
def prefixEnd_2874777 : Nat := 4983230072969 + 3 ^ 40 * 2874777 * 2
def baseEnd_2874777 : Nat := 492047458496801385155549

theorem tailTrace_2874777 : CollatzResearch.WordTrace tailWord_2874777 prefixEnd_2874777 492047458496801385155549 := by
  unfold tailWord_2874777
  simp only [CollatzResearch.WordTrace]
  refine ⟨104851731106181376668366585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69901154070787584445577723 104851731106181376668366585)
  ·
    refine ⟨78638798329636032501274939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104851731106181376668366585 78638798329636032501274939)
    ·
      refine ⟨117958197494454048751912409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78638798329636032501274939 117958197494454048751912409)
      ·
        refine ⟨88468648120840536563934307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117958197494454048751912409 88468648120840536563934307)
        ·
          refine ⟨132702972181260804845901461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88468648120840536563934307 132702972181260804845901461)
          ·
            refine ⟨6220451820996600227151631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132702972181260804845901461 6220451820996600227151631)
            ·
              refine ⟨9330677731494900340727447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220451820996600227151631 9330677731494900340727447)
              ·
                refine ⟨13996016597242350511091171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330677731494900340727447 13996016597242350511091171)
                ·
                  refine ⟨20994024895863525766636757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13996016597242350511091171 20994024895863525766636757)
                  ·
                    refine ⟨492047458496801385155549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20994024895863525766636757 492047458496801385155549)
                    ·
                      rfl

theorem cell23_2874777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_2874777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874777 prefixEnd_2874777 := by exact prefixLift 2874777
  have htrace : WordTrace (prefixWord ++ tailWord_2874777) baseStart_2874777 baseEnd_2874777 := by
    simpa [prefixWord, tailWord_2874777, baseEnd_2874777] using wordTrace_append hprefix tailTrace_2874777
  have hstable : (prefixWord ++ tailWord_2874777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874777).length < 2 ^ (prefixWord ++ tailWord_2874777).sum := by decide
  have hdescent : baseEnd_2874777 < baseStart_2874777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874781 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 5]
def baseStart_2874781 : Nat := 118140960795 + 2874781 * 2 ^ 59
def prefixEnd_2874781 : Nat := 4983230072969 + 3 ^ 40 * 2874781 * 2
def baseEnd_2874781 : Nat := 164016047712558015535181

theorem tailTrace_2874781 : CollatzResearch.WordTrace tailWord_2874781 prefixEnd_2874781 164016047712558015535181 := by
  unfold tailWord_2874781
  simp only [CollatzResearch.WordTrace]
  refine ⟨104851876998166885351512197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69901251332111256901008131 104851876998166885351512197)
  ·
    refine ⟨19659726937156291003408537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104851876998166885351512197 19659726937156291003408537)
    ·
      refine ⟨14744795202867218252556403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19659726937156291003408537 14744795202867218252556403)
      ·
        refine ⟨22117192804300827378834605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14744795202867218252556403 22117192804300827378834605)
        ·
          refine ⟨8293947301612810267062977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22117192804300827378834605 8293947301612810267062977)
          ·
            refine ⟨6220460476209607700297233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8293947301612810267062977 6220460476209607700297233)
            ·
              refine ⟨4665345357157205775222925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220460476209607700297233 4665345357157205775222925)
              ·
                refine ⟨1749504508933952165708597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665345357157205775222925 1749504508933952165708597)
                ·
                  refine ⟨164016047712558015535181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1749504508933952165708597 164016047712558015535181)
                  ·
                    rfl

theorem cell23_2874781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_2874781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874781 prefixEnd_2874781 := by exact prefixLift 2874781
  have htrace : WordTrace (prefixWord ++ tailWord_2874781) baseStart_2874781 baseEnd_2874781 := by
    simpa [prefixWord, tailWord_2874781, baseEnd_2874781] using wordTrace_append hprefix tailTrace_2874781
  have hstable : (prefixWord ++ tailWord_2874781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874781).length < 2 ^ (prefixWord ++ tailWord_2874781).sum := by decide
  have hdescent : baseEnd_2874781 < baseStart_2874781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874792 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2874792 : Nat := 118140960795 + 2874792 * 2 ^ 59
def prefixEnd_2874792 : Nat := 4983230072969 + 3 ^ 40 * 2874792 * 2
def baseEnd_2874792 : Nat := 1476150077700221596779079

theorem tailTrace_2874792 : CollatzResearch.WordTrace tailWord_2874792 prefixEnd_2874792 1476150077700221596779079 := by
  unfold tailWord_2874792
  simp only [CollatzResearch.WordTrace]
  refine ⟨52426139100563517115081315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69901518800751356153441753 52426139100563517115081315)
  ·
    refine ⟨78639208650845275672621973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52426139100563517115081315 78639208650845275672621973)
    ·
      refine ⟨3686212905508372297154155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78639208650845275672621973 3686212905508372297154155)
      ·
        refine ⟨5529319358262558445731233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686212905508372297154155 5529319358262558445731233)
        ·
          refine ⟨4146989518696918834298425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529319358262558445731233 4146989518696918834298425)
          ·
            refine ⟨3110242139022689125723819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146989518696918834298425 3110242139022689125723819)
            ·
              refine ⟨4665363208534033688585729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110242139022689125723819 4665363208534033688585729)
              ·
                refine ⟨3499022406400525266439297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4665363208534033688585729 3499022406400525266439297)
                ·
                  refine ⟨2624266804800393949829473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499022406400525266439297 2624266804800393949829473)
                  ·
                    refine ⟨1968200103600295462372105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624266804800393949829473 1968200103600295462372105)
                    ·
                      refine ⟨1476150077700221596779079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968200103600295462372105 1476150077700221596779079)
                      ·
                        rfl

theorem cell23_2874792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2874792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874792 prefixEnd_2874792 := by exact prefixLift 2874792
  have htrace : WordTrace (prefixWord ++ tailWord_2874792) baseStart_2874792 baseEnd_2874792 := by
    simpa [prefixWord, tailWord_2874792, baseEnd_2874792] using wordTrace_append hprefix tailTrace_2874792
  have hstable : (prefixWord ++ tailWord_2874792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874792).length < 2 ^ (prefixWord ++ tailWord_2874792).sum := by decide
  have hdescent : baseEnd_2874792 < baseStart_2874792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874824 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 3, 4]
def baseStart_2874824 : Nat := 118140960795 + 2874824 * 2 ^ 59
def prefixEnd_2874824 : Nat := 4983230072969 + 3 ^ 40 * 2874824 * 2
def baseEnd_2874824 : Nat := 492055503027055157192977

theorem tailTrace_2874824 : CollatzResearch.WordTrace tailWord_2874824 prefixEnd_2874824 492055503027055157192977 := by
  unfold tailWord_2874824
  simp only [CollatzResearch.WordTrace]
  refine ⟨52426722668505551847663763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69902296891340735796885017 52426722668505551847663763)
  ·
    refine ⟨78640084002758327771495645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52426722668505551847663763 78640084002758327771495645)
    ·
      refine ⟨29490031501034372914310867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78640084002758327771495645 29490031501034372914310867)
      ·
        refine ⟨44235047251551559371466301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29490031501034372914310867 44235047251551559371466301)
        ·
          refine ⟨16588142719331834764299863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44235047251551559371466301 16588142719331834764299863)
          ·
            refine ⟨24882214078997752146449795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588142719331834764299863 24882214078997752146449795)
            ·
              refine ⟨37323321118496628219674693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24882214078997752146449795 37323321118496628219674693)
              ·
                refine ⟨6998122709718117791189005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37323321118496628219674693 6998122709718117791189005)
                ·
                  refine ⟨2624296016144294171695877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6998122709718117791189005 2624296016144294171695877)
                  ·
                    refine ⟨492055503027055157192977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624296016144294171695877 492055503027055157192977)
                    ·
                      rfl

theorem cell23_2874824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_2874824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874824 prefixEnd_2874824 := by exact prefixLift 2874824
  have htrace : WordTrace (prefixWord ++ tailWord_2874824) baseStart_2874824 baseEnd_2874824 := by
    simpa [prefixWord, tailWord_2874824, baseEnd_2874824] using wordTrace_append hprefix tailTrace_2874824
  have hstable : (prefixWord ++ tailWord_2874824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874824).length < 2 ^ (prefixWord ++ tailWord_2874824).sum := by decide
  have hdescent : baseEnd_2874824 < baseStart_2874824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874837 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 10]
def baseStart_2874837 : Nat := 118140960795 + 2874837 * 2 ^ 59
def prefixEnd_2874837 : Nat := 4983230072969 + 3 ^ 40 * 2874837 * 2
def baseEnd_2874837 : Nat := 164019242703297102301819

theorem tailTrace_2874837 : CollatzResearch.WordTrace tailWord_2874837 prefixEnd_2874837 164019242703297102301819 := by
  unfold tailWord_2874837
  simp only [CollatzResearch.WordTrace]
  refine ⟨104853919485964006915550765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69902612990642671277033843 104853919485964006915550765)
  ·
    refine ⟨39320219807236502593331537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104853919485964006915550765 39320219807236502593331537)
    ·
      refine ⟨29490164855427376944998653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39320219807236502593331537 29490164855427376944998653)
      ·
        refine ⟨11058811820785266354374495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29490164855427376944998653 11058811820785266354374495)
        ·
          refine ⟨16588217731177899531561743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11058811820785266354374495 16588217731177899531561743)
          ·
            refine ⟨24882326596766849297342615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588217731177899531561743 24882326596766849297342615)
            ·
              refine ⟨37323489895150273946013923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24882326596766849297342615 37323489895150273946013923)
              ·
                refine ⟨55985234842725410919020885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37323489895150273946013923 55985234842725410919020885)
                ·
                  refine ⟨164019242703297102301819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 55985234842725410919020885 164019242703297102301819)
                  ·
                    rfl

theorem cell23_2874837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_2874837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874837 prefixEnd_2874837 := by exact prefixLift 2874837
  have htrace : WordTrace (prefixWord ++ tailWord_2874837) baseStart_2874837 baseEnd_2874837 := by
    simpa [prefixWord, tailWord_2874837, baseEnd_2874837] using wordTrace_append hprefix tailTrace_2874837
  have hstable : (prefixWord ++ tailWord_2874837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874837).length < 2 ^ (prefixWord ++ tailWord_2874837).sum := by decide
  have hdescent : baseEnd_2874837 < baseStart_2874837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874851 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2874851 : Nat := 118140960795 + 2874851 * 2 ^ 59
def prefixEnd_2874851 : Nat := 4983230072969 + 3 ^ 40 * 2874851 * 2
def baseEnd_2874851 : Nat := 1476180373058836865941307

theorem tailTrace_2874851 : CollatzResearch.WordTrace tailWord_2874851 prefixEnd_2874851 1476180373058836865941307 := by
  unfold tailWord_2874851
  simp only [CollatzResearch.WordTrace]
  refine ⟨104854430107913287306560407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69902953405275524871040271 104854430107913287306560407)
  ·
    refine ⟨157281645161869930959840611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104854430107913287306560407 157281645161869930959840611)
    ·
      refine ⟨235922467742804896439760917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157281645161869930959840611 235922467742804896439760917)
      ·
        refine ⟨11058865675443979520613793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235922467742804896439760917 11058865675443979520613793)
        ·
          refine ⟨8294149256582984640460345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11058865675443979520613793 8294149256582984640460345)
          ·
            refine ⟨6220611942437238480345259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294149256582984640460345 6220611942437238480345259)
            ·
              refine ⟨9330917913655857720517889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220611942437238480345259 9330917913655857720517889)
              ·
                refine ⟨6998188435241893290388417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9330917913655857720517889 6998188435241893290388417)
                ·
                  refine ⟨5248641326431419967791313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6998188435241893290388417 5248641326431419967791313)
                  ·
                    refine ⟨3936480994823564975843485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5248641326431419967791313 3936480994823564975843485)
                    ·
                      refine ⟨1476180373058836865941307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3936480994823564975843485 1476180373058836865941307)
                      ·
                        rfl

theorem cell23_2874851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2874851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874851 prefixEnd_2874851 := by exact prefixLift 2874851
  have htrace : WordTrace (prefixWord ++ tailWord_2874851) baseStart_2874851 baseEnd_2874851 := by
    simpa [prefixWord, tailWord_2874851, baseEnd_2874851] using wordTrace_append hprefix tailTrace_2874851
  have hstable : (prefixWord ++ tailWord_2874851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874851).length < 2 ^ (prefixWord ++ tailWord_2874851).sum := by decide
  have hdescent : baseEnd_2874851 < baseStart_2874851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874858 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2874858 : Nat := 118140960795 + 2874858 * 2 ^ 59
def prefixEnd_2874858 : Nat := 4983230072969 + 3 ^ 40 * 2874858 * 2
def baseEnd_2874858 : Nat := 492061322474472779517925

theorem tailTrace_2874858 : CollatzResearch.WordTrace tailWord_2874858 prefixEnd_2874858 492061322474472779517925 := by
  unfold tailWord_2874858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26213671354721981875516307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69903123612591951668043485 26213671354721981875516307)
  ·
    refine ⟨39320507032082972813274461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26213671354721981875516307 39320507032082972813274461)
    ·
      refine ⟨14745190137031114804977923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39320507032082972813274461 14745190137031114804977923)
      ·
        refine ⟨22117785205546672207466885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14745190137031114804977923 22117785205546672207466885)
        ·
          refine ⟨4147084726040001038900041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22117785205546672207466885 4147084726040001038900041)
          ·
            refine ⟨3110313544530000779175031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4147084726040001038900041 3110313544530000779175031)
            ·
              refine ⟨4665470316795001168762547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110313544530000779175031 4665470316795001168762547)
              ·
                refine ⟨6998205475192501753143821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665470316795001168762547 6998205475192501753143821)
                ·
                  refine ⟨2624327053197188157428933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6998205475192501753143821 2624327053197188157428933)
                  ·
                    refine ⟨492061322474472779517925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624327053197188157428933 492061322474472779517925)
                    ·
                      rfl

theorem cell23_2874858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2874858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874858 prefixEnd_2874858 := by exact prefixLift 2874858
  have htrace : WordTrace (prefixWord ++ tailWord_2874858) baseStart_2874858 baseEnd_2874858 := by
    simpa [prefixWord, tailWord_2874858, baseEnd_2874858] using wordTrace_append hprefix tailTrace_2874858
  have hstable : (prefixWord ++ tailWord_2874858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874858).length < 2 ^ (prefixWord ++ tailWord_2874858).sum := by decide
  have hdescent : baseEnd_2874858 < baseStart_2874858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874915 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 1, 1, 3]
def baseStart_2874915 : Nat := 118140960795 + 2874915 * 2 ^ 59
def prefixEnd_2874915 : Nat := 4983230072969 + 3 ^ 40 * 2874915 * 2
def baseEnd_2874915 : Nat := 1476213235820724615541013

theorem tailTrace_2874915 : CollatzResearch.WordTrace tailWord_2874915 prefixEnd_2874915 1476213235820724615541013 := by
  unfold tailWord_2874915
  simp only [CollatzResearch.WordTrace]
  refine ⟨104856764379681426236890199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69904509586454284157926799 104856764379681426236890199)
  ·
    refine ⟨157285146569522139355335299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104856764379681426236890199 157285146569522139355335299)
    ·
      refine ⟨235927719854283209033002949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157285146569522139355335299 235927719854283209033002949)
      ·
        refine ⟨44236447472678101693688053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235927719854283209033002949 44236447472678101693688053)
        ·
          refine ⟨4147166950563572033783255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44236447472678101693688053 4147166950563572033783255)
          ·
            refine ⟨6220750425845358050674883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147166950563572033783255 6220750425845358050674883)
            ·
              refine ⟨9331125638768037076012325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220750425845358050674883 9331125638768037076012325)
              ·
                refine ⟨1749586057269006951752311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9331125638768037076012325 1749586057269006951752311)
                ·
                  refine ⟨2624379085903510427628467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749586057269006951752311 2624379085903510427628467)
                  ·
                    refine ⟨3936568628855265641442701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2624379085903510427628467 3936568628855265641442701)
                    ·
                      refine ⟨1476213235820724615541013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3936568628855265641442701 1476213235820724615541013)
                      ·
                        rfl

theorem cell23_2874915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_2874915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874915 prefixEnd_2874915 := by exact prefixLift 2874915
  have htrace : WordTrace (prefixWord ++ tailWord_2874915) baseStart_2874915 baseEnd_2874915 := by
    simpa [prefixWord, tailWord_2874915, baseEnd_2874915] using wordTrace_append hprefix tailTrace_2874915
  have hstable : (prefixWord ++ tailWord_2874915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874915).length < 2 ^ (prefixWord ++ tailWord_2874915).sum := by decide
  have hdescent : baseEnd_2874915 < baseStart_2874915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874931 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 2, 4]
def baseStart_2874931 : Nat := 118140960795 + 2874931 * 2 ^ 59
def prefixEnd_2874931 : Nat := 4983230072969 + 3 ^ 40 * 2874931 * 2
def baseEnd_2874931 : Nat := 492073817170398850980313

theorem tailTrace_2874931 : CollatzResearch.WordTrace tailWord_2874931 prefixEnd_2874931 492073817170398850980313 := by
  unfold tailWord_2874931
  simp only [CollatzResearch.WordTrace]
  refine ⟨104857347947623460969472647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69904898631748973979648431 104857347947623460969472647)
  ·
    refine ⟨157286021921435191454208971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104857347947623460969472647 157286021921435191454208971)
    ·
      refine ⟨235929032882152787181313457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157286021921435191454208971 235929032882152787181313457)
      ·
        refine ⟨176946774661614590385985093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235929032882152787181313457 176946774661614590385985093)
        ·
          refine ⟨33177520249052735697372205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176946774661614590385985093 33177520249052735697372205)
          ·
            refine ⟨12441570093394775886514577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33177520249052735697372205 12441570093394775886514577)
            ·
              refine ⟨9331177570046081914885933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12441570093394775886514577 9331177570046081914885933)
              ·
                refine ⟨3499191588767280718082225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9331177570046081914885933 3499191588767280718082225)
                ·
                  refine ⟨2624393691575460538561669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499191588767280718082225 2624393691575460538561669)
                  ·
                    refine ⟨492073817170398850980313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2624393691575460538561669 492073817170398850980313)
                    ·
                      rfl

theorem cell23_2874931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 4].length) (baseStart_2874931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874931 prefixEnd_2874931 := by exact prefixLift 2874931
  have htrace : WordTrace (prefixWord ++ tailWord_2874931) baseStart_2874931 baseEnd_2874931 := by
    simpa [prefixWord, tailWord_2874931, baseEnd_2874931] using wordTrace_append hprefix tailTrace_2874931
  have hstable : (prefixWord ++ tailWord_2874931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874931).length < 2 ^ (prefixWord ++ tailWord_2874931).sum := by decide
  have hdescent : baseEnd_2874931 < baseStart_2874931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874938 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2]
def baseStart_2874938 : Nat := 118140960795 + 2874938 * 2 ^ 59
def prefixEnd_2874938 : Nat := 4983230072969 + 3 ^ 40 * 2874938 * 2
def baseEnd_2874938 : Nat := 1476225045875778025553407

theorem tailTrace_2874938 : CollatzResearch.WordTrace tailWord_2874938 prefixEnd_2874938 1476225045875778025553407 := by
  unfold tailWord_2874938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26214400814649525291244367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69905068839065400776651645 26214400814649525291244367)
  ·
    refine ⟨39321601221974287936866551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26214400814649525291244367 39321601221974287936866551)
    ·
      refine ⟨58982401832961431905299827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39321601221974287936866551 58982401832961431905299827)
      ·
        refine ⟨88473602749442147857949741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58982401832961431905299827 88473602749442147857949741)
        ·
          refine ⟨33177601031040805446731153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88473602749442147857949741 33177601031040805446731153)
          ·
            refine ⟨24883200773280604085048365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33177601031040805446731153 24883200773280604085048365)
            ·
              refine ⟨9331200289980226531893137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24883200773280604085048365 9331200289980226531893137)
              ·
                refine ⟨6998400217485169898919853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9331200289980226531893137 6998400217485169898919853)
                ·
                  refine ⟨2624400081556938712094945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6998400217485169898919853 2624400081556938712094945)
                  ·
                    refine ⟨1968300061167704034071209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624400081556938712094945 1968300061167704034071209)
                    ·
                      refine ⟨1476225045875778025553407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968300061167704034071209 1476225045875778025553407)
                      ·
                        rfl

theorem cell23_2874938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_2874938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874938 prefixEnd_2874938 := by exact prefixLift 2874938
  have htrace : WordTrace (prefixWord ++ tailWord_2874938) baseStart_2874938 baseEnd_2874938 := by
    simpa [prefixWord, tailWord_2874938, baseEnd_2874938] using wordTrace_append hprefix tailTrace_2874938
  have hstable : (prefixWord ++ tailWord_2874938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874938).length < 2 ^ (prefixWord ++ tailWord_2874938).sum := by decide
  have hdescent : baseEnd_2874938 < baseStart_2874938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874972 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2874972 : Nat := 118140960795 + 2874972 * 2 ^ 59
def prefixEnd_2874972 : Nat := 4983230072969 + 3 ^ 40 * 2874972 * 2
def baseEnd_2874972 : Nat := 1476242504218030892528251

theorem tailTrace_2874972 : CollatzResearch.WordTrace tailWord_2874972 prefixEnd_2874972 1476242504218030892528251 := by
  unfold tailWord_2874972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52429421670237462485857585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69905895560316616647810113 52429421670237462485857585)
  ·
    refine ⟨39322066252678096864393189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52429421670237462485857585 39322066252678096864393189)
    ·
      refine ⟨7372887422377143162073723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39322066252678096864393189 7372887422377143162073723)
      ·
        refine ⟨11059331133565714743110585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7372887422377143162073723 11059331133565714743110585)
        ·
          refine ⟨8294498350174286057332939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11059331133565714743110585 8294498350174286057332939)
          ·
            refine ⟨12441747525261429085999409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294498350174286057332939 12441747525261429085999409)
            ·
              refine ⟨9331310643946071814499557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12441747525261429085999409 9331310643946071814499557)
              ·
                refine ⟨1749620745739888465218667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9331310643946071814499557 1749620745739888465218667)
                ·
                  refine ⟨2624431118609832697828001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749620745739888465218667 2624431118609832697828001)
                  ·
                    refine ⟨1968323338957374523371001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624431118609832697828001 1968323338957374523371001)
                    ·
                      refine ⟨1476242504218030892528251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968323338957374523371001 1476242504218030892528251)
                      ·
                        rfl

theorem cell23_2874972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2874972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2874972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2874972 prefixEnd_2874972 := by exact prefixLift 2874972
  have htrace : WordTrace (prefixWord ++ tailWord_2874972) baseStart_2874972 baseEnd_2874972 := by
    simpa [prefixWord, tailWord_2874972, baseEnd_2874972] using wordTrace_append hprefix tailTrace_2874972
  have hstable : (prefixWord ++ tailWord_2874972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874972).length < 2 ^ (prefixWord ++ tailWord_2874972).sum := by decide
  have hdescent : baseEnd_2874972 < baseStart_2874972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875011 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 3, 4, 2]
def baseStart_2875011 : Nat := 118140960795 + 2875011 * 2 ^ 59
def prefixEnd_2875011 : Nat := 4983230072969 + 3 ^ 40 * 2875011 * 2
def baseEnd_2875011 : Nat := 1476262529963556239940571

theorem tailTrace_2875011 : CollatzResearch.WordTrace tailWord_2875011 prefixEnd_2875011 1476262529963556239940571 := by
  unfold tailWord_2875011
  simp only [CollatzResearch.WordTrace]
  refine ⟨104860265787333634632384887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69906843858222423088256591 104860265787333634632384887)
  ·
    refine ⟨157290398681000451948577331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104860265787333634632384887 157290398681000451948577331)
    ·
      refine ⟨235935598021500677922865997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157290398681000451948577331 235935598021500677922865997)
      ·
        refine ⟨88475849258062754221074749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235935598021500677922865997 88475849258062754221074749)
        ·
          refine ⟨33178443471773532832903031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88475849258062754221074749 33178443471773532832903031)
          ·
            refine ⟨49767665207660299249354547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33178443471773532832903031 49767665207660299249354547)
            ·
              refine ⟨74651497811490448874031821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49767665207660299249354547 74651497811490448874031821)
              ·
                refine ⟨27994311679308918327761933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74651497811490448874031821 27994311679308918327761933)
                ·
                  refine ⟨10497866879740844372910725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27994311679308918327761933 10497866879740844372910725)
                  ·
                    refine ⟨1968350039951408319920761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10497866879740844372910725 1968350039951408319920761)
                    ·
                      refine ⟨1476262529963556239940571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968350039951408319920761 1476262529963556239940571)
                      ·
                        rfl

theorem cell23_2875011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_2875011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875011 prefixEnd_2875011 := by exact prefixLift 2875011
  have htrace : WordTrace (prefixWord ++ tailWord_2875011) baseStart_2875011 baseEnd_2875011 := by
    simpa [prefixWord, tailWord_2875011, baseEnd_2875011] using wordTrace_append hprefix tailTrace_2875011
  have hstable : (prefixWord ++ tailWord_2875011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875011).length < 2 ^ (prefixWord ++ tailWord_2875011).sum := by decide
  have hdescent : baseEnd_2875011 < baseStart_2875011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875024 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_2875024 : Nat := 118140960795 + 2875024 * 2 ^ 59
def prefixEnd_2875024 : Nat := 4983230072969 + 3 ^ 40 * 2875024 * 2
def baseEnd_2875024 : Nat := 1476269205212064689078011

theorem tailTrace_2875024 : CollatzResearch.WordTrace tailWord_2875024 prefixEnd_2875024 1476269205212064689078011 := by
  unfold tailWord_2875024
  simp only [CollatzResearch.WordTrace]
  refine ⟨52430369968143268926304063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69907159957524358568405417 52430369968143268926304063)
  ·
    refine ⟨78645554952214903389456095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52430369968143268926304063 78645554952214903389456095)
    ·
      refine ⟨117968332428322355084184143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78645554952214903389456095 117968332428322355084184143)
      ·
        refine ⟨176952498642483532626276215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117968332428322355084184143 176952498642483532626276215)
        ·
          refine ⟨265428747963725298939414323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176952498642483532626276215 265428747963725298939414323)
          ·
            refine ⟨398143121945587948409121485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265428747963725298939414323 398143121945587948409121485)
            ·
              refine ⟨149303670729595480653420557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398143121945587948409121485 149303670729595480653420557)
              ·
                refine ⟨55988876523598305245032709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149303670729595480653420557 55988876523598305245032709)
                ·
                  refine ⟨10497914348174682233443633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55988876523598305245032709 10497914348174682233443633)
                  ·
                    refine ⟨7873435761131011675082725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10497914348174682233443633 7873435761131011675082725)
                    ·
                      refine ⟨1476269205212064689078011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7873435761131011675082725 1476269205212064689078011)
                      ·
                        rfl

theorem cell23_2875024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_2875024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875024 prefixEnd_2875024 := by exact prefixLift 2875024
  have htrace : WordTrace (prefixWord ++ tailWord_2875024) baseStart_2875024 baseEnd_2875024 := by
    simpa [prefixWord, tailWord_2875024, baseEnd_2875024] using wordTrace_append hprefix tailTrace_2875024
  have hstable : (prefixWord ++ tailWord_2875024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875024).length < 2 ^ (prefixWord ++ tailWord_2875024).sum := by decide
  have hdescent : baseEnd_2875024 < baseStart_2875024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
