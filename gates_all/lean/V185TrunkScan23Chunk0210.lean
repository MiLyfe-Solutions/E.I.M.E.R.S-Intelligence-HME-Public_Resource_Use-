import V185TrunkScan23Chunk0209

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1241504 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 2, 5]
def baseStart_1241504 : Nat := 118140960795 + 1241504 * 2 ^ 59
def prefixEnd_1241504 : Nat := 4983230072969 + 3 ^ 40 * 1241504 * 2
def baseEnd_1241504 : Nat := 212496095493205281196811

theorem tailTrace_1241504 : CollatzResearch.WordTrace tailWord_1241504 prefixEnd_1241504 212496095493205281196811 := by
  unfold tailWord_1241504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22640685447125257423789783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30187580596167009898386377 22640685447125257423789783)
  ·
    refine ⟨33961028170687886135684675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22640685447125257423789783 33961028170687886135684675)
    ·
      refine ⟨50941542256031829203527013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33961028170687886135684675 50941542256031829203527013)
      ·
        refine ⟨9551539173005967975661315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50941542256031829203527013 9551539173005967975661315)
        ·
          refine ⟨14327308759508951963491973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9551539173005967975661315 14327308759508951963491973)
          ·
            refine ⟨2686370392407928493154745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14327308759508951963491973 2686370392407928493154745)
            ·
              refine ⟨2014777794305946369866059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2686370392407928493154745 2014777794305946369866059)
              ·
                refine ⟨3022166691458919554799089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014777794305946369866059 3022166691458919554799089)
                ·
                  refine ⟨2266625018594189666099317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022166691458919554799089 2266625018594189666099317)
                  ·
                    refine ⟨212496095493205281196811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2266625018594189666099317 212496095493205281196811)
                    ·
                      rfl

theorem cell23_1241504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_1241504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241504 prefixEnd_1241504 := by exact prefixLift 1241504
  have htrace : WordTrace (prefixWord ++ tailWord_1241504) baseStart_1241504 baseEnd_1241504 := by
    simpa [prefixWord, tailWord_1241504, baseEnd_1241504] using wordTrace_append hprefix tailTrace_1241504
  have hstable : (prefixWord ++ tailWord_1241504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241504).length < 2 ^ (prefixWord ++ tailWord_1241504).sum := by decide
  have hdescent : baseEnd_1241504 < baseStart_1241504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241525 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 5]
def baseStart_1241525 : Nat := 118140960795 + 1241525 * 2 ^ 59
def prefixEnd_1241525 : Nat := 4983230072969 + 3 ^ 40 * 1241525 * 2
def baseEnd_1241525 : Nat := 70833229952595584603093

theorem tailTrace_1241525 : CollatzResearch.WordTrace tailWord_1241525 prefixEnd_1241525 70833229952595584603093 := by
  unfold tailWord_1241525
  simp only [CollatzResearch.WordTrace]
  refine ⟨45282136827174435434094029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30188091218116290289396019 45282136827174435434094029)
  ·
    refine ⟨16980801310190413287785261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45282136827174435434094029 16980801310190413287785261)
    ·
      refine ⟨6367800491321404982919473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16980801310190413287785261 6367800491321404982919473)
      ·
        refine ⟨4775850368491053737189605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6367800491321404982919473 4775850368491053737189605)
        ·
          refine ⟨895471944092072575723051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4775850368491053737189605 895471944092072575723051)
          ·
            refine ⟨1343207916138108863584577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895471944092072575723051 1343207916138108863584577)
            ·
              refine ⟨1007405937103581647688433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343207916138108863584577 1007405937103581647688433)
              ·
                refine ⟨755554452827686235766325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007405937103581647688433 755554452827686235766325)
                ·
                  refine ⟨70833229952595584603093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 755554452827686235766325 70833229952595584603093)
                  ·
                    rfl

theorem cell23_1241525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_1241525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241525 prefixEnd_1241525 := by exact prefixLift 1241525
  have htrace : WordTrace (prefixWord ++ tailWord_1241525) baseStart_1241525 baseEnd_1241525 := by
    simpa [prefixWord, tailWord_1241525, baseEnd_1241525] using wordTrace_append hprefix tailTrace_1241525
  have hstable : (prefixWord ++ tailWord_1241525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241525).length < 2 ^ (prefixWord ++ tailWord_1241525).sum := by decide
  have hdescent : baseEnd_1241525 < baseStart_1241525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241577 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_1241577 : Nat := 118140960795 + 1241577 * 2 ^ 59
def prefixEnd_1241577 : Nat := 4983230072969 + 3 ^ 40 * 1241577 * 2
def baseEnd_1241577 : Nat := 212508590189131352659199

theorem tailTrace_1241577 : CollatzResearch.WordTrace tailWord_1241577 prefixEnd_1241577 212508590189131352659199 := by
  unfold tailWord_1241577
  simp only [CollatzResearch.WordTrace]
  refine ⟨45284033422986048314986985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30189355615324032209991323 45284033422986048314986985)
  ·
    refine ⟨33963025067239536236240239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45284033422986048314986985 33963025067239536236240239)
    ·
      refine ⟨50944537600859304354360359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33963025067239536236240239 50944537600859304354360359)
      ·
        refine ⟨76416806401288956531540539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50944537600859304354360359 76416806401288956531540539)
        ·
          refine ⟨114625209601933434797310809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76416806401288956531540539 114625209601933434797310809)
          ·
            refine ⟨85968907201450076097983107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114625209601933434797310809 85968907201450076097983107)
            ·
              refine ⟨128953360802175114146974661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85968907201450076097983107 128953360802175114146974661)
              ·
                refine ⟨24178755150407833902557749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128953360802175114146974661 24178755150407833902557749)
                ·
                  refine ⟨2266758295350734428364789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24178755150407833902557749 2266758295350734428364789)
                  ·
                    refine ⟨212508590189131352659199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2266758295350734428364789 212508590189131352659199)
                    ·
                      rfl

theorem cell23_1241577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_1241577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241577 prefixEnd_1241577 := by exact prefixLift 1241577
  have htrace : WordTrace (prefixWord ++ tailWord_1241577) baseStart_1241577 baseEnd_1241577 := by
    simpa [prefixWord, tailWord_1241577, baseEnd_1241577] using wordTrace_append hprefix tailTrace_1241577
  have hstable : (prefixWord ++ tailWord_1241577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241577).length < 2 ^ (prefixWord ++ tailWord_1241577).sum := by decide
  have hdescent : baseEnd_1241577 < baseStart_1241577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241581 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 6]
def baseStart_1241581 : Nat := 118140960795 + 1241581 * 2 ^ 59
def prefixEnd_1241581 : Nat := 4983230072969 + 3 ^ 40 * 1241581 * 2
def baseEnd_1241581 : Nat := 70836424943334671369731

theorem tailTrace_1241581 : CollatzResearch.WordTrace tailWord_1241581 prefixEnd_1241581 70836424943334671369731 := by
  unfold tailWord_1241581
  simp only [CollatzResearch.WordTrace]
  refine ⟨45284179314971556998132597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30189452876647704665421731 45284179314971556998132597)
  ·
    refine ⟨4245391810778583468574931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45284179314971556998132597 4245391810778583468574931)
    ·
      refine ⟨6368087716167875202862397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245391810778583468574931 6368087716167875202862397)
      ·
        refine ⟨2388032893562953201073399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6368087716167875202862397 2388032893562953201073399)
        ·
          refine ⟨3582049340344429801610099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388032893562953201073399 3582049340344429801610099)
          ·
            refine ⟨5373074010516644702415149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582049340344429801610099 5373074010516644702415149)
            ·
              refine ⟨2014902753943741763405681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5373074010516644702415149 2014902753943741763405681)
              ·
                refine ⟨1511177065457806322554261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014902753943741763405681 1511177065457806322554261)
                ·
                  refine ⟨70836424943334671369731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1511177065457806322554261 70836424943334671369731)
                  ·
                    rfl

theorem cell23_1241581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_1241581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241581 prefixEnd_1241581 := by exact prefixLift 1241581
  have htrace : WordTrace (prefixWord ++ tailWord_1241581) baseStart_1241581 baseEnd_1241581 := by
    simpa [prefixWord, tailWord_1241581, baseEnd_1241581] using wordTrace_append hprefix tailTrace_1241581
  have hstable : (prefixWord ++ tailWord_1241581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241581).length < 2 ^ (prefixWord ++ tailWord_1241581).sum := by decide
  have hdescent : baseEnd_1241581 < baseStart_1241581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241601 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_1241601 : Nat := 118140960795 + 1241601 * 2 ^ 59
def prefixEnd_1241601 : Nat := 4983230072969 + 3 ^ 40 * 1241601 * 2
def baseEnd_1241601 : Nat := 637538094103101964077487

theorem tailTrace_1241601 : CollatzResearch.WordTrace tailWord_1241601 prefixEnd_1241601 637538094103101964077487 := by
  unfold tailWord_1241601
  simp only [CollatzResearch.WordTrace]
  refine ⟨45284908774899100413860657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30189939183266066942573771 45284908774899100413860657)
  ·
    refine ⟨33963681581174325310395493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45284908774899100413860657 33963681581174325310395493)
    ·
      refine ⟨6368190296470185995699155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33963681581174325310395493 6368190296470185995699155)
      ·
        refine ⟨9552285444705278993548733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368190296470185995699155 9552285444705278993548733)
        ·
          refine ⟨3582107041764479622580775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9552285444705278993548733 3582107041764479622580775)
          ·
            refine ⟨5373160562646719433871163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582107041764479622580775 5373160562646719433871163)
            ·
              refine ⟨8059740843970079150806745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373160562646719433871163 8059740843970079150806745)
              ·
                refine ⟨6044805632977559363105059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8059740843970079150806745 6044805632977559363105059)
                ·
                  refine ⟨9067208449466339044657589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6044805632977559363105059 9067208449466339044657589)
                  ·
                    refine ⟨850050792137469285436649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9067208449466339044657589 850050792137469285436649)
                    ·
                      refine ⟨637538094103101964077487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850050792137469285436649 637538094103101964077487)
                      ·
                        rfl

theorem cell23_1241601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_1241601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241601 prefixEnd_1241601 := by exact prefixLift 1241601
  have htrace : WordTrace (prefixWord ++ tailWord_1241601) baseStart_1241601 baseEnd_1241601 := by
    simpa [prefixWord, tailWord_1241601, baseEnd_1241601] using wordTrace_append hprefix tailTrace_1241601
  have hstable : (prefixWord ++ tailWord_1241601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241601).length < 2 ^ (prefixWord ++ tailWord_1241601).sum := by decide
  have hdescent : baseEnd_1241601 < baseStart_1241601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241611 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 1, 5]
def baseStart_1241611 : Nat := 118140960795 + 1241611 * 2 ^ 59
def prefixEnd_1241611 : Nat := 4983230072969 + 3 ^ 40 * 1241611 * 2
def baseEnd_1241611 : Nat := 212514409636548974984147

theorem tailTrace_1241611 : CollatzResearch.WordTrace tailWord_1241611 prefixEnd_1241611 212514409636548974984147 := by
  unfold tailWord_1241611
  simp only [CollatzResearch.WordTrace]
  refine ⟨45285273504862872121724687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30190182336575248081149791 45285273504862872121724687)
  ·
    refine ⟨67927910257294308182587031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45285273504862872121724687 67927910257294308182587031)
    ·
      refine ⟨101891865385941462273880547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67927910257294308182587031 101891865385941462273880547)
      ·
        refine ⟨152837798078912193410820821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101891865385941462273880547 152837798078912193410820821)
        ·
          refine ⟨3582135892474504533066113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 152837798078912193410820821 3582135892474504533066113)
          ·
            refine ⟨2686601919355878399799585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3582135892474504533066113 2686601919355878399799585)
            ·
              refine ⟨2014951439516908799849689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2686601919355878399799585 2014951439516908799849689)
              ·
                refine ⟨1511213579637681599887267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014951439516908799849689 1511213579637681599887267)
                ·
                  refine ⟨2266820369456522399830901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511213579637681599887267 2266820369456522399830901)
                  ·
                    refine ⟨212514409636548974984147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2266820369456522399830901 212514409636548974984147)
                    ·
                      rfl

theorem cell23_1241611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 5].length) (baseStart_1241611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241611 prefixEnd_1241611 := by exact prefixLift 1241611
  have htrace : WordTrace (prefixWord ++ tailWord_1241611) baseStart_1241611 baseEnd_1241611 := by
    simpa [prefixWord, tailWord_1241611, baseEnd_1241611] using wordTrace_append hprefix tailTrace_1241611
  have hstable : (prefixWord ++ tailWord_1241611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241611).length < 2 ^ (prefixWord ++ tailWord_1241611).sum := by decide
  have hdescent : baseEnd_1241611 < baseStart_1241611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241637 : List Nat := [1, 3, 1, 2, 2, 1, 13]
def baseStart_1241637 : Nat := 118140960795 + 1241637 * 2 ^ 59
def prefixEnd_1241637 : Nat := 4983230072969 + 3 ^ 40 * 1241637 * 2
def baseEnd_1241637 : Nat := 7871068881563750904041

theorem tailTrace_1241637 : CollatzResearch.WordTrace tailWord_1241637 prefixEnd_1241637 7871068881563750904041 := by
  unfold tailWord_1241637
  simp only [CollatzResearch.WordTrace]
  refine ⟨45286221802768678562171165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30190814535179119041447443 45286221802768678562171165)
  ·
    refine ⟨16982333176038254460814187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45286221802768678562171165 16982333176038254460814187)
    ·
      refine ⟨25473499764057381691221281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16982333176038254460814187 25473499764057381691221281)
      ·
        refine ⟨19105124823043036268415961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25473499764057381691221281 19105124823043036268415961)
        ·
          refine ⟨14328843617282277201311971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19105124823043036268415961 14328843617282277201311971)
          ·
            refine ⟨21493265425923415801967957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14328843617282277201311971 21493265425923415801967957)
            ·
              refine ⟨7871068881563750904041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 21493265425923415801967957 7871068881563750904041)
              ·
                rfl

theorem cell23_1241637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 13].length) (baseStart_1241637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241637 prefixEnd_1241637 := by exact prefixLift 1241637
  have htrace : WordTrace (prefixWord ++ tailWord_1241637) baseStart_1241637 baseEnd_1241637 := by
    simpa [prefixWord, tailWord_1241637, baseEnd_1241637] using wordTrace_append hprefix tailTrace_1241637
  have hstable : (prefixWord ++ tailWord_1241637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241637).length < 2 ^ (prefixWord ++ tailWord_1241637).sum := by decide
  have hdescent : baseEnd_1241637 < baseStart_1241637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241642 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1241642 : Nat := 118140960795 + 1241642 * 2 ^ 59
def prefixEnd_1241642 : Nat := 4983230072969 + 3 ^ 40 * 1241642 * 2
def baseEnd_1241642 : Nat := 637559146809936303664799

theorem tailTrace_1241642 : CollatzResearch.WordTrace tailWord_1241642 prefixEnd_1241642 637559146809936303664799 := by
  unfold tailWord_1241642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321601041937641104025795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30190936111833709610735453 11321601041937641104025795)
  ·
    refine ⟨16982401562906461656038693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321601041937641104025795 16982401562906461656038693)
    ·
      refine ⟨3184200293044961560507255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16982401562906461656038693 3184200293044961560507255)
      ·
        refine ⟨4776300439567442340760883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184200293044961560507255 4776300439567442340760883)
        ·
          refine ⟨7164450659351163511141325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776300439567442340760883 7164450659351163511141325)
          ·
            refine ⟨2686668997256686316677997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7164450659351163511141325 2686668997256686316677997)
            ·
              refine ⟨1007500873971257368754249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2686668997256686316677997 1007500873971257368754249)
              ·
                refine ⟨755625655478443026565687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007500873971257368754249 755625655478443026565687)
                ·
                  refine ⟨1133438483217664539848531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755625655478443026565687 1133438483217664539848531)
                  ·
                    refine ⟨1700157724826496809772797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1133438483217664539848531 1700157724826496809772797)
                    ·
                      refine ⟨637559146809936303664799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700157724826496809772797 637559146809936303664799)
                      ·
                        rfl

theorem cell23_1241642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1241642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241642 prefixEnd_1241642 := by exact prefixLift 1241642
  have htrace : WordTrace (prefixWord ++ tailWord_1241642) baseStart_1241642 baseEnd_1241642 := by
    simpa [prefixWord, tailWord_1241642, baseEnd_1241642] using wordTrace_append hprefix tailTrace_1241642
  have hstable : (prefixWord ++ tailWord_1241642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241642).length < 2 ^ (prefixWord ++ tailWord_1241642).sum := by decide
  have hdescent : baseEnd_1241642 < baseStart_1241642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241648 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 3, 2, 2]
def baseStart_1241648 : Nat := 118140960795 + 1241648 * 2 ^ 59
def prefixEnd_1241648 : Nat := 4983230072969 + 3 ^ 40 * 1241648 * 2
def baseEnd_1241648 : Nat := 637562227693863280189771

theorem tailTrace_1241648 : CollatzResearch.WordTrace tailWord_1241648 prefixEnd_1241648 637562227693863280189771 := by
  unfold tailWord_1241648
  simp only [CollatzResearch.WordTrace]
  refine ⟨22643311502864413720410799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30191082003819218293881065 22643311502864413720410799)
  ·
    refine ⟨33964967254296620580616199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22643311502864413720410799 33964967254296620580616199)
    ·
      refine ⟨50947450881444930870924299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33964967254296620580616199 50947450881444930870924299)
      ·
        refine ⟨76421176322167396306386449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50947450881444930870924299 76421176322167396306386449)
        ·
          refine ⟨57315882241625547229789837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76421176322167396306386449 57315882241625547229789837)
          ·
            refine ⟨21493455840609580211171189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57315882241625547229789837 21493455840609580211171189)
            ·
              refine ⟨2015011485057148144797299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21493455840609580211171189 2015011485057148144797299)
              ·
                refine ⟨3022517227585722217195949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015011485057148144797299 3022517227585722217195949)
                ·
                  refine ⟨1133443960344645831448481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3022517227585722217195949 1133443960344645831448481)
                  ·
                    refine ⟨850082970258484373586361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1133443960344645831448481 850082970258484373586361)
                    ·
                      refine ⟨637562227693863280189771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850082970258484373586361 637562227693863280189771)
                      ·
                        rfl

theorem cell23_1241648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 2, 2].length) (baseStart_1241648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241648 prefixEnd_1241648 := by exact prefixLift 1241648
  have htrace : WordTrace (prefixWord ++ tailWord_1241648) baseStart_1241648 baseEnd_1241648 := by
    simpa [prefixWord, tailWord_1241648, baseEnd_1241648] using wordTrace_append hprefix tailTrace_1241648
  have hstable : (prefixWord ++ tailWord_1241648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241648).length < 2 ^ (prefixWord ++ tailWord_1241648).sum := by decide
  have hdescent : baseEnd_1241648 < baseStart_1241648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241658 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_1241658 : Nat := 118140960795 + 1241658 * 2 ^ 59
def prefixEnd_1241658 : Nat := 4983230072969 + 3 ^ 40 * 1241658 * 2
def baseEnd_1241658 : Nat := 212522454166802747021575

theorem tailTrace_1241658 : CollatzResearch.WordTrace tailWord_1241658 prefixEnd_1241658 212522454166802747021575 := by
  unfold tailWord_1241658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321746933923149787171407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30191325157128399432457085 11321746933923149787171407)
  ·
    refine ⟨16982620400884724680757111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321746933923149787171407 16982620400884724680757111)
    ·
      refine ⟨25473930601327087021135667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16982620400884724680757111 25473930601327087021135667)
      ·
        refine ⟨38210895901990630531703501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25473930601327087021135667 38210895901990630531703501)
        ·
          refine ⟨14329085963246486449388813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38210895901990630531703501 14329085963246486449388813)
          ·
            refine ⟨5373407236217432418520805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14329085963246486449388813 5373407236217432418520805)
            ·
              refine ⟨1007513856790768578472651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5373407236217432418520805 1007513856790768578472651)
              ·
                refine ⟨1511270785186152867708977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007513856790768578472651 1511270785186152867708977)
                ·
                  refine ⟨1133453088889614650781733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511270785186152867708977 1133453088889614650781733)
                  ·
                    refine ⟨212522454166802747021575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1133453088889614650781733 212522454166802747021575)
                    ·
                      rfl

theorem cell23_1241658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_1241658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241658 prefixEnd_1241658 := by exact prefixLift 1241658
  have htrace : WordTrace (prefixWord ++ tailWord_1241658) baseStart_1241658 baseEnd_1241658 := by
    simpa [prefixWord, tailWord_1241658, baseEnd_1241658] using wordTrace_append hprefix tailTrace_1241658
  have hstable : (prefixWord ++ tailWord_1241658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241658).length < 2 ^ (prefixWord ++ tailWord_1241658).sum := by decide
  have hdescent : baseEnd_1241658 < baseStart_1241658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241662 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1241662 : Nat := 118140960795 + 1241662 * 2 ^ 59
def prefixEnd_1241662 : Nat := 4983230072969 + 3 ^ 40 * 1241662 * 2
def baseEnd_1241662 : Nat := 212523138807675408471569

theorem tailTrace_1241662 : CollatzResearch.WordTrace tailWord_1241662 prefixEnd_1241662 212523138807675408471569 := by
  unfold tailWord_1241662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660891703459763478978905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30191422418452071887887493 5660891703459763478978905)
  ·
    refine ⟨4245668777594822609234179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5660891703459763478978905 4245668777594822609234179)
    ·
      refine ⟨6368503166392233913851269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245668777594822609234179 6368503166392233913851269)
      ·
        refine ⟨1194094343698543858847113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6368503166392233913851269 1194094343698543858847113)
        ·
          refine ⟨895570757773907894135335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1194094343698543858847113 895570757773907894135335)
          ·
            refine ⟨1343356136660861841203003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895570757773907894135335 1343356136660861841203003)
            ·
              refine ⟨2015034204991292761804505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343356136660861841203003 2015034204991292761804505)
              ·
                refine ⟨1511275653743469571353379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015034204991292761804505 1511275653743469571353379)
                ·
                  refine ⟨2266913480615204357030069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511275653743469571353379 2266913480615204357030069)
                  ·
                    refine ⟨212523138807675408471569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2266913480615204357030069 212523138807675408471569)
                    ·
                      rfl

theorem cell23_1241662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1241662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241662 prefixEnd_1241662 := by exact prefixLift 1241662
  have htrace : WordTrace (prefixWord ++ tailWord_1241662) baseStart_1241662 baseEnd_1241662 := by
    simpa [prefixWord, tailWord_1241662, baseEnd_1241662] using wordTrace_append hprefix tailTrace_1241662
  have hstable : (prefixWord ++ tailWord_1241662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241662).length < 2 ^ (prefixWord ++ tailWord_1241662).sum := by decide
  have hdescent : baseEnd_1241662 < baseStart_1241662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241681 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_1241681 : Nat := 118140960795 + 1241681 * 2 ^ 59
def prefixEnd_1241681 : Nat := 4983230072969 + 3 ^ 40 * 1241681 * 2
def baseEnd_1241681 : Nat := 637579172555461651077119

theorem tailTrace_1241681 : CollatzResearch.WordTrace tailWord_1241681 prefixEnd_1241681 637579172555461651077119 := by
  unfold tailWord_1241681
  simp only [CollatzResearch.WordTrace]
  refine ⟨45287826614609274076772897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30191884409739516051181931 45287826614609274076772897)
  ·
    refine ⟨33965869960956955557579673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45287826614609274076772897 33965869960956955557579673)
    ·
      refine ⟨25474402470717716668184755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33965869960956955557579673 25474402470717716668184755)
      ·
        refine ⟨38211603706076575002277133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25474402470717716668184755 38211603706076575002277133)
        ·
          refine ⟨14329351389778715625853925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38211603706076575002277133 14329351389778715625853925)
          ·
            refine ⟨2686753385583509179847611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14329351389778715625853925 2686753385583509179847611)
            ·
              refine ⟨4030130078375263769771417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686753385583509179847611 4030130078375263769771417)
              ·
                refine ⟨3022597558781447827328563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4030130078375263769771417 3022597558781447827328563)
                ·
                  refine ⟨4533896338172171740992845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022597558781447827328563 4533896338172171740992845)
                  ·
                    refine ⟨1700211126814564402872317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4533896338172171740992845 1700211126814564402872317)
                    ·
                      refine ⟨637579172555461651077119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700211126814564402872317 637579172555461651077119)
                      ·
                        rfl

theorem cell23_1241681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_1241681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241681 prefixEnd_1241681 := by exact prefixLift 1241681
  have htrace : WordTrace (prefixWord ++ tailWord_1241681) baseStart_1241681 baseEnd_1241681 := by
    simpa [prefixWord, tailWord_1241681, baseEnd_1241681] using wordTrace_append hprefix tailTrace_1241681
  have hstable : (prefixWord ++ tailWord_1241681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241681).length < 2 ^ (prefixWord ++ tailWord_1241681).sum := by decide
  have hdescent : baseEnd_1241681 < baseStart_1241681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241724 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1241724 : Nat := 118140960795 + 1241724 * 2 ^ 59
def prefixEnd_1241724 : Nat := 4983230072969 + 3 ^ 40 * 1241724 * 2
def baseEnd_1241724 : Nat := 637601252223604982839421

theorem tailTrace_1241724 : CollatzResearch.WordTrace tailWord_1241724 prefixEnd_1241724 637601252223604982839421 := by
  unfold tailWord_1241724
  simp only [CollatzResearch.WordTrace]
  refine ⟨22644697476726746210294113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30192929968968994947058817 22644697476726746210294113)
  ·
    refine ⟨16983523107545059657720585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22644697476726746210294113 16983523107545059657720585)
    ·
      refine ⟨12737642330658794743290439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16983523107545059657720585 12737642330658794743290439)
      ·
        refine ⟨19106463495988192114935659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12737642330658794743290439 19106463495988192114935659)
        ·
          refine ⟨28659695243982288172403489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19106463495988192114935659 28659695243982288172403489)
          ·
            refine ⟨21494771432986716129302617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28659695243982288172403489 21494771432986716129302617)
            ·
              refine ⟨16121078574740037096976963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21494771432986716129302617 16121078574740037096976963)
              ·
                refine ⟨24181617862110055645465445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16121078574740037096976963 24181617862110055645465445)
                ·
                  refine ⟨4534053349145635433524771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24181617862110055645465445 4534053349145635433524771)
                  ·
                    refine ⟨6801080023718453150287157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4534053349145635433524771 6801080023718453150287157)
                    ·
                      refine ⟨637601252223604982839421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6801080023718453150287157 637601252223604982839421)
                      ·
                        rfl

theorem cell23_1241724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1241724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241724 prefixEnd_1241724 := by exact prefixLift 1241724
  have htrace : WordTrace (prefixWord ++ tailWord_1241724) baseStart_1241724 baseEnd_1241724 := by
    simpa [prefixWord, tailWord_1241724, baseEnd_1241724] using wordTrace_append hprefix tailTrace_1241724
  have hstable : (prefixWord ++ tailWord_1241724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241724).length < 2 ^ (prefixWord ++ tailWord_1241724).sum := by decide
  have hdescent : baseEnd_1241724 < baseStart_1241724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241784 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1241784 : Nat := 118140960795 + 1241784 * 2 ^ 59
def prefixEnd_1241784 : Nat := 4983230072969 + 3 ^ 40 * 1241784 * 2
def baseEnd_1241784 : Nat := 637632061062874748089145

theorem tailTrace_1241784 : CollatzResearch.WordTrace tailWord_1241784 prefixEnd_1241784 637632061062874748089145 := by
  unfold tailWord_1241784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22645791666618061333886203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30194388888824081778514937 22645791666618061333886203)
  ·
    refine ⟨33968687499927092000829305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22645791666618061333886203 33968687499927092000829305)
    ·
      refine ⟨25476515624945319000621979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33968687499927092000829305 25476515624945319000621979)
      ·
        refine ⟨38214773437417978500932969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25476515624945319000621979 38214773437417978500932969)
        ·
          refine ⟨28661080078063483875699727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38214773437417978500932969 28661080078063483875699727)
          ·
            refine ⟨42991620117095225813549591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28661080078063483875699727 42991620117095225813549591)
            ·
              refine ⟨64487430175642838720324387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42991620117095225813549591 64487430175642838720324387)
              ·
                refine ⟨96731145263464258080486581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64487430175642838720324387 96731145263464258080486581)
                ·
                  refine ⟨9068544868449774195045617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96731145263464258080486581 9068544868449774195045617)
                  ·
                    refine ⟨6801408651337330646284213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9068544868449774195045617 6801408651337330646284213)
                    ·
                      refine ⟨637632061062874748089145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6801408651337330646284213 637632061062874748089145)
                      ·
                        rfl

theorem cell23_1241784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1241784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241784 prefixEnd_1241784 := by exact prefixLift 1241784
  have htrace : WordTrace (prefixWord ++ tailWord_1241784) baseStart_1241784 baseEnd_1241784 := by
    simpa [prefixWord, tailWord_1241784, baseEnd_1241784] using wordTrace_append hprefix tailTrace_1241784
  have hstable : (prefixWord ++ tailWord_1241784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241784).length < 2 ^ (prefixWord ++ tailWord_1241784).sum := by decide
  have hdescent : baseEnd_1241784 < baseStart_1241784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241812 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1241812 : Nat := 118140960795 + 1241812 * 2 ^ 59
def prefixEnd_1241812 : Nat := 4983230072969 + 3 ^ 40 * 1241812 * 2
def baseEnd_1241812 : Nat := 70849604280133404282113

theorem tailTrace_1241812 : CollatzResearch.WordTrace tailWord_1241812 prefixEnd_1241812 70849604280133404282113 := by
  unfold tailWord_1241812
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646302288567341724895845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30195069718089788966527793 22646302288567341724895845)
  ·
    refine ⟨4246181679106376573417971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22646302288567341724895845 4246181679106376573417971)
    ·
      refine ⟨6369272518659564860126957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4246181679106376573417971 6369272518659564860126957)
      ·
        refine ⟨2388477194497336822547609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6369272518659564860126957 2388477194497336822547609)
        ·
          refine ⟨1791357895873002616910707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388477194497336822547609 1791357895873002616910707)
          ·
            refine ⟨2687036843809503925366061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791357895873002616910707 2687036843809503925366061)
            ·
              refine ⟨1007638816428563972012273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2687036843809503925366061 1007638816428563972012273)
              ·
                refine ⟨755729112321422979009205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007638816428563972012273 755729112321422979009205)
                ·
                  refine ⟨70849604280133404282113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 755729112321422979009205 70849604280133404282113)
                  ·
                    rfl

theorem cell23_1241812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1241812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241812 prefixEnd_1241812 := by exact prefixLift 1241812
  have htrace : WordTrace (prefixWord ++ tailWord_1241812) baseStart_1241812 baseEnd_1241812 := by
    simpa [prefixWord, tailWord_1241812, baseEnd_1241812] using wordTrace_append hprefix tailTrace_1241812
  have hstable : (prefixWord ++ tailWord_1241812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241812).length < 2 ^ (prefixWord ++ tailWord_1241812).sum := by decide
  have hdescent : baseEnd_1241812 < baseStart_1241812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241848 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_1241848 : Nat := 118140960795 + 1241848 * 2 ^ 59
def prefixEnd_1241848 : Nat := 4983230072969 + 3 ^ 40 * 1241848 * 2
def baseEnd_1241848 : Nat := 637664923824762497688851

theorem tailTrace_1241848 : CollatzResearch.WordTrace tailWord_1241848 prefixEnd_1241848 637664923824762497688851 := by
  unfold tailWord_1241848
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646958802502130799051099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30195945070002841065401465 22646958802502130799051099)
  ·
    refine ⟨33970438203753196198576649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22646958802502130799051099 33970438203753196198576649)
    ·
      refine ⟨25477828652814897148932487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33970438203753196198576649 25477828652814897148932487)
      ·
        refine ⟨38216742979222345723398731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25477828652814897148932487 38216742979222345723398731)
        ·
          refine ⟨57325114468833518585098097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38216742979222345723398731 57325114468833518585098097)
          ·
            refine ⟨42993835851625138938823573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57325114468833518585098097 42993835851625138938823573)
            ·
              refine ⟨2015336055544928387757355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42993835851625138938823573 2015336055544928387757355)
              ·
                refine ⟨3023004083317392581636033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015336055544928387757355 3023004083317392581636033)
                ·
                  refine ⟨2267253062488044436227025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3023004083317392581636033 2267253062488044436227025)
                  ·
                    refine ⟨1700439796866033327170269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267253062488044436227025 1700439796866033327170269)
                    ·
                      refine ⟨637664923824762497688851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700439796866033327170269 637664923824762497688851)
                      ·
                        rfl

theorem cell23_1241848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_1241848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241848 prefixEnd_1241848 := by exact prefixLift 1241848
  have htrace : WordTrace (prefixWord ++ tailWord_1241848) baseStart_1241848 baseEnd_1241848 := by
    simpa [prefixWord, tailWord_1241848, baseEnd_1241848] using wordTrace_append hprefix tailTrace_1241848
  have hstable : (prefixWord ++ tailWord_1241848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241848).length < 2 ^ (prefixWord ++ tailWord_1241848).sum := by decide
  have hdescent : baseEnd_1241848 < baseStart_1241848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241911 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 1, 6]
def baseStart_1241911 : Nat := 118140960795 + 1241911 * 2 ^ 59
def prefixEnd_1241911 : Nat := 4983230072969 + 3 ^ 40 * 1241911 * 2
def baseEnd_1241911 : Nat := 212565757701998583733687

theorem tailTrace_1241911 : CollatzResearch.WordTrace tailWord_1241911 prefixEnd_1241911 212565757701998583733687 := by
  unfold tailWord_1241911
  simp only [CollatzResearch.WordTrace]
  refine ⟨45296215403776023357645587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30197476935850682238430391 45296215403776023357645587)
  ·
    refine ⟨67944323105664035036468381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45296215403776023357645587 67944323105664035036468381)
    ·
      refine ⟨25479121164624013138675643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67944323105664035036468381 25479121164624013138675643)
      ·
        refine ⟨38218681746936019708013465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25479121164624013138675643 38218681746936019708013465)
        ·
          refine ⟨28664011310202014781010099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38218681746936019708013465 28664011310202014781010099)
          ·
            refine ⟨42996016965303022171515149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28664011310202014781010099 42996016965303022171515149)
            ·
              refine ⟨16123506361988633314318181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42996016965303022171515149 16123506361988633314318181)
              ·
                refine ⟨3023157442872868746434659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16123506361988633314318181 3023157442872868746434659)
                ·
                  refine ⟨4534736164309303119651989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023157442872868746434659 4534736164309303119651989)
                  ·
                    refine ⟨212565757701998583733687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4534736164309303119651989 212565757701998583733687)
                    ·
                      rfl

theorem cell23_1241911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_1241911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241911 prefixEnd_1241911 := by exact prefixLift 1241911
  have htrace : WordTrace (prefixWord ++ tailWord_1241911) baseStart_1241911 baseEnd_1241911 := by
    simpa [prefixWord, tailWord_1241911, baseEnd_1241911] using wordTrace_append hprefix tailTrace_1241911
  have hstable : (prefixWord ++ tailWord_1241911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241911).length < 2 ^ (prefixWord ++ tailWord_1241911).sum := by decide
  have hdescent : baseEnd_1241911 < baseStart_1241911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241912 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 1, 1, 3]
def baseStart_1241912 : Nat := 118140960795 + 1241912 * 2 ^ 59
def prefixEnd_1241912 : Nat := 4983230072969 + 3 ^ 40 * 1241912 * 2
def baseEnd_1241912 : Nat := 637697786586650247288557

theorem tailTrace_1241912 : CollatzResearch.WordTrace tailWord_1241912 prefixEnd_1241912 637697786586650247288557 := by
  unfold tailWord_1241912
  simp only [CollatzResearch.WordTrace]
  refine ⟨22648125938386200264215995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30197501251181600352287993 22648125938386200264215995)
  ·
    refine ⟨33972188907579300396323993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22648125938386200264215995 33972188907579300396323993)
    ·
      refine ⟨25479141680684475297242995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33972188907579300396323993 25479141680684475297242995)
      ·
        refine ⟨38218712521026712945864493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25479141680684475297242995 38218712521026712945864493)
        ·
          refine ⟨14332017195385017354699185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38218712521026712945864493 14332017195385017354699185)
          ·
            refine ⟨10749012896538763016024389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14332017195385017354699185 10749012896538763016024389)
            ·
              refine ⟨2015439918101018065504573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10749012896538763016024389 2015439918101018065504573)
              ·
                refine ⟨755789969287881774564215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2015439918101018065504573 755789969287881774564215)
                ·
                  refine ⟨1133684953931822661846323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755789969287881774564215 1133684953931822661846323)
                  ·
                    refine ⟨1700527430897733992769485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1133684953931822661846323 1700527430897733992769485)
                    ·
                      refine ⟨637697786586650247288557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700527430897733992769485 637697786586650247288557)
                      ·
                        rfl

theorem cell23_1241912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_1241912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241912 prefixEnd_1241912 := by exact prefixLift 1241912
  have htrace : WordTrace (prefixWord ++ tailWord_1241912) baseStart_1241912 baseEnd_1241912 := by
    simpa [prefixWord, tailWord_1241912, baseEnd_1241912] using wordTrace_append hprefix tailTrace_1241912
  have hstable : (prefixWord ++ tailWord_1241912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241912).length < 2 ^ (prefixWord ++ tailWord_1241912).sum := by decide
  have hdescent : baseEnd_1241912 < baseStart_1241912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241928 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1241928 : Nat := 118140960795 + 1241928 * 2 ^ 59
def prefixEnd_1241928 : Nat := 4983230072969 + 3 ^ 40 * 1241928 * 2
def baseEnd_1241928 : Nat := 212568667425707394896161

theorem tailTrace_1241928 : CollatzResearch.WordTrace tailWord_1241928 prefixEnd_1241928 212568667425707394896161 := by
  unfold tailWord_1241928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22648417722357217630507219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30197890296476290174009625 22648417722357217630507219)
  ·
    refine ⟨33972626583535826445760829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22648417722357217630507219 33972626583535826445760829)
    ·
      refine ⟨12739734968825934917160311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33972626583535826445760829 12739734968825934917160311)
      ·
        refine ⟨19109602453238902375740467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12739734968825934917160311 19109602453238902375740467)
        ·
          refine ⟨28664403679858353563610701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19109602453238902375740467 28664403679858353563610701)
          ·
            refine ⟨10749151379946882586354013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28664403679858353563610701 10749151379946882586354013)
            ·
              refine ⟨4030931767480080969882755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10749151379946882586354013 4030931767480080969882755)
              ·
                refine ⟨6046397651220121454824133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030931767480080969882755 6046397651220121454824133)
                ·
                  refine ⟨1133699559603772772779525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6046397651220121454824133 1133699559603772772779525)
                  ·
                    refine ⟨212568667425707394896161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1133699559603772772779525 212568667425707394896161)
                    ·
                      rfl

theorem cell23_1241928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1241928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241928 prefixEnd_1241928 := by exact prefixLift 1241928
  have htrace : WordTrace (prefixWord ++ tailWord_1241928) baseStart_1241928 baseEnd_1241928 := by
    simpa [prefixWord, tailWord_1241928, baseEnd_1241928] using wordTrace_append hprefix tailTrace_1241928
  have hstable : (prefixWord ++ tailWord_1241928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241928).length < 2 ^ (prefixWord ++ tailWord_1241928).sum := by decide
  have hdescent : baseEnd_1241928 < baseStart_1241928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241938 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1241938 : Nat := 118140960795 + 1241938 * 2 ^ 59
def prefixEnd_1241938 : Nat := 4983230072969 + 3 ^ 40 * 1241938 * 2
def baseEnd_1241938 : Nat := 637711137083667145563437

theorem tailTrace_1241938 : CollatzResearch.WordTrace tailWord_1241938 prefixEnd_1241938 637711137083667145563437 := by
  unfold tailWord_1241938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324300043669551742219617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30198133449785471312585645 11324300043669551742219617)
  ·
    refine ⟨8493225032752163806664713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11324300043669551742219617 8493225032752163806664713)
    ·
      refine ⟨6369918774564122854998535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8493225032752163806664713 6369918774564122854998535)
      ·
        refine ⟨9554878161846184282497803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6369918774564122854998535 9554878161846184282497803)
        ·
          refine ⟨14332317242769276423746705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9554878161846184282497803 14332317242769276423746705)
          ·
            refine ⟨10749237932076957317810029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14332317242769276423746705 10749237932076957317810029)
            ·
              refine ⟨4030964224528858994178761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10749237932076957317810029 4030964224528858994178761)
              ·
                refine ⟨3023223168396644245634071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4030964224528858994178761 3023223168396644245634071)
                ·
                  refine ⟨4534834752594966368451107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023223168396644245634071 4534834752594966368451107)
                  ·
                    refine ⟨6802252128892449552676661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4534834752594966368451107 6802252128892449552676661)
                    ·
                      refine ⟨637711137083667145563437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6802252128892449552676661 637711137083667145563437)
                      ·
                        rfl

theorem cell23_1241938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1241938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241938 prefixEnd_1241938 := by exact prefixLift 1241938
  have htrace : WordTrace (prefixWord ++ tailWord_1241938) baseStart_1241938 baseEnd_1241938 := by
    simpa [prefixWord, tailWord_1241938, baseEnd_1241938] using wordTrace_append hprefix tailTrace_1241938
  have hstable : (prefixWord ++ tailWord_1241938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241938).length < 2 ^ (prefixWord ++ tailWord_1241938).sum := by decide
  have hdescent : baseEnd_1241938 < baseStart_1241938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241941 : List Nat := [1, 3, 2, 2, 2, 1, 2, 10]
def baseStart_1241941 : Nat := 118140960795 + 1241941 * 2 ^ 59
def prefixEnd_1241941 : Nat := 4983230072969 + 3 ^ 40 * 1241941 * 2
def baseEnd_1241941 : Nat := 23618988056504838289849

theorem tailTrace_1241941 : CollatzResearch.WordTrace tailWord_1241941 prefixEnd_1241941 23618988056504838289849 := by
  unfold tailWord_1241941
  simp only [CollatzResearch.WordTrace]
  refine ⟨45297309593667338481237677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30198206395778225654158451 45297309593667338481237677)
  ·
    refine ⟨16986491097625251930464129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45297309593667338481237677 16986491097625251930464129)
    ·
      refine ⟨12739868323218938947848097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16986491097625251930464129 12739868323218938947848097)
      ·
        refine ⟨9554901242414204210886073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12739868323218938947848097 9554901242414204210886073)
        ·
          refine ⟨7166175931810653158164555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9554901242414204210886073 7166175931810653158164555)
          ·
            refine ⟨10749263897715979737246833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166175931810653158164555 10749263897715979737246833)
            ·
              refine ⟨8061947923286984802935125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749263897715979737246833 8061947923286984802935125)
              ·
                refine ⟨23618988056504838289849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8061947923286984802935125 23618988056504838289849)
                ·
                  rfl

theorem cell23_1241941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 10].length) (baseStart_1241941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241941 prefixEnd_1241941 := by exact prefixLift 1241941
  have htrace : WordTrace (prefixWord ++ tailWord_1241941) baseStart_1241941 baseEnd_1241941 := by
    simpa [prefixWord, tailWord_1241941, baseEnd_1241941] using wordTrace_append hprefix tailTrace_1241941
  have hstable : (prefixWord ++ tailWord_1241941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241941).length < 2 ^ (prefixWord ++ tailWord_1241941).sum := by decide
  have hdescent : baseEnd_1241941 < baseStart_1241941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241955 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 3]
def baseStart_1241955 : Nat := 118140960795 + 1241955 * 2 ^ 59
def prefixEnd_1241955 : Nat := 4983230072969 + 3 ^ 40 * 1241955 * 2
def baseEnd_1241955 : Nat := 637719866254793579050859

theorem tailTrace_1241955 : CollatzResearch.WordTrace tailWord_1241955 prefixEnd_1241955 637719866254793579050859 := by
  unfold tailWord_1241955
  simp only [CollatzResearch.WordTrace]
  refine ⟨45297820215616618872247319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30198546810411079248164879 45297820215616618872247319)
  ·
    refine ⟨67946730323424928308370979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45297820215616618872247319 67946730323424928308370979)
    ·
      refine ⟨101920095485137392462556469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67946730323424928308370979 101920095485137392462556469)
      ·
        refine ⟨9555008951731630543364669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101920095485137392462556469 9555008951731630543364669)
        ·
          refine ⟨3583128356899361453761751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9555008951731630543364669 3583128356899361453761751)
          ·
            refine ⟨5374692535349042180642627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583128356899361453761751 5374692535349042180642627)
            ·
              refine ⟨8062038803023563270963941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5374692535349042180642627 8062038803023563270963941)
              ·
                refine ⟨1511632275566918113305739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8062038803023563270963941 1511632275566918113305739)
                ·
                  refine ⟨2267448413350377169958609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511632275566918113305739 2267448413350377169958609)
                  ·
                    refine ⟨1700586310012782877468957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267448413350377169958609 1700586310012782877468957)
                    ·
                      refine ⟨637719866254793579050859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700586310012782877468957 637719866254793579050859)
                      ·
                        rfl

theorem cell23_1241955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_1241955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241955 prefixEnd_1241955 := by exact prefixLift 1241955
  have htrace : WordTrace (prefixWord ++ tailWord_1241955) baseStart_1241955 baseEnd_1241955 := by
    simpa [prefixWord, tailWord_1241955, baseEnd_1241955] using wordTrace_append hprefix tailTrace_1241955
  have hstable : (prefixWord ++ tailWord_1241955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241955).length < 2 ^ (prefixWord ++ tailWord_1241955).sum := by decide
  have hdescent : baseEnd_1241955 < baseStart_1241955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241968 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_1241968 : Nat := 118140960795 + 1241968 * 2 ^ 59
def prefixEnd_1241968 : Nat := 4983230072969 + 3 ^ 40 * 1241968 * 2
def baseEnd_1241968 : Nat := 637726541503302028188299

theorem tailTrace_1241968 : CollatzResearch.WordTrace tailWord_1241968 prefixEnd_1241968 637726541503302028188299 := by
  unfold tailWord_1241968
  simp only [CollatzResearch.WordTrace]
  refine ⟨22649147182284761046235279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30198862909713014728313705 22649147182284761046235279)
  ·
    refine ⟨33973720773427141569352919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22649147182284761046235279 33973720773427141569352919)
    ·
      refine ⟨50960581160140712354029379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33973720773427141569352919 50960581160140712354029379)
      ·
        refine ⟨76440871740211068531044069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50960581160140712354029379 76440871740211068531044069)
        ·
          refine ⟨14332663451289575349570763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76440871740211068531044069 14332663451289575349570763)
          ·
            refine ⟨21498995176934363024356145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14332663451289575349570763 21498995176934363024356145)
            ·
              refine ⟨16124246382700772268267109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21498995176934363024356145 16124246382700772268267109)
              ·
                refine ⟨3023296196756394800300083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16124246382700772268267109 3023296196756394800300083)
                ·
                  refine ⟨4534944295134592200450125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023296196756394800300083 4534944295134592200450125)
                  ·
                    refine ⟨1700604110675472075168797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4534944295134592200450125 1700604110675472075168797)
                    ·
                      refine ⟨637726541503302028188299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700604110675472075168797 637726541503302028188299)
                      ·
                        rfl

theorem cell23_1241968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_1241968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241968 prefixEnd_1241968 := by exact prefixLift 1241968
  have htrace : WordTrace (prefixWord ++ tailWord_1241968) baseStart_1241968 baseEnd_1241968 := by
    simpa [prefixWord, tailWord_1241968, baseEnd_1241968] using wordTrace_append hprefix tailTrace_1241968
  have hstable : (prefixWord ++ tailWord_1241968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241968).length < 2 ^ (prefixWord ++ tailWord_1241968).sum := by decide
  have hdescent : baseEnd_1241968 < baseStart_1241968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241969 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 1, 2, 2]
def baseStart_1241969 : Nat := 118140960795 + 1241969 * 2 ^ 59
def prefixEnd_1241969 : Nat := 4983230072969 + 3 ^ 40 * 1241969 * 2
def baseEnd_1241969 : Nat := 637727054983956524275795

theorem tailTrace_1241969 : CollatzResearch.WordTrace tailWord_1241969 prefixEnd_1241969 637727054983956524275795 := by
  unfold tailWord_1241969
  simp only [CollatzResearch.WordTrace]
  refine ⟨45298330837565899263256961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30198887225043932842171307 45298330837565899263256961)
  ·
    refine ⟨33973748128174424447442721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45298330837565899263256961 33973748128174424447442721)
    ·
      refine ⟨25480311096130818335582041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33973748128174424447442721 25480311096130818335582041)
      ·
        refine ⟨19110233322098113751686531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25480311096130818335582041 19110233322098113751686531)
        ·
          refine ⟨28665349983147170627529797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19110233322098113751686531 28665349983147170627529797)
          ·
            refine ⟨5374753121840094492661837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28665349983147170627529797 5374753121840094492661837)
            ·
              refine ⟨2015532420690035434748189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5374753121840094492661837 2015532420690035434748189)
              ·
                refine ⟨755824657758763288030571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2015532420690035434748189 755824657758763288030571)
                ·
                  refine ⟨1133736986638144932045857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755824657758763288030571 1133736986638144932045857)
                  ·
                    refine ⟨850302739978608699034393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1133736986638144932045857 850302739978608699034393)
                    ·
                      refine ⟨637727054983956524275795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850302739978608699034393 637727054983956524275795)
                      ·
                        rfl

theorem cell23_1241969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_1241969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241969 prefixEnd_1241969 := by exact prefixLift 1241969
  have htrace : WordTrace (prefixWord ++ tailWord_1241969) baseStart_1241969 baseEnd_1241969 := by
    simpa [prefixWord, tailWord_1241969, baseEnd_1241969] using wordTrace_append hprefix tailTrace_1241969
  have hstable : (prefixWord ++ tailWord_1241969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241969).length < 2 ^ (prefixWord ++ tailWord_1241969).sum := by decide
  have hdescent : baseEnd_1241969 < baseStart_1241969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242001 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_1242001 : Nat := 118140960795 + 1242001 * 2 ^ 59
def prefixEnd_1242001 : Nat := 4983230072969 + 3 ^ 40 * 1242001 * 2
def baseEnd_1242001 : Nat := 212581162121633466358549

theorem tailTrace_1242001 : CollatzResearch.WordTrace tailWord_1242001 prefixEnd_1242001 212581162121633466358549 := by
  unfold tailWord_1242001
  simp only [CollatzResearch.WordTrace]
  refine ⟨45299497973449968728421857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30199665315633312485614571 45299497973449968728421857)
  ·
    refine ⟨33974623480087476546316393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45299497973449968728421857 33974623480087476546316393)
    ·
      refine ⟨25480967610065607409737295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33974623480087476546316393 25480967610065607409737295)
      ·
        refine ⟨38221451415098411114605943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25480967610065607409737295 38221451415098411114605943)
        ·
          refine ⟨57332177122647616671908915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38221451415098411114605943 57332177122647616671908915)
          ·
            refine ⟨85998265683971425007863373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57332177122647616671908915 85998265683971425007863373)
            ·
              refine ⟨32249349631489284377948765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85998265683971425007863373 32249349631489284377948765)
              ·
                refine ⟨12093506111808481641730787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32249349631489284377948765 12093506111808481641730787)
                ·
                  refine ⟨18140259167712722462596181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12093506111808481641730787 18140259167712722462596181)
                  ·
                    refine ⟨212581162121633466358549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18140259167712722462596181 212581162121633466358549)
                    ·
                      rfl

theorem cell23_1242001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_1242001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242001 prefixEnd_1242001 := by exact prefixLift 1242001
  have htrace : WordTrace (prefixWord ++ tailWord_1242001) baseStart_1242001 baseEnd_1242001 := by
    simpa [prefixWord, tailWord_1242001, baseEnd_1242001] using wordTrace_append hprefix tailTrace_1242001
  have hstable : (prefixWord ++ tailWord_1242001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242001).length < 2 ^ (prefixWord ++ tailWord_1242001).sum := by decide
  have hdescent : baseEnd_1242001 < baseStart_1242001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242006 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1242006 : Nat := 118140960795 + 1242006 * 2 ^ 59
def prefixEnd_1242006 : Nat := 4983230072969 + 3 ^ 40 * 1242006 * 2
def baseEnd_1242006 : Nat := 637746053768172879513125

theorem tailTrace_1242006 : CollatzResearch.WordTrace tailWord_1242006 prefixEnd_1242006 637746053768172879513125 := by
  unfold tailWord_1242006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831230021151990911397117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30199786892287903054902581 2831230021151990911397117)
  ·
    refine ⟨1061711257931996591773919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2831230021151990911397117 1061711257931996591773919)
    ·
      refine ⟨1592566886897994887660879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061711257931996591773919 1592566886897994887660879)
      ·
        refine ⟨2388850330346992331491319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592566886897994887660879 2388850330346992331491319)
        ·
          refine ⟨3583275495520488497236979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388850330346992331491319 3583275495520488497236979)
          ·
            refine ⟨5374913243280732745855469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583275495520488497236979 5374913243280732745855469)
            ·
              refine ⟨2015592466230274779695801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5374913243280732745855469 2015592466230274779695801)
              ·
                refine ⟨1511694349672706084771851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015592466230274779695801 1511694349672706084771851)
                ·
                  refine ⟨2267541524509059127157777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511694349672706084771851 2267541524509059127157777)
                  ·
                    refine ⟨1700656143381794345368333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267541524509059127157777 1700656143381794345368333)
                    ·
                      refine ⟨637746053768172879513125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700656143381794345368333 637746053768172879513125)
                      ·
                        rfl

theorem cell23_1242006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1242006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242006 prefixEnd_1242006 := by exact prefixLift 1242006
  have htrace : WordTrace (prefixWord ++ tailWord_1242006) baseStart_1242006 baseEnd_1242006 := by
    simpa [prefixWord, tailWord_1242006, baseEnd_1242006] using wordTrace_append hprefix tailTrace_1242006
  have hstable : (prefixWord ++ tailWord_1242006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242006).length < 2 ^ (prefixWord ++ tailWord_1242006).sum := by decide
  have hdescent : baseEnd_1242006 < baseStart_1242006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242025 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 1, 4, 2]
def baseStart_1242025 : Nat := 118140960795 + 1242025 * 2 ^ 59
def prefixEnd_1242025 : Nat := 4983230072969 + 3 ^ 40 * 1242025 * 2
def baseEnd_1242025 : Nat := 637755809900608305175537

theorem tailTrace_1242025 : CollatzResearch.WordTrace tailWord_1242025 prefixEnd_1242025 637755809900608305175537 := by
  unfold tailWord_1242025
  simp only [CollatzResearch.WordTrace]
  refine ⟨45300373325363020827295529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30200248883575347218197019 45300373325363020827295529)
  ·
    refine ⟨33975279994022265620471647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45300373325363020827295529 33975279994022265620471647)
    ·
      refine ⟨50962919991033398430707471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33975279994022265620471647 50962919991033398430707471)
      ·
        refine ⟨76444379986550097646061207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50962919991033398430707471 76444379986550097646061207)
        ·
          refine ⟨114666569979825146469091811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76444379986550097646061207 114666569979825146469091811)
          ·
            refine ⟨171999854969737719703637717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114666569979825146469091811 171999854969737719703637717)
            ·
              refine ⟨4031246600853227805554009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 171999854969737719703637717 4031246600853227805554009)
              ·
                refine ⟨3023434950639920854165507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4031246600853227805554009 3023434950639920854165507)
                ·
                  refine ⟨4535152425959881281248261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023434950639920854165507 4535152425959881281248261)
                  ·
                    refine ⟨850341079867477740234049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4535152425959881281248261 850341079867477740234049)
                    ·
                      refine ⟨637755809900608305175537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850341079867477740234049 637755809900608305175537)
                      ·
                        rfl

theorem cell23_1242025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 4, 2].length) (baseStart_1242025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242025 prefixEnd_1242025 := by exact prefixLift 1242025
  have htrace : WordTrace (prefixWord ++ tailWord_1242025) baseStart_1242025 baseEnd_1242025 := by
    simpa [prefixWord, tailWord_1242025, baseEnd_1242025] using wordTrace_append hprefix tailTrace_1242025
  have hstable : (prefixWord ++ tailWord_1242025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242025).length < 2 ^ (prefixWord ++ tailWord_1242025).sum := by decide
  have hdescent : baseEnd_1242025 < baseStart_1242025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242031 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 11]
def baseStart_1242031 : Nat := 118140960795 + 1242031 * 2 ^ 59
def prefixEnd_1242031 : Nat := 4983230072969 + 3 ^ 40 * 1242031 * 2
def baseEnd_1242031 : Nat := 70862098976059475744501

theorem tailTrace_1242031 : CollatzResearch.WordTrace tailWord_1242031 prefixEnd_1242031 70862098976059475744501 := by
  unfold tailWord_1242031
  simp only [CollatzResearch.WordTrace]
  refine ⟨45300592163341283852013947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30200394775560855901342631 45300592163341283852013947)
  ·
    refine ⟨67950888245011925778020921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45300592163341283852013947 67950888245011925778020921)
    ·
      refine ⟨50963166183758944333515691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67950888245011925778020921 50963166183758944333515691)
      ·
        refine ⟨76444749275638416500273537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50963166183758944333515691 76444749275638416500273537)
        ·
          refine ⟨57333561956728812375205153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76444749275638416500273537 57333561956728812375205153)
          ·
            refine ⟨43000171467546609281403865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57333561956728812375205153 43000171467546609281403865)
            ·
              refine ⟨32250128600659956961052899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43000171467546609281403865 32250128600659956961052899)
              ·
                refine ⟨48375192900989935441579349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32250128600659956961052899 48375192900989935441579349)
                ·
                  refine ⟨70862098976059475744501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 48375192900989935441579349 70862098976059475744501)
                  ·
                    rfl

theorem cell23_1242031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 11].length) (baseStart_1242031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242031 prefixEnd_1242031 := by exact prefixLift 1242031
  have htrace : WordTrace (prefixWord ++ tailWord_1242031) baseStart_1242031 baseEnd_1242031 := by
    simpa [prefixWord, tailWord_1242031, baseEnd_1242031] using wordTrace_append hprefix tailTrace_1242031
  have hstable : (prefixWord ++ tailWord_1242031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242031).length < 2 ^ (prefixWord ++ tailWord_1242031).sum := by decide
  have hdescent : baseEnd_1242031 < baseStart_1242031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242036 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1242036 : Nat := 118140960795 + 1242036 * 2 ^ 59
def prefixEnd_1242036 : Nat := 4983230072969 + 3 ^ 40 * 1242036 * 2
def baseEnd_1242036 : Nat := 637761458187807762137987

theorem tailTrace_1242036 : CollatzResearch.WordTrace tailWord_1242036 prefixEnd_1242036 637761458187807762137987 := by
  unfold tailWord_1242036
  simp only [CollatzResearch.WordTrace]
  refine ⟨22650387264161584852972981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30200516352215446470630641 22650387264161584852972981)
  ·
    refine ⟨2123473806015148579966217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22650387264161584852972981 2123473806015148579966217)
    ·
      refine ⟨1592605354511361434974663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2123473806015148579966217 1592605354511361434974663)
      ·
        refine ⟨2388908031767042152461995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592605354511361434974663 2388908031767042152461995)
        ·
          refine ⟨3583362047650563228692993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388908031767042152461995 3583362047650563228692993)
          ·
            refine ⟨2687521535737922421519745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583362047650563228692993 2687521535737922421519745)
            ·
              refine ⟨2015641151803441816139809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687521535737922421519745 2015641151803441816139809)
              ·
                refine ⟨1511730863852581362104857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015641151803441816139809 1511730863852581362104857)
                ·
                  refine ⟨1133798147889436021578643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511730863852581362104857 1133798147889436021578643)
                  ·
                    refine ⟨1700697221834154032367965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1133798147889436021578643 1700697221834154032367965)
                    ·
                      refine ⟨637761458187807762137987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700697221834154032367965 637761458187807762137987)
                      ·
                        rfl

theorem cell23_1242036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1242036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242036 prefixEnd_1242036 := by exact prefixLift 1242036
  have htrace : WordTrace (prefixWord ++ tailWord_1242036) baseStart_1242036 baseEnd_1242036 := by
    simpa [prefixWord, tailWord_1242036, baseEnd_1242036] using wordTrace_append hprefix tailTrace_1242036
  have hstable : (prefixWord ++ tailWord_1242036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242036).length < 2 ^ (prefixWord ++ tailWord_1242036).sum := by decide
  have hdescent : baseEnd_1242036 < baseStart_1242036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242052 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1242052 : Nat := 118140960795 + 1242052 * 2 ^ 59
def prefixEnd_1242052 : Nat := 4983230072969 + 3 ^ 40 * 1242052 * 2
def baseEnd_1242052 : Nat := 212589891292759899845971

theorem tailTrace_1242052 : CollatzResearch.WordTrace tailWord_1242052 prefixEnd_1242052 212589891292759899845971 := by
  unfold tailWord_1242052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22650679048132602219264205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30200905397510136292352273 22650679048132602219264205)
  ·
    refine ⟨8494004643049725832224077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22650679048132602219264205 8494004643049725832224077)
    ·
      refine ⟨3185251741143647187084029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8494004643049725832224077 3185251741143647187084029)
      ·
        refine ⟨1194469402928867695156511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3185251741143647187084029 1194469402928867695156511)
        ·
          refine ⟨1791704104393301542734767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194469402928867695156511 1791704104393301542734767)
          ·
            refine ⟨2687556156589952314102151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791704104393301542734767 2687556156589952314102151)
            ·
              refine ⟨4031334234884928471153227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687556156589952314102151 4031334234884928471153227)
              ·
                refine ⟨6047001352327392706729841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031334234884928471153227 6047001352327392706729841)
                ·
                  refine ⟨4535251014245544530047381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047001352327392706729841 4535251014245544530047381)
                  ·
                    refine ⟨212589891292759899845971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4535251014245544530047381 212589891292759899845971)
                    ·
                      rfl

theorem cell23_1242052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1242052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242052 prefixEnd_1242052 := by exact prefixLift 1242052
  have htrace : WordTrace (prefixWord ++ tailWord_1242052) baseStart_1242052 baseEnd_1242052 := by
    simpa [prefixWord, tailWord_1242052, baseEnd_1242052] using wordTrace_append hprefix tailTrace_1242052
  have hstable : (prefixWord ++ tailWord_1242052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242052).length < 2 ^ (prefixWord ++ tailWord_1242052).sum := by decide
  have hdescent : baseEnd_1242052 < baseStart_1242052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242088 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1242088 : Nat := 118140960795 + 1242088 * 2 ^ 59
def prefixEnd_1242088 : Nat := 4983230072969 + 3 ^ 40 * 1242088 * 2
def baseEnd_1242088 : Nat := 637788159181841558687747

theorem tailTrace_1242088 : CollatzResearch.WordTrace tailWord_1242088 prefixEnd_1242088 637788159181841558687747 := by
  unfold tailWord_1242088
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651335562067391293419459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30201780749423188391225945 22651335562067391293419459)
  ·
    refine ⟨33977003343101086940129189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22651335562067391293419459 33977003343101086940129189)
    ·
      refine ⟨6370688126831453801274223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33977003343101086940129189 6370688126831453801274223)
      ·
        refine ⟨9556032190247180701911335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6370688126831453801274223 9556032190247180701911335)
        ·
          refine ⟨14334048285370771052867003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9556032190247180701911335 14334048285370771052867003)
          ·
            refine ⟨21501072428056156579300505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14334048285370771052867003 21501072428056156579300505)
            ·
              refine ⟨16125804321042117434475379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21501072428056156579300505 16125804321042117434475379)
              ·
                refine ⟨24188706481563176151713069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16125804321042117434475379 24188706481563176151713069)
                ·
                  refine ⟨9070764930586191056892401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24188706481563176151713069 9070764930586191056892401)
                  ·
                    refine ⟨6803073697939643292669301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9070764930586191056892401 6803073697939643292669301)
                    ·
                      refine ⟨637788159181841558687747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6803073697939643292669301 637788159181841558687747)
                      ·
                        rfl

theorem cell23_1242088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1242088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242088 prefixEnd_1242088 := by exact prefixLift 1242088
  have htrace : WordTrace (prefixWord ++ tailWord_1242088) baseStart_1242088 baseEnd_1242088 := by
    simpa [prefixWord, tailWord_1242088, baseEnd_1242088] using wordTrace_append hprefix tailTrace_1242088
  have hstable : (prefixWord ++ tailWord_1242088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242088).length < 2 ^ (prefixWord ++ tailWord_1242088).sum := by decide
  have hdescent : baseEnd_1242088 < baseStart_1242088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242138 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_1242138 : Nat := 118140960795 + 1242138 * 2 ^ 59
def prefixEnd_1242138 : Nat := 4983230072969 + 3 ^ 40 * 1242138 * 2
def baseEnd_1242138 : Nat := 70868203690507373673613

theorem tailTrace_1242138 : CollatzResearch.WordTrace tailWord_1242138 prefixEnd_1242138 70868203690507373673613 := by
  unfold tailWord_1242138
  simp only [CollatzResearch.WordTrace]
  refine ⟨11326123693488410281539767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30202996515969094084106045 11326123693488410281539767)
  ·
    refine ⟨16989185540232615422309651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11326123693488410281539767 16989185540232615422309651)
    ·
      refine ⟨25483778310348923133464477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16989185540232615422309651 25483778310348923133464477)
      ·
        refine ⟨9556416866380846175049179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25483778310348923133464477 9556416866380846175049179)
        ·
          refine ⟨14334625299571269262573769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9556416866380846175049179 14334625299571269262573769)
          ·
            refine ⟨10750968974678451946930327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14334625299571269262573769 10750968974678451946930327)
            ·
              refine ⟨16126453462017677920395491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10750968974678451946930327 16126453462017677920395491)
              ·
                refine ⟨24189680193026516880593237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16126453462017677920395491 24189680193026516880593237)
                ·
                  refine ⟨70868203690507373673613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24189680193026516880593237 70868203690507373673613)
                  ·
                    rfl

theorem cell23_1242138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_1242138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242138 prefixEnd_1242138 := by exact prefixLift 1242138
  have htrace : WordTrace (prefixWord ++ tailWord_1242138) baseStart_1242138 baseEnd_1242138 := by
    simpa [prefixWord, tailWord_1242138, baseEnd_1242138] using wordTrace_append hprefix tailTrace_1242138
  have hstable : (prefixWord ++ tailWord_1242138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242138).length < 2 ^ (prefixWord ++ tailWord_1242138).sum := by decide
  have hdescent : baseEnd_1242138 < baseStart_1242138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242172 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 6]
def baseStart_1242172 : Nat := 118140960795 + 1242172 * 2 ^ 59
def prefixEnd_1242172 : Nat := 4983230072969 + 3 ^ 40 * 1242172 * 2
def baseEnd_1242172 : Nat := 70870143506313247781929

theorem tailTrace_1242172 : CollatzResearch.WordTrace tailWord_1242172 prefixEnd_1242172 70870143506313247781929 := by
  unfold tailWord_1242172
  simp only [CollatzResearch.WordTrace]
  refine ⟨22652867427915232466448385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30203823237220309955264513 22652867427915232466448385)
  ·
    refine ⟨16989650570936424349836289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22652867427915232466448385 16989650570936424349836289)
    ·
      refine ⟨12742237928202318262377217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16989650570936424349836289 12742237928202318262377217)
      ·
        refine ⟨9556678446151738696782913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12742237928202318262377217 9556678446151738696782913)
        ·
          refine ⟨7167508834613804022587185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9556678446151738696782913 7167508834613804022587185)
          ·
            refine ⟨5375631625960353016940389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167508834613804022587185 5375631625960353016940389)
            ·
              refine ⟨1007930929867566190676323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5375631625960353016940389 1007930929867566190676323)
              ·
                refine ⟨1511896394801349286014485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007930929867566190676323 1511896394801349286014485)
                ·
                  refine ⟨70870143506313247781929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1511896394801349286014485 70870143506313247781929)
                  ·
                    rfl

theorem cell23_1242172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_1242172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242172 prefixEnd_1242172 := by exact prefixLift 1242172
  have htrace : WordTrace (prefixWord ++ tailWord_1242172) baseStart_1242172 baseEnd_1242172 := by
    simpa [prefixWord, tailWord_1242172, baseEnd_1242172] using wordTrace_append hprefix tailTrace_1242172
  have hstable : (prefixWord ++ tailWord_1242172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242172).length < 2 ^ (prefixWord ++ tailWord_1242172).sum := by decide
  have hdescent : baseEnd_1242172 < baseStart_1242172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242185 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 1, 5]
def baseStart_1242185 : Nat := 118140960795 + 1242185 * 2 ^ 59
def prefixEnd_1242185 : Nat := 4983230072969 + 3 ^ 40 * 1242185 * 2
def baseEnd_1242185 : Nat := 212612655601775893058267

theorem tailTrace_1242185 : CollatzResearch.WordTrace tailWord_1242185 prefixEnd_1242185 212612655601775893058267 := by
  unfold tailWord_1242185
  simp only [CollatzResearch.WordTrace]
  refine ⟨45306209004783368153120009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30204139336522245435413339 45306209004783368153120009)
  ·
    refine ⟨33979656753587526114840007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45306209004783368153120009 33979656753587526114840007)
    ·
      refine ⟨50969485130381289172260011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33979656753587526114840007 50969485130381289172260011)
      ·
        refine ⟨76454227695571933758390017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50969485130381289172260011 76454227695571933758390017)
        ·
          refine ⟨57340670771678950318792513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76454227695571933758390017 57340670771678950318792513)
          ·
            refine ⟨43005503078759212739094385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57340670771678950318792513 43005503078759212739094385)
            ·
              refine ⟨32254127309069409554320789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43005503078759212739094385 32254127309069409554320789)
              ·
                refine ⟨1511912217612628572858787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32254127309069409554320789 1511912217612628572858787)
                ·
                  refine ⟨2267868326418942859288181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511912217612628572858787 2267868326418942859288181)
                  ·
                    refine ⟨212612655601775893058267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2267868326418942859288181 212612655601775893058267)
                    ·
                      rfl

theorem cell23_1242185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_1242185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242185 prefixEnd_1242185 := by exact prefixLift 1242185
  have htrace : WordTrace (prefixWord ++ tailWord_1242185) baseStart_1242185 baseEnd_1242185 := by
    simpa [prefixWord, tailWord_1242185, baseEnd_1242185] using wordTrace_append hprefix tailTrace_1242185
  have hstable : (prefixWord ++ tailWord_1242185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242185).length < 2 ^ (prefixWord ++ tailWord_1242185).sum := by decide
  have hdescent : baseEnd_1242185 < baseStart_1242185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242199 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 1, 1, 3]
def baseStart_1242199 : Nat := 118140960795 + 1242199 * 2 ^ 59
def prefixEnd_1242199 : Nat := 4983230072969 + 3 ^ 40 * 1242199 * 2
def baseEnd_1242199 : Nat := 637845155534490624399737

theorem tailTrace_1242199 : CollatzResearch.WordTrace tailWord_1242199 prefixEnd_1242199 637845155534490624399737 := by
  unfold tailWord_1242199
  simp only [CollatzResearch.WordTrace]
  refine ⟨45306719626732648544129651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30204479751155099029419767 45306719626732648544129651)
  ·
    refine ⟨67960079440098972816194477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45306719626732648544129651 67960079440098972816194477)
    ·
      refine ⟨25485029790037114806072929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67960079440098972816194477 25485029790037114806072929)
      ·
        refine ⟨19113772342527836104554697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25485029790037114806072929 19113772342527836104554697)
        ·
          refine ⟨14335329256895877078416023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19113772342527836104554697 14335329256895877078416023)
          ·
            refine ⟨21502993885343815617624035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14335329256895877078416023 21502993885343815617624035)
            ·
              refine ⟨32254490828015723426436053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21502993885343815617624035 32254490828015723426436053)
              ·
                refine ⟨755964628781618517807095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32254490828015723426436053 755964628781618517807095)
                ·
                  refine ⟨1133946943172427776710643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755964628781618517807095 1133946943172427776710643)
                  ·
                    refine ⟨1700920414758641665065965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1133946943172427776710643 1700920414758641665065965)
                    ·
                      refine ⟨637845155534490624399737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700920414758641665065965 637845155534490624399737)
                      ·
                        rfl

theorem cell23_1242199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_1242199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242199 prefixEnd_1242199 := by exact prefixLift 1242199
  have htrace : WordTrace (prefixWord ++ tailWord_1242199) baseStart_1242199 baseEnd_1242199 := by
    simpa [prefixWord, tailWord_1242199, baseEnd_1242199] using wordTrace_append hprefix tailTrace_1242199
  have hstable : (prefixWord ++ tailWord_1242199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242199).length < 2 ^ (prefixWord ++ tailWord_1242199).sum := by decide
  have hdescent : baseEnd_1242199 < baseStart_1242199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242206 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1242206 : Nat := 118140960795 + 1242206 * 2 ^ 59
def prefixEnd_1242206 : Nat := 4983230072969 + 3 ^ 40 * 1242206 * 2
def baseEnd_1242206 : Nat := 70872083322119121890245

theorem tailTrace_1242206 : CollatzResearch.WordTrace tailWord_1242206 prefixEnd_1242206 70872083322119121890245 := by
  unfold tailWord_1242206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663371867213411092454309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30204649958471525826422981 5663371867213411092454309)
  ·
    refine ⟨1061882225102514579835183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5663371867213411092454309 1061882225102514579835183)
    ·
      refine ⟨1592823337653771869752775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061882225102514579835183 1592823337653771869752775)
      ·
        refine ⟨2389235006480657804629163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592823337653771869752775 2389235006480657804629163)
        ·
          refine ⟨3583852509720986706943745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389235006480657804629163 3583852509720986706943745)
          ·
            refine ⟨2687889382290740030207809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583852509720986706943745 2687889382290740030207809)
            ·
              refine ⟨2015917036718055022655857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687889382290740030207809 2015917036718055022655857)
              ·
                refine ⟨1511937777538541266991893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015917036718055022655857 1511937777538541266991893)
                ·
                  refine ⟨70872083322119121890245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1511937777538541266991893 70872083322119121890245)
                  ·
                    rfl

theorem cell23_1242206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1242206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242206 prefixEnd_1242206 := by exact prefixLift 1242206
  have htrace : WordTrace (prefixWord ++ tailWord_1242206) baseStart_1242206 baseEnd_1242206 := by
    simpa [prefixWord, tailWord_1242206, baseEnd_1242206] using wordTrace_append hprefix tailTrace_1242206
  have hstable : (prefixWord ++ tailWord_1242206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242206).length < 2 ^ (prefixWord ++ tailWord_1242206).sum := by decide
  have hdescent : baseEnd_1242206 < baseStart_1242206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242222 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1242222 : Nat := 118140960795 + 1242222 * 2 ^ 59
def prefixEnd_1242222 : Nat := 4983230072969 + 3 ^ 40 * 1242222 * 2
def baseEnd_1242222 : Nat := 637856965589544034412131

theorem tailTrace_1242222 : CollatzResearch.WordTrace tailWord_1242222 prefixEnd_1242222 637856965589544034412131 := by
  unfold tailWord_1242222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663444813206165434027115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30205039003766215648144613 5663444813206165434027115)
  ·
    refine ⟨8495167219809248151040673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663444813206165434027115 8495167219809248151040673)
    ·
      refine ⟨6371375414856936113280505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8495167219809248151040673 6371375414856936113280505)
      ·
        refine ⟨4778531561142702084960379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6371375414856936113280505 4778531561142702084960379)
        ·
          refine ⟨7167797341714053127440569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778531561142702084960379 7167797341714053127440569)
          ·
            refine ⟨5375848006285539845580427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167797341714053127440569 5375848006285539845580427)
            ·
              refine ⟨8063772009428309768370641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375848006285539845580427 8063772009428309768370641)
              ·
                refine ⟨6047829007071232326277981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8063772009428309768370641 6047829007071232326277981)
                ·
                  refine ⟨2267935877651712122354243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6047829007071232326277981 2267935877651712122354243)
                  ·
                    refine ⟨3401903816477568183531365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2267935877651712122354243 3401903816477568183531365)
                    ·
                      refine ⟨637856965589544034412131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3401903816477568183531365 637856965589544034412131)
                      ·
                        rfl

theorem cell23_1242222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1242222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242222 prefixEnd_1242222 := by exact prefixLift 1242222
  have htrace : WordTrace (prefixWord ++ tailWord_1242222) baseStart_1242222 baseEnd_1242222 := by
    simpa [prefixWord, tailWord_1242222, baseEnd_1242222] using wordTrace_append hprefix tailTrace_1242222
  have hstable : (prefixWord ++ tailWord_1242222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242222).length < 2 ^ (prefixWord ++ tailWord_1242222).sum := by decide
  have hdescent : baseEnd_1242222 < baseStart_1242222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242232 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 2, 4]
def baseStart_1242232 : Nat := 118140960795 + 1242232 * 2 ^ 59
def prefixEnd_1242232 : Nat := 4983230072969 + 3 ^ 40 * 1242232 * 2
def baseEnd_1242232 : Nat := 212620700132029665095695

theorem tailTrace_1242232 : CollatzResearch.WordTrace tailWord_1242232 prefixEnd_1242232 212620700132029665095695 := by
  unfold tailWord_1242232
  simp only [CollatzResearch.WordTrace]
  refine ⟨22653961617806547590040475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30205282157075396786720633 22653961617806547590040475)
  ·
    refine ⟨33980942426709821385060713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22653961617806547590040475 33980942426709821385060713)
    ·
      refine ⟨25485706820032366038795535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33980942426709821385060713 25485706820032366038795535)
      ·
        refine ⟨38228560230048549058193303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25485706820032366038795535 38228560230048549058193303)
        ·
          refine ⟨57342840345072823587289955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38228560230048549058193303 57342840345072823587289955)
          ·
            refine ⟨86014260517609235380934933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57342840345072823587289955 86014260517609235380934933)
            ·
              refine ⟨4031918461762932908481325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86014260517609235380934933 4031918461762932908481325)
              ·
                refine ⟨1511969423161099840680497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4031918461762932908481325 1511969423161099840680497)
                ·
                  refine ⟨1133977067370824880510373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511969423161099840680497 1133977067370824880510373)
                  ·
                    refine ⟨212620700132029665095695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1133977067370824880510373 212620700132029665095695)
                    ·
                      rfl

theorem cell23_1242232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_1242232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242232 prefixEnd_1242232 := by exact prefixLift 1242232
  have htrace : WordTrace (prefixWord ++ tailWord_1242232) baseStart_1242232 baseEnd_1242232 := by
    simpa [prefixWord, tailWord_1242232, baseEnd_1242232] using wordTrace_append hprefix tailTrace_1242232
  have hstable : (prefixWord ++ tailWord_1242232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242232).length < 2 ^ (prefixWord ++ tailWord_1242232).sum := by decide
  have hdescent : baseEnd_1242232 < baseStart_1242232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242255 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_1242255 : Nat := 118140960795 + 1242255 * 2 ^ 59
def prefixEnd_1242255 : Nat := 4983230072969 + 3 ^ 40 * 1242255 * 2
def baseEnd_1242255 : Nat := 637873910451142405299479

theorem tailTrace_1242255 : CollatzResearch.WordTrace tailWord_1242255 prefixEnd_1242255 637873910451142405299479 := by
  unfold tailWord_1242255
  simp only [CollatzResearch.WordTrace]
  refine ⟨45308762114529770108168219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30205841409686513405445479 45308762114529770108168219)
  ·
    refine ⟨67963143171794655162252329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45308762114529770108168219 67963143171794655162252329)
    ·
      refine ⟨50972357378845991371689247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67963143171794655162252329 50972357378845991371689247)
      ·
        refine ⟨76458536068268987057533871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50972357378845991371689247 76458536068268987057533871)
        ·
          refine ⟨114687804102403480586300807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76458536068268987057533871 114687804102403480586300807)
          ·
            refine ⟨172031706153605220879451211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114687804102403480586300807 172031706153605220879451211)
            ·
              refine ⟨258047559230407831319176817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172031706153605220879451211 258047559230407831319176817)
              ·
                refine ⟨193535669422805873489382613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258047559230407831319176817 193535669422805873489382613)
                ·
                  refine ⟨4535992252097012659907405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 193535669422805873489382613 4535992252097012659907405)
                  ·
                    refine ⟨1700997094536379747465277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4535992252097012659907405 1700997094536379747465277)
                    ·
                      refine ⟨637873910451142405299479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1700997094536379747465277 637873910451142405299479)
                      ·
                        rfl

theorem cell23_1242255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_1242255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242255 prefixEnd_1242255 := by exact prefixLift 1242255
  have htrace : WordTrace (prefixWord ++ tailWord_1242255) baseStart_1242255 baseEnd_1242255 := by
    simpa [prefixWord, tailWord_1242255, baseEnd_1242255] using wordTrace_append hprefix tailTrace_1242255
  have hstable : (prefixWord ++ tailWord_1242255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242255).length < 2 ^ (prefixWord ++ tailWord_1242255).sum := by decide
  have hdescent : baseEnd_1242255 < baseStart_1242255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242259 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 1, 2, 3]
def baseStart_1242259 : Nat := 118140960795 + 1242259 * 2 ^ 59
def prefixEnd_1242259 : Nat := 4983230072969 + 3 ^ 40 * 1242259 * 2
def baseEnd_1242259 : Nat := 637875964373760389649461

theorem tailTrace_1242259 : CollatzResearch.WordTrace tailWord_1242259 prefixEnd_1242259 637875964373760389649461 := by
  unfold tailWord_1242259
  simp only [CollatzResearch.WordTrace]
  refine ⟨45308908006515278791313831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30205938671010185860875887 45308908006515278791313831)
  ·
    refine ⟨67963362009772918186970747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45308908006515278791313831 67963362009772918186970747)
    ·
      refine ⟨101945043014659377280456121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67963362009772918186970747 101945043014659377280456121)
      ·
        refine ⟨76458782260994532960342091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101945043014659377280456121 76458782260994532960342091)
        ·
          refine ⟨114688173391491799440513137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76458782260994532960342091 114688173391491799440513137)
          ·
            refine ⟨86016130043618849580384853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114688173391491799440513137 86016130043618849580384853)
            ·
              refine ⟨1008001523948658393520135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 86016130043618849580384853 1008001523948658393520135)
              ·
                refine ⟨1512002285922987590280203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008001523948658393520135 1512002285922987590280203)
                ·
                  refine ⟨2268003428884481385420305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512002285922987590280203 2268003428884481385420305)
                  ·
                    refine ⟨1701002571663361039065229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268003428884481385420305 1701002571663361039065229)
                    ·
                      refine ⟨637875964373760389649461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1701002571663361039065229 637875964373760389649461)
                      ·
                        rfl

theorem cell23_1242259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 2, 3].length) (baseStart_1242259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242259 prefixEnd_1242259 := by exact prefixLift 1242259
  have htrace : WordTrace (prefixWord ++ tailWord_1242259) baseStart_1242259 baseEnd_1242259 := by
    simpa [prefixWord, tailWord_1242259, baseEnd_1242259] using wordTrace_append hprefix tailTrace_1242259
  have hstable : (prefixWord ++ tailWord_1242259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242259).length < 2 ^ (prefixWord ++ tailWord_1242259).sum := by decide
  have hdescent : baseEnd_1242259 < baseStart_1242259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242266 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_1242266 : Nat := 118140960795 + 1242266 * 2 ^ 59
def prefixEnd_1242266 : Nat := 4983230072969 + 3 ^ 40 * 1242266 * 2
def baseEnd_1242266 : Nat := 212626519579447287420643

theorem tailTrace_1242266 : CollatzResearch.WordTrace tailWord_1242266 prefixEnd_1242266 212626519579447287420643 := by
  unfold tailWord_1242266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327290829372479746704663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30206108878326612657879101 11327290829372479746704663)
  ·
    refine ⟨16990936244058719620056995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11327290829372479746704663 16990936244058719620056995)
    ·
      refine ⟨25486404366088079430085493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16990936244058719620056995 25486404366088079430085493)
      ·
        refine ⟨2389350409320757446570515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25486404366088079430085493 2389350409320757446570515)
        ·
          refine ⟨3584025613981136169855773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389350409320757446570515 3584025613981136169855773)
          ·
            refine ⟨1344009605242926063695915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3584025613981136169855773 1344009605242926063695915)
            ·
              refine ⟨2016014407864389095543873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344009605242926063695915 2016014407864389095543873)
              ·
                refine ⟨1512010805898291821657905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016014407864389095543873 1512010805898291821657905)
                ·
                  refine ⟨1134008104423718866243429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512010805898291821657905 1134008104423718866243429)
                  ·
                    refine ⟨212626519579447287420643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134008104423718866243429 212626519579447287420643)
                    ·
                      rfl

theorem cell23_1242266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_1242266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242266 prefixEnd_1242266 := by exact prefixLift 1242266
  have htrace : WordTrace (prefixWord ++ tailWord_1242266) baseStart_1242266 baseEnd_1242266 := by
    simpa [prefixWord, tailWord_1242266, baseEnd_1242266] using wordTrace_append hprefix tailTrace_1242266
  have hstable : (prefixWord ++ tailWord_1242266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242266).length < 2 ^ (prefixWord ++ tailWord_1242266).sum := by decide
  have hdescent : baseEnd_1242266 < baseStart_1242266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242289 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1242289 : Nat := 118140960795 + 1242289 * 2 ^ 59
def prefixEnd_1242289 : Nat := 4983230072969 + 3 ^ 40 * 1242289 * 2
def baseEnd_1242289 : Nat := 637891368793395272274323

theorem tailTrace_1242289 : CollatzResearch.WordTrace tailWord_1242289 prefixEnd_1242289 637891368793395272274323 := by
  unfold tailWord_1242289
  simp only [CollatzResearch.WordTrace]
  refine ⟨45310002196406593914905921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30206668130937729276603947 45310002196406593914905921)
  ·
    refine ⟨33982501647304945436179441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45310002196406593914905921 33982501647304945436179441)
    ·
      refine ⟨25486876235478709077134581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33982501647304945436179441 25486876235478709077134581)
      ·
        refine ⟨2389394647076128975981367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25486876235478709077134581 2389394647076128975981367)
        ·
          refine ⟨3584091970614193463972051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389394647076128975981367 3584091970614193463972051)
          ·
            refine ⟨5376137955921290195958077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584091970614193463972051 5376137955921290195958077)
            ·
              refine ⟨2016051733470483823484279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5376137955921290195958077 2016051733470483823484279)
              ·
                refine ⟨3024077600205725735226419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016051733470483823484279 3024077600205725735226419)
                ·
                  refine ⟨4536116400308588602839629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024077600205725735226419 4536116400308588602839629)
                  ·
                    refine ⟨1701043650115720726064861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4536116400308588602839629 1701043650115720726064861)
                    ·
                      refine ⟨637891368793395272274323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1701043650115720726064861 637891368793395272274323)
                      ·
                        rfl

theorem cell23_1242289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1242289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242289 prefixEnd_1242289 := by exact prefixLift 1242289
  have htrace : WordTrace (prefixWord ++ tailWord_1242289) baseStart_1242289 baseEnd_1242289 := by
    simpa [prefixWord, tailWord_1242289, baseEnd_1242289] using wordTrace_append hprefix tailTrace_1242289
  have hstable : (prefixWord ++ tailWord_1242289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242289).length < 2 ^ (prefixWord ++ tailWord_1242289).sum := by decide
  have hdescent : baseEnd_1242289 < baseStart_1242289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242302 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1242302 : Nat := 118140960795 + 1242302 * 2 ^ 59
def prefixEnd_1242302 : Nat := 4983230072969 + 3 ^ 40 * 1242302 * 2
def baseEnd_1242302 : Nat := 637898044041903721411763

theorem tailTrace_1242302 : CollatzResearch.WordTrace tailWord_1242302 prefixEnd_1242302 637898044041903721411763 := by
  unfold tailWord_1242302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663809543169937141891145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30206984230239664756752773 5663809543169937141891145)
  ·
    refine ⟨4247857157377452856418359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5663809543169937141891145 4247857157377452856418359)
    ·
      refine ⟨6371785736066179284627539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247857157377452856418359 6371785736066179284627539)
      ·
        refine ⟨9557678604099268926941309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6371785736066179284627539 9557678604099268926941309)
        ·
          refine ⟨3584129476537225847602991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9557678604099268926941309 3584129476537225847602991)
          ·
            refine ⟨5376194214805838771404487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584129476537225847602991 5376194214805838771404487)
            ·
              refine ⟨8064291322208758157106731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376194214805838771404487 8064291322208758157106731)
              ·
                refine ⟨12096436983313137235660097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8064291322208758157106731 12096436983313137235660097)
                ·
                  refine ⟨9072327737484852926745073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12096436983313137235660097 9072327737484852926745073)
                  ·
                    refine ⟨6804245803113639695058805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9072327737484852926745073 6804245803113639695058805)
                    ·
                      refine ⟨637898044041903721411763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6804245803113639695058805 637898044041903721411763)
                      ·
                        rfl

theorem cell23_1242302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1242302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242302 prefixEnd_1242302 := by exact prefixLift 1242302
  have htrace : WordTrace (prefixWord ++ tailWord_1242302) baseStart_1242302 baseEnd_1242302 := by
    simpa [prefixWord, tailWord_1242302, baseEnd_1242302] using wordTrace_append hprefix tailTrace_1242302
  have hstable : (prefixWord ++ tailWord_1242302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242302).length < 2 ^ (prefixWord ++ tailWord_1242302).sum := by decide
  have hdescent : baseEnd_1242302 < baseStart_1242302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242392 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1242392 : Nat := 118140960795 + 1242392 * 2 ^ 59
def prefixEnd_1242392 : Nat := 4983230072969 + 3 ^ 40 * 1242392 * 2
def baseEnd_1242392 : Nat := 637944257300808369286349

theorem tailTrace_1242392 : CollatzResearch.WordTrace tailWord_1242392 prefixEnd_1242392 637944257300808369286349 := by
  unfold tailWord_1242392
  simp only [CollatzResearch.WordTrace]
  refine ⟨22656879457516721252952715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30209172610022295003936953 22656879457516721252952715)
  ·
    refine ⟨33985319186275081879429073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22656879457516721252952715 33985319186275081879429073)
    ·
      refine ⟨25488989389706311409571805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33985319186275081879429073 25488989389706311409571805)
      ·
        refine ⟨9558371021139866778589427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25488989389706311409571805 9558371021139866778589427)
        ·
          refine ⟨14337556531709800167884141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9558371021139866778589427 14337556531709800167884141)
          ·
            refine ⟨5376583699391175062956553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14337556531709800167884141 5376583699391175062956553)
            ·
              refine ⟨4032437774543381297217415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5376583699391175062956553 4032437774543381297217415)
              ·
                refine ⟨6048656661815071945826123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4032437774543381297217415 6048656661815071945826123)
                ·
                  refine ⟨9072984992722607918739185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6048656661815071945826123 9072984992722607918739185)
                  ·
                    refine ⟨6804738744541955939054389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9072984992722607918739185 6804738744541955939054389)
                    ·
                      refine ⟨637944257300808369286349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6804738744541955939054389 637944257300808369286349)
                      ·
                        rfl

theorem cell23_1242392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1242392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242392 prefixEnd_1242392 := by exact prefixLift 1242392
  have htrace : WordTrace (prefixWord ++ tailWord_1242392) baseStart_1242392 baseEnd_1242392 := by
    simpa [prefixWord, tailWord_1242392, baseEnd_1242392] using wordTrace_append hprefix tailTrace_1242392
  have hstable : (prefixWord ++ tailWord_1242392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242392).length < 2 ^ (prefixWord ++ tailWord_1242392).sum := by decide
  have hdescent : baseEnd_1242392 < baseStart_1242392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242395 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 8]
def baseStart_1242395 : Nat := 118140960795 + 1242395 * 2 ^ 59
def prefixEnd_1242395 : Nat := 4983230072969 + 3 ^ 40 * 1242395 * 2
def baseEnd_1242395 : Nat := 212648599247590619182945

theorem tailTrace_1242395 : CollatzResearch.WordTrace tailWord_1242395 prefixEnd_1242395 212648599247590619182945 := by
  unfold tailWord_1242395
  simp only [CollatzResearch.WordTrace]
  refine ⟨45313868334022574018264639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30209245556015049345509759 45313868334022574018264639)
  ·
    refine ⟨67970802501033861027396959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45313868334022574018264639 67970802501033861027396959)
    ·
      refine ⟨101956203751550791541095439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67970802501033861027396959 101956203751550791541095439)
      ·
        refine ⟨152934305627326187311643159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101956203751550791541095439 152934305627326187311643159)
        ·
          refine ⟨229401458440989280967464739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152934305627326187311643159 229401458440989280967464739)
          ·
            refine ⟨344102187661483921451197109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229401458440989280967464739 344102187661483921451197109)
            ·
              refine ⟨32259580093264117636049729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344102187661483921451197109 32259580093264117636049729)
              ·
                refine ⟨24194685069948088227037297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32259580093264117636049729 24194685069948088227037297)
                ·
                  refine ⟨18146013802461066170277973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24194685069948088227037297 18146013802461066170277973)
                  ·
                    refine ⟨212648599247590619182945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18146013802461066170277973 212648599247590619182945)
                    ·
                      rfl

theorem cell23_1242395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_1242395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242395 prefixEnd_1242395 := by exact prefixLift 1242395
  have htrace : WordTrace (prefixWord ++ tailWord_1242395) baseStart_1242395 baseEnd_1242395 := by
    simpa [prefixWord, tailWord_1242395, baseEnd_1242395] using wordTrace_append hprefix tailTrace_1242395
  have hstable : (prefixWord ++ tailWord_1242395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242395).length < 2 ^ (prefixWord ++ tailWord_1242395).sum := by decide
  have hdescent : baseEnd_1242395 < baseStart_1242395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242419 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 4]
def baseStart_1242419 : Nat := 118140960795 + 1242419 * 2 ^ 59
def prefixEnd_1242419 : Nat := 4983230072969 + 3 ^ 40 * 1242419 * 2
def baseEnd_1242419 : Nat := 637958121278479763648725

theorem tailTrace_1242419 : CollatzResearch.WordTrace tailWord_1242419 prefixEnd_1242419 637958121278479763648725 := by
  unfold tailWord_1242419
  simp only [CollatzResearch.WordTrace]
  refine ⟨45314743685935626117138311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30209829123957084078092207 45314743685935626117138311)
  ·
    refine ⟨67972115528903439175707467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45314743685935626117138311 67972115528903439175707467)
    ·
      refine ⟨101958173293355158763561201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67972115528903439175707467 101958173293355158763561201)
      ·
        refine ⟨76468629970016369072670901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101958173293355158763561201 76468629970016369072670901)
        ·
          refine ⟨7168934059689034600562897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76468629970016369072670901 7168934059689034600562897)
          ·
            refine ⟨5376700544766775950422173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168934059689034600562897 5376700544766775950422173)
            ·
              refine ⟨2016262704287540981408315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5376700544766775950422173 2016262704287540981408315)
              ·
                refine ⟨3024394056431311472112473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016262704287540981408315 3024394056431311472112473)
                ·
                  refine ⟨2268295542323483604084355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024394056431311472112473 2268295542323483604084355)
                  ·
                    refine ⟨3402443313485225406126533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2268295542323483604084355 3402443313485225406126533)
                    ·
                      refine ⟨637958121278479763648725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3402443313485225406126533 637958121278479763648725)
                      ·
                        rfl

theorem cell23_1242419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_1242419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242419 prefixEnd_1242419 := by exact prefixLift 1242419
  have htrace : WordTrace (prefixWord ++ tailWord_1242419) baseStart_1242419 baseEnd_1242419 := by
    simpa [prefixWord, tailWord_1242419, baseEnd_1242419] using wordTrace_append hprefix tailTrace_1242419
  have hstable : (prefixWord ++ tailWord_1242419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242419).length < 2 ^ (prefixWord ++ tailWord_1242419).sum := by decide
  have hdescent : baseEnd_1242419 < baseStart_1242419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242446 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_1242446 : Nat := 118140960795 + 1242446 * 2 ^ 59
def prefixEnd_1242446 : Nat := 4983230072969 + 3 ^ 40 * 1242446 * 2
def baseEnd_1242446 : Nat := 212657328418717052670367

theorem tailTrace_1242446 : CollatzResearch.WordTrace tailWord_1242446 prefixEnd_1242446 212657328418717052670367 := by
  unfold tailWord_1242446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664466057104726216046399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30210485637891873152247461 5664466057104726216046399)
  ·
    refine ⟨8496699085657089324069599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5664466057104726216046399 8496699085657089324069599)
    ·
      refine ⟨12745048628485633986104399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8496699085657089324069599 12745048628485633986104399)
      ·
        refine ⟨19117572942728450979156599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12745048628485633986104399 19117572942728450979156599)
        ·
          refine ⟨28676359414092676468734899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19117572942728450979156599 28676359414092676468734899)
          ·
            refine ⟨43014539121139014703102349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28676359414092676468734899 43014539121139014703102349)
            ·
              refine ⟨16130452170427130513663381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43014539121139014703102349 16130452170427130513663381)
              ·
                refine ⟨756114945488771742827971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16130452170427130513663381 756114945488771742827971)
                ·
                  refine ⟨1134172418233157614241957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756114945488771742827971 1134172418233157614241957)
                  ·
                    refine ⟨212657328418717052670367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134172418233157614241957 212657328418717052670367)
                    ·
                      rfl

theorem cell23_1242446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_1242446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242446 prefixEnd_1242446 := by exact prefixLift 1242446
  have htrace : WordTrace (prefixWord ++ tailWord_1242446) baseStart_1242446 baseEnd_1242446 := by
    simpa [prefixWord, tailWord_1242446, baseEnd_1242446] using wordTrace_append hprefix tailTrace_1242446
  have hstable : (prefixWord ++ tailWord_1242446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242446).length < 2 ^ (prefixWord ++ tailWord_1242446).sum := by decide
  have hdescent : baseEnd_1242446 < baseStart_1242446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242479 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 1, 5, 2]
def baseStart_1242479 : Nat := 118140960795 + 1242479 * 2 ^ 59
def prefixEnd_1242479 : Nat := 4983230072969 + 3 ^ 40 * 1242479 * 2
def baseEnd_1242479 : Nat := 637988930117749528898449

theorem tailTrace_1242479 : CollatzResearch.WordTrace tailWord_1242479 prefixEnd_1242479 637988930117749528898449 := by
  unfold tailWord_1242479
  simp only [CollatzResearch.WordTrace]
  refine ⟨45316932065718256364322491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30211288043812170909548327 45316932065718256364322491)
  ·
    refine ⟨67975398098577384546483737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45316932065718256364322491 67975398098577384546483737)
    ·
      refine ⟨50981548573933038409862803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67975398098577384546483737 50981548573933038409862803)
      ·
        refine ⟨76472322860899557614794205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50981548573933038409862803 76472322860899557614794205)
        ·
          refine ⟨28677121072837334105547827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76472322860899557614794205 28677121072837334105547827)
          ·
            refine ⟨43015681609256001158321741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28677121072837334105547827 43015681609256001158321741)
            ·
              refine ⟨16130880603471000434370653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43015681609256001158321741 16130880603471000434370653)
              ·
                refine ⟨6049080226301625162888995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16130880603471000434370653 6049080226301625162888995)
                ·
                  refine ⟨9073620339452437744333493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6049080226301625162888995 9073620339452437744333493)
                  ·
                    refine ⟨850651906823666038531265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9073620339452437744333493 850651906823666038531265)
                    ·
                      refine ⟨637988930117749528898449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850651906823666038531265 637988930117749528898449)
                      ·
                        rfl

theorem cell23_1242479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5, 2].length) (baseStart_1242479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242479 prefixEnd_1242479 := by exact prefixLift 1242479
  have htrace : WordTrace (prefixWord ++ tailWord_1242479) baseStart_1242479 baseEnd_1242479 := by
    simpa [prefixWord, tailWord_1242479, baseEnd_1242479] using wordTrace_append hprefix tailTrace_1242479
  have hstable : (prefixWord ++ tailWord_1242479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242479).length < 2 ^ (prefixWord ++ tailWord_1242479).sum := by decide
  have hdescent : baseEnd_1242479 < baseStart_1242479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242489 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 1, 5]
def baseStart_1242489 : Nat := 118140960795 + 1242489 * 2 ^ 59
def prefixEnd_1242489 : Nat := 4983230072969 + 3 ^ 40 * 1242489 * 2
def baseEnd_1242489 : Nat := 212664688308098163257801

theorem tailTrace_1242489 : CollatzResearch.WordTrace tailWord_1242489 prefixEnd_1242489 212664688308098163257801 := by
  unfold tailWord_1242489
  simp only [CollatzResearch.WordTrace]
  refine ⟨45317296795682028072186521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30211531197121352048124347 45317296795682028072186521)
  ·
    refine ⟨33987972596761521054139891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45317296795682028072186521 33987972596761521054139891)
    ·
      refine ⟨50981958895142281581209837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33987972596761521054139891 50981958895142281581209837)
      ·
        refine ⟨19118234585678355592953689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50981958895142281581209837 19118234585678355592953689)
        ·
          refine ⟨14338675939258766694715267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19118234585678355592953689 14338675939258766694715267)
          ·
            refine ⟨21508013908888150042072901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14338675939258766694715267 21508013908888150042072901)
            ·
              refine ⟨4032752607916528132888669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21508013908888150042072901 4032752607916528132888669)
              ·
                refine ⟨1512282227968698049833251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032752607916528132888669 1512282227968698049833251)
                ·
                  refine ⟨2268423341953047074749877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512282227968698049833251 2268423341953047074749877)
                  ·
                    refine ⟨212664688308098163257801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2268423341953047074749877 212664688308098163257801)
                    ·
                      rfl

theorem cell23_1242489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_1242489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242489 prefixEnd_1242489 := by exact prefixLift 1242489
  have htrace : WordTrace (prefixWord ++ tailWord_1242489) baseStart_1242489 baseEnd_1242489 := by
    simpa [prefixWord, tailWord_1242489, baseEnd_1242489] using wordTrace_append hprefix tailTrace_1242489
  have hstable : (prefixWord ++ tailWord_1242489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242489).length < 2 ^ (prefixWord ++ tailWord_1242489).sum := by decide
  have hdescent : baseEnd_1242489 < baseStart_1242489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242503 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1242503 : Nat := 118140960795 + 1242503 * 2 ^ 59
def prefixEnd_1242503 : Nat := 4983230072969 + 3 ^ 40 * 1242503 * 2
def baseEnd_1242503 : Nat := 638001253653457434998339

theorem tailTrace_1242503 : CollatzResearch.WordTrace tailWord_1242503 prefixEnd_1242503 638001253653457434998339 := by
  unfold tailWord_1242503
  simp only [CollatzResearch.WordTrace]
  refine ⟨45317807417631308463196163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30211871611754205642130775 45317807417631308463196163)
  ·
    refine ⟨67976711126446962694794245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45317807417631308463196163 67976711126446962694794245)
    ·
      refine ⟨12745633336208805505273921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67976711126446962694794245 12745633336208805505273921)
      ·
        refine ⟨9559225002156604128955441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12745633336208805505273921 9559225002156604128955441)
        ·
          refine ⟨7169418751617453096716581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9559225002156604128955441 7169418751617453096716581)
          ·
            refine ⟨1344266015928272455634359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7169418751617453096716581 1344266015928272455634359)
            ·
              refine ⟨2016399023892408683451539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344266015928272455634359 2016399023892408683451539)
              ·
                refine ⟨3024598535838613025177309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016399023892408683451539 3024598535838613025177309)
                ·
                  refine ⟨1134224450939479884441491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3024598535838613025177309 1134224450939479884441491)
                  ·
                    refine ⟨1701336676409219826662237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1134224450939479884441491 1701336676409219826662237)
                    ·
                      refine ⟨638001253653457434998339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1701336676409219826662237 638001253653457434998339)
                      ·
                        rfl

theorem cell23_1242503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1242503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242503 prefixEnd_1242503 := by exact prefixLift 1242503
  have htrace : WordTrace (prefixWord ++ tailWord_1242503) baseStart_1242503 baseEnd_1242503 := by
    simpa [prefixWord, tailWord_1242503, baseEnd_1242503] using wordTrace_append hprefix tailTrace_1242503
  have hstable : (prefixWord ++ tailWord_1242503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242503).length < 2 ^ (prefixWord ++ tailWord_1242503).sum := by decide
  have hdescent : baseEnd_1242503 < baseStart_1242503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242510 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_1242510 : Nat := 118140960795 + 1242510 * 2 ^ 59
def prefixEnd_1242510 : Nat := 4983230072969 + 3 ^ 40 * 1242510 * 2
def baseEnd_1242510 : Nat := 70889427557559878623423

theorem tailTrace_1242510 : CollatzResearch.WordTrace tailWord_1242510 prefixEnd_1242510 70889427557559878623423 := by
  unfold tailWord_1242510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664757841075743582337623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30212041819070632439133989 5664757841075743582337623)
  ·
    refine ⟨8497136761613615373506435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5664757841075743582337623 8497136761613615373506435)
    ·
      refine ⟨12745705142420423060259653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8497136761613615373506435 12745705142420423060259653)
      ·
        refine ⟨2389819714203829323798685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12745705142420423060259653 2389819714203829323798685)
        ·
          refine ⟨896182392826435996424507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2389819714203829323798685 896182392826435996424507)
          ·
            refine ⟨1344273589239653994636761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896182392826435996424507 1344273589239653994636761)
            ·
              refine ⟨1008205191929740495977571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344273589239653994636761 1008205191929740495977571)
              ·
                refine ⟨1512307787894610743966357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008205191929740495977571 1512307787894610743966357)
                ·
                  refine ⟨70889427557559878623423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1512307787894610743966357 70889427557559878623423)
                  ·
                    rfl

theorem cell23_1242510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_1242510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242510 prefixEnd_1242510 := by exact prefixLift 1242510
  have htrace : WordTrace (prefixWord ++ tailWord_1242510) baseStart_1242510 baseEnd_1242510 := by
    simpa [prefixWord, tailWord_1242510, baseEnd_1242510] using wordTrace_append hprefix tailTrace_1242510
  have hstable : (prefixWord ++ tailWord_1242510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242510).length < 2 ^ (prefixWord ++ tailWord_1242510).sum := by decide
  have hdescent : baseEnd_1242510 < baseStart_1242510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242553 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 2, 4]
def baseStart_1242553 : Nat := 118140960795 + 1242553 * 2 ^ 59
def prefixEnd_1242553 : Nat := 4983230072969 + 3 ^ 40 * 1242553 * 2
def baseEnd_1242553 : Nat := 212675642562060746457703

theorem tailTrace_1242553 : CollatzResearch.WordTrace tailWord_1242553 prefixEnd_1242553 212675642562060746457703 := by
  unfold tailWord_1242553
  simp only [CollatzResearch.WordTrace]
  refine ⟨45319631067450167002516313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30213087378300111335010875 45319631067450167002516313)
  ·
    refine ⟨33989723300587625251887235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45319631067450167002516313 33989723300587625251887235)
    ·
      refine ⟨50984584950881437877830853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33989723300587625251887235 50984584950881437877830853)
      ·
        refine ⟨9559609678290269602093285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50984584950881437877830853 9559609678290269602093285)
        ·
          refine ⟨1792426814679425550392491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9559609678290269602093285 1792426814679425550392491)
          ·
            refine ⟨2688640222019138325588737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792426814679425550392491 2688640222019138325588737)
            ·
              refine ⟨2016480166514353744191553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2688640222019138325588737 2016480166514353744191553)
              ·
                refine ⟨1512360124885765308143665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016480166514353744191553 1512360124885765308143665)
                ·
                  refine ⟨1134270093664323981107749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512360124885765308143665 1134270093664323981107749)
                  ·
                    refine ⟨212675642562060746457703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134270093664323981107749 212675642562060746457703)
                    ·
                      rfl

theorem cell23_1242553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_1242553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242553 prefixEnd_1242553 := by exact prefixLift 1242553
  have htrace : WordTrace (prefixWord ++ tailWord_1242553) baseStart_1242553 baseEnd_1242553 := by
    simpa [prefixWord, tailWord_1242553, baseEnd_1242553] using wordTrace_append hprefix tailTrace_1242553
  have hstable : (prefixWord ++ tailWord_1242553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242553).length < 2 ^ (prefixWord ++ tailWord_1242553).sum := by decide
  have hdescent : baseEnd_1242553 < baseStart_1242553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242609 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_1242609 : Nat := 118140960795 + 1242609 * 2 ^ 59
def prefixEnd_1242609 : Nat := 4983230072969 + 3 ^ 40 * 1242609 * 2
def baseEnd_1242609 : Nat := 212685227534278006757617

theorem tailTrace_1242609 : CollatzResearch.WordTrace tailWord_1242609 prefixEnd_1242609 212685227534278006757617 := by
  unfold tailWord_1242609
  simp only [CollatzResearch.WordTrace]
  refine ⟨45321673555247288566554881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30214449036831525711036587 45321673555247288566554881)
  ·
    refine ⟨33991255166435466424916161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45321673555247288566554881 33991255166435466424916161)
    ·
      refine ⟨25493441374826599818687121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33991255166435466424916161 25493441374826599818687121)
      ·
        refine ⟨19120081031119949864015341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25493441374826599818687121 19120081031119949864015341)
        ·
          refine ⟨7170030386669981199005753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19120081031119949864015341 7170030386669981199005753)
          ·
            refine ⟨5377522790002485899254315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7170030386669981199005753 5377522790002485899254315)
            ·
              refine ⟨8066284185003728848881473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377522790002485899254315 8066284185003728848881473)
              ·
                refine ⟨6049713138752796636661105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8066284185003728848881473 6049713138752796636661105)
                ·
                  refine ⟨4537284854064597477495829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6049713138752796636661105 4537284854064597477495829)
                  ·
                    refine ⟨212685227534278006757617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4537284854064597477495829 212685227534278006757617)
                    ·
                      rfl

theorem cell23_1242609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_1242609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242609 prefixEnd_1242609 := by exact prefixLift 1242609
  have htrace : WordTrace (prefixWord ++ tailWord_1242609) baseStart_1242609 baseEnd_1242609 := by
    simpa [prefixWord, tailWord_1242609, baseEnd_1242609] using wordTrace_append hprefix tailTrace_1242609
  have hstable : (prefixWord ++ tailWord_1242609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242609).length < 2 ^ (prefixWord ++ tailWord_1242609).sum := by decide
  have hdescent : baseEnd_1242609 < baseStart_1242609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242610 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1242610 : Nat := 118140960795 + 1242610 * 2 ^ 59
def prefixEnd_1242610 : Nat := 4983230072969 + 3 ^ 40 * 1242610 * 2
def baseEnd_1242610 : Nat := 638056196083488516360347

theorem tailTrace_1242610 : CollatzResearch.WordTrace tailWord_1242610 prefixEnd_1242610 638056196083488516360347 := by
  unfold tailWord_1242610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11330427507060916434335321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30214473352162443824894189 11330427507060916434335321)
  ·
    refine ⟨8497820630295687325751491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11330427507060916434335321 8497820630295687325751491)
    ·
      refine ⟨12746730945443530988627237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8497820630295687325751491 12746730945443530988627237)
      ·
        refine ⟨2390012052270662060367607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12746730945443530988627237 2390012052270662060367607)
        ·
          refine ⟨3585018078405993090551411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390012052270662060367607 3585018078405993090551411)
          ·
            refine ⟨5377527117608989635827117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585018078405993090551411 5377527117608989635827117)
            ·
              refine ⟨2016572669103371113435169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5377527117608989635827117 2016572669103371113435169)
              ·
                refine ⟨1512429501827528335076377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016572669103371113435169 1512429501827528335076377)
                ·
                  refine ⟨1134322126370646251307283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512429501827528335076377 1134322126370646251307283)
                  ·
                    refine ⟨1701483189555969376960925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1134322126370646251307283 1701483189555969376960925)
                    ·
                      refine ⟨638056196083488516360347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1701483189555969376960925 638056196083488516360347)
                      ·
                        rfl

theorem cell23_1242610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1242610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242610 prefixEnd_1242610 := by exact prefixLift 1242610
  have htrace : WordTrace (prefixWord ++ tailWord_1242610) baseStart_1242610 baseEnd_1242610 := by
    simpa [prefixWord, tailWord_1242610, baseEnd_1242610] using wordTrace_append hprefix tailTrace_1242610
  have hstable : (prefixWord ++ tailWord_1242610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242610).length < 2 ^ (prefixWord ++ tailWord_1242610).sum := by decide
  have hdescent : baseEnd_1242610 < baseStart_1242610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242679 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1242679 : Nat := 118140960795 + 1242679 * 2 ^ 59
def prefixEnd_1242679 : Nat := 4983230072969 + 3 ^ 40 * 1242679 * 2
def baseEnd_1242679 : Nat := 638091626248648746397529

theorem tailTrace_1242679 : CollatzResearch.WordTrace tailWord_1242679 prefixEnd_1242679 638091626248648746397529 := by
  unfold tailWord_1242679
  simp only [CollatzResearch.WordTrace]
  refine ⟨45324226664993690521603091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30216151109995793681068727 45324226664993690521603091)
  ·
    refine ⟨67986339997490535782404637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45324226664993690521603091 67986339997490535782404637)
    ·
      refine ⟨25494877499058950918401739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67986339997490535782404637 25494877499058950918401739)
      ·
        refine ⟨38242316248588426377602609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25494877499058950918401739 38242316248588426377602609)
        ·
          refine ⟨28681737186441319783201957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38242316248588426377602609 28681737186441319783201957)
          ·
            refine ⟨5377825722457747459350367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28681737186441319783201957 5377825722457747459350367)
            ·
              refine ⟨8066738583686621189025551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377825722457747459350367 8066738583686621189025551)
              ·
                refine ⟨12100107875529931783538327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8066738583686621189025551 12100107875529931783538327)
                ·
                  refine ⟨18150161813294897675307491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100107875529931783538327 18150161813294897675307491)
                  ·
                    refine ⟨27225242719942346512961237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18150161813294897675307491 27225242719942346512961237)
                    ·
                      refine ⟨638091626248648746397529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27225242719942346512961237 638091626248648746397529)
                      ·
                        rfl

theorem cell23_1242679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1242679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242679 prefixEnd_1242679 := by exact prefixLift 1242679
  have htrace : WordTrace (prefixWord ++ tailWord_1242679) baseStart_1242679 baseEnd_1242679 := by
    simpa [prefixWord, tailWord_1242679, baseEnd_1242679] using wordTrace_append hprefix tailTrace_1242679
  have hstable : (prefixWord ++ tailWord_1242679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242679).length < 2 ^ (prefixWord ++ tailWord_1242679).sum := by decide
  have hdescent : baseEnd_1242679 < baseStart_1242679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242684 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_1242684 : Nat := 118140960795 + 1242684 * 2 ^ 59
def prefixEnd_1242684 : Nat := 4983230072969 + 3 ^ 40 * 1242684 * 2
def baseEnd_1242684 : Nat := 638094193651921226835007

theorem tailTrace_1242684 : CollatzResearch.WordTrace tailWord_1242684 prefixEnd_1242684 638094193651921226835007 := by
  unfold tailWord_1242684
  simp only [CollatzResearch.WordTrace]
  refine ⟨22662204514987788187767553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30216272686650384250356737 22662204514987788187767553)
  ·
    refine ⟨16996653386240841140825665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22662204514987788187767553 16996653386240841140825665)
    ·
      refine ⟨12747490039680630855619249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16996653386240841140825665 12747490039680630855619249)
      ·
        refine ⟨9560617529760473141714437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12747490039680630855619249 9560617529760473141714437)
        ·
          refine ⟨1792615786830088714071457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9560617529760473141714437 1792615786830088714071457)
          ·
            refine ⟨1344461840122566535553593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1792615786830088714071457 1344461840122566535553593)
            ·
              refine ⟨1008346380091924901665195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344461840122566535553593 1008346380091924901665195)
              ·
                refine ⟨1512519570137887352497793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008346380091924901665195 1512519570137887352497793)
                ·
                  refine ⟨1134389677603415514373345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512519570137887352497793 1134389677603415514373345)
                  ·
                    refine ⟨850792258202561635780009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1134389677603415514373345 850792258202561635780009)
                    ·
                      refine ⟨638094193651921226835007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850792258202561635780009 638094193651921226835007)
                      ·
                        rfl

theorem cell23_1242684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_1242684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242684 prefixEnd_1242684 := by exact prefixLift 1242684
  have htrace : WordTrace (prefixWord ++ tailWord_1242684) baseStart_1242684 baseEnd_1242684 := by
    simpa [prefixWord, tailWord_1242684, baseEnd_1242684] using wordTrace_append hprefix tailTrace_1242684
  have hstable : (prefixWord ++ tailWord_1242684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242684).length < 2 ^ (prefixWord ++ tailWord_1242684).sum := by decide
  have hdescent : baseEnd_1242684 < baseStart_1242684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242729 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 8]
def baseStart_1242729 : Nat := 118140960795 + 1242729 * 2 ^ 59
def prefixEnd_1242729 : Nat := 4983230072969 + 3 ^ 40 * 1242729 * 2
def baseEnd_1242729 : Nat := 70901922253485950085811

theorem tailTrace_1242729 : CollatzResearch.WordTrace tailWord_1242729 prefixEnd_1242729 70901922253485950085811 := by
  unfold tailWord_1242729
  simp only [CollatzResearch.WordTrace]
  refine ⟨45326050314812549060923241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30217366876541699373948827 45326050314812549060923241)
  ·
    refine ⟨33994537736109411795692431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45326050314812549060923241 33994537736109411795692431)
    ·
      refine ⟨50991806604164117693538647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33994537736109411795692431 50991806604164117693538647)
      ·
        refine ⟨76487709906246176540307971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50991806604164117693538647 76487709906246176540307971)
        ·
          refine ⟨114731564859369264810461957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76487709906246176540307971 114731564859369264810461957)
          ·
            refine ⟨21512168411131737151961617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114731564859369264810461957 21512168411131737151961617)
            ·
              refine ⟨16134126308348802863971213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21512168411131737151961617 16134126308348802863971213)
              ·
                refine ⟨6050297365630801073989205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16134126308348802863971213 6050297365630801073989205)
                ·
                  refine ⟨70901922253485950085811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6050297365630801073989205 70901922253485950085811)
                  ·
                    rfl

theorem cell23_1242729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_1242729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242729 prefixEnd_1242729 := by exact prefixLift 1242729
  have htrace : WordTrace (prefixWord ++ tailWord_1242729) baseStart_1242729 baseEnd_1242729 := by
    simpa [prefixWord, tailWord_1242729, baseEnd_1242729] using wordTrace_append hprefix tailTrace_1242729
  have hstable : (prefixWord ++ tailWord_1242729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242729).length < 2 ^ (prefixWord ++ tailWord_1242729).sum := by decide
  have hdescent : baseEnd_1242729 < baseStart_1242729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242760 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1242760 : Nat := 118140960795 + 1242760 * 2 ^ 59
def prefixEnd_1242760 : Nat := 4983230072969 + 3 ^ 40 * 1242760 * 2
def baseEnd_1242760 : Nat := 638133218181662929484657

theorem tailTrace_1242760 : CollatzResearch.WordTrace tailWord_1242760 prefixEnd_1242760 638133218181662929484657 := by
  unfold tailWord_1242760
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663590488850120677650867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30218120651800160903534489 22663590488850120677650867)
  ·
    refine ⟨33995385733275181016476301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22663590488850120677650867 33995385733275181016476301)
    ·
      refine ⟨12748269649978192881178613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33995385733275181016476301 12748269649978192881178613)
      ·
        refine ⟨1195150279685455582610495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12748269649978192881178613 1195150279685455582610495)
        ·
          refine ⟨1792725419528183373915743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195150279685455582610495 1792725419528183373915743)
          ·
            refine ⟨2689088129292275060873615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792725419528183373915743 2689088129292275060873615)
            ·
              refine ⟨4033632193938412591310423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689088129292275060873615 4033632193938412591310423)
              ·
                refine ⟨6050448290907618886965635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033632193938412591310423 6050448290907618886965635)
                ·
                  refine ⟨9075672436361428330448453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050448290907618886965635 9075672436361428330448453)
                  ·
                    refine ⟨1701688581817767811959085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9075672436361428330448453 1701688581817767811959085)
                    ·
                      refine ⟨638133218181662929484657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1701688581817767811959085 638133218181662929484657)
                      ·
                        rfl

theorem cell23_1242760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1242760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242760 prefixEnd_1242760 := by exact prefixLift 1242760
  have htrace : WordTrace (prefixWord ++ tailWord_1242760) baseStart_1242760 baseEnd_1242760 := by
    simpa [prefixWord, tailWord_1242760, baseEnd_1242760] using wordTrace_append hprefix tailTrace_1242760
  have hstable : (prefixWord ++ tailWord_1242760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242760).length < 2 ^ (prefixWord ++ tailWord_1242760).sum := by decide
  have hdescent : baseEnd_1242760 < baseStart_1242760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242780 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 6]
def baseStart_1242780 : Nat := 118140960795 + 1242780 * 2 ^ 59
def prefixEnd_1242780 : Nat := 4983230072969 + 3 ^ 40 * 1242780 * 2
def baseEnd_1242780 : Nat := 70904831977194761248285

theorem tailTrace_1242780 : CollatzResearch.WordTrace tailWord_1242780 prefixEnd_1242780 70904831977194761248285 := by
  unfold tailWord_1242780
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663955218813892385514897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30218606958418523180686529 22663955218813892385514897)
  ·
    refine ⟨16997966414110419289136173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22663955218813892385514897 16997966414110419289136173)
    ·
      refine ⟨6374237405291407233426065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16997966414110419289136173 6374237405291407233426065)
      ·
        refine ⟨4780678053968555425069549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6374237405291407233426065 4780678053968555425069549)
        ·
          refine ⟨1792754270238208284401081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4780678053968555425069549 1792754270238208284401081)
          ·
            refine ⟨1344565702678656213300811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1792754270238208284401081 1344565702678656213300811)
            ·
              refine ⟨2016848554017984319951217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344565702678656213300811 2016848554017984319951217)
              ·
                refine ⟨1512636415513488239963413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016848554017984319951217 1512636415513488239963413)
                ·
                  refine ⟨70904831977194761248285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1512636415513488239963413 70904831977194761248285)
                  ·
                    rfl

theorem cell23_1242780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_1242780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242780 prefixEnd_1242780 := by exact prefixLift 1242780
  have htrace : WordTrace (prefixWord ++ tailWord_1242780) baseStart_1242780 baseEnd_1242780 := by
    simpa [prefixWord, tailWord_1242780, baseEnd_1242780] using wordTrace_append hprefix tailTrace_1242780
  have hstable : (prefixWord ++ tailWord_1242780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242780).length < 2 ^ (prefixWord ++ tailWord_1242780).sum := by decide
  have hdescent : baseEnd_1242780 < baseStart_1242780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242813 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_1242813 : Nat := 118140960795 + 1242813 * 2 ^ 59
def prefixEnd_1242813 : Nat := 4983230072969 + 3 ^ 40 * 1242813 * 2
def baseEnd_1242813 : Nat := 638160432656351222121913

theorem tailTrace_1242813 : CollatzResearch.WordTrace tailWord_1242813 prefixEnd_1242813 638160432656351222121913 := by
  unfold tailWord_1242813
  simp only [CollatzResearch.WordTrace]
  refine ⟨45329114046508231406981093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30219409364338820937987395 45329114046508231406981093)
  ·
    refine ⟨8499208883720293388808955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45329114046508231406981093 8499208883720293388808955)
    ·
      refine ⟨12748813325580440083213433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8499208883720293388808955 12748813325580440083213433)
      ·
        refine ⟨9561609994185330062410075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12748813325580440083213433 9561609994185330062410075)
        ·
          refine ⟨14342414991277995093615113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9561609994185330062410075 14342414991277995093615113)
          ·
            refine ⟨10756811243458496320211335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14342414991277995093615113 10756811243458496320211335)
            ·
              refine ⟨16135216865187744480317003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10756811243458496320211335 16135216865187744480317003)
              ·
                refine ⟨24202825297781616720475505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16135216865187744480317003 24202825297781616720475505)
                ·
                  refine ⟨18152118973336212540356629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24202825297781616720475505 18152118973336212540356629)
                  ·
                    refine ⟨850880576875134962829217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18152118973336212540356629 850880576875134962829217)
                    ·
                      refine ⟨638160432656351222121913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850880576875134962829217 638160432656351222121913)
                      ·
                        rfl

theorem cell23_1242813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_1242813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242813 prefixEnd_1242813 := by exact prefixLift 1242813
  have htrace : WordTrace (prefixWord ++ tailWord_1242813) baseStart_1242813 baseEnd_1242813 := by
    simpa [prefixWord, tailWord_1242813, baseEnd_1242813] using wordTrace_append hprefix tailTrace_1242813
  have hstable : (prefixWord ++ tailWord_1242813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242813).length < 2 ^ (prefixWord ++ tailWord_1242813).sum := by decide
  have hdescent : baseEnd_1242813 < baseStart_1242813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242816 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_1242816 : Nat := 118140960795 + 1242816 * 2 ^ 59
def prefixEnd_1242816 : Nat := 4983230072969 + 3 ^ 40 * 1242816 * 2
def baseEnd_1242816 : Nat := 638161973098314710384399

theorem tailTrace_1242816 : CollatzResearch.WordTrace tailWord_1242816 prefixEnd_1242816 638161973098314710384399 := by
  unfold tailWord_1242816
  simp only [CollatzResearch.WordTrace]
  refine ⟨22664611732748681459670151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30219482310331575279560201 22664611732748681459670151)
  ·
    refine ⟨33996917599123022189505227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22664611732748681459670151 33996917599123022189505227)
    ·
      refine ⟨50995376398684533284257841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33996917599123022189505227 50995376398684533284257841)
      ·
        refine ⟨38246532299013399963193381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50995376398684533284257841 38246532299013399963193381)
        ·
          refine ⟨7171224806065012493098759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38246532299013399963193381 7171224806065012493098759)
          ·
            refine ⟨10756837209097518739648139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171224806065012493098759 10756837209097518739648139)
            ·
              refine ⟨16135255813646278109472209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10756837209097518739648139 16135255813646278109472209)
              ·
                refine ⟨12101441860234708582104157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16135255813646278109472209 12101441860234708582104157)
                ·
                  refine ⟨4538040697588015718289059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12101441860234708582104157 4538040697588015718289059)
                  ·
                    refine ⟨6807061046382023577433589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4538040697588015718289059 6807061046382023577433589)
                    ·
                      refine ⟨638161973098314710384399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6807061046382023577433589 638161973098314710384399)
                      ·
                        rfl

theorem cell23_1242816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_1242816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242816 prefixEnd_1242816 := by exact prefixLift 1242816
  have htrace : WordTrace (prefixWord ++ tailWord_1242816) baseStart_1242816 baseEnd_1242816 := by
    simpa [prefixWord, tailWord_1242816, baseEnd_1242816] using wordTrace_append hprefix tailTrace_1242816
  have hstable : (prefixWord ++ tailWord_1242816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242816).length < 2 ^ (prefixWord ++ tailWord_1242816).sum := by decide
  have hdescent : baseEnd_1242816 < baseStart_1242816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242818 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1242818 : Nat := 118140960795 + 1242818 * 2 ^ 59
def prefixEnd_1242818 : Nat := 4983230072969 + 3 ^ 40 * 1242818 * 2
def baseEnd_1242818 : Nat := 212721000019874567519797

theorem tailTrace_1242818 : CollatzResearch.WordTrace tailWord_1242818 prefixEnd_1242818 212721000019874567519797 := by
  unfold tailWord_1242818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11332324102872529315228277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30219530940993411507275405 11332324102872529315228277)
  ·
    refine ⟨1062405384644299623302651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11332324102872529315228277 1062405384644299623302651)
    ·
      refine ⟨1593608076966449434953977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062405384644299623302651 1593608076966449434953977)
      ·
        refine ⟨1195206057724837076215483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1593608076966449434953977 1195206057724837076215483)
        ·
          refine ⟨1792809086587255614323225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195206057724837076215483 1792809086587255614323225)
          ·
            refine ⟨1344606814940441710742419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1792809086587255614323225 1344606814940441710742419)
            ·
              refine ⟨2016910222410662566113629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344606814940441710742419 2016910222410662566113629)
              ·
                refine ⟨756341333403998462292611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2016910222410662566113629 756341333403998462292611)
                ·
                  refine ⟨1134512000105997693438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756341333403998462292611 1134512000105997693438917)
                  ·
                    refine ⟨212721000019874567519797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134512000105997693438917 212721000019874567519797)
                    ·
                      rfl

theorem cell23_1242818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1242818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242818 prefixEnd_1242818 := by exact prefixLift 1242818
  have htrace : WordTrace (prefixWord ++ tailWord_1242818) baseStart_1242818 baseEnd_1242818 := by
    simpa [prefixWord, tailWord_1242818, baseEnd_1242818] using wordTrace_append hprefix tailTrace_1242818
  have hstable : (prefixWord ++ tailWord_1242818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242818).length < 2 ^ (prefixWord ++ tailWord_1242818).sum := by decide
  have hdescent : baseEnd_1242818 < baseStart_1242818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242833 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_1242833 : Nat := 118140960795 + 1242833 * 2 ^ 59
def prefixEnd_1242833 : Nat := 4983230072969 + 3 ^ 40 * 1242833 * 2
def baseEnd_1242833 : Nat := 638170702269441143871821

theorem tailTrace_1242833 : CollatzResearch.WordTrace tailWord_1242833 prefixEnd_1242833 638170702269441143871821 := by
  unfold tailWord_1242833
  simp only [CollatzResearch.WordTrace]
  refine ⟨45329843506435774822709153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30219895670957183215139435 45329843506435774822709153)
  ·
    refine ⟨33997382629826831117031865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45329843506435774822709153 33997382629826831117031865)
    ·
      refine ⟨25498036972370123337773899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33997382629826831117031865 25498036972370123337773899)
      ·
        refine ⟨38247055458555185006660849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25498036972370123337773899 38247055458555185006660849)
        ·
          refine ⟨28685291593916388754995637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38247055458555185006660849 28685291593916388754995637)
          ·
            refine ⟨2689246086929661445780841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28685291593916388754995637 2689246086929661445780841)
            ·
              refine ⟨2016934565197246084335631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689246086929661445780841 2016934565197246084335631)
              ·
                refine ⟨3025401847795869126503447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016934565197246084335631 3025401847795869126503447)
                ·
                  refine ⟨4538102771693803689755171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025401847795869126503447 4538102771693803689755171)
                  ·
                    refine ⟨6807154157540705534632757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4538102771693803689755171 6807154157540705534632757)
                    ·
                      refine ⟨638170702269441143871821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6807154157540705534632757 638170702269441143871821)
                      ·
                        rfl

theorem cell23_1242833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_1242833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242833 prefixEnd_1242833 := by exact prefixLift 1242833
  have htrace : WordTrace (prefixWord ++ tailWord_1242833) baseStart_1242833 baseEnd_1242833 := by
    simpa [prefixWord, tailWord_1242833, baseEnd_1242833] using wordTrace_append hprefix tailTrace_1242833
  have hstable : (prefixWord ++ tailWord_1242833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242833).length < 2 ^ (prefixWord ++ tailWord_1242833).sum := by decide
  have hdescent : baseEnd_1242833 < baseStart_1242833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242863 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_1242863 : Nat := 118140960795 + 1242863 * 2 ^ 59
def prefixEnd_1242863 : Nat := 4983230072969 + 3 ^ 40 * 1242863 * 2
def baseEnd_1242863 : Nat := 638186106689076026496683

theorem tailTrace_1242863 : CollatzResearch.WordTrace tailWord_1242863 prefixEnd_1242863 638186106689076026496683 := by
  unfold tailWord_1242863
  simp only [CollatzResearch.WordTrace]
  refine ⟨45330937696327089946301243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30220625130884726630867495 45330937696327089946301243)
  ·
    refine ⟨67996406544490634919451865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45330937696327089946301243 67996406544490634919451865)
    ·
      refine ⟨50997304908367976189588899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67996406544490634919451865 50997304908367976189588899)
      ·
        refine ⟨76495957362551964284383349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50997304908367976189588899 76495957362551964284383349)
        ·
          refine ⟨7171496002739246651660939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76495957362551964284383349 7171496002739246651660939)
          ·
            refine ⟨10757244004108869977491409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171496002739246651660939 10757244004108869977491409)
            ·
              refine ⟨8067933003081652483118557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10757244004108869977491409 8067933003081652483118557)
              ·
                refine ⟨3025474876155619681169459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8067933003081652483118557 3025474876155619681169459)
                ·
                  refine ⟨4538212314233429521754189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025474876155619681169459 4538212314233429521754189)
                  ·
                    refine ⟨1701829617837536070657821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4538212314233429521754189 1701829617837536070657821)
                    ·
                      refine ⟨638186106689076026496683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1701829617837536070657821 638186106689076026496683)
                      ·
                        rfl

theorem cell23_1242863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_1242863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242863 prefixEnd_1242863 := by exact prefixLift 1242863
  have htrace : WordTrace (prefixWord ++ tailWord_1242863) baseStart_1242863 baseEnd_1242863 := by
    simpa [prefixWord, tailWord_1242863, baseEnd_1242863] using wordTrace_append hprefix tailTrace_1242863
  have hstable : (prefixWord ++ tailWord_1242863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242863).length < 2 ^ (prefixWord ++ tailWord_1242863).sum := by decide
  have hdescent : baseEnd_1242863 < baseStart_1242863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242898 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1242898 : Nat := 118140960795 + 1242898 * 2 ^ 59
def prefixEnd_1242898 : Nat := 4983230072969 + 3 ^ 40 * 1242898 * 2
def baseEnd_1242898 : Nat := 638204078511983389559023

theorem tailTrace_1242898 : CollatzResearch.WordTrace tailWord_1242898 prefixEnd_1242898 638204078511983389559023 := by
  unfold tailWord_1242898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11333053562800072730956337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30221476167466860615883565 11333053562800072730956337)
  ·
    refine ⟨8499790172100054548217253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11333053562800072730956337 8499790172100054548217253)
    ·
      refine ⟨1593710657268760227790735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8499790172100054548217253 1593710657268760227790735)
      ·
        refine ⟨2390565985903140341686103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593710657268760227790735 2390565985903140341686103)
        ·
          refine ⟨3585848978854710512529155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390565985903140341686103 3585848978854710512529155)
          ·
            refine ⟨5378773468282065768793733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585848978854710512529155 5378773468282065768793733)
            ·
              refine ⟨1008520025302887331648825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5378773468282065768793733 1008520025302887331648825)
              ·
                refine ⟨756390018977165498736619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008520025302887331648825 756390018977165498736619)
                ·
                  refine ⟨1134585028465748248104929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756390018977165498736619 1134585028465748248104929)
                  ·
                    refine ⟨850938771349311186078697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1134585028465748248104929 850938771349311186078697)
                    ·
                      refine ⟨638204078511983389559023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850938771349311186078697 638204078511983389559023)
                      ·
                        rfl

theorem cell23_1242898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1242898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242898 prefixEnd_1242898 := by exact prefixLift 1242898
  have htrace : WordTrace (prefixWord ++ tailWord_1242898) baseStart_1242898 baseEnd_1242898 := by
    simpa [prefixWord, tailWord_1242898, baseEnd_1242898] using wordTrace_append hprefix tailTrace_1242898
  have hstable : (prefixWord ++ tailWord_1242898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242898).length < 2 ^ (prefixWord ++ tailWord_1242898).sum := by decide
  have hdescent : baseEnd_1242898 < baseStart_1242898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242903 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1242903 : Nat := 118140960795 + 1242903 * 2 ^ 59
def prefixEnd_1242903 : Nat := 4983230072969 + 3 ^ 40 * 1242903 * 2
def baseEnd_1242903 : Nat := 638206645915255869996499

theorem tailTrace_1242903 : CollatzResearch.WordTrace tailWord_1242903 prefixEnd_1242903 638206645915255869996499 := by
  unfold tailWord_1242903
  simp only [CollatzResearch.WordTrace]
  refine ⟨45332396616182176777757363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30221597744121451185171575 45332396616182176777757363)
  ·
    refine ⟨67998594924273265166636045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45332396616182176777757363 67998594924273265166636045)
    ·
      refine ⟨25499473096602474437488517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67998594924273265166636045 25499473096602474437488517)
      ·
        refine ⟨4781151205612963957029097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25499473096602474437488517 4781151205612963957029097)
        ·
          refine ⟨3585863404209722967771823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4781151205612963957029097 3585863404209722967771823)
          ·
            refine ⟨5378795106314584451657735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585863404209722967771823 5378795106314584451657735)
            ·
              refine ⟨8068192659471876677486603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378795106314584451657735 8068192659471876677486603)
              ·
                refine ⟨12102288989207815016229905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8068192659471876677486603 12102288989207815016229905)
                ·
                  refine ⟨9076716741905861262172429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12102288989207815016229905 9076716741905861262172429)
                  ·
                    refine ⟨3403768778214697973314661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9076716741905861262172429 3403768778214697973314661)
                    ·
                      refine ⟨638206645915255869996499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3403768778214697973314661 638206645915255869996499)
                      ·
                        rfl

theorem cell23_1242903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1242903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242903 prefixEnd_1242903 := by exact prefixLift 1242903
  have htrace : WordTrace (prefixWord ++ tailWord_1242903) baseStart_1242903 baseEnd_1242903 := by
    simpa [prefixWord, tailWord_1242903, baseEnd_1242903] using wordTrace_append hprefix tailTrace_1242903
  have hstable : (prefixWord ++ tailWord_1242903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242903).length < 2 ^ (prefixWord ++ tailWord_1242903).sum := by decide
  have hdescent : baseEnd_1242903 < baseStart_1242903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242913 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1242913 : Nat := 118140960795 + 1242913 * 2 ^ 59
def prefixEnd_1242913 : Nat := 4983230072969 + 3 ^ 40 * 1242913 * 2
def baseEnd_1242913 : Nat := 212737260240600276957151

theorem tailTrace_1242913 : CollatzResearch.WordTrace tailWord_1242913 prefixEnd_1242913 212737260240600276957151 := by
  unfold tailWord_1242913
  simp only [CollatzResearch.WordTrace]
  refine ⟨45332761346145948485621393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30221840897430632323747595 45332761346145948485621393)
  ·
    refine ⟨33999571009609461364216045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45332761346145948485621393 33999571009609461364216045)
    ·
      refine ⟨12749839128603548011581017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33999571009609461364216045 12749839128603548011581017)
      ·
        refine ⟨9562379346452661008685763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12749839128603548011581017 9562379346452661008685763)
        ·
          refine ⟨14343569019678991513028645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9562379346452661008685763 14343569019678991513028645)
          ·
            refine ⟨2689419191189810908692871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14343569019678991513028645 2689419191189810908692871)
            ·
              refine ⟨4034128786784716363039307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689419191189810908692871 4034128786784716363039307)
              ·
                refine ⟨6051193180177074544558961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034128786784716363039307 6051193180177074544558961)
                ·
                  refine ⟨4538394885132805908419221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6051193180177074544558961 4538394885132805908419221)
                  ·
                    refine ⟨212737260240600276957151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4538394885132805908419221 212737260240600276957151)
                    ·
                      rfl

theorem cell23_1242913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1242913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242913 prefixEnd_1242913 := by exact prefixLift 1242913
  have htrace : WordTrace (prefixWord ++ tailWord_1242913) baseStart_1242913 baseEnd_1242913 := by
    simpa [prefixWord, tailWord_1242913, baseEnd_1242913] using wordTrace_append hprefix tailTrace_1242913
  have hstable : (prefixWord ++ tailWord_1242913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242913).length < 2 ^ (prefixWord ++ tailWord_1242913).sum := by decide
  have hdescent : baseEnd_1242913 < baseStart_1242913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242941 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1242941 : Nat := 118140960795 + 1242941 * 2 ^ 59
def prefixEnd_1242941 : Nat := 4983230072969 + 3 ^ 40 * 1242941 * 2
def baseEnd_1242941 : Nat := 638226158180126721321325

theorem tailTrace_1242941 : CollatzResearch.WordTrace tailWord_1242941 prefixEnd_1242941 638226158180126721321325 := by
  unfold tailWord_1242941
  simp only [CollatzResearch.WordTrace]
  refine ⟨45333782590044509267640677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30222521726696339511760451 45333782590044509267640677)
  ·
    refine ⟨8500084235633345487682627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45333782590044509267640677 8500084235633345487682627)
    ·
      refine ⟨12750126353450018231523941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8500084235633345487682627 12750126353450018231523941)
      ·
        refine ⟨2390648691271878418410739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12750126353450018231523941 2390648691271878418410739)
        ·
          refine ⟨3585973036907817627616109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390648691271878418410739 3585973036907817627616109)
          ·
            refine ⟨1344739888840431610356041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3585973036907817627616109 1344739888840431610356041)
            ·
              refine ⟨1008554916630323707767031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344739888840431610356041 1008554916630323707767031)
              ·
                refine ⟨1512832374945485561650547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008554916630323707767031 1512832374945485561650547)
                ·
                  refine ⟨2269248562418228342475821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512832374945485561650547 2269248562418228342475821)
                  ·
                    refine ⟨850968210906835628428433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269248562418228342475821 850968210906835628428433)
                    ·
                      refine ⟨638226158180126721321325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 850968210906835628428433 638226158180126721321325)
                      ·
                        rfl

theorem cell23_1242941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1242941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242941 prefixEnd_1242941 := by exact prefixLift 1242941
  have htrace : WordTrace (prefixWord ++ tailWord_1242941) baseStart_1242941 baseEnd_1242941 := by
    simpa [prefixWord, tailWord_1242941, baseEnd_1242941] using wordTrace_append hprefix tailTrace_1242941
  have hstable : (prefixWord ++ tailWord_1242941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242941).length < 2 ^ (prefixWord ++ tailWord_1242941).sum := by decide
  have hdescent : baseEnd_1242941 < baseStart_1242941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242953 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_1242953 : Nat := 118140960795 + 1242953 * 2 ^ 59
def prefixEnd_1242953 : Nat := 4983230072969 + 3 ^ 40 * 1242953 * 2
def baseEnd_1242953 : Nat := 638232319947980674371269

theorem tailTrace_1242953 : CollatzResearch.WordTrace tailWord_1242953 prefixEnd_1242953 638232319947980674371269 := by
  unfold tailWord_1242953
  simp only [CollatzResearch.WordTrace]
  refine ⟨45334220266001035317077513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30222813510667356878051675 45334220266001035317077513)
  ·
    refine ⟨34000665199500776487808135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45334220266001035317077513 34000665199500776487808135)
    ·
      refine ⟨51000997799251164731712203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34000665199500776487808135 51000997799251164731712203)
      ·
        refine ⟨76501496698876747097568305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51000997799251164731712203 76501496698876747097568305)
        ·
          refine ⟨57376122524157560323176229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76501496698876747097568305 57376122524157560323176229)
          ·
            refine ⟨10758022973279542560595543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57376122524157560323176229 10758022973279542560595543)
            ·
              refine ⟨16137034459919313840893315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10758022973279542560595543 16137034459919313840893315)
              ·
                refine ⟨24205551689878970761339973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16137034459919313840893315 24205551689878970761339973)
                ·
                  refine ⟨4538540941852307017751245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24205551689878970761339973 4538540941852307017751245)
                  ·
                    refine ⟨1701952853194615131656717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4538540941852307017751245 1701952853194615131656717)
                    ·
                      refine ⟨638232319947980674371269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1701952853194615131656717 638232319947980674371269)
                      ·
                        rfl

theorem cell23_1242953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_1242953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242953 prefixEnd_1242953 := by exact prefixLift 1242953
  have htrace : WordTrace (prefixWord ++ tailWord_1242953) baseStart_1242953 baseEnd_1242953 := by
    simpa [prefixWord, tailWord_1242953, baseEnd_1242953] using wordTrace_append hprefix tailTrace_1242953
  have hstable : (prefixWord ++ tailWord_1242953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242953).length < 2 ^ (prefixWord ++ tailWord_1242953).sum := by decide
  have hdescent : baseEnd_1242953 < baseStart_1242953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242990 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1242990 : Nat := 118140960795 + 1242990 * 2 ^ 59
def prefixEnd_1242990 : Nat := 4983230072969 + 3 ^ 40 * 1242990 * 2
def baseEnd_1242990 : Nat := 212750439577399009869533

theorem tailTrace_1242990 : CollatzResearch.WordTrace tailWord_1242990 prefixEnd_1242990 212750439577399009869533 := by
  unfold tailWord_1242990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666946220858373829521803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30223713177911327090782949 5666946220858373829521803)
  ·
    refine ⟨8500419331287560744282705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5666946220858373829521803 8500419331287560744282705)
    ·
      refine ⟨6375314498465670558212029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8500419331287560744282705 6375314498465670558212029)
      ·
        refine ⟨2390742936924626459329511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6375314498465670558212029 2390742936924626459329511)
        ·
          refine ⟨3586114405386939688994267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390742936924626459329511 3586114405386939688994267)
          ·
            refine ⟨5379171608080409533491401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586114405386939688994267 5379171608080409533491401)
            ·
              refine ⟨4034378706060307150118551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5379171608080409533491401 4034378706060307150118551)
              ·
                refine ⟨6051568059090460725177827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034378706060307150118551 6051568059090460725177827)
                ·
                  refine ⟨9077352088635691087766741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051568059090460725177827 9077352088635691087766741)
                  ·
                    refine ⟨212750439577399009869533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9077352088635691087766741 212750439577399009869533)
                    ·
                      rfl

theorem cell23_1242990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1242990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242990 prefixEnd_1242990 := by exact prefixLift 1242990
  have htrace : WordTrace (prefixWord ++ tailWord_1242990) baseStart_1242990 baseEnd_1242990 := by
    simpa [prefixWord, tailWord_1242990, baseEnd_1242990] using wordTrace_append hprefix tailTrace_1242990
  have hstable : (prefixWord ++ tailWord_1242990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242990).length < 2 ^ (prefixWord ++ tailWord_1242990).sum := by decide
  have hdescent : baseEnd_1242990 < baseStart_1242990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242993 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_1242993 : Nat := 118140960795 + 1242993 * 2 ^ 59
def prefixEnd_1242993 : Nat := 4983230072969 + 3 ^ 40 * 1242993 * 2
def baseEnd_1242993 : Nat := 638252859174160517871085

theorem tailTrace_1242993 : CollatzResearch.WordTrace tailWord_1242993 prefixEnd_1242993 638252859174160517871085 := by
  unfold tailWord_1242993
  simp only [CollatzResearch.WordTrace]
  refine ⟨45335679185856122148533633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30223786123904081432355755 45335679185856122148533633)
  ·
    refine ⟨34001759389392091611400225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45335679185856122148533633 34001759389392091611400225)
    ·
      refine ⟨25501319542044068708550169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34001759389392091611400225 25501319542044068708550169)
      ·
        refine ⟨19125989656533051531412627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25501319542044068708550169 19125989656533051531412627)
        ·
          refine ⟨28688984484799577297118941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19125989656533051531412627 28688984484799577297118941)
          ·
            refine ⟨10758369181799841486419603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28688984484799577297118941 10758369181799841486419603)
            ·
              refine ⟨16137553772699762229629405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10758369181799841486419603 16137553772699762229629405)
              ·
                refine ⟨6051582664762410836111027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16137553772699762229629405 6051582664762410836111027)
                ·
                  refine ⟨9077373997143616254166541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051582664762410836111027 9077373997143616254166541)
                  ·
                    refine ⟨3404015248928856095312453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9077373997143616254166541 3404015248928856095312453)
                    ·
                      refine ⟨638252859174160517871085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3404015248928856095312453 638252859174160517871085)
                      ·
                        rfl

theorem cell23_1242993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_1242993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1242993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1242993 prefixEnd_1242993 := by exact prefixLift 1242993
  have htrace : WordTrace (prefixWord ++ tailWord_1242993) baseStart_1242993 baseEnd_1242993 := by
    simpa [prefixWord, tailWord_1242993, baseEnd_1242993] using wordTrace_append hprefix tailTrace_1242993
  have hstable : (prefixWord ++ tailWord_1242993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242993).length < 2 ^ (prefixWord ++ tailWord_1242993).sum := by decide
  have hdescent : baseEnd_1242993 < baseStart_1242993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243047 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1243047 : Nat := 118140960795 + 1243047 * 2 ^ 59
def prefixEnd_1243047 : Nat := 4983230072969 + 3 ^ 40 * 1243047 * 2
def baseEnd_1243047 : Nat := 638280587129503306595837

theorem tailTrace_1243047 : CollatzResearch.WordTrace tailWord_1243047 prefixEnd_1243047 638280587129503306595837 := by
  unfold tailWord_1243047
  simp only [CollatzResearch.WordTrace]
  refine ⟨45337648727660489370999395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30225099151773659580666263 45337648727660489370999395)
  ·
    refine ⟨68006473091490734056499093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45337648727660489370999395 68006473091490734056499093)
    ·
      refine ⟨3187803426163628158898395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68006473091490734056499093 3187803426163628158898395)
      ·
        refine ⟨4781705139245442238347593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187803426163628158898395 4781705139245442238347593)
        ·
          refine ⟨3586278854434081678760695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4781705139245442238347593 3586278854434081678760695)
          ·
            refine ⟨5379418281651122518141043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586278854434081678760695 5379418281651122518141043)
            ·
              refine ⟨8069127422476683777211565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379418281651122518141043 8069127422476683777211565)
              ·
                refine ⟨3025922783428756416454337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8069127422476683777211565 3025922783428756416454337)
                ·
                  refine ⟨2269442087571567312340753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025922783428756416454337 2269442087571567312340753)
                  ·
                    refine ⟨1702081565678675484255565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2269442087571567312340753 1702081565678675484255565)
                    ·
                      refine ⟨638280587129503306595837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702081565678675484255565 638280587129503306595837)
                      ·
                        rfl

theorem cell23_1243047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1243047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243047 prefixEnd_1243047 := by exact prefixLift 1243047
  have htrace : WordTrace (prefixWord ++ tailWord_1243047) baseStart_1243047 baseEnd_1243047 := by
    simpa [prefixWord, tailWord_1243047, baseEnd_1243047] using wordTrace_append hprefix tailTrace_1243047
  have hstable : (prefixWord ++ tailWord_1243047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243047).length < 2 ^ (prefixWord ++ tailWord_1243047).sum := by decide
  have hdescent : baseEnd_1243047 < baseStart_1243047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243080 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1243080 : Nat := 118140960795 + 1243080 * 2 ^ 59
def prefixEnd_1243080 : Nat := 4983230072969 + 3 ^ 40 * 1243080 * 2
def baseEnd_1243080 : Nat := 212765843997033892494395

theorem tailTrace_1243080 : CollatzResearch.WordTrace tailWord_1243080 prefixEnd_1243080 212765843997033892494395 := by
  unfold tailWord_1243080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22669426168270468003475347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30225901557693957337967129 22669426168270468003475347)
  ·
    refine ⟨34004139252405702005213021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22669426168270468003475347 34004139252405702005213021)
    ·
      refine ⟨12751552219652138251954883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34004139252405702005213021 12751552219652138251954883)
      ·
        refine ⟨19127328329478207377932325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12751552219652138251954883 19127328329478207377932325)
        ·
          refine ⟨3586374061777163883362311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19127328329478207377932325 3586374061777163883362311)
          ·
            refine ⟨5379561092665745825043467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586374061777163883362311 5379561092665745825043467)
            ·
              refine ⟨8069341638998618737565201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379561092665745825043467 8069341638998618737565201)
              ·
                refine ⟨6052006229248964053173901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8069341638998618737565201 6052006229248964053173901)
                ·
                  refine ⟨2269502335968361519940213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6052006229248964053173901 2269502335968361519940213)
                  ·
                    refine ⟨212765843997033892494395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2269502335968361519940213 212765843997033892494395)
                    ·
                      rfl

theorem cell23_1243080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1243080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243080 prefixEnd_1243080 := by exact prefixLift 1243080
  have htrace : WordTrace (prefixWord ++ tailWord_1243080) baseStart_1243080 baseEnd_1243080 := by
    simpa [prefixWord, tailWord_1243080, baseEnd_1243080] using wordTrace_append hprefix tailTrace_1243080
  have hstable : (prefixWord ++ tailWord_1243080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243080).length < 2 ^ (prefixWord ++ tailWord_1243080).sum := by decide
  have hdescent : baseEnd_1243080 < baseStart_1243080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243144 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1243144 : Nat := 118140960795 + 1243144 * 2 ^ 59
def prefixEnd_1243144 : Nat := 4983230072969 + 3 ^ 40 * 1243144 * 2
def baseEnd_1243144 : Nat := 212776798250996475694297

theorem tailTrace_1243144 : CollatzResearch.WordTrace tailWord_1243144 prefixEnd_1243144 212776798250996475694297 := by
  unfold tailWord_1243144
  simp only [CollatzResearch.WordTrace]
  refine ⟨22670593304154537468640243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30227457738872716624853657 22670593304154537468640243)
  ·
    refine ⟨34005889956231806202960365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22670593304154537468640243 34005889956231806202960365)
    ·
      refine ⟨12752208733586927326110137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34005889956231806202960365 12752208733586927326110137)
      ·
        refine ⟨9564156550190195494582603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12752208733586927326110137 9564156550190195494582603)
        ·
          refine ⟨14346234825285293241873905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9564156550190195494582603 14346234825285293241873905)
          ·
            refine ⟨10759676118963969931405429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14346234825285293241873905 10759676118963969931405429)
            ·
              refine ⟨1008719636152872181069259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10759676118963969931405429 1008719636152872181069259)
              ·
                refine ⟨1513079454229308271603889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008719636152872181069259 1513079454229308271603889)
                ·
                  refine ⟨1134809590671981203702917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513079454229308271603889 1134809590671981203702917)
                  ·
                    refine ⟨212776798250996475694297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134809590671981203702917 212776798250996475694297)
                    ·
                      rfl

theorem cell23_1243144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1243144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243144 prefixEnd_1243144 := by exact prefixLift 1243144
  have htrace : WordTrace (prefixWord ++ tailWord_1243144) baseStart_1243144 baseEnd_1243144 := by
    simpa [prefixWord, tailWord_1243144, baseEnd_1243144] using wordTrace_append hprefix tailTrace_1243144
  have hstable : (prefixWord ++ tailWord_1243144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243144).length < 2 ^ (prefixWord ++ tailWord_1243144).sum := by decide
  have hdescent : baseEnd_1243144 < baseStart_1243144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243167 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 3]
def baseStart_1243167 : Nat := 118140960795 + 1243167 * 2 ^ 59
def prefixEnd_1243167 : Nat := 4983230072969 + 3 ^ 40 * 1243167 * 2
def baseEnd_1243167 : Nat := 638342204808042837095285

theorem tailTrace_1243167 : CollatzResearch.WordTrace tailWord_1243167 prefixEnd_1243167 638342204808042837095285 := by
  unfold tailWord_1243167
  simp only [CollatzResearch.WordTrace]
  refine ⟨45342025487225749865367755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30228016991483833243578503 45342025487225749865367755)
  ·
    refine ⟨68013038230838624798051633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45342025487225749865367755 68013038230838624798051633)
    ·
      refine ⟨51009778673128968598538725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68013038230838624798051633 51009778673128968598538725)
      ·
        refine ⟨9564333501211681612226011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51009778673128968598538725 9564333501211681612226011)
        ·
          refine ⟨14346500251817522418339017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9564333501211681612226011 14346500251817522418339017)
          ·
            refine ⟨10759875188863141813754263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14346500251817522418339017 10759875188863141813754263)
            ·
              refine ⟨16139812783294712720631395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10759875188863141813754263 16139812783294712720631395)
              ·
                refine ⟨24209719174942069080947093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16139812783294712720631395 24209719174942069080947093)
                ·
                  refine ⟨1134830586325409488169395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24209719174942069080947093 1134830586325409488169395)
                  ·
                    refine ⟨1702245879488114232254093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1134830586325409488169395 1702245879488114232254093)
                    ·
                      refine ⟨638342204808042837095285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702245879488114232254093 638342204808042837095285)
                      ·
                        rfl

theorem cell23_1243167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_1243167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243167 prefixEnd_1243167 := by exact prefixLift 1243167
  have htrace : WordTrace (prefixWord ++ tailWord_1243167) baseStart_1243167 baseEnd_1243167 := by
    simpa [prefixWord, tailWord_1243167, baseEnd_1243167] using wordTrace_append hprefix tailTrace_1243167
  have hstable : (prefixWord ++ tailWord_1243167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243167).length < 2 ^ (prefixWord ++ tailWord_1243167).sum := by decide
  have hdescent : baseEnd_1243167 < baseStart_1243167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243201 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1243201 : Nat := 118140960795 + 1243201 * 2 ^ 59
def prefixEnd_1243201 : Nat := 4983230072969 + 3 ^ 40 * 1243201 * 2
def baseEnd_1243201 : Nat := 638359663150295704070129

theorem tailTrace_1243201 : CollatzResearch.WordTrace tailWord_1243201 prefixEnd_1243201 638359663150295704070129 := by
  unfold tailWord_1243201
  simp only [CollatzResearch.WordTrace]
  refine ⟨45343265569102573672105457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30228843712735049114736971 45343265569102573672105457)
  ·
    refine ⟨34007449176826930254079093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45343265569102573672105457 34007449176826930254079093)
    ·
      refine ⟨3188198360327524711319915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34007449176826930254079093 3188198360327524711319915)
      ·
        refine ⟨4782297540491287066979873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188198360327524711319915 4782297540491287066979873)
        ·
          refine ⟨3586723155368465300234905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4782297540491287066979873 3586723155368465300234905)
          ·
            refine ⟨2690042366526348975176179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586723155368465300234905 2690042366526348975176179)
            ·
              refine ⟨4035063549789523462764269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690042366526348975176179 4035063549789523462764269)
              ·
                refine ⟨1513148831171071298536601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4035063549789523462764269 1513148831171071298536601)
                ·
                  refine ⟨1134861623378303473902451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513148831171071298536601 1134861623378303473902451)
                  ·
                    refine ⟨1702292435067455210853677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1134861623378303473902451 1702292435067455210853677)
                    ·
                      refine ⟨638359663150295704070129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702292435067455210853677 638359663150295704070129)
                      ·
                        rfl

theorem cell23_1243201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1243201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243201 prefixEnd_1243201 := by exact prefixLift 1243201
  have htrace : WordTrace (prefixWord ++ tailWord_1243201) baseStart_1243201 baseEnd_1243201 := by
    simpa [prefixWord, tailWord_1243201, baseEnd_1243201] using wordTrace_append hprefix tailTrace_1243201
  have hstable : (prefixWord ++ tailWord_1243201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243201).length < 2 ^ (prefixWord ++ tailWord_1243201).sum := by decide
  have hdescent : baseEnd_1243201 < baseStart_1243201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243224 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 1, 4, 2]
def baseStart_1243224 : Nat := 118140960795 + 1243224 * 2 ^ 59
def prefixEnd_1243224 : Nat := 4983230072969 + 3 ^ 40 * 1243224 * 2
def baseEnd_1243224 : Nat := 638371473205349114082523

theorem tailTrace_1243224 : CollatzResearch.WordTrace tailWord_1243224 prefixEnd_1243224 638371473205349114082523 := by
  unfold tailWord_1243224
  simp only [CollatzResearch.WordTrace]
  refine ⟨22672052224009624300096363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30229402965346165733461817 22672052224009624300096363)
  ·
    refine ⟨34008078336014436450144545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22672052224009624300096363 34008078336014436450144545)
    ·
      refine ⟨25506058752010827337608409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34008078336014436450144545 25506058752010827337608409)
      ·
        refine ⟨19129544064008120503206307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25506058752010827337608409 19129544064008120503206307)
        ·
          refine ⟨28694316096012180754809461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19129544064008120503206307 28694316096012180754809461)
          ·
            refine ⟨2690092134001141945763387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28694316096012180754809461 2690092134001141945763387)
            ·
              refine ⟨4035138201001712918645081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690092134001141945763387 4035138201001712918645081)
              ·
                refine ⟨3026353650751284688983811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035138201001712918645081 3026353650751284688983811)
                ·
                  refine ⟨4539530476126927033475717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026353650751284688983811 4539530476126927033475717)
                  ·
                    refine ⟨851161964273798818776697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539530476126927033475717 851161964273798818776697)
                    ·
                      refine ⟨638371473205349114082523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851161964273798818776697 638371473205349114082523)
                      ·
                        rfl

theorem cell23_1243224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_1243224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243224 prefixEnd_1243224 := by exact prefixLift 1243224
  have htrace : WordTrace (prefixWord ++ tailWord_1243224) baseStart_1243224 baseEnd_1243224 := by
    simpa [prefixWord, tailWord_1243224, baseEnd_1243224] using wordTrace_append hprefix tailTrace_1243224
  have hstable : (prefixWord ++ tailWord_1243224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243224).length < 2 ^ (prefixWord ++ tailWord_1243224).sum := by decide
  have hdescent : baseEnd_1243224 < baseStart_1243224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243228 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_1243228 : Nat := 118140960795 + 1243228 * 2 ^ 59
def prefixEnd_1243228 : Nat := 4983230072969 + 3 ^ 40 * 1243228 * 2
def baseEnd_1243228 : Nat := 638373527127967098432505

theorem tailTrace_1243228 : CollatzResearch.WordTrace tailWord_1243228 prefixEnd_1243228 638373527127967098432505 := by
  unfold tailWord_1243228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22672125170002378641669169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30229500226669838188892225 22672125170002378641669169)
  ·
    refine ⟨17004093877501783981251877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22672125170002378641669169 17004093877501783981251877)
    ·
      refine ⟨3188267602031584496484727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17004093877501783981251877 3188267602031584496484727)
      ·
        refine ⟨4782401403047376744727091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188267602031584496484727 4782401403047376744727091)
        ·
          refine ⟨7173602104571065117090637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782401403047376744727091 7173602104571065117090637)
          ·
            refine ⟨2690100789214149418908989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7173602104571065117090637 2690100789214149418908989)
            ·
              refine ⟨1008787795955306032090871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2690100789214149418908989 1008787795955306032090871)
              ·
                refine ⟨1513181693932959048136307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008787795955306032090871 1513181693932959048136307)
                ·
                  refine ⟨2269772540899438572204461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513181693932959048136307 2269772540899438572204461)
                  ·
                    refine ⟨851164702837289464576673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269772540899438572204461 851164702837289464576673)
                    ·
                      refine ⟨638373527127967098432505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851164702837289464576673 638373527127967098432505)
                      ·
                        rfl

theorem cell23_1243228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_1243228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243228 prefixEnd_1243228 := by exact prefixLift 1243228
  have htrace : WordTrace (prefixWord ++ tailWord_1243228) baseStart_1243228 baseEnd_1243228 := by
    simpa [prefixWord, tailWord_1243228, baseEnd_1243228] using wordTrace_append hprefix tailTrace_1243228
  have hstable : (prefixWord ++ tailWord_1243228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243228).length < 2 ^ (prefixWord ++ tailWord_1243228).sum := by decide
  have hdescent : baseEnd_1243228 < baseStart_1243228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243241 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 2, 2, 2]
def baseStart_1243241 : Nat := 118140960795 + 1243241 * 2 ^ 59
def prefixEnd_1243241 : Nat := 4983230072969 + 3 ^ 40 * 1243241 * 2
def baseEnd_1243241 : Nat := 638380202376475547569945

theorem tailTrace_1243241 : CollatzResearch.WordTrace tailWord_1243241 prefixEnd_1243241 638380202376475547569945 := by
  unfold tailWord_1243241
  simp only [CollatzResearch.WordTrace]
  refine ⟨45344724488957660503561577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30229816325971773669041051 45344724488957660503561577)
  ·
    refine ⟨34008543366718245377671183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45344724488957660503561577 34008543366718245377671183)
    ·
      refine ⟨51012815050077368066506775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34008543366718245377671183 51012815050077368066506775)
      ·
        refine ⟨76519222575116052099760163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51012815050077368066506775 76519222575116052099760163)
        ·
          refine ⟨114778833862674078149640245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76519222575116052099760163 114778833862674078149640245)
          ·
            refine ⟨10760515674625694826528773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114778833862674078149640245 10760515674625694826528773)
            ·
              refine ⟨2017596688992317779974145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10760515674625694826528773 2017596688992317779974145)
              ·
                refine ⟨1513197516744238334980609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017596688992317779974145 1513197516744238334980609)
                ·
                  refine ⟨1134898137558178751235457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513197516744238334980609 1134898137558178751235457)
                  ·
                    refine ⟨851173603168634063426593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1134898137558178751235457 851173603168634063426593)
                    ·
                      refine ⟨638380202376475547569945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851173603168634063426593 638380202376475547569945)
                      ·
                        rfl

theorem cell23_1243241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 2, 2].length) (baseStart_1243241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243241 prefixEnd_1243241 := by exact prefixLift 1243241
  have htrace : WordTrace (prefixWord ++ tailWord_1243241) baseStart_1243241 baseEnd_1243241 := by
    simpa [prefixWord, tailWord_1243241, baseEnd_1243241] using wordTrace_append hprefix tailTrace_1243241
  have hstable : (prefixWord ++ tailWord_1243241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243241).length < 2 ^ (prefixWord ++ tailWord_1243241).sum := by decide
  have hdescent : baseEnd_1243241 < baseStart_1243241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243254 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1243254 : Nat := 118140960795 + 1243254 * 2 ^ 59
def prefixEnd_1243254 : Nat := 4983230072969 + 3 ^ 40 * 1243254 * 2
def baseEnd_1243254 : Nat := 638386877624983996707385

theorem tailTrace_1243254 : CollatzResearch.WordTrace tailWord_1243254 prefixEnd_1243254 638386877624983996707385 := by
  unfold tailWord_1243254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834074914869410232736551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30230132425273709149189877 2834074914869410232736551)
  ·
    refine ⟨4251112372304115349104827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2834074914869410232736551 4251112372304115349104827)
    ·
      refine ⟨6376668558456173023657241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4251112372304115349104827 6376668558456173023657241)
      ·
        refine ⟨4782501418842129767742931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6376668558456173023657241 4782501418842129767742931)
        ·
          refine ⟨7173752128263194651614397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782501418842129767742931 7173752128263194651614397)
          ·
            refine ⟨2690157048098697994355399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7173752128263194651614397 2690157048098697994355399)
            ·
              refine ⟨4035235572148046991533099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690157048098697994355399 4035235572148046991533099)
              ·
                refine ⟨6052853358222070487299649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035235572148046991533099 6052853358222070487299649)
                ·
                  refine ⟨4539640018666552865474737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6052853358222070487299649 4539640018666552865474737)
                  ·
                    refine ⟨3404730013999914649106053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4539640018666552865474737 3404730013999914649106053)
                    ·
                      refine ⟨638386877624983996707385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3404730013999914649106053 638386877624983996707385)
                      ·
                        rfl

theorem cell23_1243254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1243254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243254 prefixEnd_1243254 := by exact prefixLift 1243254
  have htrace : WordTrace (prefixWord ++ tailWord_1243254) baseStart_1243254 baseEnd_1243254 := by
    simpa [prefixWord, tailWord_1243254, baseEnd_1243254] using wordTrace_append hprefix tailTrace_1243254
  have hstable : (prefixWord ++ tailWord_1243254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243254).length < 2 ^ (prefixWord ++ tailWord_1243254).sum := by decide
  have hdescent : baseEnd_1243254 < baseStart_1243254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243257 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_1243257 : Nat := 118140960795 + 1243257 * 2 ^ 59
def prefixEnd_1243257 : Nat := 4983230072969 + 3 ^ 40 * 1243257 * 2
def baseEnd_1243257 : Nat := 638388418066947484969871

theorem tailTrace_1243257 : CollatzResearch.WordTrace tailWord_1243257 prefixEnd_1243257 638388418066947484969871 := by
  unfold tailWord_1243257
  simp only [CollatzResearch.WordTrace]
  refine ⟨45345308056899695236144025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30230205371266463490762683 45345308056899695236144025)
  ·
    refine ⟨34008981042674771427108019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45345308056899695236144025 34008981042674771427108019)
    ·
      refine ⟨51013471564012157140662029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34008981042674771427108019 51013471564012157140662029)
      ·
        refine ⟨19130051836504558927748261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51013471564012157140662029 19130051836504558927748261)
        ·
          refine ⟨3586884719344604798952799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19130051836504558927748261 3586884719344604798952799)
          ·
            refine ⟨5380327079016907198429199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586884719344604798952799 5380327079016907198429199)
            ·
              refine ⟨8070490618525360797643799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380327079016907198429199 8070490618525360797643799)
              ·
                refine ⟨12105735927788041196465699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8070490618525360797643799 12105735927788041196465699)
                ·
                  refine ⟨18158603891682061794698549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12105735927788041196465699 18158603891682061794698549)
                  ·
                    refine ⟨1702369114845193293252989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18158603891682061794698549 1702369114845193293252989)
                    ·
                      refine ⟨638388418066947484969871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702369114845193293252989 638388418066947484969871)
                      ·
                        rfl

theorem cell23_1243257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_1243257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243257 prefixEnd_1243257 := by exact prefixLift 1243257
  have htrace : WordTrace (prefixWord ++ tailWord_1243257) baseStart_1243257 baseEnd_1243257 := by
    simpa [prefixWord, tailWord_1243257, baseEnd_1243257] using wordTrace_append hprefix tailTrace_1243257
  have hstable : (prefixWord ++ tailWord_1243257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243257).length < 2 ^ (prefixWord ++ tailWord_1243257).sum := by decide
  have hdescent : baseEnd_1243257 < baseStart_1243257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243286 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1243286 : Nat := 118140960795 + 1243286 * 2 ^ 59
def prefixEnd_1243286 : Nat := 4983230072969 + 3 ^ 40 * 1243286 * 2
def baseEnd_1243286 : Nat := 638403309005927871507239

theorem tailTrace_1243286 : CollatzResearch.WordTrace tailWord_1243286 prefixEnd_1243286 638403309005927871507239 := by
  unfold tailWord_1243286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834147860862164574309357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30230910515863088792633141 2834147860862164574309357)
  ·
    refine ⟨1062805447823311715366009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2834147860862164574309357 1062805447823311715366009)
    ·
      refine ⟨797104085867483786524507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1062805447823311715366009 797104085867483786524507)
      ·
        refine ⟨1195656128801225679786761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797104085867483786524507 1195656128801225679786761)
        ·
          refine ⟨896742096600919259840071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1195656128801225679786761 896742096600919259840071)
          ·
            refine ⟨1345113144901378889760107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896742096600919259840071 1345113144901378889760107)
            ·
              refine ⟨2017669717352068334640161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345113144901378889760107 2017669717352068334640161)
              ·
                refine ⟨1513252288014051250980121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017669717352068334640161 1513252288014051250980121)
                ·
                  refine ⟨1134939216010538438235091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513252288014051250980121 1134939216010538438235091)
                  ·
                    refine ⟨1702408824015807657352637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1134939216010538438235091 1702408824015807657352637)
                    ·
                      refine ⟨638403309005927871507239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702408824015807657352637 638403309005927871507239)
                      ·
                        rfl

theorem cell23_1243286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1243286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243286 prefixEnd_1243286 := by exact prefixLift 1243286
  have htrace : WordTrace (prefixWord ++ tailWord_1243286) baseStart_1243286 baseEnd_1243286 := by
    simpa [prefixWord, tailWord_1243286, baseEnd_1243286] using wordTrace_append hprefix tailTrace_1243286
  have hstable : (prefixWord ++ tailWord_1243286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243286).length < 2 ^ (prefixWord ++ tailWord_1243286).sum := by decide
  have hdescent : baseEnd_1243286 < baseStart_1243286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243314 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_1243314 : Nat := 118140960795 + 1243314 * 2 ^ 59
def prefixEnd_1243314 : Nat := 4983230072969 + 3 ^ 40 * 1243314 * 2
def baseEnd_1243314 : Nat := 638417686464253761957109

theorem tailTrace_1243314 : CollatzResearch.WordTrace tailWord_1243314 prefixEnd_1243314 638417686464253761957109 := by
  unfold tailWord_1243314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11336846754423298492742249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30231591345128795980645997 11336846754423298492742249)
  ·
    refine ⟨8502635065817473869556687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11336846754423298492742249 8502635065817473869556687)
    ·
      refine ⟨12753952598726210804335031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8502635065817473869556687 12753952598726210804335031)
      ·
        refine ⟨19130928898089316206502547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12753952598726210804335031 19130928898089316206502547)
        ·
          refine ⟨28696393347133974309753821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19130928898089316206502547 28696393347133974309753821)
          ·
            refine ⟨10761147505175240366157683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28696393347133974309753821 10761147505175240366157683)
            ·
              refine ⟨16141721257762860549236525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10761147505175240366157683 16141721257762860549236525)
              ·
                refine ⟨6053145471661072705963697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16141721257762860549236525 6053145471661072705963697)
                ·
                  refine ⟨4539859103745804529472773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6053145471661072705963697 4539859103745804529472773)
                  ·
                    refine ⟨851223581952338349276145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539859103745804529472773 851223581952338349276145)
                    ·
                      refine ⟨638417686464253761957109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851223581952338349276145 638417686464253761957109)
                      ·
                        rfl

theorem cell23_1243314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_1243314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243314 prefixEnd_1243314 := by exact prefixLift 1243314
  have htrace : WordTrace (prefixWord ++ tailWord_1243314) baseStart_1243314 baseEnd_1243314 := by
    simpa [prefixWord, tailWord_1243314, baseEnd_1243314] using wordTrace_append hprefix tailTrace_1243314
  have hstable : (prefixWord ++ tailWord_1243314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243314).length < 2 ^ (prefixWord ++ tailWord_1243314).sum := by decide
  have hdescent : baseEnd_1243314 < baseStart_1243314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243391 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 2, 3, 2]
def baseStart_1243391 : Nat := 118140960795 + 1243391 * 2 ^ 59
def prefixEnd_1243391 : Nat := 4983230072969 + 3 ^ 40 * 1243391 * 2
def baseEnd_1243391 : Nat := 638457224474649960694255

theorem tailTrace_1243391 : CollatzResearch.WordTrace tailWord_1243391 prefixEnd_1243391 638457224474649960694255 := by
  unfold tailWord_1243391
  simp only [CollatzResearch.WordTrace]
  refine ⟨45350195438414236121522027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30233463625609490747681351 45350195438414236121522027)
  ·
    refine ⟨68025293157621354182283041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45350195438414236121522027 68025293157621354182283041)
    ·
      refine ⟨51018969868216015636712281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68025293157621354182283041 51018969868216015636712281)
      ·
        refine ⟨38264227401162011727534211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51018969868216015636712281 38264227401162011727534211)
        ·
          refine ⟨57396341101743017591301317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38264227401162011727534211 57396341101743017591301317)
          ·
            refine ⟨10761813956576815798368997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57396341101743017591301317 10761813956576815798368997)
            ·
              refine ⟨2017840116858152962194187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10761813956576815798368997 2017840116858152962194187)
              ·
                refine ⟨3026760175287229443291281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017840116858152962194187 3026760175287229443291281)
                ·
                  refine ⟨2270070131465422082468461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3026760175287229443291281 2270070131465422082468461)
                  ·
                    refine ⟨851276299299533280925673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2270070131465422082468461 851276299299533280925673)
                    ·
                      refine ⟨638457224474649960694255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851276299299533280925673 638457224474649960694255)
                      ·
                        rfl

theorem cell23_1243391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_1243391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243391 prefixEnd_1243391 := by exact prefixLift 1243391
  have htrace : WordTrace (prefixWord ++ tailWord_1243391) baseStart_1243391 baseEnd_1243391 := by
    simpa [prefixWord, tailWord_1243391, baseEnd_1243391] using wordTrace_append hprefix tailTrace_1243391
  have hstable : (prefixWord ++ tailWord_1243391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243391).length < 2 ^ (prefixWord ++ tailWord_1243391).sum := by decide
  have hdescent : baseEnd_1243391 < baseStart_1243391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243401 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 1, 5]
def baseStart_1243401 : Nat := 118140960795 + 1243401 * 2 ^ 59
def prefixEnd_1243401 : Nat := 4983230072969 + 3 ^ 40 * 1243401 * 2
def baseEnd_1243401 : Nat := 212820786427064973856403

theorem tailTrace_1243401 : CollatzResearch.WordTrace tailWord_1243401 prefixEnd_1243401 212820786427064973856403 := by
  unfold tailWord_1243401
  simp only [CollatzResearch.WordTrace]
  refine ⟨45350560168378007829386057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30233706778918671886257371 45350560168378007829386057)
  ·
    refine ⟨34012920126283505872039543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45350560168378007829386057 34012920126283505872039543)
    ·
      refine ⟨51019380189425258808059315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34012920126283505872039543 51019380189425258808059315)
      ·
        refine ⟨76529070284137888212088973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51019380189425258808059315 76529070284137888212088973)
        ·
          refine ⟨28698401356551708079533365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76529070284137888212088973 28698401356551708079533365)
          ·
            refine ⟨2690475127176722632456253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28698401356551708079533365 2690475127176722632456253)
            ·
              refine ⟨1008928172691270987171095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2690475127176722632456253 1008928172691270987171095)
              ·
                refine ⟨1513392259036906480756643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008928172691270987171095 1513392259036906480756643)
                ·
                  refine ⟨2270088388555359721134965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513392259036906480756643 2270088388555359721134965)
                  ·
                    refine ⟨212820786427064973856403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2270088388555359721134965 212820786427064973856403)
                    ·
                      rfl

theorem cell23_1243401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 5].length) (baseStart_1243401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243401 prefixEnd_1243401 := by exact prefixLift 1243401
  have htrace : WordTrace (prefixWord ++ tailWord_1243401) baseStart_1243401 baseEnd_1243401 := by
    simpa [prefixWord, tailWord_1243401, baseEnd_1243401] using wordTrace_append hprefix tailTrace_1243401
  have hstable : (prefixWord ++ tailWord_1243401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243401).length < 2 ^ (prefixWord ++ tailWord_1243401).sum := by decide
  have hdescent : baseEnd_1243401 < baseStart_1243401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243415 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 1, 1, 3]
def baseStart_1243415 : Nat := 118140960795 + 1243415 * 2 ^ 59
def prefixEnd_1243415 : Nat := 4983230072969 + 3 ^ 40 * 1243415 * 2
def baseEnd_1243415 : Nat := 638469548010357866794145

theorem tailTrace_1243415 : CollatzResearch.WordTrace tailWord_1243415 prefixEnd_1243415 638469548010357866794145 := by
  unfold tailWord_1243415
  simp only [CollatzResearch.WordTrace]
  refine ⟨45351070790327288220395699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30234047193551525480263799 45351070790327288220395699)
  ·
    refine ⟨68026606185490932330593549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45351070790327288220395699 68026606185490932330593549)
    ·
      refine ⟨25509977319559099623972581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68026606185490932330593549 25509977319559099623972581)
      ·
        refine ⟨4783120747417331179494859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25509977319559099623972581 4783120747417331179494859)
        ·
          refine ⟨7174681121125996769242289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783120747417331179494859 7174681121125996769242289)
          ·
            refine ⟨5381010840844497576931717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7174681121125996769242289 5381010840844497576931717)
            ·
              refine ⟨1008939532658343295674697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5381010840844497576931717 1008939532658343295674697)
              ·
                refine ⟨756704649493757471756023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008939532658343295674697 756704649493757471756023)
                ·
                  refine ⟨1135056974240636207634035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756704649493757471756023 1135056974240636207634035)
                  ·
                    refine ⟨1702585461360954311451053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1135056974240636207634035 1702585461360954311451053)
                    ·
                      refine ⟨638469548010357866794145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702585461360954311451053 638469548010357866794145)
                      ·
                        rfl

theorem cell23_1243415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_1243415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243415 prefixEnd_1243415 := by exact prefixLift 1243415
  have htrace : WordTrace (prefixWord ++ tailWord_1243415) baseStart_1243415 baseEnd_1243415 := by
    simpa [prefixWord, tailWord_1243415, baseEnd_1243415] using wordTrace_append hprefix tailTrace_1243415
  have hstable : (prefixWord ++ tailWord_1243415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243415).length < 2 ^ (prefixWord ++ tailWord_1243415).sum := by decide
  have hdescent : baseEnd_1243415 < baseStart_1243415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243455 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 1, 2, 2]
def baseStart_1243455 : Nat := 118140960795 + 1243455 * 2 ^ 59
def prefixEnd_1243455 : Nat := 4983230072969 + 3 ^ 40 * 1243455 * 2
def baseEnd_1243455 : Nat := 638490087236537710293961

theorem tailTrace_1243455 : CollatzResearch.WordTrace tailWord_1243455 prefixEnd_1243455 638490087236537710293961 := by
  unfold tailWord_1243455
  simp only [CollatzResearch.WordTrace]
  refine ⟨45352529710182375051851819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30235019806788250034567879 45352529710182375051851819)
  ·
    refine ⟨68028794565273562577777729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45352529710182375051851819 68028794565273562577777729)
    ·
      refine ⟨51021595923955171933333297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68028794565273562577777729 51021595923955171933333297)
      ·
        refine ⟨38266196942966378949999973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51021595923955171933333297 38266196942966378949999973)
        ·
          refine ⟨7174911926806196053124995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38266196942966378949999973 7174911926806196053124995)
          ·
            refine ⟨10762367890209294079687493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174911926806196053124995 10762367890209294079687493)
            ·
              refine ⟨2017943979414242639941405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10762367890209294079687493 2017943979414242639941405)
              ·
                refine ⟨756728992280340989978027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2017943979414242639941405 756728992280340989978027)
                ·
                  refine ⟨1135093488420511484967041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756728992280340989978027 1135093488420511484967041)
                  ·
                    refine ⟨851320116315383613725281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1135093488420511484967041 851320116315383613725281)
                    ·
                      refine ⟨638490087236537710293961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851320116315383613725281 638490087236537710293961)
                      ·
                        rfl

theorem cell23_1243455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_1243455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243455 prefixEnd_1243455 := by exact prefixLift 1243455
  have htrace : WordTrace (prefixWord ++ tailWord_1243455) baseStart_1243455 baseEnd_1243455 := by
    simpa [prefixWord, tailWord_1243455, baseEnd_1243455] using wordTrace_append hprefix tailTrace_1243455
  have hstable : (prefixWord ++ tailWord_1243455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243455).length < 2 ^ (prefixWord ++ tailWord_1243455).sum := by decide
  have hdescent : baseEnd_1243455 < baseStart_1243455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243467 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_1243467 : Nat := 118140960795 + 1243467 * 2 ^ 59
def prefixEnd_1243467 : Nat := 4983230072969 + 3 ^ 40 * 1243467 * 2
def baseEnd_1243467 : Nat := 638496249004391663343905

theorem tailTrace_1243467 : CollatzResearch.WordTrace tailWord_1243467 prefixEnd_1243467 638496249004391663343905 := by
  unfold tailWord_1243467
  simp only [CollatzResearch.WordTrace]
  refine ⟨45352967386138901101288655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30235311590759267400859103 45352967386138901101288655)
  ·
    refine ⟨68029451079208351651932983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45352967386138901101288655 68029451079208351651932983)
    ·
      refine ⟨102044176618812527477899475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68029451079208351651932983 102044176618812527477899475)
      ·
        refine ⟨153066264928218791216849213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102044176618812527477899475 153066264928218791216849213)
        ·
          refine ⟨57399849348082046706318455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153066264928218791216849213 57399849348082046706318455)
          ·
            refine ⟨86099774022123070059477683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57399849348082046706318455 86099774022123070059477683)
            ·
              refine ⟨129149661033184605089216525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86099774022123070059477683 129149661033184605089216525)
              ·
                refine ⟨48431122887444226908456197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129149661033184605089216525 48431122887444226908456197)
                ·
                  refine ⟨9080835541395792545335537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48431122887444226908456197 9080835541395792545335537)
                  ·
                    refine ⟨6810626656046844409001653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9080835541395792545335537 6810626656046844409001653)
                    ·
                      refine ⟨638496249004391663343905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6810626656046844409001653 638496249004391663343905)
                      ·
                        rfl

theorem cell23_1243467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_1243467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243467 prefixEnd_1243467 := by exact prefixLift 1243467
  have htrace : WordTrace (prefixWord ++ tailWord_1243467) baseStart_1243467 baseEnd_1243467 := by
    simpa [prefixWord, tailWord_1243467, baseEnd_1243467] using wordTrace_append hprefix tailTrace_1243467
  have hstable : (prefixWord ++ tailWord_1243467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243467).length < 2 ^ (prefixWord ++ tailWord_1243467).sum := by decide
  have hdescent : baseEnd_1243467 < baseStart_1243467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243471 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 3]
def baseStart_1243471 : Nat := 118140960795 + 1243471 * 2 ^ 59
def prefixEnd_1243471 : Nat := 4983230072969 + 3 ^ 40 * 1243471 * 2
def baseEnd_1243471 : Nat := 638498302927009647693887

theorem tailTrace_1243471 : CollatzResearch.WordTrace tailWord_1243471 prefixEnd_1243471 638498302927009647693887 := by
  unfold tailWord_1243471
  simp only [CollatzResearch.WordTrace]
  refine ⟨45353113278124409784434267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30235408852082939856289511 45353113278124409784434267)
  ·
    refine ⟨68029669917186614676651401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45353113278124409784434267 68029669917186614676651401)
    ·
      refine ⟨51022252437889961007488551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68029669917186614676651401 51022252437889961007488551)
      ·
        refine ⟨76533378656834941511232827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51022252437889961007488551 76533378656834941511232827)
        ·
          refine ⟨114800067985252412266849241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76533378656834941511232827 114800067985252412266849241)
          ·
            refine ⟨86100050988939309200136931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114800067985252412266849241 86100050988939309200136931)
            ·
              refine ⟨129150076483408963800205397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86100050988939309200136931 129150076483408963800205397)
              ·
                refine ⟨1513477458789948794533657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 129150076483408963800205397 1513477458789948794533657)
                ·
                  refine ⟨1135108094092461595900243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513477458789948794533657 1135108094092461595900243)
                  ·
                    refine ⟨1702662141138692393850365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1135108094092461595900243 1702662141138692393850365)
                    ·
                      refine ⟨638498302927009647693887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702662141138692393850365 638498302927009647693887)
                      ·
                        rfl

theorem cell23_1243471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_1243471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243471 prefixEnd_1243471 := by exact prefixLift 1243471
  have htrace : WordTrace (prefixWord ++ tailWord_1243471) baseStart_1243471 baseEnd_1243471 := by
    simpa [prefixWord, tailWord_1243471, baseEnd_1243471] using wordTrace_append hprefix tailTrace_1243471
  have hstable : (prefixWord ++ tailWord_1243471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243471).length < 2 ^ (prefixWord ++ tailWord_1243471).sum := by decide
  have hdescent : baseEnd_1243471 < baseStart_1243471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243488 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3]
def baseStart_1243488 : Nat := 118140960795 + 1243488 * 2 ^ 59
def prefixEnd_1243488 : Nat := 4983230072969 + 3 ^ 40 * 1243488 * 2
def baseEnd_1243488 : Nat := 638507032098136081181309

theorem tailTrace_1243488 : CollatzResearch.WordTrace tailWord_1243488 prefixEnd_1243488 638507032098136081181309 := by
  unfold tailWord_1243488
  simp only [CollatzResearch.WordTrace]
  refine ⟨22676866659531410843901559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30235822212708547791868745 22676866659531410843901559)
  ·
    refine ⟨34015299989297116265852339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22676866659531410843901559 34015299989297116265852339)
    ·
      refine ⟨51022949983945674398778509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34015299989297116265852339 51022949983945674398778509)
      ·
        refine ⟨19133606243979627899541941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51022949983945674398778509 19133606243979627899541941)
        ·
          refine ⟨1793775585373090115582057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19133606243979627899541941 1793775585373090115582057)
          ·
            refine ⟨1345331689029817586686543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1793775585373090115582057 1345331689029817586686543)
            ·
              refine ⟨2017997533544726380029815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345331689029817586686543 2017997533544726380029815)
              ·
                refine ⟨3026996300317089570044723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017997533544726380029815 3026996300317089570044723)
                ·
                  refine ⟨4540494450475634355067085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026996300317089570044723 4540494450475634355067085)
                  ·
                    refine ⟨1702685418928362883150157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4540494450475634355067085 1702685418928362883150157)
                    ·
                      refine ⟨638507032098136081181309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702685418928362883150157 638507032098136081181309)
                      ·
                        rfl

theorem cell23_1243488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_1243488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243488 prefixEnd_1243488 := by exact prefixLift 1243488
  have htrace : WordTrace (prefixWord ++ tailWord_1243488) baseStart_1243488 baseEnd_1243488 := by
    simpa [prefixWord, tailWord_1243488, baseEnd_1243488] using wordTrace_append hprefix tailTrace_1243488
  have hstable : (prefixWord ++ tailWord_1243488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243488).length < 2 ^ (prefixWord ++ tailWord_1243488).sum := by decide
  have hdescent : baseEnd_1243488 < baseStart_1243488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243528 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_1243528 : Nat := 118140960795 + 1243528 * 2 ^ 59
def prefixEnd_1243528 : Nat := 4983230072969 + 3 ^ 40 * 1243528 * 2
def baseEnd_1243528 : Nat := 638527571324315924681125

theorem tailTrace_1243528 : CollatzResearch.WordTrace tailWord_1243528 prefixEnd_1243528 638527571324315924681125 := by
  unfold tailWord_1243528
  simp only [CollatzResearch.WordTrace]
  refine ⟨22677596119458954259629619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30236794825945272346172825 22677596119458954259629619)
  ·
    refine ⟨34016394179188431389444429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22677596119458954259629619 34016394179188431389444429)
    ·
      refine ⟨12756147817195661771041661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34016394179188431389444429 12756147817195661771041661)
      ·
        refine ⟨4783555431448373164140623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12756147817195661771041661 4783555431448373164140623)
        ·
          refine ⟨7175333147172559746210935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783555431448373164140623 7175333147172559746210935)
          ·
            refine ⟨10762999720758839619316403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175333147172559746210935 10762999720758839619316403)
            ·
              refine ⟨16144499581138259428974605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10762999720758839619316403 16144499581138259428974605)
              ·
                refine ⟨6054187342926847285865477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16144499581138259428974605 6054187342926847285865477)
                ·
                  refine ⟨1135160126798783866099777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6054187342926847285865477 1135160126798783866099777)
                  ·
                    refine ⟨851370095099087899574833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1135160126798783866099777 851370095099087899574833)
                    ·
                      refine ⟨638527571324315924681125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851370095099087899574833 638527571324315924681125)
                      ·
                        rfl

theorem cell23_1243528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_1243528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243528 prefixEnd_1243528 := by exact prefixLift 1243528
  have htrace : WordTrace (prefixWord ++ tailWord_1243528) baseStart_1243528 baseEnd_1243528 := by
    simpa [prefixWord, tailWord_1243528, baseEnd_1243528] using wordTrace_append hprefix tailTrace_1243528
  have hstable : (prefixWord ++ tailWord_1243528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243528).length < 2 ^ (prefixWord ++ tailWord_1243528).sum := by decide
  have hdescent : baseEnd_1243528 < baseStart_1243528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243581 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1243581 : Nat := 118140960795 + 1243581 * 2 ^ 59
def prefixEnd_1243581 : Nat := 4983230072969 + 3 ^ 40 * 1243581 * 2
def baseEnd_1243581 : Nat := 212851595266334739106127

theorem tailTrace_1243581 : CollatzResearch.WordTrace tailWord_1243581 prefixEnd_1243581 212851595266334739106127 := by
  unfold tailWord_1243581
  simp only [CollatzResearch.WordTrace]
  refine ⟨45357125307725898570938597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30238083538483932380625731 45357125307725898570938597)
  ·
    refine ⟨8504460995198605982050987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45357125307725898570938597 8504460995198605982050987)
    ·
      refine ⟨12756691492797908973076481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8504460995198605982050987 12756691492797908973076481)
      ·
        refine ⟨9567518619598431729807361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12756691492797908973076481 9567518619598431729807361)
        ·
          refine ⟨7175638964698823797355521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9567518619598431729807361 7175638964698823797355521)
          ·
            refine ⟨5381729223524117848016641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7175638964698823797355521 5381729223524117848016641)
            ·
              refine ⟨4036296917643088386012481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5381729223524117848016641 4036296917643088386012481)
              ·
                refine ⟨3027222688232316289509361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036296917643088386012481 3027222688232316289509361)
                ·
                  refine ⟨2270417016174237217132021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3027222688232316289509361 2270417016174237217132021)
                  ·
                    refine ⟨212851595266334739106127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2270417016174237217132021 212851595266334739106127)
                    ·
                      rfl

theorem cell23_1243581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1243581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243581 prefixEnd_1243581 := by exact prefixLift 1243581
  have htrace : WordTrace (prefixWord ++ tailWord_1243581) baseStart_1243581 baseEnd_1243581 := by
    simpa [prefixWord, tailWord_1243581, baseEnd_1243581] using wordTrace_append hprefix tailTrace_1243581
  have hstable : (prefixWord ++ tailWord_1243581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243581).length < 2 ^ (prefixWord ++ tailWord_1243581).sum := by decide
  have hdescent : baseEnd_1243581 < baseStart_1243581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243584 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_1243584 : Nat := 118140960795 + 1243584 * 2 ^ 59
def prefixEnd_1243584 : Nat := 4983230072969 + 3 ^ 40 * 1243584 * 2
def baseEnd_1243584 : Nat := 638556326240967705580867

theorem tailTrace_1243584 : CollatzResearch.WordTrace tailWord_1243584 prefixEnd_1243584 638556326240967705580867 := by
  unfold tailWord_1243584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22678617363357515041648903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30238156484476686722198537 22678617363357515041648903)
  ·
    refine ⟨34017926045036272562473355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22678617363357515041648903 34017926045036272562473355)
    ·
      refine ⟨51026889067554408843710033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34017926045036272562473355 51026889067554408843710033)
      ·
        refine ⟨38270166800665806632782525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51026889067554408843710033 38270166800665806632782525)
        ·
          refine ⟨14351312550249677487293447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38270166800665806632782525 14351312550249677487293447)
          ·
            refine ⟨21526968825374516230940171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14351312550249677487293447 21526968825374516230940171)
            ·
              refine ⟨32290453238061774346410257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21526968825374516230940171 32290453238061774346410257)
              ·
                refine ⟨24217839928546330759807693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32290453238061774346410257 24217839928546330759807693)
                ·
                  refine ⟨9081689973204874034927885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24217839928546330759807693 9081689973204874034927885)
                  ·
                    refine ⟨3405633739951827763097957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9081689973204874034927885 3405633739951827763097957)
                    ·
                      refine ⟨638556326240967705580867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3405633739951827763097957 638556326240967705580867)
                      ·
                        rfl

theorem cell23_1243584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_1243584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243584 prefixEnd_1243584 := by exact prefixLift 1243584
  have htrace : WordTrace (prefixWord ++ tailWord_1243584) baseStart_1243584 baseEnd_1243584 := by
    simpa [prefixWord, tailWord_1243584, baseEnd_1243584] using wordTrace_append hprefix tailTrace_1243584
  have hstable : (prefixWord ++ tailWord_1243584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243584).length < 2 ^ (prefixWord ++ tailWord_1243584).sum := by decide
  have hdescent : baseEnd_1243584 < baseStart_1243584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243638 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1243638 : Nat := 118140960795 + 1243638 * 2 ^ 59
def prefixEnd_1243638 : Nat := 4983230072969 + 3 ^ 40 * 1243638 * 2
def baseEnd_1243638 : Nat := 638584054196310494305619

theorem tailTrace_1243638 : CollatzResearch.WordTrace tailWord_1243638 prefixEnd_1243638 638584054196310494305619 := by
  unfold tailWord_1243638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834950266782462331610223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30239469512346264870509045 2834950266782462331610223)
  ·
    refine ⟨4252425400173693497415335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2834950266782462331610223 4252425400173693497415335)
    ·
      refine ⟨6378638100260540246123003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252425400173693497415335 6378638100260540246123003)
      ·
        refine ⟨9567957150390810369184505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6378638100260540246123003 9567957150390810369184505)
        ·
          refine ⟨7175967862793107776888379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9567957150390810369184505 7175967862793107776888379)
          ·
            refine ⟨10763951794189661665332569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175967862793107776888379 10763951794189661665332569)
            ·
              refine ⟨8072963845642246248999427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10763951794189661665332569 8072963845642246248999427)
              ·
                refine ⟨12109445768463369373499141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072963845642246248999427 12109445768463369373499141)
                ·
                  refine ⟨2270521081586881757531089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12109445768463369373499141 2270521081586881757531089)
                  ·
                    refine ⟨1702890811190161318148317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2270521081586881757531089 1702890811190161318148317)
                    ·
                      refine ⟨638584054196310494305619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702890811190161318148317 638584054196310494305619)
                      ·
                        rfl

theorem cell23_1243638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1243638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243638 prefixEnd_1243638 := by exact prefixLift 1243638
  have htrace : WordTrace (prefixWord ++ tailWord_1243638) baseStart_1243638 baseEnd_1243638 := by
    simpa [prefixWord, tailWord_1243638, baseEnd_1243638] using wordTrace_append hprefix tailTrace_1243638
  have hstable : (prefixWord ++ tailWord_1243638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243638).length < 2 ^ (prefixWord ++ tailWord_1243638).sum := by decide
  have hdescent : baseEnd_1243638 < baseStart_1243638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243641 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 6]
def baseStart_1243641 : Nat := 118140960795 + 1243641 * 2 ^ 59
def prefixEnd_1243641 : Nat := 4983230072969 + 3 ^ 40 * 1243641 * 2
def baseEnd_1243641 : Nat := 70953954959808220285345

theorem tailTrace_1243641 : CollatzResearch.WordTrace tailWord_1243641 prefixEnd_1243641 70953954959808220285345 := by
  unfold tailWord_1243641
  simp only [CollatzResearch.WordTrace]
  refine ⟨45359313687508528818122777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30239542458339019212081851 45359313687508528818122777)
  ·
    refine ⟨34019485265631396613592083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45359313687508528818122777 34019485265631396613592083)
    ·
      refine ⟨51029227898447094920388125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34019485265631396613592083 51029227898447094920388125)
      ·
        refine ⟨19135960461917660595145547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51029227898447094920388125 19135960461917660595145547)
        ·
          refine ⟨28703940692876490892718321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19135960461917660595145547 28703940692876490892718321)
          ·
            refine ⟨21527955519657368169538741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28703940692876490892718321 21527955519657368169538741)
            ·
              refine ⟨2018245829967878265894257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21527955519657368169538741 2018245829967878265894257)
              ·
                refine ⟨1513684372475908699420693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018245829967878265894257 1513684372475908699420693)
                ·
                  refine ⟨70953954959808220285345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1513684372475908699420693 70953954959808220285345)
                  ·
                    rfl

theorem cell23_1243641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_1243641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243641 prefixEnd_1243641 := by exact prefixLift 1243641
  have htrace : WordTrace (prefixWord ++ tailWord_1243641) baseStart_1243641 baseEnd_1243641 := by
    simpa [prefixWord, tailWord_1243641, baseEnd_1243641] using wordTrace_append hprefix tailTrace_1243641
  have hstable : (prefixWord ++ tailWord_1243641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243641).length < 2 ^ (prefixWord ++ tailWord_1243641).sum := by decide
  have hdescent : baseEnd_1243641 < baseStart_1243641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243658 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_1243658 : Nat := 118140960795 + 1243658 * 2 ^ 59
def prefixEnd_1243658 : Nat := 4983230072969 + 3 ^ 40 * 1243658 * 2
def baseEnd_1243658 : Nat := 70954924867711157339503

theorem tailTrace_1243658 : CollatzResearch.WordTrace tailWord_1243658 prefixEnd_1243658 70954924867711157339503 := by
  unfold tailWord_1243658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339983432111735180372907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30239955818964627147661085 11339983432111735180372907)
  ·
    refine ⟨17009975148167602770559361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11339983432111735180372907 17009975148167602770559361)
    ·
      refine ⟨12757481361125702077919521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17009975148167602770559361 12757481361125702077919521)
      ·
        refine ⟨9568111020844276558439641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12757481361125702077919521 9568111020844276558439641)
        ·
          refine ⟨7176083265633207418829731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9568111020844276558439641 7176083265633207418829731)
          ·
            refine ⟨10764124898449811128244597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176083265633207418829731 10764124898449811128244597)
            ·
              refine ⟨1009136709229669793272931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10764124898449811128244597 1009136709229669793272931)
              ·
                refine ⟨1513705063844504689909397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009136709229669793272931 1513705063844504689909397)
                ·
                  refine ⟨70954924867711157339503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1513705063844504689909397 70954924867711157339503)
                  ·
                    rfl

theorem cell23_1243658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_1243658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243658 prefixEnd_1243658 := by exact prefixLift 1243658
  have htrace : WordTrace (prefixWord ++ tailWord_1243658) baseStart_1243658 baseEnd_1243658 := by
    simpa [prefixWord, tailWord_1243658, baseEnd_1243658] using wordTrace_append hprefix tailTrace_1243658
  have hstable : (prefixWord ++ tailWord_1243658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243658).length < 2 ^ (prefixWord ++ tailWord_1243658).sum := by decide
  have hdescent : baseEnd_1243658 < baseStart_1243658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243664 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_1243664 : Nat := 118140960795 + 1243664 * 2 ^ 59
def prefixEnd_1243664 : Nat := 4983230072969 + 3 ^ 40 * 1243664 * 2
def baseEnd_1243664 : Nat := 638597404693327392580499

theorem tailTrace_1243664 : CollatzResearch.WordTrace tailWord_1243664 prefixEnd_1243664 638597404693327392580499 := by
  unfold tailWord_1243664
  simp only [CollatzResearch.WordTrace]
  refine ⟨22680076283212601873105023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30240101710950135830806697 22680076283212601873105023)
  ·
    refine ⟨34020114424818902809657535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22680076283212601873105023 34020114424818902809657535)
    ·
      refine ⟨51030171637228354214486303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34020114424818902809657535 51030171637228354214486303)
      ·
        refine ⟨76545257455842531321729455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51030171637228354214486303 76545257455842531321729455)
        ·
          refine ⟨114817886183763796982594183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76545257455842531321729455 114817886183763796982594183)
          ·
            refine ⟨172226829275645695473891275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114817886183763796982594183 172226829275645695473891275)
            ·
              refine ⟨258340243913468543210836913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172226829275645695473891275 258340243913468543210836913)
              ·
                refine ⟨193755182935101407408127685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258340243913468543210836913 193755182935101407408127685)
                ·
                  refine ⟨36329096800331513889023941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193755182935101407408127685 36329096800331513889023941)
                  ·
                    refine ⟨6811705650062158854191989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36329096800331513889023941 6811705650062158854191989)
                    ·
                      refine ⟨638597404693327392580499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6811705650062158854191989 638597404693327392580499)
                      ·
                        rfl

theorem cell23_1243664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_1243664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243664 prefixEnd_1243664 := by exact prefixLift 1243664
  have htrace : WordTrace (prefixWord ++ tailWord_1243664) baseStart_1243664 baseEnd_1243664 := by
    simpa [prefixWord, tailWord_1243664, baseEnd_1243664] using wordTrace_append hprefix tailTrace_1243664
  have hstable : (prefixWord ++ tailWord_1243664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243664).length < 2 ^ (prefixWord ++ tailWord_1243664).sum := by decide
  have hdescent : baseEnd_1243664 < baseStart_1243664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243702 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1243702 : Nat := 118140960795 + 1243702 * 2 ^ 59
def prefixEnd_1243702 : Nat := 4983230072969 + 3 ^ 40 * 1243702 * 2
def baseEnd_1243702 : Nat := 638616916958198243905325

theorem tailTrace_1243702 : CollatzResearch.WordTrace tailWord_1243702 prefixEnd_1243702 638616916958198243905325 := by
  unfold tailWord_1243702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835096158767971014755835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30241025693525024157395573 2835096158767971014755835)
  ·
    refine ⟨4252644238151956522133753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835096158767971014755835 4252644238151956522133753)
    ·
      refine ⟨3189483178613967391600315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4252644238151956522133753 3189483178613967391600315)
      ·
        refine ⟨4784224767920951087400473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189483178613967391600315 4784224767920951087400473)
        ·
          refine ⟨3588168575940713315550355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784224767920951087400473 3588168575940713315550355)
          ·
            refine ⟨5382252863911069973325533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588168575940713315550355 5382252863911069973325533)
            ·
              refine ⟨2018344823966651239997075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5382252863911069973325533 2018344823966651239997075)
              ·
                refine ⟨3027517235949976859995613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018344823966651239997075 3027517235949976859995613)
                ·
                  refine ⟨1135318963481241322498355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3027517235949976859995613 1135318963481241322498355)
                  ·
                    refine ⟨1702978445221861983747533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1135318963481241322498355 1702978445221861983747533)
                    ·
                      refine ⟨638616916958198243905325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1702978445221861983747533 638616916958198243905325)
                      ·
                        rfl

theorem cell23_1243702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1243702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243702 prefixEnd_1243702 := by exact prefixLift 1243702
  have htrace : WordTrace (prefixWord ++ tailWord_1243702) baseStart_1243702 baseEnd_1243702 := by
    simpa [prefixWord, tailWord_1243702, baseEnd_1243702] using wordTrace_append hprefix tailTrace_1243702
  have hstable : (prefixWord ++ tailWord_1243702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243702).length < 2 ^ (prefixWord ++ tailWord_1243702).sum := by decide
  have hdescent : baseEnd_1243702 < baseStart_1243702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243711 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_1243711 : Nat := 118140960795 + 1243711 * 2 ^ 59
def prefixEnd_1243711 : Nat := 4983230072969 + 3 ^ 40 * 1243711 * 2
def baseEnd_1243711 : Nat := 638621538284088708692783

theorem tailTrace_1243711 : CollatzResearch.WordTrace tailWord_1243711 prefixEnd_1243711 638621538284088708692783 := by
  unfold tailWord_1243711
  simp only [CollatzResearch.WordTrace]
  refine ⟨45361866797254930773170987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30241244531503287182113991 45361866797254930773170987)
  ·
    refine ⟨68042800195882396159756481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45361866797254930773170987 68042800195882396159756481)
    ·
      refine ⟨51032100146911797119817361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68042800195882396159756481 51032100146911797119817361)
      ·
        refine ⟨38274075110183847839863021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51032100146911797119817361 38274075110183847839863021)
        ·
          refine ⟨14352778166318942939948633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38274075110183847839863021 14352778166318942939948633)
          ·
            refine ⟨10764583624739207204961475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14352778166318942939948633 10764583624739207204961475)
            ·
              refine ⟨16146875437108810807442213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10764583624739207204961475 16146875437108810807442213)
              ·
                refine ⟨3027539144457902026395415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16146875437108810807442213 3027539144457902026395415)
                ·
                  refine ⟨4541308716686853039593123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027539144457902026395415 4541308716686853039593123)
                  ·
                    refine ⟨6811963075030279559389685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4541308716686853039593123 6811963075030279559389685)
                    ·
                      refine ⟨638621538284088708692783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6811963075030279559389685 638621538284088708692783)
                      ·
                        rfl

theorem cell23_1243711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_1243711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243711 prefixEnd_1243711 := by exact prefixLift 1243711
  have htrace : WordTrace (prefixWord ++ tailWord_1243711) baseStart_1243711 baseEnd_1243711 := by
    simpa [prefixWord, tailWord_1243711, baseEnd_1243711] using wordTrace_append hprefix tailTrace_1243711
  have hstable : (prefixWord ++ tailWord_1243711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243711).length < 2 ^ (prefixWord ++ tailWord_1243711).sum := by decide
  have hdescent : baseEnd_1243711 < baseStart_1243711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243725 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1243725 : Nat := 118140960795 + 1243725 * 2 ^ 59
def prefixEnd_1243725 : Nat := 4983230072969 + 3 ^ 40 * 1243725 * 2
def baseEnd_1243725 : Nat := 638628727013251653917719

theorem tailTrace_1243725 : CollatzResearch.WordTrace tailWord_1243725 prefixEnd_1243725 638628727013251653917719 := by
  unfold tailWord_1243725
  simp only [CollatzResearch.WordTrace]
  refine ⟨45362377419204211164180629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30241584946136140776120419 45362377419204211164180629)
  ·
    refine ⟨2126361441525197398320967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45362377419204211164180629 2126361441525197398320967)
    ·
      refine ⟨3189542162287796097481451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126361441525197398320967 3189542162287796097481451)
      ·
        refine ⟨4784313243431694146222177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189542162287796097481451 4784313243431694146222177)
        ·
          refine ⟨3588234932573770609666633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784313243431694146222177 3588234932573770609666633)
          ·
            refine ⟨2691176199430327957249975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3588234932573770609666633 2691176199430327957249975)
            ·
              refine ⟨4036764299145491935874963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691176199430327957249975 4036764299145491935874963)
              ·
                refine ⟨6055146448718237903812445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036764299145491935874963 6055146448718237903812445)
                ·
                  refine ⟨2270679918269339213929667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6055146448718237903812445 2270679918269339213929667)
                  ·
                    refine ⟨3406019877404008820894501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2270679918269339213929667 3406019877404008820894501)
                    ·
                      refine ⟨638628727013251653917719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3406019877404008820894501 638628727013251653917719)
                      ·
                        rfl

theorem cell23_1243725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1243725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243725 prefixEnd_1243725 := by exact prefixLift 1243725
  have htrace : WordTrace (prefixWord ++ tailWord_1243725) baseStart_1243725 baseEnd_1243725 := by
    simpa [prefixWord, tailWord_1243725, baseEnd_1243725] using wordTrace_append hprefix tailTrace_1243725
  have hstable : (prefixWord ++ tailWord_1243725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243725).length < 2 ^ (prefixWord ++ tailWord_1243725).sum := by decide
  have hdescent : baseEnd_1243725 < baseStart_1243725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243728 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3]
def baseStart_1243728 : Nat := 118140960795 + 1243728 * 2 ^ 59
def prefixEnd_1243728 : Nat := 4983230072969 + 3 ^ 40 * 1243728 * 2
def baseEnd_1243728 : Nat := 638630267455215142180205

theorem tailTrace_1243728 : CollatzResearch.WordTrace tailWord_1243728 prefixEnd_1243728 638630267455215142180205 := by
  unfold tailWord_1243728
  simp only [CollatzResearch.WordTrace]
  refine ⟨22681243419096671338269919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30241657892128895117693225 22681243419096671338269919)
  ·
    refine ⟨34021865128645007007404879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22681243419096671338269919 34021865128645007007404879)
    ·
      refine ⟨51032797692967510511107319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34021865128645007007404879 51032797692967510511107319)
      ·
        refine ⟨76549196539451265766660979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51032797692967510511107319 76549196539451265766660979)
        ·
          refine ⟨114823794809176898649991469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76549196539451265766660979 114823794809176898649991469)
          ·
            refine ⟨43058923053441336993746801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114823794809176898649991469 43058923053441336993746801)
            ·
              refine ⟨32294192290081002745310101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43058923053441336993746801 32294192290081002745310101)
              ·
                refine ⟨1513790263597547003686411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32294192290081002745310101 1513790263597547003686411)
                ·
                  refine ⟨2270685395396320505529617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513790263597547003686411 2270685395396320505529617)
                  ·
                    refine ⟨1703014046547240379147213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2270685395396320505529617 1703014046547240379147213)
                    ·
                      refine ⟨638630267455215142180205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703014046547240379147213 638630267455215142180205)
                      ·
                        rfl

theorem cell23_1243728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_1243728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243728 prefixEnd_1243728 := by exact prefixLift 1243728
  have htrace : WordTrace (prefixWord ++ tailWord_1243728) baseStart_1243728 baseEnd_1243728 := by
    simpa [prefixWord, tailWord_1243728, baseEnd_1243728] using wordTrace_append hprefix tailTrace_1243728
  have hstable : (prefixWord ++ tailWord_1243728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243728).length < 2 ^ (prefixWord ++ tailWord_1243728).sum := by decide
  have hdescent : baseEnd_1243728 < baseStart_1243728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243752 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1243752 : Nat := 118140960795 + 1243752 * 2 ^ 59
def prefixEnd_1243752 : Nat := 4983230072969 + 3 ^ 40 * 1243752 * 2
def baseEnd_1243752 : Nat := 212880863663641016093365

theorem tailTrace_1243752 : CollatzResearch.WordTrace tailWord_1243752 prefixEnd_1243752 212880863663641016093365 := by
  unfold tailWord_1243752
  simp only [CollatzResearch.WordTrace]
  refine ⟨22681681095053197387706755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30242241460070929850275673 22681681095053197387706755)
  ·
    refine ⟨34022521642579796081560133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22681681095053197387706755 34022521642579796081560133)
    ·
      refine ⟨6379222807983711765292525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34022521642579796081560133 6379222807983711765292525)
      ·
        refine ⟨2392208552993891911984697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6379222807983711765292525 2392208552993891911984697)
        ·
          refine ⟨1794156414745418933988523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2392208552993891911984697 1794156414745418933988523)
          ·
            refine ⟨2691234622118128400982785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794156414745418933988523 2691234622118128400982785)
            ·
              refine ⟨2018425966588596300737089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691234622118128400982785 2018425966588596300737089)
              ·
                refine ⟨1513819474941447225552817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018425966588596300737089 1513819474941447225552817)
                ·
                  refine ⟨1135364606206085419164613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513819474941447225552817 1135364606206085419164613)
                  ·
                    refine ⟨212880863663641016093365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1135364606206085419164613 212880863663641016093365)
                    ·
                      rfl

theorem cell23_1243752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1243752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243752 prefixEnd_1243752 := by exact prefixLift 1243752
  have htrace : WordTrace (prefixWord ++ tailWord_1243752) baseStart_1243752 baseEnd_1243752 := by
    simpa [prefixWord, tailWord_1243752, baseEnd_1243752] using wordTrace_append hprefix tailTrace_1243752
  have hstable : (prefixWord ++ tailWord_1243752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243752).length < 2 ^ (prefixWord ++ tailWord_1243752).sum := by decide
  have hdescent : baseEnd_1243752 < baseStart_1243752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243759 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 1, 2, 2]
def baseStart_1243759 : Nat := 118140960795 + 1243759 * 2 ^ 59
def prefixEnd_1243759 : Nat := 4983230072969 + 3 ^ 40 * 1243759 * 2
def baseEnd_1243759 : Nat := 638646185355504520892563

theorem tailTrace_1243759 : CollatzResearch.WordTrace tailWord_1243759 prefixEnd_1243759 638646185355504520892563 := by
  unfold tailWord_1243759
  simp only [CollatzResearch.WordTrace]
  refine ⟨45363617501081034970918331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30242411667387356647278887 45363617501081034970918331)
  ·
    refine ⟨68045426251621552456377497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45363617501081034970918331 68045426251621552456377497)
    ·
      refine ⟨51034069688716164342283123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68045426251621552456377497 51034069688716164342283123)
      ·
        refine ⟨76551104533074246513424685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51034069688716164342283123 76551104533074246513424685)
        ·
          refine ⟨28706664199902842442534257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76551104533074246513424685 28706664199902842442534257)
          ·
            refine ⟨21529998149927131831900693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28706664199902842442534257 21529998149927131831900693)
            ·
              refine ⟨1009218663277834304620345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21529998149927131831900693 1009218663277834304620345)
              ·
                refine ⟨756913997458375728465259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009218663277834304620345 756913997458375728465259)
                ·
                  refine ⟨1135370996187563592697889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756913997458375728465259 1135370996187563592697889)
                  ·
                    refine ⟨851528247140672694523417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1135370996187563592697889 851528247140672694523417)
                    ·
                      refine ⟨638646185355504520892563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851528247140672694523417 638646185355504520892563)
                      ·
                        rfl

theorem cell23_1243759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 2, 2].length) (baseStart_1243759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243759 prefixEnd_1243759 := by exact prefixLift 1243759
  have htrace : WordTrace (prefixWord ++ tailWord_1243759) baseStart_1243759 baseEnd_1243759 := by
    simpa [prefixWord, tailWord_1243759, baseEnd_1243759] using wordTrace_append hprefix tailTrace_1243759
  have hstable : (prefixWord ++ tailWord_1243759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243759).length < 2 ^ (prefixWord ++ tailWord_1243759).sum := by decide
  have hdescent : baseEnd_1243759 < baseStart_1243759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243765 : List Nat := [1, 3, 4, 2, 2, 2, 1, 8]
def baseStart_1243765 : Nat := 118140960795 + 1243765 * 2 ^ 59
def prefixEnd_1243765 : Nat := 4983230072969 + 3 ^ 40 * 1243765 * 2
def baseEnd_1243765 : Nat := 23653676527386351756205

theorem tailTrace_1243765 : CollatzResearch.WordTrace tailWord_1243765 prefixEnd_1243765 23653676527386351756205 := by
  unfold tailWord_1243765
  simp only [CollatzResearch.WordTrace]
  refine ⟨45363836339059297995636749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30242557559372865330424499 45363836339059297995636749)
  ·
    refine ⟨17011438627147236748363781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45363836339059297995636749 17011438627147236748363781)
    ·
      refine ⟨3189644742590106890318209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17011438627147236748363781 3189644742590106890318209)
      ·
        refine ⟨2392233556942580167738657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189644742590106890318209 2392233556942580167738657)
        ·
          refine ⟨1794175167706935125803993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2392233556942580167738657 1794175167706935125803993)
          ·
            refine ⟨1345631375780201344352995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794175167706935125803993 1345631375780201344352995)
            ·
              refine ⟨2018447063670302016529493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345631375780201344352995 2018447063670302016529493)
              ·
                refine ⟨23653676527386351756205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2018447063670302016529493 23653676527386351756205)
                ·
                  rfl

theorem cell23_1243765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 8].length) (baseStart_1243765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243765 prefixEnd_1243765 := by exact prefixLift 1243765
  have htrace : WordTrace (prefixWord ++ tailWord_1243765) baseStart_1243765 baseEnd_1243765 := by
    simpa [prefixWord, tailWord_1243765, baseEnd_1243765] using wordTrace_append hprefix tailTrace_1243765
  have hstable : (prefixWord ++ tailWord_1243765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243765).length < 2 ^ (prefixWord ++ tailWord_1243765).sum := by decide
  have hdescent : baseEnd_1243765 < baseStart_1243765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243785 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 1, 3, 2]
def baseStart_1243785 : Nat := 118140960795 + 1243785 * 2 ^ 59
def prefixEnd_1243785 : Nat := 4983230072969 + 3 ^ 40 * 1243785 * 2
def baseEnd_1243785 : Nat := 638659535852521419167443

theorem tailTrace_1243785 : CollatzResearch.WordTrace tailWord_1243785 prefixEnd_1243785 638659535852521419167443 := by
  unfold tailWord_1243785
  simp only [CollatzResearch.WordTrace]
  refine ⟨45364565798986841411364809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30243043865991227607576539 45364565798986841411364809)
  ·
    refine ⟨34023424349240131058523607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45364565798986841411364809 34023424349240131058523607)
    ·
      refine ⟨51035136523860196587785411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34023424349240131058523607 51035136523860196587785411)
      ·
        refine ⟨76552704785790294881678117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51035136523860196587785411 76552704785790294881678117)
        ·
          refine ⟨14353632147335680290314647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76552704785790294881678117 14353632147335680290314647)
          ·
            refine ⟨21530448221003520435471971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14353632147335680290314647 21530448221003520435471971)
            ·
              refine ⟨32295672331505280653207957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21530448221003520435471971 32295672331505280653207957)
              ·
                refine ⟨1513859640539310030619123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32295672331505280653207957 1513859640539310030619123)
                ·
                  refine ⟨2270789460808965045928685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513859640539310030619123 2270789460808965045928685)
                  ·
                    refine ⟨851546047803361892223257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2270789460808965045928685 851546047803361892223257)
                    ·
                      refine ⟨638659535852521419167443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851546047803361892223257 638659535852521419167443)
                      ·
                        rfl

theorem cell23_1243785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 3, 2].length) (baseStart_1243785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243785 prefixEnd_1243785 := by exact prefixLift 1243785
  have htrace : WordTrace (prefixWord ++ tailWord_1243785) baseStart_1243785 baseEnd_1243785 := by
    simpa [prefixWord, tailWord_1243785, baseEnd_1243785] using wordTrace_append hprefix tailTrace_1243785
  have hstable : (prefixWord ++ tailWord_1243785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243785).length < 2 ^ (prefixWord ++ tailWord_1243785).sum := by decide
  have hdescent : baseEnd_1243785 < baseStart_1243785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243801 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_1243801 : Nat := 118140960795 + 1243801 * 2 ^ 59
def prefixEnd_1243801 : Nat := 4983230072969 + 3 ^ 40 * 1243801 * 2
def baseEnd_1243801 : Nat := 638667751542993356567369

theorem tailTrace_1243801 : CollatzResearch.WordTrace tailWord_1243801 prefixEnd_1243801 638667751542993356567369 := by
  unfold tailWord_1243801
  simp only [CollatzResearch.WordTrace]
  refine ⟨45365149366928876143947257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30243432911285917429298171 45365149366928876143947257)
  ·
    refine ⟨34023862025196657107960443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45365149366928876143947257 34023862025196657107960443)
    ·
      refine ⟨51035793037794985661940665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34023862025196657107960443 51035793037794985661940665)
      ·
        refine ⟨38276844778346239246455499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51035793037794985661940665 38276844778346239246455499)
        ·
          refine ⟨57415267167519358869683249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38276844778346239246455499 57415267167519358869683249)
          ·
            refine ⟨43061450375639519152262437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57415267167519358869683249 43061450375639519152262437)
            ·
              refine ⟨8074021945432409841049207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43061450375639519152262437 8074021945432409841049207)
              ·
                refine ⟨12111032918148614761573811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074021945432409841049207 12111032918148614761573811)
                ·
                  refine ⟨18166549377222922142360717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12111032918148614761573811 18166549377222922142360717)
                  ·
                    refine ⟨6812456016458595803385269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18166549377222922142360717 6812456016458595803385269)
                    ·
                      refine ⟨638667751542993356567369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6812456016458595803385269 638667751542993356567369)
                      ·
                        rfl

theorem cell23_1243801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_1243801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243801 prefixEnd_1243801 := by exact prefixLift 1243801
  have htrace : WordTrace (prefixWord ++ tailWord_1243801) baseStart_1243801 baseEnd_1243801 := by
    simpa [prefixWord, tailWord_1243801, baseEnd_1243801] using wordTrace_append hprefix tailTrace_1243801
  have hstable : (prefixWord ++ tailWord_1243801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243801).length < 2 ^ (prefixWord ++ tailWord_1243801).sum := by decide
  have hdescent : baseEnd_1243801 < baseStart_1243801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243809 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1243809 : Nat := 118140960795 + 1243809 * 2 ^ 59
def prefixEnd_1243809 : Nat := 4983230072969 + 3 ^ 40 * 1243809 * 2
def baseEnd_1243809 : Nat := 638671859388229325267333

theorem tailTrace_1243809 : CollatzResearch.WordTrace tailWord_1243809 prefixEnd_1243809 638671859388229325267333 := by
  unfold tailWord_1243809
  simp only [CollatzResearch.WordTrace]
  refine ⟨45365441150899893510238481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30243627433933262340158987 45365441150899893510238481)
  ·
    refine ⟨34024080863174920132678861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45365441150899893510238481 34024080863174920132678861)
    ·
      refine ⟨12759030323690595049754573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34024080863174920132678861 12759030323690595049754573)
      ·
        refine ⟨4784636371383973143657965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12759030323690595049754573 4784636371383973143657965)
        ·
          refine ⟨1794238639268989928871737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4784636371383973143657965 1794238639268989928871737)
          ·
            refine ⟨1345678979451742446653803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794238639268989928871737 1345678979451742446653803)
            ·
              refine ⟨2018518469177613669980705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345678979451742446653803 2018518469177613669980705)
              ·
                refine ⟨1513888851883210252485529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018518469177613669980705 1513888851883210252485529)
                ·
                  refine ⟨1135416638912407689364147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513888851883210252485529 1135416638912407689364147)
                  ·
                    refine ⟨1703124958368611534046221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1135416638912407689364147 1703124958368611534046221)
                    ·
                      refine ⟨638671859388229325267333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703124958368611534046221 638671859388229325267333)
                      ·
                        rfl

theorem cell23_1243809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1243809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243809 prefixEnd_1243809 := by exact prefixLift 1243809
  have htrace : WordTrace (prefixWord ++ tailWord_1243809) baseStart_1243809 baseEnd_1243809 := by
    simpa [prefixWord, tailWord_1243809, baseEnd_1243809] using wordTrace_append hprefix tailTrace_1243809
  have hstable : (prefixWord ++ tailWord_1243809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243809).length < 2 ^ (prefixWord ++ tailWord_1243809).sum := by decide
  have hdescent : baseEnd_1243809 < baseStart_1243809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243838 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_1243838 : Nat := 118140960795 + 1243838 * 2 ^ 59
def prefixEnd_1243838 : Nat := 4983230072969 + 3 ^ 40 * 1243838 * 2
def baseEnd_1243838 : Nat := 70965194480801079089411

theorem tailTrace_1243838 : CollatzResearch.WordTrace tailWord_1243838 prefixEnd_1243838 70965194480801079089411 := by
  unfold tailWord_1243838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670812358474353932880521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30244332578529887642029445 5670812358474353932880521)
  ·
    refine ⟨4253109268855765449660391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5670812358474353932880521 4253109268855765449660391)
    ·
      refine ⟨6379663903283648174490587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253109268855765449660391 6379663903283648174490587)
      ·
        refine ⟨9569495854925472261735881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6379663903283648174490587 9569495854925472261735881)
        ·
          refine ⟨7177121891194104196301911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9569495854925472261735881 7177121891194104196301911)
          ·
            refine ⟨10765682836791156294452867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177121891194104196301911 10765682836791156294452867)
            ·
              refine ⟨16148524255186734441679301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10765682836791156294452867 16148524255186734441679301)
              ·
                refine ⟨3027848297847512707814869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16148524255186734441679301 3027848297847512707814869)
                ·
                  refine ⟨70965194480801079089411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3027848297847512707814869 70965194480801079089411)
                  ·
                    rfl

theorem cell23_1243838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_1243838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243838 prefixEnd_1243838 := by exact prefixLift 1243838
  have htrace : WordTrace (prefixWord ++ tailWord_1243838) baseStart_1243838 baseEnd_1243838 := by
    simpa [prefixWord, tailWord_1243838, baseEnd_1243838] using wordTrace_append hprefix tailTrace_1243838
  have hstable : (prefixWord ++ tailWord_1243838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243838).length < 2 ^ (prefixWord ++ tailWord_1243838).sum := by decide
  have hdescent : baseEnd_1243838 < baseStart_1243838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243888 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_1243888 : Nat := 118140960795 + 1243888 * 2 ^ 59
def prefixEnd_1243888 : Nat := 4983230072969 + 3 ^ 40 * 1243888 * 2
def baseEnd_1243888 : Nat := 638712424359934516179469

theorem tailTrace_1243888 : CollatzResearch.WordTrace tailWord_1243888 prefixEnd_1243888 638712424359934516179469 := by
  unfold tailWord_1243888
  simp only [CollatzResearch.WordTrace]
  refine ⟨22684161258806845001182159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30245548345075793334909545 22684161258806845001182159)
  ·
    refine ⟨34026241888210267501773239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22684161258806845001182159 34026241888210267501773239)
    ·
      refine ⟨51039362832315401252659859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34026241888210267501773239 51039362832315401252659859)
      ·
        refine ⟨76559044248473101878989789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51039362832315401252659859 76559044248473101878989789)
        ·
          refine ⟨28709641593177413204621171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76559044248473101878989789 28709641593177413204621171)
          ·
            refine ⟨43064462389766119806931757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28709641593177413204621171 43064462389766119806931757)
            ·
              refine ⟨16149173396162294927599409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43064462389766119806931757 16149173396162294927599409)
              ·
                refine ⟨12111880047121721195699557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16149173396162294927599409 12111880047121721195699557)
                ·
                  refine ⟨2270977508835322724193667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12111880047121721195699557 2270977508835322724193667)
                  ·
                    refine ⟨3406466263252984086290501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2270977508835322724193667 3406466263252984086290501)
                    ·
                      refine ⟨638712424359934516179469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3406466263252984086290501 638712424359934516179469)
                      ·
                        rfl

theorem cell23_1243888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_1243888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243888 prefixEnd_1243888 := by exact prefixLift 1243888
  have htrace : WordTrace (prefixWord ++ tailWord_1243888) baseStart_1243888 baseEnd_1243888 := by
    simpa [prefixWord, tailWord_1243888, baseEnd_1243888] using wordTrace_append hprefix tailTrace_1243888
  have hstable : (prefixWord ++ tailWord_1243888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243888).length < 2 ^ (prefixWord ++ tailWord_1243888).sum := by decide
  have hdescent : baseEnd_1243888 < baseStart_1243888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243902 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1243902 : Nat := 118140960795 + 1243902 * 2 ^ 59
def prefixEnd_1243902 : Nat := 4983230072969 + 3 ^ 40 * 1243902 * 2
def baseEnd_1243902 : Nat := 212906537696365820468135

theorem tailTrace_1243902 : CollatzResearch.WordTrace tailWord_1243902 prefixEnd_1243902 212906537696365820468135 := by
  unfold tailWord_1243902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671104142445371299171745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30245888759708646928915973 5671104142445371299171745)
  ·
    refine ⟨4253328106834028474378809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5671104142445371299171745 4253328106834028474378809)
    ·
      refine ⟨3189996080125521355784107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4253328106834028474378809 3189996080125521355784107)
      ·
        refine ⟨4784994120188282033676161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189996080125521355784107 4784994120188282033676161)
        ·
          refine ⟨3588745590141211525257121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784994120188282033676161 3588745590141211525257121)
          ·
            refine ⟨2691559192605908643942841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3588745590141211525257121 2691559192605908643942841)
            ·
              refine ⟨2018669394454431482957131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691559192605908643942841 2018669394454431482957131)
              ·
                refine ⟨3028004091681647224435697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018669394454431482957131 3028004091681647224435697)
                ·
                  refine ⟨2271003068761235418326773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028004091681647224435697 2271003068761235418326773)
                  ·
                    refine ⟨212906537696365820468135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2271003068761235418326773 212906537696365820468135)
                    ·
                      rfl

theorem cell23_1243902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1243902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243902 prefixEnd_1243902 := by exact prefixLift 1243902
  have htrace : WordTrace (prefixWord ++ tailWord_1243902) baseStart_1243902 baseEnd_1243902 := by
    simpa [prefixWord, tailWord_1243902, baseEnd_1243902] using wordTrace_append hprefix tailTrace_1243902
  have hstable : (prefixWord ++ tailWord_1243902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243902).length < 2 ^ (prefixWord ++ tailWord_1243902).sum := by decide
  have hdescent : baseEnd_1243902 < baseStart_1243902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243905 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_1243905 : Nat := 118140960795 + 1243905 * 2 ^ 59
def prefixEnd_1243905 : Nat := 4983230072969 + 3 ^ 40 * 1243905 * 2
def baseEnd_1243905 : Nat := 638721153531060949666891

theorem tailTrace_1243905 : CollatzResearch.WordTrace tailWord_1243905 prefixEnd_1243905 638721153531060949666891 := by
  unfold tailWord_1243905
  simp only [CollatzResearch.WordTrace]
  refine ⟨45368942558552101905733169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30245961705701401270488779 45368942558552101905733169)
  ·
    refine ⟨34026706918914076429299877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45368942558552101905733169 34026706918914076429299877)
    ·
      refine ⟨6380007547296389330493727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34026706918914076429299877 6380007547296389330493727)
      ·
        refine ⟨9570011320944583995740591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6380007547296389330493727 9570011320944583995740591)
        ·
          refine ⟨14355016981416875993610887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9570011320944583995740591 14355016981416875993610887)
          ·
            refine ⟨21532525472125313990416331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14355016981416875993610887 21532525472125313990416331)
            ·
              refine ⟨32298788208187970985624497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21532525472125313990416331 32298788208187970985624497)
              ·
                refine ⟨24224091156140978239218373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32298788208187970985624497 24224091156140978239218373)
                ·
                  refine ⟨4542017091776433419853445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24224091156140978239218373 4542017091776433419853445)
                  ·
                    refine ⟨851628204708081266222521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4542017091776433419853445 851628204708081266222521)
                    ·
                      refine ⟨638721153531060949666891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851628204708081266222521 638721153531060949666891)
                      ·
                        rfl

theorem cell23_1243905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_1243905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243905 prefixEnd_1243905 := by exact prefixLift 1243905
  have htrace : WordTrace (prefixWord ++ tailWord_1243905) baseStart_1243905 baseEnd_1243905 := by
    simpa [prefixWord, tailWord_1243905, baseEnd_1243905] using wordTrace_append hprefix tailTrace_1243905
  have hstable : (prefixWord ++ tailWord_1243905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243905).length < 2 ^ (prefixWord ++ tailWord_1243905).sum := by decide
  have hdescent : baseEnd_1243905 < baseStart_1243905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243918 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1243918 : Nat := 118140960795 + 1243918 * 2 ^ 59
def prefixEnd_1243918 : Nat := 4983230072969 + 3 ^ 40 * 1243918 * 2
def baseEnd_1243918 : Nat := 638727828779569398804331

theorem tailTrace_1243918 : CollatzResearch.WordTrace tailWord_1243918 prefixEnd_1243918 638727828779569398804331 := by
  unfold tailWord_1243918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671177088438125640744551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30246277805003336750637605 5671177088438125640744551)
  ·
    refine ⟨8506765632657188461116827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671177088438125640744551 8506765632657188461116827)
    ·
      refine ⟨12760148448985782691675241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506765632657188461116827 12760148448985782691675241)
      ·
        refine ⟨9570111336739337018756431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12760148448985782691675241 9570111336739337018756431)
        ·
          refine ⟨14355167005109005528134647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9570111336739337018756431 14355167005109005528134647)
          ·
            refine ⟨21532750507663508292201971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14355167005109005528134647 21532750507663508292201971)
            ·
              refine ⟨32299125761495262438302957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21532750507663508292201971 32299125761495262438302957)
              ·
                refine ⟨12112172160560723414363609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32299125761495262438302957 12112172160560723414363609)
                ·
                  refine ⟨9084129120420542560772707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12112172160560723414363609 9084129120420542560772707)
                  ·
                    refine ⟨13626193680630813841159061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9084129120420542560772707 13626193680630813841159061)
                    ·
                      refine ⟨638727828779569398804331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13626193680630813841159061 638727828779569398804331)
                      ·
                        rfl

theorem cell23_1243918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1243918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243918 prefixEnd_1243918 := by exact prefixLift 1243918
  have htrace : WordTrace (prefixWord ++ tailWord_1243918) baseStart_1243918 baseEnd_1243918 := by
    simpa [prefixWord, tailWord_1243918, baseEnd_1243918] using wordTrace_append hprefix tailTrace_1243918
  have hstable : (prefixWord ++ tailWord_1243918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243918).length < 2 ^ (prefixWord ++ tailWord_1243918).sum := by decide
  have hdescent : baseEnd_1243918 < baseStart_1243918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243925 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1243925 : Nat := 118140960795 + 1243925 * 2 ^ 59
def prefixEnd_1243925 : Nat := 4983230072969 + 3 ^ 40 * 1243925 * 2
def baseEnd_1243925 : Nat := 638731423144150871416799

theorem tailTrace_1243925 : CollatzResearch.WordTrace tailWord_1243925 prefixEnd_1243925 638731423144150871416799 := by
  unfold tailWord_1243925
  simp only [CollatzResearch.WordTrace]
  refine ⟨45369672018479645321461229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30246448012319763547640819 45369672018479645321461229)
  ·
    refine ⟨17013627006929866995547961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45369672018479645321461229 17013627006929866995547961)
    ·
      refine ⟨12760220255197400246660971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17013627006929866995547961 12760220255197400246660971)
      ·
        refine ⟨19140330382796100369991457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12760220255197400246660971 19140330382796100369991457)
        ·
          refine ⟨14355247787097075277493593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19140330382796100369991457 14355247787097075277493593)
          ·
            refine ⟨10766435840322806458120195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14355247787097075277493593 10766435840322806458120195)
            ·
              refine ⟨16149653760484209687180293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10766435840322806458120195 16149653760484209687180293)
              ·
                refine ⟨3028060080090789316346305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16149653760484209687180293 3028060080090789316346305)
                ·
                  refine ⟨2271045060068091987259729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028060080090789316346305 2271045060068091987259729)
                  ·
                    refine ⟨1703283795051068990444797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2271045060068091987259729 1703283795051068990444797)
                    ·
                      refine ⟨638731423144150871416799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703283795051068990444797 638731423144150871416799)
                      ·
                        rfl

theorem cell23_1243925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1243925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243925 prefixEnd_1243925 := by exact prefixLift 1243925
  have htrace : WordTrace (prefixWord ++ tailWord_1243925) baseStart_1243925 baseEnd_1243925 := by
    simpa [prefixWord, tailWord_1243925, baseEnd_1243925] using wordTrace_append hprefix tailTrace_1243925
  have hstable : (prefixWord ++ tailWord_1243925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243925).length < 2 ^ (prefixWord ++ tailWord_1243925).sum := by decide
  have hdescent : baseEnd_1243925 < baseStart_1243925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243956 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_1243956 : Nat := 118140960795 + 1243956 * 2 ^ 59
def prefixEnd_1243956 : Nat := 4983230072969 + 3 ^ 40 * 1243956 * 2
def baseEnd_1243956 : Nat := 638747341044440250129157

theorem tailTrace_1243956 : CollatzResearch.WordTrace tailWord_1243956 prefixEnd_1243956 638747341044440250129157 := by
  unfold tailWord_1243956
  simp only [CollatzResearch.WordTrace]
  refine ⟨22685401340683668807919861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30247201787578225077226481 22685401340683668807919861)
  ·
    refine ⟨2126756375689093950742487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22685401340683668807919861 2126756375689093950742487)
    ·
      refine ⟨3190134563533640926113731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126756375689093950742487 3190134563533640926113731)
      ·
        refine ⟨4785201845300461389170597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190134563533640926113731 4785201845300461389170597)
        ·
          refine ⟨897225345993836510469487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4785201845300461389170597 897225345993836510469487)
          ·
            refine ⟨1345838018990754765704231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897225345993836510469487 1345838018990754765704231)
            ·
              refine ⟨2018757028486132148556347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345838018990754765704231 2018757028486132148556347)
              ·
                refine ⟨3028135542729198222834521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018757028486132148556347 3028135542729198222834521)
                ·
                  refine ⟨2271101657046898667125891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028135542729198222834521 2271101657046898667125891)
                  ·
                    refine ⟨3406652485570348000688837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271101657046898667125891 3406652485570348000688837)
                    ·
                      refine ⟨638747341044440250129157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3406652485570348000688837 638747341044440250129157)
                      ·
                        rfl

theorem cell23_1243956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_1243956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243956 prefixEnd_1243956 := by exact prefixLift 1243956
  have htrace : WordTrace (prefixWord ++ tailWord_1243956) baseStart_1243956 baseEnd_1243956 := by
    simpa [prefixWord, tailWord_1243956, baseEnd_1243956] using wordTrace_append hprefix tailTrace_1243956
  have hstable : (prefixWord ++ tailWord_1243956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243956).length < 2 ^ (prefixWord ++ tailWord_1243956).sum := by decide
  have hdescent : baseEnd_1243956 < baseStart_1243956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243966 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1243966 : Nat := 118140960795 + 1243966 * 2 ^ 59
def prefixEnd_1243966 : Nat := 4983230072969 + 3 ^ 40 * 1243966 * 2
def baseEnd_1243966 : Nat := 212917491950328403668037

theorem tailTrace_1243966 : CollatzResearch.WordTrace tailWord_1243966 prefixEnd_1243966 212917491950328403668037 := by
  unfold tailWord_1243966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671395926416388665462969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30247444940887406215802501 5671395926416388665462969)
  ·
    refine ⟨4253546944812291499097227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5671395926416388665462969 4253546944812291499097227)
    ·
      refine ⟨6380320417218437248645841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253546944812291499097227 6380320417218437248645841)
      ·
        refine ⟨4785240312913827936484381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6380320417218437248645841 4785240312913827936484381)
        ·
          refine ⟨1794465117342685476181643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4785240312913827936484381 1794465117342685476181643)
          ·
            refine ⟨2691697676014028214272465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794465117342685476181643 2691697676014028214272465)
            ·
              refine ⟨2018773257010521160704349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691697676014028214272465 2018773257010521160704349)
              ·
                refine ⟨757039971378945435264131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018773257010521160704349 757039971378945435264131)
                ·
                  refine ⟨1135559957068418152896197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757039971378945435264131 1135559957068418152896197)
                  ·
                    refine ⟨212917491950328403668037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1135559957068418152896197 212917491950328403668037)
                    ·
                      rfl

theorem cell23_1243966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1243966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243966 prefixEnd_1243966 := by exact prefixLift 1243966
  have htrace : WordTrace (prefixWord ++ tailWord_1243966) baseStart_1243966 baseEnd_1243966 := by
    simpa [prefixWord, tailWord_1243966, baseEnd_1243966] using wordTrace_append hprefix tailTrace_1243966
  have hstable : (prefixWord ++ tailWord_1243966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243966).length < 2 ^ (prefixWord ++ tailWord_1243966).sum := by decide
  have hdescent : baseEnd_1243966 < baseStart_1243966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243982 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_1243982 : Nat := 118140960795 + 1243982 * 2 ^ 59
def prefixEnd_1243982 : Nat := 4983230072969 + 3 ^ 40 * 1243982 * 2
def baseEnd_1243982 : Nat := 638760691541457148404037

theorem tailTrace_1243982 : CollatzResearch.WordTrace tailWord_1243982 prefixEnd_1243982 638760691541457148404037 := by
  unfold tailWord_1243982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671468872409143007035775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30247833986182096037524133 5671468872409143007035775)
  ·
    refine ⟨8507203308613714510553663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671468872409143007035775 8507203308613714510553663)
    ·
      refine ⟨12760804962920571765830495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8507203308613714510553663 12760804962920571765830495)
      ·
        refine ⟨19141207444380857648745743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12760804962920571765830495 19141207444380857648745743)
        ·
          refine ⟨28711811166571286473118615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19141207444380857648745743 28711811166571286473118615)
          ·
            refine ⟨43067716749856929709677923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28711811166571286473118615 43067716749856929709677923)
            ·
              refine ⟨64601575124785394564516885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43067716749856929709677923 64601575124785394564516885)
              ·
                refine ⟨3028198833974315370211729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64601575124785394564516885 3028198833974315370211729)
                ·
                  refine ⟨2271149125480736527658797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028198833974315370211729 2271149125480736527658797)
                  ·
                    refine ⟨851680922055276197872049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2271149125480736527658797 851680922055276197872049)
                    ·
                      refine ⟨638760691541457148404037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851680922055276197872049 638760691541457148404037)
                      ·
                        rfl

theorem cell23_1243982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_1243982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243982 prefixEnd_1243982 := by exact prefixLift 1243982
  have htrace : WordTrace (prefixWord ++ tailWord_1243982) baseStart_1243982 baseEnd_1243982 := by
    simpa [prefixWord, tailWord_1243982, baseEnd_1243982] using wordTrace_append hprefix tailTrace_1243982
  have hstable : (prefixWord ++ tailWord_1243982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243982).length < 2 ^ (prefixWord ++ tailWord_1243982).sum := by decide
  have hdescent : baseEnd_1243982 < baseStart_1243982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243989 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_1243989 : Nat := 118140960795 + 1243989 * 2 ^ 59
def prefixEnd_1243989 : Nat := 4983230072969 + 3 ^ 40 * 1243989 * 2
def baseEnd_1243989 : Nat := 638764285906038621016505

theorem tailTrace_1243989 : CollatzResearch.WordTrace tailWord_1243989 prefixEnd_1243989 638764285906038621016505 := by
  unfold tailWord_1243989
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372006290247784251791021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30248004193498522834527347 45372006290247784251791021)
  ·
    refine ⟨17014502358842919094421633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45372006290247784251791021 17014502358842919094421633)
    ·
      refine ⟨12760876769132189320816225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17014502358842919094421633 12760876769132189320816225)
      ·
        refine ⟨9570657576849141990612169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12760876769132189320816225 9570657576849141990612169)
        ·
          refine ⟨7177993182636856492959127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9570657576849141990612169 7177993182636856492959127)
          ·
            refine ⟨10766989773955284739438691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177993182636856492959127 10766989773955284739438691)
            ·
              refine ⟨16150484660932927109158037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10766989773955284739438691 16150484660932927109158037)
              ·
                refine ⟨757053968481230958241783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16150484660932927109158037 757053968481230958241783)
                ·
                  refine ⟨1135580952721846437362675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757053968481230958241783 1135580952721846437362675)
                  ·
                    refine ⟨1703371429082769656044013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1135580952721846437362675 1703371429082769656044013)
                    ·
                      refine ⟨638764285906038621016505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703371429082769656044013 638764285906038621016505)
                      ·
                        rfl

theorem cell23_1243989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_1243989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1243989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1243989 prefixEnd_1243989 := by exact prefixLift 1243989
  have htrace : WordTrace (prefixWord ++ tailWord_1243989) baseStart_1243989 baseEnd_1243989 := by
    simpa [prefixWord, tailWord_1243989, baseEnd_1243989] using wordTrace_append hprefix tailTrace_1243989
  have hstable : (prefixWord ++ tailWord_1243989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243989).length < 2 ^ (prefixWord ++ tailWord_1243989).sum := by decide
  have hdescent : baseEnd_1243989 < baseStart_1243989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244005 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_1244005 : Nat := 118140960795 + 1244005 * 2 ^ 59
def prefixEnd_1244005 : Nat := 4983230072969 + 3 ^ 40 * 1244005 * 2
def baseEnd_1244005 : Nat := 212924167198836852805477

theorem tailTrace_1244005 : CollatzResearch.WordTrace tailWord_1244005 prefixEnd_1244005 212924167198836852805477 := by
  unfold tailWord_1244005
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372589858189818984373469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30248393238793212656248979 45372589858189818984373469)
  ·
    refine ⟨17014721196821182119140051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45372589858189818984373469 17014721196821182119140051)
    ·
      refine ⟨25522081795231773178710077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17014721196821182119140051 25522081795231773178710077)
      ·
        refine ⟨9570780673211914942016279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25522081795231773178710077 9570780673211914942016279)
        ·
          refine ⟨14356171009817872413024419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9570780673211914942016279 14356171009817872413024419)
          ·
            refine ⟨21534256514726808619536629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14356171009817872413024419 21534256514726808619536629)
            ·
              refine ⟨2018836548255638308081559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21534256514726808619536629 2018836548255638308081559)
              ·
                refine ⟨3028254822383457462122339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018836548255638308081559 3028254822383457462122339)
                ·
                  refine ⟨4542382233575186193183509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028254822383457462122339 4542382233575186193183509)
                  ·
                    refine ⟨212924167198836852805477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4542382233575186193183509 212924167198836852805477)
                    ·
                      rfl

theorem cell23_1244005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_1244005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244005 prefixEnd_1244005 := by exact prefixLift 1244005
  have htrace : WordTrace (prefixWord ++ tailWord_1244005) baseStart_1244005 baseEnd_1244005 := by
    simpa [prefixWord, tailWord_1244005, baseEnd_1244005] using wordTrace_append hprefix tailTrace_1244005
  have hstable : (prefixWord ++ tailWord_1244005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244005).length < 2 ^ (prefixWord ++ tailWord_1244005).sum := by decide
  have hdescent : baseEnd_1244005 < baseStart_1244005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244012 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_1244012 : Nat := 118140960795 + 1244012 * 2 ^ 59
def prefixEnd_1244012 : Nat := 4983230072969 + 3 ^ 40 * 1244012 * 2
def baseEnd_1244012 : Nat := 638776095961092031028899

theorem tailTrace_1244012 : CollatzResearch.WordTrace tailWord_1244012 prefixEnd_1244012 638776095961092031028899 := by
  unfold tailWord_1244012
  simp only [CollatzResearch.WordTrace]
  refine ⟨22686422584582229589939145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30248563446109639453252193 22686422584582229589939145)
  ·
    refine ⟨17014816938436672192454359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22686422584582229589939145 17014816938436672192454359)
    ·
      refine ⟨25522225407655008288681539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17014816938436672192454359 25522225407655008288681539)
      ·
        refine ⟨38283338111482512433022309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25522225407655008288681539 38283338111482512433022309)
        ·
          refine ⟨7178125895902971081191683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38283338111482512433022309 7178125895902971081191683)
          ·
            refine ⟨10767188843854456621787525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7178125895902971081191683 10767188843854456621787525)
            ·
              refine ⟨2018847908222710616585161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10767188843854456621787525 2018847908222710616585161)
              ·
                refine ⟨1514135931167032962438871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018847908222710616585161 1514135931167032962438871)
                ·
                  refine ⟨2271203896750549443658307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514135931167032962438871 2271203896750549443658307)
                  ·
                    refine ⟨3406805845125824165487461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271203896750549443658307 3406805845125824165487461)
                    ·
                      refine ⟨638776095961092031028899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3406805845125824165487461 638776095961092031028899)
                      ·
                        rfl

theorem cell23_1244012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_1244012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244012 prefixEnd_1244012 := by exact prefixLift 1244012
  have htrace : WordTrace (prefixWord ++ tailWord_1244012) baseStart_1244012 baseEnd_1244012 := by
    simpa [prefixWord, tailWord_1244012, baseEnd_1244012] using wordTrace_append hprefix tailTrace_1244012
  have hstable : (prefixWord ++ tailWord_1244012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244012).length < 2 ^ (prefixWord ++ tailWord_1244012).sum := by decide
  have hdescent : baseEnd_1244012 < baseStart_1244012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244015 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_1244015 : Nat := 118140960795 + 1244015 * 2 ^ 59
def prefixEnd_1244015 : Nat := 4983230072969 + 3 ^ 40 * 1244015 * 2
def baseEnd_1244015 : Nat := 638777636403055519291385

theorem tailTrace_1244015 : CollatzResearch.WordTrace tailWord_1244015 prefixEnd_1244015 638777636403055519291385 := by
  unfold tailWord_1244015
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372954588153590692237499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30248636392102393794824999 45372954588153590692237499)
  ·
    refine ⟨68059431882230386038356249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45372954588153590692237499 68059431882230386038356249)
    ·
      refine ⟨51044573911672789528767187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68059431882230386038356249 51044573911672789528767187)
      ·
        refine ⟨76566860867509184293150781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51044573911672789528767187 76566860867509184293150781)
        ·
          refine ⟨28712572825315944109931543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76566860867509184293150781 28712572825315944109931543)
          ·
            refine ⟨43068859237973916164897315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28712572825315944109931543 43068859237973916164897315)
            ·
              refine ⟨64603288856960874247345973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43068859237973916164897315 64603288856960874247345973)
              ·
                refine ⟨6056558330340081960688685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64603288856960874247345973 6056558330340081960688685)
                ·
                  refine ⟨2271209373877530735258257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6056558330340081960688685 2271209373877530735258257)
                  ·
                    refine ⟨1703407030408148051443693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2271209373877530735258257 1703407030408148051443693)
                    ·
                      refine ⟨638777636403055519291385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703407030408148051443693 638777636403055519291385)
                      ·
                        rfl

theorem cell23_1244015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_1244015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244015 prefixEnd_1244015 := by exact prefixLift 1244015
  have htrace : WordTrace (prefixWord ++ tailWord_1244015) baseStart_1244015 baseEnd_1244015 := by
    simpa [prefixWord, tailWord_1244015, baseEnd_1244015] using wordTrace_append hprefix tailTrace_1244015
  have hstable : (prefixWord ++ tailWord_1244015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244015).length < 2 ^ (prefixWord ++ tailWord_1244015).sum := by decide
  have hdescent : baseEnd_1244015 < baseStart_1244015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244066 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1244066 : Nat := 118140960795 + 1244066 * 2 ^ 59
def prefixEnd_1244066 : Nat := 4983230072969 + 3 ^ 40 * 1244066 * 2
def baseEnd_1244066 : Nat := 638803823916434819753651

theorem tailTrace_1244066 : CollatzResearch.WordTrace tailWord_1244066 prefixEnd_1244066 638803823916434819753651 := by
  unfold tailWord_1244066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11343703677742206600586013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30249876473979217601562701 11343703677742206600586013)
  ·
    refine ⟨4253888879153327475219755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11343703677742206600586013 4253888879153327475219755)
    ·
      refine ⟨6380833318729991212829633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253888879153327475219755 6380833318729991212829633)
      ·
        refine ⟨4785624989047493409622225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6380833318729991212829633 4785624989047493409622225)
        ·
          refine ⟨3589218741785620057216669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4785624989047493409622225 3589218741785620057216669)
          ·
            refine ⟨1345957028169607521456251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3589218741785620057216669 1345957028169607521456251)
            ·
              refine ⟨2018935542254411282184377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345957028169607521456251 2018935542254411282184377)
              ·
                refine ⟨1514201656690808461638283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018935542254411282184377 1514201656690808461638283)
                ·
                  refine ⟨2271302485036212692457425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514201656690808461638283 2271302485036212692457425)
                  ·
                    refine ⟨1703476863777159519343069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2271302485036212692457425 1703476863777159519343069)
                    ·
                      refine ⟨638803823916434819753651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703476863777159519343069 638803823916434819753651)
                      ·
                        rfl

theorem cell23_1244066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1244066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244066 prefixEnd_1244066 := by exact prefixLift 1244066
  have htrace : WordTrace (prefixWord ++ tailWord_1244066) baseStart_1244066 baseEnd_1244066 := by
    simpa [prefixWord, tailWord_1244066, baseEnd_1244066] using wordTrace_append hprefix tailTrace_1244066
  have hstable : (prefixWord ++ tailWord_1244066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244066).length < 2 ^ (prefixWord ++ tailWord_1244066).sum := by decide
  have hdescent : baseEnd_1244066 < baseStart_1244066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244086 : List Nat := [5, 1, 4, 1, 2, 10]
def baseStart_1244086 : Nat := 118140960795 + 1244086 * 2 ^ 59
def prefixEnd_1244086 : Nat := 4983230072969 + 3 ^ 40 * 1244086 * 2
def baseEnd_1244086 : Nat := 2628864582426027742813

theorem tailTrace_1244086 : CollatzResearch.WordTrace tailWord_1244086 prefixEnd_1244086 2628864582426027742813 := by
  unfold tailWord_1244086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835971510681023113629507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30250362780597579878714741 2835971510681023113629507)
  ·
    refine ⟨4253957266021534670444261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835971510681023113629507 4253957266021534670444261)
    ·
      refine ⟨797616987379037750708299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4253957266021534670444261 797616987379037750708299)
      ·
        refine ⟨1196425481068556626062449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797616987379037750708299 1196425481068556626062449)
        ·
          refine ⟨897319110801417469546837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196425481068556626062449 897319110801417469546837)
          ·
            refine ⟨2628864582426027742813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 897319110801417469546837 2628864582426027742813)
            ·
              rfl

theorem cell23_1244086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 10].length) (baseStart_1244086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244086 prefixEnd_1244086 := by exact prefixLift 1244086
  have htrace : WordTrace (prefixWord ++ tailWord_1244086) baseStart_1244086 baseEnd_1244086 := by
    simpa [prefixWord, tailWord_1244086, baseEnd_1244086] using wordTrace_append hprefix tailTrace_1244086
  have hstable : (prefixWord ++ tailWord_1244086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244086).length < 2 ^ (prefixWord ++ tailWord_1244086).sum := by decide
  have hdescent : baseEnd_1244086 < baseStart_1244086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244155 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 4, 5]
def baseStart_1244155 : Nat := 118140960795 + 1244155 * 2 ^ 59
def prefixEnd_1244155 : Nat := 4983230072969 + 3 ^ 40 * 1244155 * 2
def baseEnd_1244155 : Nat := 212949841231561657180247

theorem tailTrace_1244155 : CollatzResearch.WordTrace tailWord_1244155 prefixEnd_1244155 212949841231561657180247 := by
  unfold tailWord_1244155
  simp only [CollatzResearch.WordTrace]
  refine ⟨45378060807646394602333919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30252040538430929734889279 45378060807646394602333919)
  ·
    refine ⟨68067091211469591903500879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45378060807646394602333919 68067091211469591903500879)
    ·
      refine ⟨102100636817204387855251319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68067091211469591903500879 102100636817204387855251319)
      ·
        refine ⟨153150955225806581782876979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102100636817204387855251319 153150955225806581782876979)
        ·
          refine ⟨229726432838709872674315469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153150955225806581782876979 229726432838709872674315469)
          ·
            refine ⟨86147412314516202252868301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229726432838709872674315469 86147412314516202252868301)
            ·
              refine ⟨32305279617943575844825613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86147412314516202252868301 32305279617943575844825613)
              ·
                refine ⟨12114479856728840941809605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32305279617943575844825613 12114479856728840941809605)
                ·
                  refine ⟨2271464973136657676589301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12114479856728840941809605 2271464973136657676589301)
                  ·
                    refine ⟨212949841231561657180247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2271464973136657676589301 212949841231561657180247)
                    ·
                      rfl

theorem cell23_1244155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 5].length) (baseStart_1244155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244155 prefixEnd_1244155 := by exact prefixLift 1244155
  have htrace : WordTrace (prefixWord ++ tailWord_1244155) baseStart_1244155 baseEnd_1244155 := by
    simpa [prefixWord, tailWord_1244155, baseEnd_1244155] using wordTrace_append hprefix tailTrace_1244155
  have hstable : (prefixWord ++ tailWord_1244155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244155).length < 2 ^ (prefixWord ++ tailWord_1244155).sum := by decide
  have hdescent : baseEnd_1244155 < baseStart_1244155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244165 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_1244165 : Nat := 118140960795 + 1244165 * 2 ^ 59
def prefixEnd_1244165 : Nat := 4983230072969 + 3 ^ 40 * 1244165 * 2
def baseEnd_1244165 : Nat := 638854658501229932415695

theorem tailTrace_1244165 : CollatzResearch.WordTrace tailWord_1244165 prefixEnd_1244165 638854658501229932415695 := by
  unfold tailWord_1244165
  simp only [CollatzResearch.WordTrace]
  refine ⟨45378425537610166310197949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30252283691740110873465299 45378425537610166310197949)
  ·
    refine ⟨17016909576603812366324231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45378425537610166310197949 17016909576603812366324231)
    ·
      refine ⟨25525364364905718549486347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17016909576603812366324231 25525364364905718549486347)
      ·
        refine ⟨38288046547358577824229521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25525364364905718549486347 38288046547358577824229521)
        ·
          refine ⟨28716034910518933368172141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38288046547358577824229521 28716034910518933368172141)
          ·
            refine ⟨10768513091444600013064553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28716034910518933368172141 10768513091444600013064553)
            ·
              refine ⟨8076384818583450009798415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10768513091444600013064553 8076384818583450009798415)
              ·
                refine ⟨12114577227875175014697623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8076384818583450009798415 12114577227875175014697623)
                ·
                  refine ⟨18171865841812762522046435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12114577227875175014697623 18171865841812762522046435)
                  ·
                    refine ⟨27257798762719143783069653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18171865841812762522046435 27257798762719143783069653)
                    ·
                      refine ⟨638854658501229932415695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27257798762719143783069653 638854658501229932415695)
                      ·
                        rfl

theorem cell23_1244165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_1244165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244165 prefixEnd_1244165 := by exact prefixLift 1244165
  have htrace : WordTrace (prefixWord ++ tailWord_1244165) baseStart_1244165 baseEnd_1244165 := by
    simpa [prefixWord, tailWord_1244165, baseEnd_1244165] using wordTrace_append hprefix tailTrace_1244165
  have hstable : (prefixWord ++ tailWord_1244165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244165).length < 2 ^ (prefixWord ++ tailWord_1244165).sum := by decide
  have hdescent : baseEnd_1244165 < baseStart_1244165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244232 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 6]
def baseStart_1244232 : Nat := 118140960795 + 1244232 * 2 ^ 59
def prefixEnd_1244232 : Nat := 4983230072969 + 3 ^ 40 * 1244232 * 2
def baseEnd_1244232 : Nat := 70987673522786796697543

theorem tailTrace_1244232 : CollatzResearch.WordTrace tailWord_1244232 prefixEnd_1244232 70987673522786796697543 := by
  unfold tailWord_1244232
  simp only [CollatzResearch.WordTrace]
  refine ⟨22690434614183718376443475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30253912818911624501924633 22690434614183718376443475)
  ·
    refine ⟨34035651921275577564665213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22690434614183718376443475 34035651921275577564665213)
    ·
      refine ⟨12763369470478341586749455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34035651921275577564665213 12763369470478341586749455)
      ·
        refine ⟨19145054205717512380124183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12763369470478341586749455 19145054205717512380124183)
        ·
          refine ⟨28717581308576268570186275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19145054205717512380124183 28717581308576268570186275)
          ·
            refine ⟨43076371962864402855279413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28717581308576268570186275 43076371962864402855279413)
            ·
              refine ⟨4038409871518537767682445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43076371962864402855279413 4038409871518537767682445)
              ·
                refine ⟨1514403701819451662880917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4038409871518537767682445 1514403701819451662880917)
                ·
                  refine ⟨70987673522786796697543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1514403701819451662880917 70987673522786796697543)
                  ·
                    rfl

theorem cell23_1244232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 6].length) (baseStart_1244232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244232 prefixEnd_1244232 := by exact prefixLift 1244232
  have htrace : WordTrace (prefixWord ++ tailWord_1244232) baseStart_1244232 baseEnd_1244232 := by
    simpa [prefixWord, tailWord_1244232, baseEnd_1244232] using wordTrace_append hprefix tailTrace_1244232
  have hstable : (prefixWord ++ tailWord_1244232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244232).length < 2 ^ (prefixWord ++ tailWord_1244232).sum := by decide
  have hdescent : baseEnd_1244232 < baseStart_1244232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244270 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1244270 : Nat := 118140960795 + 1244270 * 2 ^ 59
def prefixEnd_1244270 : Nat := 4983230072969 + 3 ^ 40 * 1244270 * 2
def baseEnd_1244270 : Nat := 212969524656650673867571

theorem tailTrace_1244270 : CollatzResearch.WordTrace tailWord_1244270 prefixEnd_1244270 212969524656650673867571 := by
  unfold tailWord_1244270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5672781900278721155346283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30254836801486512828513509 5672781900278721155346283)
  ·
    refine ⟨8509172850418081733019425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5672781900278721155346283 8509172850418081733019425)
    ·
      refine ⟨6381879637813561299764569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8509172850418081733019425 6381879637813561299764569)
      ·
        refine ⟨4786409728360170974823427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6381879637813561299764569 4786409728360170974823427)
        ·
          refine ⟨7179614592540256462235141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786409728360170974823427 7179614592540256462235141)
          ·
            refine ⟨1346177736101298086669089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7179614592540256462235141 1346177736101298086669089)
            ·
              refine ⟨1009633302075973565001817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346177736101298086669089 1009633302075973565001817)
              ·
                refine ⟨757224976556980173751363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009633302075973565001817 757224976556980173751363)
                ·
                  refine ⟨1135837464835470260627045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757224976556980173751363 1135837464835470260627045)
                  ·
                    refine ⟨212969524656650673867571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1135837464835470260627045 212969524656650673867571)
                    ·
                      rfl

theorem cell23_1244270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1244270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244270 prefixEnd_1244270 := by exact prefixLift 1244270
  have htrace : WordTrace (prefixWord ++ tailWord_1244270) baseStart_1244270 baseEnd_1244270 := by
    simpa [prefixWord, tailWord_1244270, baseEnd_1244270] using wordTrace_append hprefix tailTrace_1244270
  have hstable : (prefixWord ++ tailWord_1244270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244270).length < 2 ^ (prefixWord ++ tailWord_1244270).sum := by decide
  have hdescent : baseEnd_1244270 < baseStart_1244270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244316 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1244316 : Nat := 118140960795 + 1244316 * 2 ^ 59
def prefixEnd_1244316 : Nat := 4983230072969 + 3 ^ 40 * 1244316 * 2
def baseEnd_1244316 : Nat := 638932194080058841627501

theorem tailTrace_1244316 : CollatzResearch.WordTrace tailWord_1244316 prefixEnd_1244316 638932194080058841627501 := by
  unfold tailWord_1244316
  simp only [CollatzResearch.WordTrace]
  refine ⟨22691966480031559549472401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30255955306708746065963201 22691966480031559549472401)
  ·
    refine ⟨17018974860023669662104301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22691966480031559549472401 17018974860023669662104301)
    ·
      refine ⟨6382115572508876123289113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17018974860023669662104301 6382115572508876123289113)
      ·
        refine ⟨4786586679381657092466835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6382115572508876123289113 4786586679381657092466835)
        ·
          refine ⟨7179880019072485638700253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786586679381657092466835 7179880019072485638700253)
          ·
            refine ⟨2692455007152182114512595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7179880019072485638700253 2692455007152182114512595)
            ·
              refine ⟨4038682510728273171768893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692455007152182114512595 4038682510728273171768893)
              ·
                refine ⟨1514505941523102439413335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4038682510728273171768893 1514505941523102439413335)
                ·
                  refine ⟨2271758912284653659120003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514505941523102439413335 2271758912284653659120003)
                  ·
                    refine ⟨3407638368426980488680005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271758912284653659120003 3407638368426980488680005)
                    ·
                      refine ⟨638932194080058841627501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3407638368426980488680005 638932194080058841627501)
                      ·
                        rfl

theorem cell23_1244316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1244316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244316 prefixEnd_1244316 := by exact prefixLift 1244316
  have htrace : WordTrace (prefixWord ++ tailWord_1244316) baseStart_1244316 baseEnd_1244316 := by
    simpa [prefixWord, tailWord_1244316, baseEnd_1244316] using wordTrace_append hprefix tailTrace_1244316
  have hstable : (prefixWord ++ tailWord_1244316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244316).length < 2 ^ (prefixWord ++ tailWord_1244316).sum := by decide
  have hdescent : baseEnd_1244316 < baseStart_1244316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244353 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1244353 : Nat := 118140960795 + 1244353 * 2 ^ 59
def prefixEnd_1244353 : Nat := 4983230072969 + 3 ^ 40 * 1244353 * 2
def baseEnd_1244353 : Nat := 638951192864275196864831

theorem tailTrace_1244353 : CollatzResearch.WordTrace tailWord_1244353 prefixEnd_1244353 638951192864275196864831 := by
  unfold tailWord_1244353
  simp only [CollatzResearch.WordTrace]
  refine ⟨45385282460929074418041713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30256854973952716278694475 45385282460929074418041713)
  ·
    refine ⟨34038961845696805813531285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45385282460929074418041713 34038961845696805813531285)
    ·
      refine ⟨1595576336517037772509279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34038961845696805813531285 1595576336517037772509279)
      ·
        refine ⟨2393364504775556658763919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595576336517037772509279 2393364504775556658763919)
        ·
          refine ⟨3590046757163334988145879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393364504775556658763919 3590046757163334988145879)
          ·
            refine ⟨5385070135745002482218819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590046757163334988145879 5385070135745002482218819)
            ·
              refine ⟨8077605203617503723328229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385070135745002482218819 8077605203617503723328229)
              ·
                refine ⟨1514550975678281948124043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8077605203617503723328229 1514550975678281948124043)
                ·
                  refine ⟨2271826463517422922186065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514550975678281948124043 2271826463517422922186065)
                  ·
                    refine ⟨1703869847638067191639549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2271826463517422922186065 1703869847638067191639549)
                    ·
                      refine ⟨638951192864275196864831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703869847638067191639549 638951192864275196864831)
                      ·
                        rfl

theorem cell23_1244353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1244353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244353 prefixEnd_1244353 := by exact prefixLift 1244353
  have htrace : WordTrace (prefixWord ++ tailWord_1244353) baseStart_1244353 baseEnd_1244353 := by
    simpa [prefixWord, tailWord_1244353, baseEnd_1244353] using wordTrace_append hprefix tailTrace_1244353
  have hstable : (prefixWord ++ tailWord_1244353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244353).length < 2 ^ (prefixWord ++ tailWord_1244353).sum := by decide
  have hdescent : baseEnd_1244353 < baseStart_1244353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244359 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_1244359 : Nat := 118140960795 + 1244359 * 2 ^ 59
def prefixEnd_1244359 : Nat := 4983230072969 + 3 ^ 40 * 1244359 * 2
def baseEnd_1244359 : Nat := 638954273748202173389803

theorem tailTrace_1244359 : CollatzResearch.WordTrace tailWord_1244359 prefixEnd_1244359 638954273748202173389803 := by
  unfold tailWord_1244359
  simp only [CollatzResearch.WordTrace]
  refine ⟨45385501298907337442760131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30257000865938224961840087 45385501298907337442760131)
  ·
    refine ⟨68078251948361006164140197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45385501298907337442760131 68078251948361006164140197)
    ·
      refine ⟨12764672240317688655776287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68078251948361006164140197 12764672240317688655776287)
      ·
        refine ⟨19147008360476532983664431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764672240317688655776287 19147008360476532983664431)
        ·
          refine ⟨28720512540714799475496647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19147008360476532983664431 28720512540714799475496647)
          ·
            refine ⟨43080768811072199213244971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28720512540714799475496647 43080768811072199213244971)
            ·
              refine ⟨64621153216608298819867457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43080768811072199213244971 64621153216608298819867457)
              ·
                refine ⟨48465864912456224114900593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64621153216608298819867457 48465864912456224114900593)
                ·
                  refine ⟨36349398684342168086175445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48465864912456224114900593 36349398684342168086175445)
                  ·
                    refine ⟨851939031664269564519737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36349398684342168086175445 851939031664269564519737)
                    ·
                      refine ⟨638954273748202173389803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851939031664269564519737 638954273748202173389803)
                      ·
                        rfl

theorem cell23_1244359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_1244359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244359 prefixEnd_1244359 := by exact prefixLift 1244359
  have htrace : WordTrace (prefixWord ++ tailWord_1244359) baseStart_1244359 baseEnd_1244359 := by
    simpa [prefixWord, tailWord_1244359, baseEnd_1244359] using wordTrace_append hprefix tailTrace_1244359
  have hstable : (prefixWord ++ tailWord_1244359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244359).length < 2 ^ (prefixWord ++ tailWord_1244359).sum := by decide
  have hdescent : baseEnd_1244359 < baseStart_1244359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244404 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1244404 : Nat := 118140960795 + 1244404 * 2 ^ 59
def prefixEnd_1244404 : Nat := 4983230072969 + 3 ^ 40 * 1244404 * 2
def baseEnd_1244404 : Nat := 638977380377654497327097

theorem tailTrace_1244404 : CollatzResearch.WordTrace tailWord_1244404 prefixEnd_1244404 638977380377654497327097 := by
  unfold tailWord_1244404
  simp only [CollatzResearch.WordTrace]
  refine ⟨22693571291872155064074133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30258095055829540085432177 22693571291872155064074133)
  ·
    refine ⟨1063761154306507268628475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22693571291872155064074133 1063761154306507268628475)
    ·
      refine ⟨1595641731459760902942713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1063761154306507268628475 1595641731459760902942713)
      ·
        refine ⟨1196731298594820677207035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1595641731459760902942713 1196731298594820677207035)
        ·
          refine ⟨1795096947892231015810553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196731298594820677207035 1795096947892231015810553)
          ·
            refine ⟨1346322710919173261857915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1795096947892231015810553 1346322710919173261857915)
            ·
              refine ⟨2019484066378759892786873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346322710919173261857915 2019484066378759892786873)
              ·
                refine ⟨1514613049784069919590155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2019484066378759892786873 1514613049784069919590155)
                ·
                  refine ⟨2271919574676104879385233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514613049784069919590155 2271919574676104879385233)
                  ·
                    refine ⟨1703939681007078659538925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2271919574676104879385233 1703939681007078659538925)
                    ·
                      refine ⟨638977380377654497327097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1703939681007078659538925 638977380377654497327097)
                      ·
                        rfl

theorem cell23_1244404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1244404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244404 prefixEnd_1244404 := by exact prefixLift 1244404
  have htrace : WordTrace (prefixWord ++ tailWord_1244404) baseStart_1244404 baseEnd_1244404 := by
    simpa [prefixWord, tailWord_1244404, baseEnd_1244404] using wordTrace_append hprefix tailTrace_1244404
  have hstable : (prefixWord ++ tailWord_1244404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244404).length < 2 ^ (prefixWord ++ tailWord_1244404).sum := by decide
  have hdescent : baseEnd_1244404 < baseStart_1244404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244432 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_1244432 : Nat := 118140960795 + 1244432 * 2 ^ 59
def prefixEnd_1244432 : Nat := 4983230072969 + 3 ^ 40 * 1244432 * 2
def baseEnd_1244432 : Nat := 638991757835980387776967

theorem tailTrace_1244432 : CollatzResearch.WordTrace tailWord_1244432 prefixEnd_1244432 638991757835980387776967 := by
  unfold tailWord_1244432
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694081913821435455083775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30258775885095247273445033 22694081913821435455083775)
  ·
    refine ⟨34041122870732153182625663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22694081913821435455083775 34041122870732153182625663)
    ·
      refine ⟨51061684306098229773938495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34041122870732153182625663 51061684306098229773938495)
      ·
        refine ⟨76592526459147344660907743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51061684306098229773938495 76592526459147344660907743)
        ·
          refine ⟨114888789688721016991361615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76592526459147344660907743 114888789688721016991361615)
          ·
            refine ⟨172333184533081525487042423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114888789688721016991361615 172333184533081525487042423)
            ·
              refine ⟨258499776799622288230563635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172333184533081525487042423 258499776799622288230563635)
              ·
                refine ⟨387749665199433432345845453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258499776799622288230563635 387749665199433432345845453)
                ·
                  refine ⟨145406124449787537129692045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387749665199433432345845453 145406124449787537129692045)
                  ·
                    refine ⟨54527296668670326423634517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145406124449787537129692045 54527296668670326423634517)
                    ·
                      refine ⟨638991757835980387776967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 54527296668670326423634517 638991757835980387776967)
                      ·
                        rfl

theorem cell23_1244432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_1244432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244432 prefixEnd_1244432 := by exact prefixLift 1244432
  have htrace : WordTrace (prefixWord ++ tailWord_1244432) baseStart_1244432 baseEnd_1244432 := by
    simpa [prefixWord, tailWord_1244432, baseEnd_1244432] using wordTrace_append hprefix tailTrace_1244432
  have hstable : (prefixWord ++ tailWord_1244432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244432).length < 2 ^ (prefixWord ++ tailWord_1244432).sum := by decide
  have hdescent : baseEnd_1244432 < baseStart_1244432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244440 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 2, 2, 2]
def baseStart_1244440 : Nat := 118140960795 + 1244440 * 2 ^ 59
def prefixEnd_1244440 : Nat := 4983230072969 + 3 ^ 40 * 1244440 * 2
def baseEnd_1244440 : Nat := 638995865681216356476931

theorem tailTrace_1244440 : CollatzResearch.WordTrace tailWord_1244440 prefixEnd_1244440 638995865681216356476931 := by
  unfold tailWord_1244440
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694227805806944138229387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30258970407742592184305849 22694227805806944138229387)
  ·
    refine ⟨34041341708710416207344081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22694227805806944138229387 34041341708710416207344081)
    ·
      refine ⟨25531006281532812155508061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34041341708710416207344081 25531006281532812155508061)
      ·
        refine ⟨9574127355574804558315523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25531006281532812155508061 9574127355574804558315523)
        ·
          refine ⟨14361191033362206837473285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9574127355574804558315523 14361191033362206837473285)
          ·
            refine ⟨2692723318755413782026241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14361191033362206837473285 2692723318755413782026241)
            ·
              refine ⟨2019542489066560336519681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2692723318755413782026241 2019542489066560336519681)
              ·
                refine ⟨1514656866799920252389761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2019542489066560336519681 1514656866799920252389761)
                ·
                  refine ⟨1135992650099940189292321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1514656866799920252389761 1135992650099940189292321)
                  ·
                    refine ⟨851994487574955141969241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1135992650099940189292321 851994487574955141969241)
                    ·
                      refine ⟨638995865681216356476931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 851994487574955141969241 638995865681216356476931)
                      ·
                        rfl

theorem cell23_1244440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_1244440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244440 prefixEnd_1244440 := by exact prefixLift 1244440
  have htrace : WordTrace (prefixWord ++ tailWord_1244440) baseStart_1244440 baseEnd_1244440 := by
    simpa [prefixWord, tailWord_1244440, baseEnd_1244440] using wordTrace_append hprefix tailTrace_1244440
  have hstable : (prefixWord ++ tailWord_1244440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244440).length < 2 ^ (prefixWord ++ tailWord_1244440).sum := by decide
  have hdescent : baseEnd_1244440 < baseStart_1244440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244456 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1244456 : Nat := 118140960795 + 1244456 * 2 ^ 59
def prefixEnd_1244456 : Nat := 4983230072969 + 3 ^ 40 * 1244456 * 2
def baseEnd_1244456 : Nat := 639004081371688293876857

theorem tailTrace_1244456 : CollatzResearch.WordTrace tailWord_1244456 prefixEnd_1244456 639004081371688293876857 := by
  unfold tailWord_1244456
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694519589777961504520611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30259359453037282006027481 22694519589777961504520611)
  ·
    refine ⟨34041779384666942256780917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22694519589777961504520611 34041779384666942256780917)
    ·
      refine ⟨3191416817312525836573211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34041779384666942256780917 3191416817312525836573211)
      ·
        refine ⟨4787125225968788754859817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191416817312525836573211 4787125225968788754859817)
        ·
          refine ⟨3590343919476591566144863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4787125225968788754859817 3590343919476591566144863)
          ·
            refine ⟨5385515879214887349217295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590343919476591566144863 5385515879214887349217295)
            ·
              refine ⟨8078273818822331023825943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385515879214887349217295 8078273818822331023825943)
              ·
                refine ⟨12117410728233496535738915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8078273818822331023825943 12117410728233496535738915)
                ·
                  refine ⟨18176116092350244803608373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12117410728233496535738915 18176116092350244803608373)
                  ·
                    refine ⟨1704010883657835450338285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18176116092350244803608373 1704010883657835450338285)
                    ·
                      refine ⟨639004081371688293876857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1704010883657835450338285 639004081371688293876857)
                      ·
                        rfl

theorem cell23_1244456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1244456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244456 prefixEnd_1244456 := by exact prefixLift 1244456
  have htrace : WordTrace (prefixWord ++ tailWord_1244456) baseStart_1244456 baseEnd_1244456 := by
    simpa [prefixWord, tailWord_1244456, baseEnd_1244456] using wordTrace_append hprefix tailTrace_1244456
  have hstable : (prefixWord ++ tailWord_1244456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244456).length < 2 ^ (prefixWord ++ tailWord_1244456).sum := by decide
  have hdescent : baseEnd_1244456 < baseStart_1244456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244476 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1244476 : Nat := 118140960795 + 1244476 * 2 ^ 59
def prefixEnd_1244476 : Nat := 4983230072969 + 3 ^ 40 * 1244476 * 2
def baseEnd_1244476 : Nat := 213004783661592738542255

theorem tailTrace_1244476 : CollatzResearch.WordTrace tailWord_1244476 prefixEnd_1244476 213004783661592738542255 := by
  unfold tailWord_1244476
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694884319741733212384641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30259845759655644283179521 22694884319741733212384641)
  ·
    refine ⟨17021163239806299909288481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22694884319741733212384641 17021163239806299909288481)
    ·
      refine ⟨12765872429854724931966361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17021163239806299909288481 12765872429854724931966361)
      ·
        refine ⟨9574404322391043698974771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12765872429854724931966361 9574404322391043698974771)
        ·
          refine ⟨14361606483586565548462157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9574404322391043698974771 14361606483586565548462157)
          ·
            refine ⟨5385602431344962080673309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14361606483586565548462157 5385602431344962080673309)
            ·
              refine ⟨2019600911754360780252491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5385602431344962080673309 2019600911754360780252491)
              ·
                refine ⟨3029401367631541170378737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019600911754360780252491 3029401367631541170378737)
                ·
                  refine ⟨2272051025723655877784053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029401367631541170378737 2272051025723655877784053)
                  ·
                    refine ⟨213004783661592738542255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2272051025723655877784053 213004783661592738542255)
                    ·
                      rfl

theorem cell23_1244476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1244476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244476 prefixEnd_1244476 := by exact prefixLift 1244476
  have htrace : WordTrace (prefixWord ++ tailWord_1244476) baseStart_1244476 baseEnd_1244476 := by
    simpa [prefixWord, tailWord_1244476, baseEnd_1244476] using wordTrace_append hprefix tailTrace_1244476
  have hstable : (prefixWord ++ tailWord_1244476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244476).length < 2 ^ (prefixWord ++ tailWord_1244476).sum := by decide
  have hdescent : baseEnd_1244476 < baseStart_1244476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244496 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 4, 4, 2]
def baseStart_1244496 : Nat := 118140960795 + 1244496 * 2 ^ 59
def prefixEnd_1244496 : Nat := 4983230072969 + 3 ^ 40 * 1244496 * 2
def baseEnd_1244496 : Nat := 639024620597868137376673

theorem tailTrace_1244496 : CollatzResearch.WordTrace tailWord_1244496 prefixEnd_1244496 639024620597868137376673 := by
  unfold tailWord_1244496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22695249049705504920248671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30260332066274006560331561 22695249049705504920248671)
  ·
    refine ⟨34042873574558257380373007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22695249049705504920248671 34042873574558257380373007)
    ·
      refine ⟨51064310361837386070559511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34042873574558257380373007 51064310361837386070559511)
      ·
        refine ⟨76596465542756079105839267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51064310361837386070559511 76596465542756079105839267)
        ·
          refine ⟨114894698314134118658758901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76596465542756079105839267 114894698314134118658758901)
          ·
            refine ⟨10771377966950073624258647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114894698314134118658758901 10771377966950073624258647)
            ·
              refine ⟨16157066950425110436387971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10771377966950073624258647 16157066950425110436387971)
              ·
                refine ⟨24235600425637665654581957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16157066950425110436387971 24235600425637665654581957)
                ·
                  refine ⟨4544175079807062310234117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24235600425637665654581957 4544175079807062310234117)
                  ·
                    refine ⟨852032827463824183168897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4544175079807062310234117 852032827463824183168897)
                    ·
                      refine ⟨639024620597868137376673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852032827463824183168897 639024620597868137376673)
                      ·
                        rfl

theorem cell23_1244496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 4, 2].length) (baseStart_1244496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244496 prefixEnd_1244496 := by exact prefixLift 1244496
  have htrace : WordTrace (prefixWord ++ tailWord_1244496) baseStart_1244496 baseEnd_1244496 := by
    simpa [prefixWord, tailWord_1244496, baseEnd_1244496] using wordTrace_append hprefix tailTrace_1244496
  have hstable : (prefixWord ++ tailWord_1244496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244496).length < 2 ^ (prefixWord ++ tailWord_1244496).sum := by decide
  have hdescent : baseEnd_1244496 < baseStart_1244496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244506 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_1244506 : Nat := 118140960795 + 1244506 * 2 ^ 59
def prefixEnd_1244506 : Nat := 4983230072969 + 3 ^ 40 * 1244506 * 2
def baseEnd_1244506 : Nat := 213009918468137699417209

theorem tailTrace_1244506 : CollatzResearch.WordTrace tailWord_1244506 prefixEnd_1244506 213009918468137699417209 := by
  unfold tailWord_1244506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347715707343695387090343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30260575219583187698907581 11347715707343695387090343)
  ·
    refine ⟨17021573561015543080635515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11347715707343695387090343 17021573561015543080635515)
    ·
      refine ⟨25532360341523314620953273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17021573561015543080635515 25532360341523314620953273)
      ·
        refine ⟨19149270256142485965714955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25532360341523314620953273 19149270256142485965714955)
        ·
          refine ⟨28723905384213728948572433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19149270256142485965714955 28723905384213728948572433)
          ·
            refine ⟨21542929038160296711429325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28723905384213728948572433 21542929038160296711429325)
            ·
              refine ⟨8078598389310111266785997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21542929038160296711429325 8078598389310111266785997)
              ·
                refine ⟨3029474395991291725044749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8078598389310111266785997 3029474395991291725044749)
                ·
                  refine ⟨1136052898496734396891781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3029474395991291725044749 1136052898496734396891781)
                  ·
                    refine ⟨213009918468137699417209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136052898496734396891781 213009918468137699417209)
                    ·
                      rfl

theorem cell23_1244506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_1244506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244506 prefixEnd_1244506 := by exact prefixLift 1244506
  have htrace : WordTrace (prefixWord ++ tailWord_1244506) baseStart_1244506 baseEnd_1244506 := by
    simpa [prefixWord, tailWord_1244506, baseEnd_1244506] using wordTrace_append hprefix tailTrace_1244506
  have hstable : (prefixWord ++ tailWord_1244506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244506).length < 2 ^ (prefixWord ++ tailWord_1244506).sum := by decide
  have hdescent : baseEnd_1244506 < baseStart_1244506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244516 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_1244516 : Nat := 118140960795 + 1244516 * 2 ^ 59
def prefixEnd_1244516 : Nat := 4983230072969 + 3 ^ 40 * 1244516 * 2
def baseEnd_1244516 : Nat := 639034890210958059126581

theorem tailTrace_1244516 : CollatzResearch.WordTrace tailWord_1244516 prefixEnd_1244516 639034890210958059126581 := by
  unfold tailWord_1244516
  simp only [CollatzResearch.WordTrace]
  refine ⟨22695613779669276628112701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30260818372892368837483601 22695613779669276628112701)
  ·
    refine ⟨8510855167375978735542263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22695613779669276628112701 8510855167375978735542263)
    ·
      refine ⟨12766282751063968103313395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8510855167375978735542263 12766282751063968103313395)
      ·
        refine ⟨19149424126595952154970093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12766282751063968103313395 19149424126595952154970093)
        ·
          refine ⟨7181034047473482058113785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19149424126595952154970093 7181034047473482058113785)
          ·
            refine ⟨5385775535605111543585339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7181034047473482058113785 5385775535605111543585339)
            ·
              refine ⟨8078663303407667315378009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385775535605111543585339 8078663303407667315378009)
              ·
                refine ⟨6058997477555750486533507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8078663303407667315378009 6058997477555750486533507)
                ·
                  refine ⟨9088496216333625729800261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058997477555750486533507 9088496216333625729800261)
                  ·
                    refine ⟨1704093040562554824337549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9088496216333625729800261 1704093040562554824337549)
                    ·
                      refine ⟨639034890210958059126581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1704093040562554824337549 639034890210958059126581)
                      ·
                        rfl

theorem cell23_1244516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_1244516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244516 prefixEnd_1244516 := by exact prefixLift 1244516
  have htrace : WordTrace (prefixWord ++ tailWord_1244516) baseStart_1244516 baseEnd_1244516 := by
    simpa [prefixWord, tailWord_1244516, baseEnd_1244516] using wordTrace_append hprefix tailTrace_1244516
  have hstable : (prefixWord ++ tailWord_1244516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244516).length < 2 ^ (prefixWord ++ tailWord_1244516).sum := by decide
  have hdescent : baseEnd_1244516 < baseStart_1244516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244616 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1244616 : Nat := 118140960795 + 1244616 * 2 ^ 59
def prefixEnd_1244616 : Nat := 4983230072969 + 3 ^ 40 * 1244616 * 2
def baseEnd_1244616 : Nat := 639086238276407667876121

theorem tailTrace_1244616 : CollatzResearch.WordTrace tailWord_1244616 prefixEnd_1244616 639086238276407667876121 := by
  unfold tailWord_1244616
  simp only [CollatzResearch.WordTrace]
  refine ⟨22697437429488135167432851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30263249905984180223243801 22697437429488135167432851)
  ·
    refine ⟨34046156144232202751149277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22697437429488135167432851 34046156144232202751149277)
    ·
      refine ⟨12767308554087076031680979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34046156144232202751149277 12767308554087076031680979)
      ·
        refine ⟨19150962831130614047521469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12767308554087076031680979 19150962831130614047521469)
        ·
          refine ⟨7181611061673980267820551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19150962831130614047521469 7181611061673980267820551)
          ·
            refine ⟨10772416592510970401730827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7181611061673980267820551 10772416592510970401730827)
            ·
              refine ⟨16158624888766455602596241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10772416592510970401730827 16158624888766455602596241)
              ·
                refine ⟨12118968666574841701947181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16158624888766455602596241 12118968666574841701947181)
                ·
                  refine ⟨4544613249965565638230193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12118968666574841701947181 4544613249965565638230193)
                  ·
                    refine ⟨3408459937474174228672645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544613249965565638230193 3408459937474174228672645)
                    ·
                      refine ⟨639086238276407667876121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3408459937474174228672645 639086238276407667876121)
                      ·
                        rfl

theorem cell23_1244616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1244616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244616 prefixEnd_1244616 := by exact prefixLift 1244616
  have htrace : WordTrace (prefixWord ++ tailWord_1244616) baseStart_1244616 baseEnd_1244616 := by
    simpa [prefixWord, tailWord_1244616, baseEnd_1244616] using wordTrace_append hprefix tailTrace_1244616
  have hstable : (prefixWord ++ tailWord_1244616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244616).length < 2 ^ (prefixWord ++ tailWord_1244616).sum := by decide
  have hdescent : baseEnd_1244616 < baseStart_1244616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244630 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1244630 : Nat := 118140960795 + 1244630 * 2 ^ 59
def prefixEnd_1244630 : Nat := 4983230072969 + 3 ^ 40 * 1244630 * 2
def baseEnd_1244630 : Nat := 213031142335190204367019

theorem tailTrace_1244630 : CollatzResearch.WordTrace tailWord_1244630 prefixEnd_1244630 213031142335190204367019 := by
  unfold tailWord_1244630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837211592557846920367209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30263590320617033817250229 2837211592557846920367209)
  ·
    refine ⟨2127908694418385190275407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2837211592557846920367209 2127908694418385190275407)
    ·
      refine ⟨3191863041627577785413111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127908694418385190275407 3191863041627577785413111)
      ·
        refine ⟨4787794562441366678119667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191863041627577785413111 4787794562441366678119667)
        ·
          refine ⟨7181691843662050017179501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787794562441366678119667 7181691843662050017179501)
          ·
            refine ⟨2693134441373268756442313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7181691843662050017179501 2693134441373268756442313)
            ·
              refine ⟨2019850831029951567331735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693134441373268756442313 2019850831029951567331735)
              ·
                refine ⟨3029776246544927350997603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019850831029951567331735 3029776246544927350997603)
                ·
                  refine ⟨4544664369817391026496405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029776246544927350997603 4544664369817391026496405)
                  ·
                    refine ⟨213031142335190204367019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4544664369817391026496405 213031142335190204367019)
                    ·
                      rfl

theorem cell23_1244630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1244630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244630 prefixEnd_1244630 := by exact prefixLift 1244630
  have htrace : WordTrace (prefixWord ++ tailWord_1244630) baseStart_1244630 baseEnd_1244630 := by
    simpa [prefixWord, tailWord_1244630, baseEnd_1244630] using wordTrace_append hprefix tailTrace_1244630
  have hstable : (prefixWord ++ tailWord_1244630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244630).length < 2 ^ (prefixWord ++ tailWord_1244630).sum := by decide
  have hdescent : baseEnd_1244630 < baseStart_1244630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244633 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_1244633 : Nat := 118140960795 + 1244633 * 2 ^ 59
def prefixEnd_1244633 : Nat := 4983230072969 + 3 ^ 40 * 1244633 * 2
def baseEnd_1244633 : Nat := 639094967447534101363543

theorem tailTrace_1244633 : CollatzResearch.WordTrace tailWord_1244633 prefixEnd_1244633 639094967447534101363543 := by
  unfold tailWord_1244633
  simp only [CollatzResearch.WordTrace]
  refine ⟨45395494899914682238234553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30263663266609788158823035 45395494899914682238234553)
  ·
    refine ⟨34046621174936011678675915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45395494899914682238234553 34046621174936011678675915)
    ·
      refine ⟨51069931762404017518013873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34046621174936011678675915 51069931762404017518013873)
      ·
        refine ⟨38302448821803013138510405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51069931762404017518013873 38302448821803013138510405)
        ·
          refine ⟨7181709154088064963470701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38302448821803013138510405 7181709154088064963470701)
          ·
            refine ⟨2693140932783024361301513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7181709154088064963470701 2693140932783024361301513)
            ·
              refine ⟨2019855699587268270976135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693140932783024361301513 2019855699587268270976135)
              ·
                refine ⟨3029783549380902406464203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019855699587268270976135 3029783549380902406464203)
                ·
                  refine ⟨4544675324071353609696305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029783549380902406464203 4544675324071353609696305)
                  ·
                    refine ⟨3408506493053515207272229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544675324071353609696305 3408506493053515207272229)
                    ·
                      refine ⟨639094967447534101363543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3408506493053515207272229 639094967447534101363543)
                      ·
                        rfl

theorem cell23_1244633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_1244633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244633 prefixEnd_1244633 := by exact prefixLift 1244633
  have htrace : WordTrace (prefixWord ++ tailWord_1244633) baseStart_1244633 baseEnd_1244633 := by
    simpa [prefixWord, tailWord_1244633, baseEnd_1244633] using wordTrace_append hprefix tailTrace_1244633
  have hstable : (prefixWord ++ tailWord_1244633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244633).length < 2 ^ (prefixWord ++ tailWord_1244633).sum := by decide
  have hdescent : baseEnd_1244633 < baseStart_1244633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244637 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_1244637 : Nat := 118140960795 + 1244637 * 2 ^ 59
def prefixEnd_1244637 : Nat := 4983230072969 + 3 ^ 40 * 1244637 * 2
def baseEnd_1244637 : Nat := 639097021370152085713525

theorem tailTrace_1244637 : CollatzResearch.WordTrace tailWord_1244637 prefixEnd_1244637 639097021370152085713525 := by
  unfold tailWord_1244637
  simp only [CollatzResearch.WordTrace]
  refine ⟨45395640791900190921380165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30263760527933460614253443 45395640791900190921380165)
  ·
    refine ⟨8511682648481285797758781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45395640791900190921380165 8511682648481285797758781)
    ·
      refine ⟨3191880993180482174159543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8511682648481285797758781 3191880993180482174159543)
      ·
        refine ⟨4787821489770723261239315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191880993180482174159543 4787821489770723261239315)
        ·
          refine ⟨7181732234656084891858973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787821489770723261239315 7181732234656084891858973)
          ·
            refine ⟨2693149587996031834447115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7181732234656084891858973 2693149587996031834447115)
            ·
              refine ⟨4039724381994047751670673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693149587996031834447115 4039724381994047751670673)
              ·
                refine ⟨3029793286495535813753005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039724381994047751670673 3029793286495535813753005)
                ·
                  refine ⟨1136172482435825930157377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3029793286495535813753005 1136172482435825930157377)
                  ·
                    refine ⟨852129361826869447618033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1136172482435825930157377 852129361826869447618033)
                    ·
                      refine ⟨639097021370152085713525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852129361826869447618033 639097021370152085713525)
                      ·
                        rfl

theorem cell23_1244637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_1244637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244637 prefixEnd_1244637 := by exact prefixLift 1244637
  have htrace : WordTrace (prefixWord ++ tailWord_1244637) baseStart_1244637 baseEnd_1244637 := by
    simpa [prefixWord, tailWord_1244637, baseEnd_1244637] using wordTrace_append hprefix tailTrace_1244637
  have hstable : (prefixWord ++ tailWord_1244637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244637).length < 2 ^ (prefixWord ++ tailWord_1244637).sum := by decide
  have hdescent : baseEnd_1244637 < baseStart_1244637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244643 : List Nat := [1, 1, 1, 6, 2, 2, 3, 7]
def baseStart_1244643 : Nat := 118140960795 + 1244643 * 2 ^ 59
def prefixEnd_1244643 : Nat := 4983230072969 + 3 ^ 40 * 1244643 * 2
def baseEnd_1244643 : Nat := 23670374157558483786611

theorem tailTrace_1244643 : CollatzResearch.WordTrace tailWord_1244643 prefixEnd_1244643 23670374157558483786611 := by
  unfold tailWord_1244643
  simp only [CollatzResearch.WordTrace]
  refine ⟨45395859629878453946098583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30263906419918969297399055 45395859629878453946098583)
  ·
    refine ⟨68093789444817680919147875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45395859629878453946098583 68093789444817680919147875)
    ·
      refine ⟨102140684167226521378721813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68093789444817680919147875 102140684167226521378721813)
      ·
        refine ⟨4787844570338743189627585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102140684167226521378721813 4787844570338743189627585)
        ·
          refine ⟨3590883427754057392220689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4787844570338743189627585 3590883427754057392220689)
          ·
            refine ⟨2693162570815543044165517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590883427754057392220689 2693162570815543044165517)
            ·
              refine ⟨1009935964055828641562069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2693162570815543044165517 1009935964055828641562069)
              ·
                refine ⟨23670374157558483786611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1009935964055828641562069 23670374157558483786611)
                ·
                  rfl

theorem cell23_1244643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 7].length) (baseStart_1244643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244643 prefixEnd_1244643 := by exact prefixLift 1244643
  have htrace : WordTrace (prefixWord ++ tailWord_1244643) baseStart_1244643 baseEnd_1244643 := by
    simpa [prefixWord, tailWord_1244643, baseEnd_1244643] using wordTrace_append hprefix tailTrace_1244643
  have hstable : (prefixWord ++ tailWord_1244643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244643).length < 2 ^ (prefixWord ++ tailWord_1244643).sum := by decide
  have hdescent : baseEnd_1244643 < baseStart_1244643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244654 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_1244654 : Nat := 118140960795 + 1244654 * 2 ^ 59
def prefixEnd_1244654 : Nat := 4983230072969 + 3 ^ 40 * 1244654 * 2
def baseEnd_1244654 : Nat := 639105750541278519200947

theorem tailTrace_1244654 : CollatzResearch.WordTrace tailWord_1244654 prefixEnd_1244654 639105750541278519200947 := by
  unfold tailWord_1244654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674532604104825353093627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30264173888559068549832677 5674532604104825353093627)
  ·
    refine ⟨8511798906157238029640441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5674532604104825353093627 8511798906157238029640441)
    ·
      refine ⟨6383849179617928522230331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8511798906157238029640441 6383849179617928522230331)
      ·
        refine ⟨9575773769426892783345497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6383849179617928522230331 9575773769426892783345497)
        ·
          refine ⟨7181830327070169587509123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9575773769426892783345497 7181830327070169587509123)
          ·
            refine ⟨10772745490605254381263685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7181830327070169587509123 10772745490605254381263685)
            ·
              refine ⟨2019889779488485196486941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10772745490605254381263685 2019889779488485196486941)
              ·
                refine ⟨757458667308181948682603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2019889779488485196486941 757458667308181948682603)
                ·
                  refine ⟨1136188000962272923023905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757458667308181948682603 1136188000962272923023905)
                  ·
                    refine ⟨852141000721704692267929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1136188000962272923023905 852141000721704692267929)
                    ·
                      refine ⟨639105750541278519200947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852141000721704692267929 639105750541278519200947)
                      ·
                        rfl

theorem cell23_1244654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_1244654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244654 prefixEnd_1244654 := by exact prefixLift 1244654
  have htrace : WordTrace (prefixWord ++ tailWord_1244654) baseStart_1244654 baseEnd_1244654 := by
    simpa [prefixWord, tailWord_1244654, baseEnd_1244654] using wordTrace_append hprefix tailTrace_1244654
  have hstable : (prefixWord ++ tailWord_1244654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244654).length < 2 ^ (prefixWord ++ tailWord_1244654).sum := by decide
  have hdescent : baseEnd_1244654 < baseStart_1244654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244657 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 1, 2, 3]
def baseStart_1244657 : Nat := 118140960795 + 1244657 * 2 ^ 59
def prefixEnd_1244657 : Nat := 4983230072969 + 3 ^ 40 * 1244657 * 2
def baseEnd_1244657 : Nat := 639107290983242007463433

theorem tailTrace_1244657 : CollatzResearch.WordTrace tailWord_1244657 prefixEnd_1244657 639107290983242007463433 := by
  unfold tailWord_1244657
  simp only [CollatzResearch.WordTrace]
  refine ⟨45396370251827734337108225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30264246834551822891405483 45396370251827734337108225)
  ·
    refine ⟨34047277688870800752831169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45396370251827734337108225 34047277688870800752831169)
    ·
      refine ⟨25535458266653100564623377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34047277688870800752831169 25535458266653100564623377)
      ·
        refine ⟨19151593699989825423467533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25535458266653100564623377 19151593699989825423467533)
        ·
          refine ⟨7181847637496184533800325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19151593699989825423467533 7181847637496184533800325)
          ·
            refine ⟨1346596432030534600087561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7181847637496184533800325 1346596432030534600087561)
            ·
              refine ⟨1009947324022900950065671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346596432030534600087561 1009947324022900950065671)
              ·
                refine ⟨1514920986034351425098507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009947324022900950065671 1514920986034351425098507)
                ·
                  refine ⟨2272381479051527137647761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514920986034351425098507 2272381479051527137647761)
                  ·
                    refine ⟨1704286109288645353235821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272381479051527137647761 1704286109288645353235821)
                    ·
                      refine ⟨639107290983242007463433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1704286109288645353235821 639107290983242007463433)
                      ·
                        rfl

theorem cell23_1244657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_1244657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244657 prefixEnd_1244657 := by exact prefixLift 1244657
  have htrace : WordTrace (prefixWord ++ tailWord_1244657) baseStart_1244657 baseEnd_1244657 := by
    simpa [prefixWord, tailWord_1244657, baseEnd_1244657] using wordTrace_append hprefix tailTrace_1244657
  have hstable : (prefixWord ++ tailWord_1244657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244657).length < 2 ^ (prefixWord ++ tailWord_1244657).sum := by decide
  have hdescent : baseEnd_1244657 < baseStart_1244657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244663 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 5, 3, 2]
def baseStart_1244663 : Nat := 118140960795 + 1244663 * 2 ^ 59
def prefixEnd_1244663 : Nat := 4983230072969 + 3 ^ 40 * 1244663 * 2
def baseEnd_1244663 : Nat := 639110371867168983988405

theorem tailTrace_1244663 : CollatzResearch.WordTrace tailWord_1244663 prefixEnd_1244663 639110371867168983988405 := by
  unfold tailWord_1244663
  simp only [CollatzResearch.WordTrace]
  refine ⟨45396589089805997361826643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30264392726537331574551095 45396589089805997361826643)
  ·
    refine ⟨68094883634708996042739965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45396589089805997361826643 68094883634708996042739965)
    ·
      refine ⟨25535581363015873516027487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68094883634708996042739965 25535581363015873516027487)
      ·
        refine ⟨38303372044523810274041231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25535581363015873516027487 38303372044523810274041231)
        ·
          refine ⟨57455058066785715411061847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38303372044523810274041231 57455058066785715411061847)
          ·
            refine ⟨86182587100178573116592771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57455058066785715411061847 86182587100178573116592771)
            ·
              refine ⟨129273880650267859674889157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86182587100178573116592771 129273880650267859674889157)
              ·
                refine ⟨24238852621925223689041717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129273880650267859674889157 24238852621925223689041717)
                ·
                  refine ⟨2272392433305489720847661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24238852621925223689041717 2272392433305489720847661)
                  ·
                    refine ⟨852147162489558645317873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272392433305489720847661 852147162489558645317873)
                    ·
                      refine ⟨639110371867168983988405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852147162489558645317873 639110371867168983988405)
                      ·
                        rfl

theorem cell23_1244663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_1244663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244663 prefixEnd_1244663 := by exact prefixLift 1244663
  have htrace : WordTrace (prefixWord ++ tailWord_1244663) baseStart_1244663 baseEnd_1244663 := by
    simpa [prefixWord, tailWord_1244663, baseEnd_1244663] using wordTrace_append hprefix tailTrace_1244663
  have hstable : (prefixWord ++ tailWord_1244663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244663).length < 2 ^ (prefixWord ++ tailWord_1244663).sum := by decide
  have hdescent : baseEnd_1244663 < baseStart_1244663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244773 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1244773 : Nat := 118140960795 + 1244773 * 2 ^ 59
def prefixEnd_1244773 : Nat := 4983230072969 + 3 ^ 40 * 1244773 * 2
def baseEnd_1244773 : Nat := 639166854739163553612899

theorem tailTrace_1244773 : CollatzResearch.WordTrace tailWord_1244773 prefixEnd_1244773 639166854739163553612899 := by
  unfold tailWord_1244773
  simp only [CollatzResearch.WordTrace]
  refine ⟨45400601119407486148330973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30267067412938324098887315 45400601119407486148330973)
  ·
    refine ⟨17025225419777807305624115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45400601119407486148330973 17025225419777807305624115)
    ·
      refine ⟨25537838129666710958436173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17025225419777807305624115 25537838129666710958436173)
      ·
        refine ⟨9576689298625016609413565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25537838129666710958436173 9576689298625016609413565)
        ·
          refine ⟨3591258486984381228530087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9576689298625016609413565 3591258486984381228530087)
          ·
            refine ⟨5386887730476571842795131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591258486984381228530087 5386887730476571842795131)
            ·
              refine ⟨8080331595714857764192697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386887730476571842795131 8080331595714857764192697)
              ·
                refine ⟨6060248696786143323144523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8080331595714857764192697 6060248696786143323144523)
                ·
                  refine ⟨9090373045179214984716785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6060248696786143323144523 9090373045179214984716785)
                  ·
                    refine ⟨6817779783884411238537589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9090373045179214984716785 6817779783884411238537589)
                    ·
                      refine ⟨639166854739163553612899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6817779783884411238537589 639166854739163553612899)
                      ·
                        rfl

theorem cell23_1244773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1244773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244773 prefixEnd_1244773 := by exact prefixLift 1244773
  have htrace : WordTrace (prefixWord ++ tailWord_1244773) baseStart_1244773 baseEnd_1244773 := by
    simpa [prefixWord, tailWord_1244773, baseEnd_1244773] using wordTrace_append hprefix tailTrace_1244773
  have hstable : (prefixWord ++ tailWord_1244773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244773).length < 2 ^ (prefixWord ++ tailWord_1244773).sum := by decide
  have hdescent : baseEnd_1244773 < baseStart_1244773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244790 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1244790 : Nat := 118140960795 + 1244790 * 2 ^ 59
def prefixEnd_1244790 : Nat := 4983230072969 + 3 ^ 40 * 1244790 * 2
def baseEnd_1244790 : Nat := 639175583910289987100321

theorem tailTrace_1244790 : CollatzResearch.WordTrace tailWord_1244790 prefixEnd_1244790 639175583910289987100321 := by
  unfold tailWord_1244790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837576322521618628231239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30267480773563932034466549 2837576322521618628231239)
  ·
    refine ⟨4256364483782427942346859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837576322521618628231239 4256364483782427942346859)
    ·
      refine ⟨6384546725673641913520289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256364483782427942346859 6384546725673641913520289)
      ·
        refine ⟨4788410044255231435140217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6384546725673641913520289 4788410044255231435140217)
        ·
          refine ⟨3591307533191423576355163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4788410044255231435140217 3591307533191423576355163)
          ·
            refine ⟨5386961299787135364532745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591307533191423576355163 5386961299787135364532745)
            ·
              refine ⟨4040220974840351523399559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386961299787135364532745 4040220974840351523399559)
              ·
                refine ⟨6060331462260527285099339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040220974840351523399559 6060331462260527285099339)
                ·
                  refine ⟨9090497193390790927649009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6060331462260527285099339 9090497193390790927649009)
                  ·
                    refine ⟨6817872895043093195736757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9090497193390790927649009 6817872895043093195736757)
                    ·
                      refine ⟨639175583910289987100321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6817872895043093195736757 639175583910289987100321)
                      ·
                        rfl

theorem cell23_1244790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1244790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244790 prefixEnd_1244790 := by exact prefixLift 1244790
  have htrace : WordTrace (prefixWord ++ tailWord_1244790) baseStart_1244790 baseEnd_1244790 := by
    simpa [prefixWord, tailWord_1244790, baseEnd_1244790] using wordTrace_append hprefix tailTrace_1244790
  have hstable : (prefixWord ++ tailWord_1244790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244790).length < 2 ^ (prefixWord ++ tailWord_1244790).sum := by decide
  have hdescent : baseEnd_1244790 < baseStart_1244790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244800 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 2, 4, 2]
def baseStart_1244800 : Nat := 118140960795 + 1244800 * 2 ^ 59
def prefixEnd_1244800 : Nat := 4983230072969 + 3 ^ 40 * 1244800 * 2
def baseEnd_1244800 : Nat := 639180718716834947975275

theorem tailTrace_1244800 : CollatzResearch.WordTrace tailWord_1244800 prefixEnd_1244800 639180718716834947975275 := by
  unfold tailWord_1244800
  simp only [CollatzResearch.WordTrace]
  refine ⟨22700792945154834879781927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30267723926873113173042569 22700792945154834879781927)
  ·
    refine ⟨34051189417732252319672891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22700792945154834879781927 34051189417732252319672891)
    ·
      refine ⟨51076784126598378479509337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34051189417732252319672891 51076784126598378479509337)
      ·
        refine ⟨38307588094948783859632003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51076784126598378479509337 38307588094948783859632003)
        ·
          refine ⟨57461382142423175789448005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38307588094948783859632003 57461382142423175789448005)
          ·
            refine ⟨10774009151704345460521501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57461382142423175789448005 10774009151704345460521501)
            ·
              refine ⟨4040253431889129547695563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10774009151704345460521501 4040253431889129547695563)
              ·
                refine ⟨6060380147833694321543345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040253431889129547695563 6060380147833694321543345)
                ·
                  refine ⟨4545285110875270741157509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6060380147833694321543345 4545285110875270741157509)
                  ·
                    refine ⟨852240958289113263967033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4545285110875270741157509 852240958289113263967033)
                    ·
                      refine ⟨639180718716834947975275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852240958289113263967033 639180718716834947975275)
                      ·
                        rfl

theorem cell23_1244800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_1244800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244800 prefixEnd_1244800 := by exact prefixLift 1244800
  have htrace : WordTrace (prefixWord ++ tailWord_1244800) baseStart_1244800 baseEnd_1244800 := by
    simpa [prefixWord, tailWord_1244800, baseEnd_1244800] using wordTrace_append hprefix tailTrace_1244800
  have hstable : (prefixWord ++ tailWord_1244800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244800).length < 2 ^ (prefixWord ++ tailWord_1244800).sum := by decide
  have hdescent : baseEnd_1244800 < baseStart_1244800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244803 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 3]
def baseStart_1244803 : Nat := 118140960795 + 1244803 * 2 ^ 59
def prefixEnd_1244803 : Nat := 4983230072969 + 3 ^ 40 * 1244803 * 2
def baseEnd_1244803 : Nat := 639182259158798436237761

theorem tailTrace_1244803 : CollatzResearch.WordTrace tailWord_1244803 prefixEnd_1244803 639182259158798436237761 := by
  unfold tailWord_1244803
  simp only [CollatzResearch.WordTrace]
  refine ⟨45401695309298801271923063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30267796872865867514615375 45401695309298801271923063)
  ·
    refine ⟨68102542963948201907884595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45401695309298801271923063 68102542963948201907884595)
    ·
      refine ⟨102153814445922302861826893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68102542963948201907884595 102153814445922302861826893)
      ·
        refine ⟨38307680417220863573185085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102153814445922302861826893 38307680417220863573185085)
        ·
          refine ⟨14365380156457823839944407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38307680417220863573185085 14365380156457823839944407)
          ·
            refine ⟨21548070234686735759916611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14365380156457823839944407 21548070234686735759916611)
            ·
              refine ⟨32322105352030103639874917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21548070234686735759916611 32322105352030103639874917)
              ·
                refine ⟨6060394753505644432476547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32322105352030103639874917 6060394753505644432476547)
                ·
                  refine ⟨9090592130258466648714821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6060394753505644432476547 9090592130258466648714821)
                  ·
                    refine ⟨1704486024423462496634029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9090592130258466648714821 1704486024423462496634029)
                    ·
                      refine ⟨639182259158798436237761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1704486024423462496634029 639182259158798436237761)
                      ·
                        rfl

theorem cell23_1244803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_1244803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244803 prefixEnd_1244803 := by exact prefixLift 1244803
  have htrace : WordTrace (prefixWord ++ tailWord_1244803) baseStart_1244803 baseEnd_1244803 := by
    simpa [prefixWord, tailWord_1244803, baseEnd_1244803] using wordTrace_append hprefix tailTrace_1244803
  have hstable : (prefixWord ++ tailWord_1244803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244803).length < 2 ^ (prefixWord ++ tailWord_1244803).sum := by decide
  have hdescent : baseEnd_1244803 < baseStart_1244803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244810 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_1244810 : Nat := 118140960795 + 1244810 * 2 ^ 59
def prefixEnd_1244810 : Nat := 4983230072969 + 3 ^ 40 * 1244810 * 2
def baseEnd_1244810 : Nat := 213061951174459969616743

theorem tailTrace_1244810 : CollatzResearch.WordTrace tailWord_1244810 prefixEnd_1244810 213061951174459969616743 := by
  unfold tailWord_1244810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11350487655068360366856971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30267967080182294311618589 11350487655068360366856971)
  ·
    refine ⟨17025731482602540550285457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11350487655068360366856971 17025731482602540550285457)
    ·
      refine ⟨12769298611951905412714093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17025731482602540550285457 12769298611951905412714093)
      ·
        refine ⟨4788486979481964529767785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12769298611951905412714093 4788486979481964529767785)
        ·
          refine ⟨3591365234611473397325839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4788486979481964529767785 3591365234611473397325839)
          ·
            refine ⟨5387047851917210095988759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591365234611473397325839 5387047851917210095988759)
            ·
              refine ⟨8080571777875815143983139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387047851917210095988759 8080571777875815143983139)
              ·
                refine ⟨12120857666813722715974709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8080571777875815143983139 12120857666813722715974709)
                ·
                  refine ⟨1136330406263786504622629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12120857666813722715974709 1136330406263786504622629)
                  ·
                    refine ⟨213061951174459969616743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136330406263786504622629 213061951174459969616743)
                    ·
                      rfl

theorem cell23_1244810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_1244810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244810 prefixEnd_1244810 := by exact prefixLift 1244810
  have htrace : WordTrace (prefixWord ++ tailWord_1244810) baseStart_1244810 baseEnd_1244810 := by
    simpa [prefixWord, tailWord_1244810, baseEnd_1244810] using wordTrace_append hprefix tailTrace_1244810
  have hstable : (prefixWord ++ tailWord_1244810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244810).length < 2 ^ (prefixWord ++ tailWord_1244810).sum := by decide
  have hdescent : baseEnd_1244810 < baseStart_1244810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244830 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1244830 : Nat := 118140960795 + 1244830 * 2 ^ 59
def prefixEnd_1244830 : Nat := 4983230072969 + 3 ^ 40 * 1244830 * 2
def baseEnd_1244830 : Nat := 639196123136469830600137

theorem tailTrace_1244830 : CollatzResearch.WordTrace tailWord_1244830 prefixEnd_1244830 639196123136469830600137 := by
  unfold tailWord_1244830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675335010025123110394493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30268453386800656588770629 5675335010025123110394493)
  ·
    refine ⟨2128250628759421166397935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5675335010025123110394493 2128250628759421166397935)
    ·
      refine ⟨3192375943139131749596903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128250628759421166397935 3192375943139131749596903)
      ·
        refine ⟨4788563914708697624395355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3192375943139131749596903 4788563914708697624395355)
        ·
          refine ⟨7182845872063046436593033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788563914708697624395355 7182845872063046436593033)
          ·
            refine ⟨5387134404047284827444775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7182845872063046436593033 5387134404047284827444775)
            ·
              refine ⟨8080701606070927241167163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387134404047284827444775 8080701606070927241167163)
              ·
                refine ⟨12121052409106390861750745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8080701606070927241167163 12121052409106390861750745)
                ·
                  refine ⟨9090789306829793146313059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12121052409106390861750745 9090789306829793146313059)
                  ·
                    refine ⟨13636183960244689719469589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9090789306829793146313059 13636183960244689719469589)
                    ·
                      refine ⟨639196123136469830600137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13636183960244689719469589 639196123136469830600137)
                      ·
                        rfl

theorem cell23_1244830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1244830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244830 prefixEnd_1244830 := by exact prefixLift 1244830
  have htrace : WordTrace (prefixWord ++ tailWord_1244830) baseStart_1244830 baseEnd_1244830 := by
    simpa [prefixWord, tailWord_1244830, baseEnd_1244830] using wordTrace_append hprefix tailTrace_1244830
  have hstable : (prefixWord ++ tailWord_1244830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244830).length < 2 ^ (prefixWord ++ tailWord_1244830).sum := by decide
  have hdescent : baseEnd_1244830 < baseStart_1244830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244900 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_1244900 : Nat := 118140960795 + 1244900 * 2 ^ 59
def prefixEnd_1244900 : Nat := 4983230072969 + 3 ^ 40 * 1244900 * 2
def baseEnd_1244900 : Nat := 213077355594094852241605

theorem tailTrace_1244900 : CollatzResearch.WordTrace tailWord_1244900 prefixEnd_1244900 213077355594094852241605 := by
  unfold tailWord_1244900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22702616594973693419102077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30270155459964924558802769 22702616594973693419102077)
  ·
    refine ⟨8513481223115135032163279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22702616594973693419102077 8513481223115135032163279)
    ·
      refine ⟨12770221834672702548244919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8513481223115135032163279 12770221834672702548244919)
      ·
        refine ⟨19155332752009053822367379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12770221834672702548244919 19155332752009053822367379)
        ·
          refine ⟨28732999128013580733551069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19155332752009053822367379 28732999128013580733551069)
          ·
            refine ⟨10774874673005092775081651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28732999128013580733551069 10774874673005092775081651)
            ·
              refine ⟨16162312009507639162622477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10774874673005092775081651 16162312009507639162622477)
              ·
                refine ⟨6060867003565364685983429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16162312009507639162622477 6060867003565364685983429)
                ·
                  refine ⟨1136412563168505878621893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6060867003565364685983429 1136412563168505878621893)
                  ·
                    refine ⟨213077355594094852241605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136412563168505878621893 213077355594094852241605)
                    ·
                      rfl

theorem cell23_1244900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_1244900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244900 prefixEnd_1244900 := by exact prefixLift 1244900
  have htrace : WordTrace (prefixWord ++ tailWord_1244900) baseStart_1244900 baseEnd_1244900 := by
    simpa [prefixWord, tailWord_1244900, baseEnd_1244900] using wordTrace_append hprefix tailTrace_1244900
  have hstable : (prefixWord ++ tailWord_1244900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244900).length < 2 ^ (prefixWord ++ tailWord_1244900).sum := by decide
  have hdescent : baseEnd_1244900 < baseStart_1244900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244901 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1244901 : Nat := 118140960795 + 1244901 * 2 ^ 59
def prefixEnd_1244901 : Nat := 4983230072969 + 3 ^ 40 * 1244901 * 2
def baseEnd_1244901 : Nat := 639232580262939052812311

theorem tailTrace_1244901 : CollatzResearch.WordTrace tailWord_1244901 prefixEnd_1244901 639232580262939052812311 := by
  unfold tailWord_1244901
  simp only [CollatzResearch.WordTrace]
  refine ⟨45405269662943764008990557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30270179775295842672660371 45405269662943764008990557)
  ·
    refine ⟨17026976123603911503371459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45405269662943764008990557 17026976123603911503371459)
    ·
      refine ⟨25540464185405867255057189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17026976123603911503371459 25540464185405867255057189)
      ·
        refine ⟨4788837034763600110323223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25540464185405867255057189 4788837034763600110323223)
        ·
          refine ⟨7183255552145400165484835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788837034763600110323223 7183255552145400165484835)
          ·
            refine ⟨10774883328218100248227253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183255552145400165484835 10774883328218100248227253)
            ·
              refine ⟨1010145312020446898271305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10774883328218100248227253 1010145312020446898271305)
              ·
                refine ⟨757608984015335173703479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010145312020446898271305 757608984015335173703479)
                ·
                  refine ⟨1136413476023002760555219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757608984015335173703479 1136413476023002760555219)
                  ·
                    refine ⟨1704620214034504140832829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1136413476023002760555219 1704620214034504140832829)
                    ·
                      refine ⟨639232580262939052812311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1704620214034504140832829 639232580262939052812311)
                      ·
                        rfl

theorem cell23_1244901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1244901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244901 prefixEnd_1244901 := by exact prefixLift 1244901
  have htrace : WordTrace (prefixWord ++ tailWord_1244901) baseStart_1244901 baseEnd_1244901 := by
    simpa [prefixWord, tailWord_1244901, baseEnd_1244901] using wordTrace_append hprefix tailTrace_1244901
  have hstable : (prefixWord ++ tailWord_1244901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244901).length < 2 ^ (prefixWord ++ tailWord_1244901).sum := by decide
  have hdescent : baseEnd_1244901 < baseStart_1244901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244910 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1244910 : Nat := 118140960795 + 1244910 * 2 ^ 59
def prefixEnd_1244910 : Nat := 4983230072969 + 3 ^ 40 * 1244910 * 2
def baseEnd_1244910 : Nat := 639237201588829517599769

theorem tailTrace_1244910 : CollatzResearch.WordTrace tailWord_1244910 prefixEnd_1244910 639237201588829517599769 := by
  unfold tailWord_1244910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675699739988894818258523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30270398613274105697378789 5675699739988894818258523)
  ·
    refine ⟨8513549609983342227387785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675699739988894818258523 8513549609983342227387785)
    ·
      refine ⟨6385162207487506670540839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8513549609983342227387785 6385162207487506670540839)
      ·
        refine ⟨9577743311231260005811259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6385162207487506670540839 9577743311231260005811259)
        ·
          refine ⟨14366614966846890008716889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9577743311231260005811259 14366614966846890008716889)
          ·
            refine ⟨10774961225135167506537667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14366614966846890008716889 10774961225135167506537667)
            ·
              refine ⟨16162441837702751259806501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10774961225135167506537667 16162441837702751259806501)
              ·
                refine ⟨3030457844569265861213719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16162441837702751259806501 3030457844569265861213719)
                ·
                  refine ⟨4545686766853898791820579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030457844569265861213719 4545686766853898791820579)
                  ·
                    refine ⟨6818530150280848187730869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545686766853898791820579 6818530150280848187730869)
                    ·
                      refine ⟨639237201588829517599769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6818530150280848187730869 639237201588829517599769)
                      ·
                        rfl

theorem cell23_1244910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1244910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244910 prefixEnd_1244910 := by exact prefixLift 1244910
  have htrace : WordTrace (prefixWord ++ tailWord_1244910) baseStart_1244910 baseEnd_1244910 := by
    simpa [prefixWord, tailWord_1244910, baseEnd_1244910] using wordTrace_append hprefix tailTrace_1244910
  have hstable : (prefixWord ++ tailWord_1244910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244910).length < 2 ^ (prefixWord ++ tailWord_1244910).sum := by decide
  have hdescent : baseEnd_1244910 < baseStart_1244910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244913 : List Nat := [1, 2, 2, 2, 2, 3, 1, 10]
def baseStart_1244913 : Nat := 118140960795 + 1244913 * 2 ^ 59
def prefixEnd_1244913 : Nat := 4983230072969 + 3 ^ 40 * 1244913 * 2
def baseEnd_1244913 : Nat := 23675508964103444661565

theorem tailTrace_1244913 : CollatzResearch.WordTrace tailWord_1244913 prefixEnd_1244913 23675508964103444661565 := by
  unfold tailWord_1244913
  simp only [CollatzResearch.WordTrace]
  refine ⟨45405707338900290058427393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30270471559266860038951595 45405707338900290058427393)
  ·
    refine ⟨34054280504175217543820545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45405707338900290058427393 34054280504175217543820545)
    ·
      refine ⟨25540710378131413157865409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34054280504175217543820545 25540710378131413157865409)
      ·
        refine ⟨19155532783598559868399057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25540710378131413157865409 19155532783598559868399057)
        ·
          refine ⟨14366649587698919901299293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19155532783598559868399057 14366649587698919901299293)
          ·
            refine ⟨5387493595387094962987235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14366649587698919901299293 5387493595387094962987235)
            ·
              refine ⟨8081240393080642444480853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387493595387094962987235 8081240393080642444480853)
              ·
                refine ⟨23675508964103444661565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8081240393080642444480853 23675508964103444661565)
                ·
                  rfl

theorem cell23_1244913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 10].length) (baseStart_1244913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244913 prefixEnd_1244913 := by exact prefixLift 1244913
  have htrace : WordTrace (prefixWord ++ tailWord_1244913) baseStart_1244913 baseEnd_1244913 := by
    simpa [prefixWord, tailWord_1244913, baseEnd_1244913] using wordTrace_append hprefix tailTrace_1244913
  have hstable : (prefixWord ++ tailWord_1244913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244913).length < 2 ^ (prefixWord ++ tailWord_1244913).sum := by decide
  have hdescent : baseEnd_1244913 < baseStart_1244913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244927 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 3]
def baseStart_1244927 : Nat := 118140960795 + 1244927 * 2 ^ 59
def prefixEnd_1244927 : Nat := 4983230072969 + 3 ^ 40 * 1244927 * 2
def baseEnd_1244927 : Nat := 639245930759955951087191

theorem tailTrace_1244927 : CollatzResearch.WordTrace tailWord_1244927 prefixEnd_1244927 639245930759955951087191 := by
  unfold tailWord_1244927
  simp only [CollatzResearch.WordTrace]
  refine ⟨45406217960849570449437035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30270811973899713632958023 45406217960849570449437035)
  ·
    refine ⟨68109326941274355674155553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45406217960849570449437035 68109326941274355674155553)
    ·
      refine ⟨51081995205955766755616665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68109326941274355674155553 51081995205955766755616665)
      ·
        refine ⟨38311496404466825066712499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51081995205955766755616665 38311496404466825066712499)
        ·
          refine ⟨57467244606700237600068749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38311496404466825066712499 57467244606700237600068749)
          ·
            refine ⟨21550216727512589100025781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57467244606700237600068749 21550216727512589100025781)
            ·
              refine ⟨2020332818204305228127417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21550216727512589100025781 2020332818204305228127417)
              ·
                refine ⟨1515249613653228921095563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020332818204305228127417 1515249613653228921095563)
                ·
                  refine ⟨2272874420479843381643345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515249613653228921095563 2272874420479843381643345)
                  ·
                    refine ⟨1704655815359882536232509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272874420479843381643345 1704655815359882536232509)
                    ·
                      refine ⟨639245930759955951087191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1704655815359882536232509 639245930759955951087191)
                      ·
                        rfl

theorem cell23_1244927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_1244927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244927 prefixEnd_1244927 := by exact prefixLift 1244927
  have htrace : WordTrace (prefixWord ++ tailWord_1244927) baseStart_1244927 baseEnd_1244927 := by
    simpa [prefixWord, tailWord_1244927, baseEnd_1244927] using wordTrace_append hprefix tailTrace_1244927
  have hstable : (prefixWord ++ tailWord_1244927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244927).length < 2 ^ (prefixWord ++ tailWord_1244927).sum := by decide
  have hdescent : baseEnd_1244927 < baseStart_1244927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244930 : List Nat := [3, 4, 1, 1, 1, 1, 1, 11]
def baseStart_1244930 : Nat := 118140960795 + 1244930 * 2 ^ 59
def prefixEnd_1244930 : Nat := 4983230072969 + 3 ^ 40 * 1244930 * 2
def baseEnd_1244930 : Nat := 23675832266737757012951

theorem tailTrace_1244930 : CollatzResearch.WordTrace tailWord_1244930 prefixEnd_1244930 23675832266737757012951 := by
  unfold tailWord_1244930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11351581844959675490449061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30270884919892467974530829 11351581844959675490449061)
  ·
    refine ⟨2128421595929939154459199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11351581844959675490449061 2128421595929939154459199)
    ·
      refine ⟨3192632393894908731688799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128421595929939154459199 3192632393894908731688799)
      ·
        refine ⟨4788948590842363097533199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3192632393894908731688799 4788948590842363097533199)
        ·
          refine ⟨7183422886263544646299799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788948590842363097533199 7183422886263544646299799)
          ·
            refine ⟨10775134329395316969449699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183422886263544646299799 10775134329395316969449699)
            ·
              refine ⟨16162701494092975454174549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10775134329395316969449699 16162701494092975454174549)
              ·
                refine ⟨23675832266737757012951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 16162701494092975454174549 23675832266737757012951)
                ·
                  rfl

theorem cell23_1244930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_1244930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244930 prefixEnd_1244930 := by exact prefixLift 1244930
  have htrace : WordTrace (prefixWord ++ tailWord_1244930) baseStart_1244930 baseEnd_1244930 := by
    simpa [prefixWord, tailWord_1244930, baseEnd_1244930] using wordTrace_append hprefix tailTrace_1244930
  have hstable : (prefixWord ++ tailWord_1244930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244930).length < 2 ^ (prefixWord ++ tailWord_1244930).sum := by decide
  have hdescent : baseEnd_1244930 < baseStart_1244930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244940 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1244940 : Nat := 118140960795 + 1244940 * 2 ^ 59
def prefixEnd_1244940 : Nat := 4983230072969 + 3 ^ 40 * 1244940 * 2
def baseEnd_1244940 : Nat := 639252606008464400224631

theorem tailTrace_1244940 : CollatzResearch.WordTrace tailWord_1244940 prefixEnd_1244940 639252606008464400224631 := by
  unfold tailWord_1244940
  simp only [CollatzResearch.WordTrace]
  refine ⟨22703346054901236834830137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30271128073201649113106849 22703346054901236834830137)
  ·
    refine ⟨17027509541175927626122603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22703346054901236834830137 17027509541175927626122603)
    ·
      refine ⟨25541264311763891439183905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17027509541175927626122603 25541264311763891439183905)
      ·
        refine ⟨19155948233822918579387929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25541264311763891439183905 19155948233822918579387929)
        ·
          refine ⟨14366961175367188934540947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19155948233822918579387929 14366961175367188934540947)
          ·
            refine ⟨21550441763050783401811421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14366961175367188934540947 21550441763050783401811421)
            ·
              refine ⟨8081415661144043775679283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21550441763050783401811421 8081415661144043775679283)
              ·
                refine ⟨12122123491716065663518925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081415661144043775679283 12122123491716065663518925)
                ·
                  refine ⟨4545796309393524623819597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12122123491716065663518925 4545796309393524623819597)
                  ·
                    refine ⟨1704673616022571733932349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4545796309393524623819597 1704673616022571733932349)
                    ·
                      refine ⟨639252606008464400224631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1704673616022571733932349 639252606008464400224631)
                      ·
                        rfl

theorem cell23_1244940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1244940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244940 prefixEnd_1244940 := by exact prefixLift 1244940
  have htrace : WordTrace (prefixWord ++ tailWord_1244940) baseStart_1244940 baseEnd_1244940 := by
    simpa [prefixWord, tailWord_1244940, baseEnd_1244940] using wordTrace_append hprefix tailTrace_1244940
  have hstable : (prefixWord ++ tailWord_1244940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244940).length < 2 ^ (prefixWord ++ tailWord_1244940).sum := by decide
  have hdescent : baseEnd_1244940 < baseStart_1244940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244953 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_1244953 : Nat := 118140960795 + 1244953 * 2 ^ 59
def prefixEnd_1244953 : Nat := 4983230072969 + 3 ^ 40 * 1244953 * 2
def baseEnd_1244953 : Nat := 639259281256972849362071

theorem tailTrace_1244953 : CollatzResearch.WordTrace tailWord_1244953 prefixEnd_1244953 639259281256972849362071 := by
  unfold tailWord_1244953
  simp only [CollatzResearch.WordTrace]
  refine ⟨45407166258755376889883513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30271444172503584593255675 45407166258755376889883513)
  ·
    refine ⟨34055374694066532667412635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45407166258755376889883513 34055374694066532667412635)
    ·
      refine ⟨51083062041099799001118953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34055374694066532667412635 51083062041099799001118953)
      ·
        refine ⟨38312296530824849250839215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51083062041099799001118953 38312296530824849250839215)
        ·
          refine ⟨57468444796237273876258823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38312296530824849250839215 57468444796237273876258823)
          ·
            refine ⟨86202667194355910814388235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57468444796237273876258823 86202667194355910814388235)
            ·
              refine ⟨129304000791533866221582353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86202667194355910814388235 129304000791533866221582353)
              ·
                refine ⟨96978000593650399666186765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129304000791533866221582353 96978000593650399666186765)
                ·
                  refine ⟨36366750222618899874820037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96978000593650399666186765 36366750222618899874820037)
                  ·
                    refine ⟨6818765666741043726528757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36366750222618899874820037 6818765666741043726528757)
                    ·
                      refine ⟨639259281256972849362071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6818765666741043726528757 639259281256972849362071)
                      ·
                        rfl

theorem cell23_1244953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_1244953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244953 prefixEnd_1244953 := by exact prefixLift 1244953
  have htrace : WordTrace (prefixWord ++ tailWord_1244953) baseStart_1244953 baseEnd_1244953 := by
    simpa [prefixWord, tailWord_1244953, baseEnd_1244953] using wordTrace_append hprefix tailTrace_1244953
  have hstable : (prefixWord ++ tailWord_1244953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244953).length < 2 ^ (prefixWord ++ tailWord_1244953).sum := by decide
  have hdescent : baseEnd_1244953 < baseStart_1244953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244997 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 1, 4, 2]
def baseStart_1244997 : Nat := 118140960795 + 1244997 * 2 ^ 59
def prefixEnd_1244997 : Nat := 4983230072969 + 3 ^ 40 * 1244997 * 2
def baseEnd_1244997 : Nat := 639281874405770677211869

theorem tailTrace_1244997 : CollatzResearch.WordTrace tailWord_1244997 prefixEnd_1244997 639281874405770677211869 := by
  unfold tailWord_1244997
  simp only [CollatzResearch.WordTrace]
  refine ⟨45408771070595972404485245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30272514047063981602990163 45408771070595972404485245)
  ·
    refine ⟨17028289151473489651681967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45408771070595972404485245 17028289151473489651681967)
    ·
      refine ⟨25542433727210234477522951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17028289151473489651681967 25542433727210234477522951)
      ·
        refine ⟨38313650590815351716284427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25542433727210234477522951 38313650590815351716284427)
        ·
          refine ⟨57470475886223027574426641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38313650590815351716284427 57470475886223027574426641)
          ·
            refine ⟨43102856914667270680819981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57470475886223027574426641 43102856914667270680819981)
            ·
              refine ⟨16163571343000226505307493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43102856914667270680819981 16163571343000226505307493)
              ·
                refine ⟨3030669626812542469745155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16163571343000226505307493 3030669626812542469745155)
                ·
                  refine ⟨4546004440218813704617733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030669626812542469745155 4546004440218813704617733)
                  ·
                    refine ⟨852375832541027569615825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546004440218813704617733 852375832541027569615825)
                    ·
                      refine ⟨639281874405770677211869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852375832541027569615825 639281874405770677211869)
                      ·
                        rfl

theorem cell23_1244997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_1244997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1244997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1244997 prefixEnd_1244997 := by exact prefixLift 1244997
  have htrace : WordTrace (prefixWord ++ tailWord_1244997) baseStart_1244997 baseEnd_1244997 := by
    simpa [prefixWord, tailWord_1244997, baseEnd_1244997] using wordTrace_append hprefix tailTrace_1244997
  have hstable : (prefixWord ++ tailWord_1244997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244997).length < 2 ^ (prefixWord ++ tailWord_1244997).sum := by decide
  have hdescent : baseEnd_1244997 < baseStart_1244997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245050 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_1245050 : Nat := 118140960795 + 1245050 * 2 ^ 59
def prefixEnd_1245050 : Nat := 4983230072969 + 3 ^ 40 * 1245050 * 2
def baseEnd_1245050 : Nat := 213103029626819656616375

theorem tailTrace_1245050 : CollatzResearch.WordTrace tailWord_1245050 prefixEnd_1245050 213103029626819656616375 := by
  unfold tailWord_1245050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11352676034850990614041151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30273802759602641637443069 11352676034850990614041151)
  ·
    refine ⟨17029014052276485921061727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11352676034850990614041151 17029014052276485921061727)
    ·
      refine ⟨25543521078414728881592591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17029014052276485921061727 25543521078414728881592591)
      ·
        refine ⟨38315281617622093322388887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25543521078414728881592591 38315281617622093322388887)
        ·
          refine ⟨57472922426433139983583331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38315281617622093322388887 57472922426433139983583331)
          ·
            refine ⟨86209383639649709975374997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57472922426433139983583331 86209383639649709975374997)
            ·
              refine ⟨4041064858108580155095703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86209383639649709975374997 4041064858108580155095703)
              ·
                refine ⟨6061597287162870232643555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041064858108580155095703 6061597287162870232643555)
                ·
                  refine ⟨9092395930744305348965333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061597287162870232643555 9092395930744305348965333)
                  ·
                    refine ⟨213103029626819656616375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9092395930744305348965333 213103029626819656616375)
                    ·
                      rfl

theorem cell23_1245050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_1245050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245050 prefixEnd_1245050 := by exact prefixLift 1245050
  have htrace : WordTrace (prefixWord ++ tailWord_1245050) baseStart_1245050 baseEnd_1245050 := by
    simpa [prefixWord, tailWord_1245050, baseEnd_1245050] using wordTrace_append hprefix tailTrace_1245050
  have hstable : (prefixWord ++ tailWord_1245050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245050).length < 2 ^ (prefixWord ++ tailWord_1245050).sum := by decide
  have hdescent : baseEnd_1245050 < baseStart_1245050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245165 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1245165 : Nat := 118140960795 + 1245165 * 2 ^ 59
def prefixEnd_1245165 : Nat := 4983230072969 + 3 ^ 40 * 1245165 * 2
def baseEnd_1245165 : Nat := 213122713051908673303699

theorem tailTrace_1245165 : CollatzResearch.WordTrace tailWord_1245165 prefixEnd_1245165 213122713051908673303699 := by
  unfold tailWord_1245165
  simp only [CollatzResearch.WordTrace]
  refine ⟨45414898533987337096600949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30276599022658224731067299 45414898533987337096600949)
  ·
    refine ⟨4257646737561312852806339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45414898533987337096600949 4257646737561312852806339)
    ·
      refine ⟨6386470106341969279209509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4257646737561312852806339 6386470106341969279209509)
      ·
        refine ⟨1197463144939119239851783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6386470106341969279209509 1197463144939119239851783)
        ·
          refine ⟨1796194717408678859777675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1197463144939119239851783 1796194717408678859777675)
          ·
            refine ⟨2694292076113018289666513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796194717408678859777675 2694292076113018289666513)
            ·
              refine ⟨2020719057084763717249885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2694292076113018289666513 2020719057084763717249885)
              ·
                refine ⟨757769646406786393968707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2020719057084763717249885 757769646406786393968707)
                ·
                  refine ⟨1136654469610179590953061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757769646406786393968707 1136654469610179590953061)
                  ·
                    refine ⟨213122713051908673303699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136654469610179590953061 213122713051908673303699)
                    ·
                      rfl

theorem cell23_1245165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1245165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245165 prefixEnd_1245165 := by exact prefixLift 1245165
  have htrace : WordTrace (prefixWord ++ tailWord_1245165) baseStart_1245165 baseEnd_1245165 := by
    simpa [prefixWord, tailWord_1245165, baseEnd_1245165] using wordTrace_append hprefix tailTrace_1245165
  have hstable : (prefixWord ++ tailWord_1245165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245165).length < 2 ^ (prefixWord ++ tailWord_1245165).sum := by decide
  have hdescent : baseEnd_1245165 < baseStart_1245165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245228 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 1, 2, 2]
def baseStart_1245228 : Nat := 118140960795 + 1245228 * 2 ^ 59
def prefixEnd_1245228 : Nat := 4983230072969 + 3 ^ 40 * 1245228 * 2
def baseEnd_1245228 : Nat := 639400488436959273423307

theorem tailTrace_1245228 : CollatzResearch.WordTrace tailWord_1245228 prefixEnd_1245228 639400488436959273423307 := by
  unfold tailWord_1245228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22708598166379549428072169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30278130888506065904096225 22708598166379549428072169)
  ·
    refine ⟨17031448624784662071054127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22708598166379549428072169 17031448624784662071054127)
    ·
      refine ⟨25547172937176993106581191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17031448624784662071054127 25547172937176993106581191)
      ·
        refine ⟨38320759405765489659871787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25547172937176993106581191 38320759405765489659871787)
        ·
          refine ⟨57481139108648234489807681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38320759405765489659871787 57481139108648234489807681)
          ·
            refine ⟨43110854331486175867355761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57481139108648234489807681 43110854331486175867355761)
            ·
              refine ⟨32333140748614631900516821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43110854331486175867355761 32333140748614631900516821)
              ·
                refine ⟨757807986295655435168363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32333140748614631900516821 757807986295655435168363)
                ·
                  refine ⟨1136711979443483152752545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757807986295655435168363 1136711979443483152752545)
                  ·
                    refine ⟨852533984582612364564409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1136711979443483152752545 852533984582612364564409)
                    ·
                      refine ⟨639400488436959273423307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852533984582612364564409 639400488436959273423307)
                      ·
                        rfl

theorem cell23_1245228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_1245228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245228 prefixEnd_1245228 := by exact prefixLift 1245228
  have htrace : WordTrace (prefixWord ++ tailWord_1245228) baseStart_1245228 baseEnd_1245228 := by
    simpa [prefixWord, tailWord_1245228, baseEnd_1245228] using wordTrace_append hprefix tailTrace_1245228
  have hstable : (prefixWord ++ tailWord_1245228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245228).length < 2 ^ (prefixWord ++ tailWord_1245228).sum := by decide
  have hdescent : baseEnd_1245228 < baseStart_1245228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245261 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1245261 : Nat := 118140960795 + 1245261 * 2 ^ 59
def prefixEnd_1245261 : Nat := 4983230072969 + 3 ^ 40 * 1245261 * 2
def baseEnd_1245261 : Nat := 639417433298557644310655

theorem tailTrace_1245261 : CollatzResearch.WordTrace tailWord_1245261 prefixEnd_1245261 639417433298557644310655 := by
  unfold tailWord_1245261
  simp only [CollatzResearch.WordTrace]
  refine ⟨45418399941639545492095637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30278933294426363661397091 45418399941639545492095637)
  ·
    refine ⟨2128987497264353694941983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45418399941639545492095637 2128987497264353694941983)
    ·
      refine ⟨3193481245896530542412975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128987497264353694941983 3193481245896530542412975)
      ·
        refine ⟨4790221868844795813619463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193481245896530542412975 4790221868844795813619463)
        ·
          refine ⟨7185332803267193720429195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790221868844795813619463 7185332803267193720429195)
          ·
            refine ⟨10777999204900790580643793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185332803267193720429195 10777999204900790580643793)
            ·
              refine ⟨8083499403675592935482845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10777999204900790580643793 8083499403675592935482845)
              ·
                refine ⟨3031312276378347350806067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8083499403675592935482845 3031312276378347350806067)
                ·
                  refine ⟨4546968414567521026209101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031312276378347350806067 4546968414567521026209101)
                  ·
                    refine ⟨1705113155462820384828413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4546968414567521026209101 1705113155462820384828413)
                    ·
                      refine ⟨639417433298557644310655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1705113155462820384828413 639417433298557644310655)
                      ·
                        rfl

theorem cell23_1245261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1245261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245261 prefixEnd_1245261 := by exact prefixLift 1245261
  have htrace : WordTrace (prefixWord ++ tailWord_1245261) baseStart_1245261 baseEnd_1245261 := by
    simpa [prefixWord, tailWord_1245261, baseEnd_1245261] using wordTrace_append hprefix tailTrace_1245261
  have hstable : (prefixWord ++ tailWord_1245261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245261).length < 2 ^ (prefixWord ++ tailWord_1245261).sum := by decide
  have hdescent : baseEnd_1245261 < baseStart_1245261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245294 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1245294 : Nat := 118140960795 + 1245294 * 2 ^ 59
def prefixEnd_1245294 : Nat := 4983230072969 + 3 ^ 40 * 1245294 * 2
def baseEnd_1245294 : Nat := 213144792720052005066001

theorem tailTrace_1245294 : CollatzResearch.WordTrace tailWord_1245294 prefixEnd_1245294 213144792720052005066001 := by
  unfold tailWord_1245294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5677450443814999016005867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30279735700346661418697957 5677450443814999016005867)
  ·
    refine ⟨8516175665722498524008801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5677450443814999016005867 8516175665722498524008801)
    ·
      refine ⟨6387131749291873893006601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8516175665722498524008801 6387131749291873893006601)
      ·
        refine ⟨4790348811968905419754951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6387131749291873893006601 4790348811968905419754951)
        ·
          refine ⟨7185523217953358129632427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790348811968905419754951 7185523217953358129632427)
          ·
            refine ⟨10778284826930037194448641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185523217953358129632427 10778284826930037194448641)
            ·
              refine ⟨8083713620197527895836481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10778284826930037194448641 8083713620197527895836481)
              ·
                refine ⟨6062785215148145921877361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8083713620197527895836481 6062785215148145921877361)
                ·
                  refine ⟨4547088911361109441408021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062785215148145921877361 4547088911361109441408021)
                  ·
                    refine ⟨213144792720052005066001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4547088911361109441408021 213144792720052005066001)
                    ·
                      rfl

theorem cell23_1245294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1245294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245294 prefixEnd_1245294 := by exact prefixLift 1245294
  have htrace : WordTrace (prefixWord ++ tailWord_1245294) baseStart_1245294 baseEnd_1245294 := by
    simpa [prefixWord, tailWord_1245294, baseEnd_1245294] using wordTrace_append hprefix tailTrace_1245294
  have hstable : (prefixWord ++ tailWord_1245294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245294).length < 2 ^ (prefixWord ++ tailWord_1245294).sum := by decide
  have hdescent : baseEnd_1245294 < baseStart_1245294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245341 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 5]
def baseStart_1245341 : Nat := 118140960795 + 1245341 * 2 ^ 59
def prefixEnd_1245341 : Nat := 4983230072969 + 3 ^ 40 * 1245341 * 2
def baseEnd_1245341 : Nat := 71050945750101925701143

theorem tailTrace_1245341 : CollatzResearch.WordTrace tailWord_1245341 prefixEnd_1245341 71050945750101925701143 := by
  unfold tailWord_1245341
  simp only [CollatzResearch.WordTrace]
  refine ⟨45421317781349719155007877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30280878520899812770005251 45421317781349719155007877)
  ·
    refine ⟨8516497084003072341563977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45421317781349719155007877 8516497084003072341563977)
    ·
      refine ⟨6387372813002304256172983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8516497084003072341563977 6387372813002304256172983)
      ·
        refine ⟨9581059219503456384259475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6387372813002304256172983 9581059219503456384259475)
        ·
          refine ⟨14371588829255184576389213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9581059219503456384259475 14371588829255184576389213)
          ·
            refine ⟨5389345810970694216145955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14371588829255184576389213 5389345810970694216145955)
            ·
              refine ⟨8084018716456041324218933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389345810970694216145955 8084018716456041324218933)
              ·
                refine ⟨757876754667753874145525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8084018716456041324218933 757876754667753874145525)
                ·
                  refine ⟨71050945750101925701143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 757876754667753874145525 71050945750101925701143)
                  ·
                    rfl

theorem cell23_1245341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_1245341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245341 prefixEnd_1245341 := by exact prefixLift 1245341
  have htrace : WordTrace (prefixWord ++ tailWord_1245341) baseStart_1245341 baseEnd_1245341 := by
    simpa [prefixWord, tailWord_1245341, baseEnd_1245341] using wordTrace_append hprefix tailTrace_1245341
  have hstable : (prefixWord ++ tailWord_1245341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245341).length < 2 ^ (prefixWord ++ tailWord_1245341).sum := by decide
  have hdescent : baseEnd_1245341 < baseStart_1245341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245461 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1245461 : Nat := 118140960795 + 1245461 * 2 ^ 59
def prefixEnd_1245461 : Nat := 4983230072969 + 3 ^ 40 * 1245461 * 2
def baseEnd_1245461 : Nat := 213173376476485620603245

theorem tailTrace_1245461 : CollatzResearch.WordTrace tailWord_1245461 prefixEnd_1245461 213173376476485620603245 := by
  unfold tailWord_1245461
  simp only [CollatzResearch.WordTrace]
  refine ⟨45425694540914979649376237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30283796360609986432917491 45425694540914979649376237)
  ·
    refine ⟨17034635452843117368516089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45425694540914979649376237 17034635452843117368516089)
    ·
      refine ⟨12775976589632338026387067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17034635452843117368516089 12775976589632338026387067)
      ·
        refine ⟨19163964884448507039580601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12775976589632338026387067 19163964884448507039580601)
        ·
          refine ⟨14372973663336380279685451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19163964884448507039580601 14372973663336380279685451)
          ·
            refine ⟨21559460495004570419528177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14372973663336380279685451 21559460495004570419528177)
            ·
              refine ⟨16169595371253427814646133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21559460495004570419528177 16169595371253427814646133)
              ·
                refine ⟨1515899566055008857623075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16169595371253427814646133 1515899566055008857623075)
                ·
                  refine ⟨2273849349082513286434613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515899566055008857623075 2273849349082513286434613)
                  ·
                    refine ⟨213173376476485620603245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2273849349082513286434613 213173376476485620603245)
                    ·
                      rfl

theorem cell23_1245461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1245461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245461 prefixEnd_1245461 := by exact prefixLift 1245461
  have htrace : WordTrace (prefixWord ++ tailWord_1245461) baseStart_1245461 baseEnd_1245461 := by
    simpa [prefixWord, tailWord_1245461, baseEnd_1245461] using wordTrace_append hprefix tailTrace_1245461
  have hstable : (prefixWord ++ tailWord_1245461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245461).length < 2 ^ (prefixWord ++ tailWord_1245461).sum := by decide
  have hdescent : baseEnd_1245461 < baseStart_1245461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245469 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1245469 : Nat := 118140960795 + 1245469 * 2 ^ 59
def prefixEnd_1245469 : Nat := 4983230072969 + 3 ^ 40 * 1245469 * 2
def baseEnd_1245469 : Nat := 213174745758230943503233

theorem tailTrace_1245469 : CollatzResearch.WordTrace tailWord_1245469 prefixEnd_1245469 213174745758230943503233 := by
  unfold tailWord_1245469
  simp only [CollatzResearch.WordTrace]
  refine ⟨45425986324885997015667461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30283990883257331343778307 45425986324885997015667461)
  ·
    refine ⟨8517372435916124440437649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45425986324885997015667461 8517372435916124440437649)
    ·
      refine ⟨6388029326937093330328237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8517372435916124440437649 6388029326937093330328237)
      ·
        refine ⟨2395510997601409998873089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6388029326937093330328237 2395510997601409998873089)
        ·
          refine ⟨1796633248201057499154817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2395510997601409998873089 1796633248201057499154817)
          ·
            refine ⟨1347474936150793124366113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1796633248201057499154817 1347474936150793124366113)
            ·
              refine ⟨1010606202113094843274585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347474936150793124366113 1010606202113094843274585)
              ·
                refine ⟨757954651584821132455939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010606202113094843274585 757954651584821132455939)
                ·
                  refine ⟨1136931977377231698683909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757954651584821132455939 1136931977377231698683909)
                  ·
                    refine ⟨213174745758230943503233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136931977377231698683909 213174745758230943503233)
                    ·
                      rfl

theorem cell23_1245469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1245469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245469 prefixEnd_1245469 := by exact prefixLift 1245469
  have htrace : WordTrace (prefixWord ++ tailWord_1245469) baseStart_1245469 baseEnd_1245469 := by
    simpa [prefixWord, tailWord_1245469, baseEnd_1245469] using wordTrace_append hprefix tailTrace_1245469
  have hstable : (prefixWord ++ tailWord_1245469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245469).length < 2 ^ (prefixWord ++ tailWord_1245469).sum := by decide
  have hdescent : baseEnd_1245469 < baseStart_1245469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245475 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 1, 1, 3]
def baseStart_1245475 : Nat := 118140960795 + 1245475 * 2 ^ 59
def prefixEnd_1245475 : Nat := 4983230072969 + 3 ^ 40 * 1245475 * 2
def baseEnd_1245475 : Nat := 639527318158619807034671

theorem tailTrace_1245475 : CollatzResearch.WordTrace tailWord_1245475 prefixEnd_1245475 639527318158619807034671 := by
  unfold tailWord_1245475
  simp only [CollatzResearch.WordTrace]
  refine ⟨45426205162864260040385879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30284136775242840026923919 45426205162864260040385879)
  ·
    refine ⟨68139307744296390060578819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45426205162864260040385879 68139307744296390060578819)
    ·
      refine ⟨102208961616444585090868229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68139307744296390060578819 102208961616444585090868229)
      ·
        refine ⟨19164180303083359704537793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102208961616444585090868229 19164180303083359704537793)
        ·
          refine ⟨14373135227312519778403345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19164180303083359704537793 14373135227312519778403345)
          ·
            refine ⟨10779851420484389833802509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14373135227312519778403345 10779851420484389833802509)
            ·
              refine ⟨4042444282681646187675941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10779851420484389833802509 4042444282681646187675941)
              ·
                refine ⟨757958303002808660189239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4042444282681646187675941 757958303002808660189239)
                ·
                  refine ⟨1136937454504212990283859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757958303002808660189239 1136937454504212990283859)
                  ·
                    refine ⟨1705406181756319485425789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1136937454504212990283859 1705406181756319485425789)
                    ·
                      refine ⟨639527318158619807034671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1705406181756319485425789 639527318158619807034671)
                      ·
                        rfl

theorem cell23_1245475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_1245475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245475 prefixEnd_1245475 := by exact prefixLift 1245475
  have htrace : WordTrace (prefixWord ++ tailWord_1245475) baseStart_1245475 baseEnd_1245475 := by
    simpa [prefixWord, tailWord_1245475, baseEnd_1245475] using wordTrace_append hprefix tailTrace_1245475
  have hstable : (prefixWord ++ tailWord_1245475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245475).length < 2 ^ (prefixWord ++ tailWord_1245475).sum := by decide
  have hdescent : baseEnd_1245475 < baseStart_1245475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245491 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 1, 6]
def baseStart_1245491 : Nat := 118140960795 + 1245491 * 2 ^ 59
def prefixEnd_1245491 : Nat := 4983230072969 + 3 ^ 40 * 1245491 * 2
def baseEnd_1245491 : Nat := 213178511283030581478199

theorem tailTrace_1245491 : CollatzResearch.WordTrace tailWord_1245491 prefixEnd_1245491 213178511283030581478199 := by
  unfold tailWord_1245491
  simp only [CollatzResearch.WordTrace]
  refine ⟨45426788730806294772968327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30284525820537529848645551 45426788730806294772968327)
  ·
    refine ⟨68140183096209442159452491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45426788730806294772968327 68140183096209442159452491)
    ·
      refine ⟨102210274644314163239178737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68140183096209442159452491 102210274644314163239178737)
      ·
        refine ⟨76657705983235622429384053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102210274644314163239178737 76657705983235622429384053)
        ·
          refine ⟨7186659935928339602754755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76657705983235622429384053 7186659935928339602754755)
          ·
            refine ⟨10779989903892509404132133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7186659935928339602754755 10779989903892509404132133)
            ·
              refine ⟨2021248106979845513274775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10779989903892509404132133 2021248106979845513274775)
              ·
                refine ⟨3031872160469768269912163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021248106979845513274775 3031872160469768269912163)
                ·
                  refine ⟨4547808240704652404868245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031872160469768269912163 4547808240704652404868245)
                  ·
                    refine ⟨213178511283030581478199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4547808240704652404868245 213178511283030581478199)
                    ·
                      rfl

theorem cell23_1245491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 6].length) (baseStart_1245491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245491 prefixEnd_1245491 := by exact prefixLift 1245491
  have htrace : WordTrace (prefixWord ++ tailWord_1245491) baseStart_1245491 baseEnd_1245491 := by
    simpa [prefixWord, tailWord_1245491, baseEnd_1245491] using wordTrace_append hprefix tailTrace_1245491
  have hstable : (prefixWord ++ tailWord_1245491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245491).length < 2 ^ (prefixWord ++ tailWord_1245491).sum := by decide
  have hdescent : baseEnd_1245491 < baseStart_1245491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245502 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_1245502 : Nat := 118140960795 + 1245502 * 2 ^ 59
def prefixEnd_1245502 : Nat := 4983230072969 + 3 ^ 40 * 1245502 * 2
def baseEnd_1245502 : Nat := 639541182136291201397047

theorem tailTrace_1245502 : CollatzResearch.WordTrace tailWord_1245502 prefixEnd_1245502 639541182136291201397047 := by
  unfold tailWord_1245502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678398741720805456452345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30284793289177629101079173 5678398741720805456452345)
  ·
    refine ⟨4258799056290604092339259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5678398741720805456452345 4258799056290604092339259)
    ·
      refine ⟨6388198584435906138508889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4258799056290604092339259 6388198584435906138508889)
      ·
        refine ⟨4791148938326929603881667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6388198584435906138508889 4791148938326929603881667)
        ·
          refine ⟨7186723407490394405822501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4791148938326929603881667 7186723407490394405822501)
          ·
            refine ⟨1347510638904448951091719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7186723407490394405822501 1347510638904448951091719)
            ·
              refine ⟨2021265958356673426637579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347510638904448951091719 2021265958356673426637579)
              ·
                refine ⟨3031898937535010139956369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021265958356673426637579 3031898937535010139956369)
                ·
                  refine ⟨2273924203151257604967277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3031898937535010139956369 2273924203151257604967277)
                  ·
                    refine ⟨852721576181721601862729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2273924203151257604967277 852721576181721601862729)
                    ·
                      refine ⟨639541182136291201397047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852721576181721601862729 639541182136291201397047)
                      ·
                        rfl

theorem cell23_1245502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_1245502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245502 prefixEnd_1245502 := by exact prefixLift 1245502
  have htrace : WordTrace (prefixWord ++ tailWord_1245502) baseStart_1245502 baseEnd_1245502 := by
    simpa [prefixWord, tailWord_1245502, baseEnd_1245502] using wordTrace_append hprefix tailTrace_1245502
  have hstable : (prefixWord ++ tailWord_1245502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245502).length < 2 ^ (prefixWord ++ tailWord_1245502).sum := by decide
  have hdescent : baseEnd_1245502 < baseStart_1245502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245511 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1245511 : Nat := 118140960795 + 1245511 * 2 ^ 59
def prefixEnd_1245511 : Nat := 4983230072969 + 3 ^ 40 * 1245511 * 2
def baseEnd_1245511 : Nat := 639545803462181666184505

theorem tailTrace_1245511 : CollatzResearch.WordTrace tailWord_1245511 prefixEnd_1245511 639545803462181666184505 := by
  unfold tailWord_1245511
  simp only [CollatzResearch.WordTrace]
  refine ⟨45427518190733838188696387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30285012127155892125797591 45427518190733838188696387)
  ·
    refine ⟨68141277286100757283044581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45427518190733838188696387 68141277286100757283044581)
    ·
      refine ⟨12776489491143891990570859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68141277286100757283044581 12776489491143891990570859)
      ·
        refine ⟨19164734236715837985856289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12776489491143891990570859 19164734236715837985856289)
        ·
          refine ⟨14373550677536878489392217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19164734236715837985856289 14373550677536878489392217)
          ·
            refine ⟨10780163008152658867044163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14373550677536878489392217 10780163008152658867044163)
            ·
              refine ⟨16170244512228988300566245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10780163008152658867044163 16170244512228988300566245)
              ·
                refine ⟨3031920846042935306356171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16170244512228988300566245 3031920846042935306356171)
                ·
                  refine ⟨4547881269064402959534257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031920846042935306356171 4547881269064402959534257)
                  ·
                    refine ⟨3410910951798302219650693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547881269064402959534257 3410910951798302219650693)
                    ·
                      refine ⟨639545803462181666184505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3410910951798302219650693 639545803462181666184505)
                      ·
                        rfl

theorem cell23_1245511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1245511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245511 prefixEnd_1245511 := by exact prefixLift 1245511
  have htrace : WordTrace (prefixWord ++ tailWord_1245511) baseStart_1245511 baseEnd_1245511 := by
    simpa [prefixWord, tailWord_1245511, baseEnd_1245511] using wordTrace_append hprefix tailTrace_1245511
  have hstable : (prefixWord ++ tailWord_1245511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245511).length < 2 ^ (prefixWord ++ tailWord_1245511).sum := by decide
  have hdescent : baseEnd_1245511 < baseStart_1245511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245575 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_1245575 : Nat := 118140960795 + 1245575 * 2 ^ 59
def prefixEnd_1245575 : Nat := 4983230072969 + 3 ^ 40 * 1245575 * 2
def baseEnd_1245575 : Nat := 639578666224069415784211

theorem tailTrace_1245575 : CollatzResearch.WordTrace tailWord_1245575 prefixEnd_1245575 639578666224069415784211 := by
  unfold tailWord_1245575
  simp only [CollatzResearch.WordTrace]
  refine ⟨45429852462501977119026179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30286568308334651412684119 45429852462501977119026179)
  ·
    refine ⟨68144778693752965678539269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45429852462501977119026179 68144778693752965678539269)
    ·
      refine ⟨12777146005078681064726113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68144778693752965678539269 12777146005078681064726113)
      ·
        refine ⟨9582859503809010798544585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12777146005078681064726113 9582859503809010798544585)
        ·
          refine ⟨7187144627856758098908439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9582859503809010798544585 7187144627856758098908439)
          ·
            refine ⟨10780716941785137148362659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187144627856758098908439 10780716941785137148362659)
            ·
              refine ⟨16171075412677705722543989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10780716941785137148362659 16171075412677705722543989)
              ·
                refine ⟨1516038319938534911488499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16171075412677705722543989 1516038319938534911488499)
                ·
                  refine ⟨2274057479907802367232749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516038319938534911488499 2274057479907802367232749)
                  ·
                    refine ⟨852771554965425887712281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2274057479907802367232749 852771554965425887712281)
                    ·
                      refine ⟨639578666224069415784211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 852771554965425887712281 639578666224069415784211)
                      ·
                        rfl

theorem cell23_1245575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_1245575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245575 prefixEnd_1245575 := by exact prefixLift 1245575
  have htrace : WordTrace (prefixWord ++ tailWord_1245575) baseStart_1245575 baseEnd_1245575 := by
    simpa [prefixWord, tailWord_1245575, baseEnd_1245575] using wordTrace_append hprefix tailTrace_1245575
  have hstable : (prefixWord ++ tailWord_1245575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245575).length < 2 ^ (prefixWord ++ tailWord_1245575).sum := by decide
  have hdescent : baseEnd_1245575 < baseStart_1245575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245688 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 5, 4]
def baseStart_1245688 : Nat := 118140960795 + 1245688 * 2 ^ 59
def prefixEnd_1245688 : Nat := 4983230072969 + 3 ^ 40 * 1245688 * 2
def baseEnd_1245688 : Nat := 213212229846009157890397

theorem tailTrace_1245688 : CollatzResearch.WordTrace tailWord_1245688 prefixEnd_1245688 213212229846009157890397 := by
  unfold tailWord_1245688
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716986955546298708944859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30289315940728398278593145 22716986955546298708944859)
  ·
    refine ⟨34075480433319448063417289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22716986955546298708944859 34075480433319448063417289)
    ·
      refine ⟨25556610324989586047562967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34075480433319448063417289 25556610324989586047562967)
      ·
        refine ⟨38334915487484379071344451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25556610324989586047562967 38334915487484379071344451)
        ·
          refine ⟨57502373231226568607016677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38334915487484379071344451 57502373231226568607016677)
          ·
            refine ⟨10781694980854981613815627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57502373231226568607016677 10781694980854981613815627)
            ·
              refine ⟨16172542471282472420723441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781694980854981613815627 16172542471282472420723441)
              ·
                refine ⟨12129406853461854315542581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16172542471282472420723441 12129406853461854315542581)
                ·
                  refine ⟨1137131892512048842082117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12129406853461854315542581 1137131892512048842082117)
                  ·
                    refine ⟨213212229846009157890397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1137131892512048842082117 213212229846009157890397)
                    ·
                      rfl

theorem cell23_1245688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_1245688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245688 prefixEnd_1245688 := by exact prefixLift 1245688
  have htrace : WordTrace (prefixWord ++ tailWord_1245688) baseStart_1245688 baseEnd_1245688 := by
    simpa [prefixWord, tailWord_1245688, baseEnd_1245688] using wordTrace_append hprefix tailTrace_1245688
  have hstable : (prefixWord ++ tailWord_1245688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245688).length < 2 ^ (prefixWord ++ tailWord_1245688).sum := by decide
  have hdescent : baseEnd_1245688 < baseStart_1245688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245745 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_1245745 : Nat := 118140960795 + 1245745 * 2 ^ 59
def prefixEnd_1245745 : Nat := 4983230072969 + 3 ^ 40 * 1245745 * 2
def baseEnd_1245745 : Nat := 639665957935333750658429

theorem tailTrace_1245745 : CollatzResearch.WordTrace tailWord_1245745 prefixEnd_1245745 639665957935333750658429 := by
  unfold tailWord_1245745
  simp only [CollatzResearch.WordTrace]
  refine ⟨45436052871886096152714689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30290701914590730768476459 45436052871886096152714689)
  ·
    refine ⟨34077039653914572114536017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45436052871886096152714689 34077039653914572114536017)
    ·
      refine ⟨25557779740435929085902013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34077039653914572114536017 25557779740435929085902013)
      ·
        refine ⟨9584167402663473407213255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25557779740435929085902013 9584167402663473407213255)
        ·
          refine ⟨14376251103995210110819883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9584167402663473407213255 14376251103995210110819883)
          ·
            refine ⟨21564376655992815166229825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14376251103995210110819883 21564376655992815166229825)
            ·
              refine ⟨16173282491994611374672369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21564376655992815166229825 16173282491994611374672369)
              ·
                refine ⟨12129961868995958531004277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16173282491994611374672369 12129961868995958531004277)
                ·
                  refine ⟨1137183925218371112281651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12129961868995958531004277 1137183925218371112281651)
                  ·
                    refine ⟨1705775887827556668422477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137183925218371112281651 1705775887827556668422477)
                    ·
                      refine ⟨639665957935333750658429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1705775887827556668422477 639665957935333750658429)
                      ·
                        rfl

theorem cell23_1245745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_1245745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245745 prefixEnd_1245745 := by exact prefixLift 1245745
  have htrace : WordTrace (prefixWord ++ tailWord_1245745) baseStart_1245745 baseEnd_1245745 := by
    simpa [prefixWord, tailWord_1245745, baseEnd_1245745] using wordTrace_append hprefix tailTrace_1245745
  have hstable : (prefixWord ++ tailWord_1245745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245745).length < 2 ^ (prefixWord ++ tailWord_1245745).sum := by decide
  have hdescent : baseEnd_1245745 < baseStart_1245745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245808 : List Nat := [2, 1, 1, 1, 7, 11]
def baseStart_1245808 : Nat := 118140960795 + 1245808 * 2 ^ 59
def prefixEnd_1245808 : Nat := 4983230072969 + 3 ^ 40 * 1245808 * 2
def baseEnd_1245808 : Nat := 2632503321878876560373

theorem tailTrace_1245808 : CollatzResearch.WordTrace tailWord_1245808 prefixEnd_1245808 2632503321878876560373 := by
  unfold tailWord_1245808
  simp only [CollatzResearch.WordTrace]
  refine ⟨22719175335328928956129039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30292233780438571941505385 22719175335328928956129039)
  ·
    refine ⟨34078763002993393434193559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22719175335328928956129039 34078763002993393434193559)
    ·
      refine ⟨51118144504490090151290339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34078763002993393434193559 51118144504490090151290339)
      ·
        refine ⟨76677216756735135226935509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51118144504490090151290339 76677216756735135226935509)
        ·
          refine ⟨1797122267735979731881301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76677216756735135226935509 1797122267735979731881301)
          ·
            refine ⟨2632503321878876560373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1797122267735979731881301 2632503321878876560373)
            ·
              rfl

theorem cell23_1245808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 11].length) (baseStart_1245808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245808 prefixEnd_1245808 := by exact prefixLift 1245808
  have htrace : WordTrace (prefixWord ++ tailWord_1245808) baseStart_1245808 baseEnd_1245808 := by
    simpa [prefixWord, tailWord_1245808, baseEnd_1245808] using wordTrace_append hprefix tailTrace_1245808
  have hstable : (prefixWord ++ tailWord_1245808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245808).length < 2 ^ (prefixWord ++ tailWord_1245808).sum := by decide
  have hdescent : baseEnd_1245808 < baseStart_1245808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245842 : List Nat := [3, 2, 3, 1, 2, 2, 3, 7]
def baseStart_1245842 : Nat := 118140960795 + 1245842 * 2 ^ 59
def prefixEnd_1245842 : Nat := 4983230072969 + 3 ^ 40 * 1245842 * 2
def baseEnd_1245842 : Nat := 23693176502178513746129

theorem tailTrace_1245842 : CollatzResearch.WordTrace tailWord_1245842 prefixEnd_1245842 23693176502178513746129 := by
  unfold tailWord_1245842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359897688133670429748945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30293060501689787812663853 11359897688133670429748945)
  ·
    refine ⟨8519923266100252822311709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11359897688133670429748945 8519923266100252822311709)
    ·
      refine ⟨3194971224787594808366891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8519923266100252822311709 3194971224787594808366891)
      ·
        refine ⟨4792456837181392212550337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194971224787594808366891 4792456837181392212550337)
        ·
          refine ⟨3594342627886044159412753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4792456837181392212550337 3594342627886044159412753)
          ·
            refine ⟨2695756970914533119559565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3594342627886044159412753 2695756970914533119559565)
            ·
              refine ⟨1010908864092949919834837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2695756970914533119559565 1010908864092949919834837)
              ·
                refine ⟨23693176502178513746129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1010908864092949919834837 23693176502178513746129)
                ·
                  rfl

theorem cell23_1245842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_1245842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245842 prefixEnd_1245842 := by exact prefixLift 1245842
  have htrace : WordTrace (prefixWord ++ tailWord_1245842) baseStart_1245842 baseEnd_1245842 := by
    simpa [prefixWord, tailWord_1245842, baseEnd_1245842] using wordTrace_append hprefix tailTrace_1245842
  have hstable : (prefixWord ++ tailWord_1245842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245842).length < 2 ^ (prefixWord ++ tailWord_1245842).sum := by decide
  have hdescent : baseEnd_1245842 < baseStart_1245842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245852 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1245852 : Nat := 118140960795 + 1245852 * 2 ^ 59
def prefixEnd_1245852 : Nat := 4983230072969 + 3 ^ 40 * 1245852 * 2
def baseEnd_1245852 : Nat := 639720900365364832020437

theorem tailTrace_1245852 : CollatzResearch.WordTrace tailWord_1245852 prefixEnd_1245852 639720900365364832020437 := by
  unfold tailWord_1245852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22719977741249226713429905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30293303654998968951239873 22719977741249226713429905)
  ·
    refine ⟨17039983305936920035072429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22719977741249226713429905 17039983305936920035072429)
    ·
      refine ⟨6389993739726345013152161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17039983305936920035072429 6389993739726345013152161)
      ·
        refine ⟨4792495304794758759864121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6389993739726345013152161 4792495304794758759864121)
        ·
          refine ⟨3594371478596069069898091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4792495304794758759864121 3594371478596069069898091)
          ·
            refine ⟨5391557217894103604847137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594371478596069069898091 5391557217894103604847137)
            ·
              refine ⟨4043667913420577703635353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5391557217894103604847137 4043667913420577703635353)
              ·
                refine ⟨3032750935065433277726515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043667913420577703635353 3032750935065433277726515)
                ·
                  refine ⟨4549126402598149916589773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032750935065433277726515 4549126402598149916589773)
                  ·
                    refine ⟨1705922400974306218721165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4549126402598149916589773 1705922400974306218721165)
                    ·
                      refine ⟨639720900365364832020437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1705922400974306218721165 639720900365364832020437)
                      ·
                        rfl

theorem cell23_1245852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1245852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245852 prefixEnd_1245852 := by exact prefixLift 1245852
  have htrace : WordTrace (prefixWord ++ tailWord_1245852) baseStart_1245852 baseEnd_1245852 := by
    simpa [prefixWord, tailWord_1245852, baseEnd_1245852] using wordTrace_append hprefix tailTrace_1245852
  have hstable : (prefixWord ++ tailWord_1245852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245852).length < 2 ^ (prefixWord ++ tailWord_1245852).sum := by decide
  have hdescent : baseEnd_1245852 < baseStart_1245852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245856 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 1, 2, 3]
def baseStart_1245856 : Nat := 118140960795 + 1245856 * 2 ^ 59
def prefixEnd_1245856 : Nat := 4983230072969 + 3 ^ 40 * 1245856 * 2
def baseEnd_1245856 : Nat := 639722954287982816370419

theorem tailTrace_1245856 : CollatzResearch.WordTrace tailWord_1245856 prefixEnd_1245856 639722954287982816370419 := by
  unfold tailWord_1245856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22720050687241981055002711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30293400916322641406670281 22720050687241981055002711)
  ·
    refine ⟨34080076030862971582504067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22720050687241981055002711 34080076030862971582504067)
    ·
      refine ⟨51120114046294457373756101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34080076030862971582504067 51120114046294457373756101)
      ·
        refine ⟨9585021383680210757579269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51120114046294457373756101 9585021383680210757579269)
        ·
          refine ⟨1797191509440039517046113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9585021383680210757579269 1797191509440039517046113)
          ·
            refine ⟨1347893632080029637784585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797191509440039517046113 1347893632080029637784585)
            ·
              refine ⟨1010920224060022228338439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347893632080029637784585 1010920224060022228338439)
              ·
                refine ⟨1516380336090033342507659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010920224060022228338439 1516380336090033342507659)
                ·
                  refine ⟨2274570504135050013761489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516380336090033342507659 2274570504135050013761489)
                  ·
                    refine ⟨1705927878101287510321117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2274570504135050013761489 1705927878101287510321117)
                    ·
                      refine ⟨639722954287982816370419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1705927878101287510321117 639722954287982816370419)
                      ·
                        rfl

theorem cell23_1245856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_1245856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245856 prefixEnd_1245856 := by exact prefixLift 1245856
  have htrace : WordTrace (prefixWord ++ tailWord_1245856) baseStart_1245856 baseEnd_1245856 := by
    simpa [prefixWord, tailWord_1245856, baseEnd_1245856] using wordTrace_append hprefix tailTrace_1245856
  have hstable : (prefixWord ++ tailWord_1245856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245856).length < 2 ^ (prefixWord ++ tailWord_1245856).sum := by decide
  have hdescent : baseEnd_1245856 < baseStart_1245856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245863 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1245863 : Nat := 118140960795 + 1245863 * 2 ^ 59
def prefixEnd_1245863 : Nat := 4983230072969 + 3 ^ 40 * 1245863 * 2
def baseEnd_1245863 : Nat := 213242182884188096327629

theorem tailTrace_1245863 : CollatzResearch.WordTrace tailWord_1245863 prefixEnd_1245863 213242182884188096327629 := by
  unfold tailWord_1245863
  simp only [CollatzResearch.WordTrace]
  refine ⟨45440356685458602305510243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30293571123639068203673495 45440356685458602305510243)
  ·
    refine ⟨68160535028187903458265365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45440356685458602305510243 68160535028187903458265365)
    ·
      refine ⟨3195025079446307974606189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68160535028187903458265365 3195025079446307974606189)
      ·
        refine ⟨1198134404792365490477321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3195025079446307974606189 1198134404792365490477321)
        ·
          refine ⟨898600803594274117857991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1198134404792365490477321 898600803594274117857991)
          ·
            refine ⟨1347901205391411176786987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898600803594274117857991 1347901205391411176786987)
            ·
              refine ⟨2021851808087116765180481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347901205391411176786987 2021851808087116765180481)
              ·
                refine ⟨1516388856065337573885361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021851808087116765180481 1516388856065337573885361)
                ·
                  refine ⟨1137291642049003180414021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1516388856065337573885361 1137291642049003180414021)
                  ·
                    refine ⟨213242182884188096327629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1137291642049003180414021 213242182884188096327629)
                    ·
                      rfl

theorem cell23_1245863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1245863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245863 prefixEnd_1245863 := by exact prefixLift 1245863
  have htrace : WordTrace (prefixWord ++ tailWord_1245863) baseStart_1245863 baseEnd_1245863 := by
    simpa [prefixWord, tailWord_1245863, baseEnd_1245863] using wordTrace_append hprefix tailTrace_1245863
  have hstable : (prefixWord ++ tailWord_1245863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245863).length < 2 ^ (prefixWord ++ tailWord_1245863).sum := by decide
  have hdescent : baseEnd_1245863 < baseStart_1245863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245869 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1245869 : Nat := 118140960795 + 1245869 * 2 ^ 59
def prefixEnd_1245869 : Nat := 4983230072969 + 3 ^ 40 * 1245869 * 2
def baseEnd_1245869 : Nat := 639729629536491265507859

theorem tailTrace_1245869 : CollatzResearch.WordTrace tailWord_1245869 prefixEnd_1245869 639729629536491265507859 := by
  unfold tailWord_1245869
  simp only [CollatzResearch.WordTrace]
  refine ⟨45440575523436865330228661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30293717015624576886819107 45440575523436865330228661)
  ·
    refine ⟨4260053955322206124708937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45440575523436865330228661 4260053955322206124708937)
    ·
      refine ⟨3195040466491654593531703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4260053955322206124708937 3195040466491654593531703)
      ·
        refine ⟨4792560699737481890297555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195040466491654593531703 4792560699737481890297555)
        ·
          refine ⟨7188841049606222835446333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792560699737481890297555 7188841049606222835446333)
          ·
            refine ⟨2695815393602333563292375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7188841049606222835446333 2695815393602333563292375)
            ·
              refine ⟨4043723090403500344938563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695815393602333563292375 4043723090403500344938563)
              ·
                refine ⟨6065584635605250517407845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043723090403500344938563 6065584635605250517407845)
                ·
                  refine ⟨1137297119175984472013971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6065584635605250517407845 1137297119175984472013971)
                  ·
                    refine ⟨1705945678763976708020957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137297119175984472013971 1705945678763976708020957)
                    ·
                      refine ⟨639729629536491265507859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1705945678763976708020957 639729629536491265507859)
                      ·
                        rfl

theorem cell23_1245869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1245869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245869 prefixEnd_1245869 := by exact prefixLift 1245869
  have htrace : WordTrace (prefixWord ++ tailWord_1245869) baseStart_1245869 baseEnd_1245869 := by
    simpa [prefixWord, tailWord_1245869, baseEnd_1245869] using wordTrace_append hprefix tailTrace_1245869
  have hstable : (prefixWord ++ tailWord_1245869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245869).length < 2 ^ (prefixWord ++ tailWord_1245869).sum := by decide
  have hdescent : baseEnd_1245869 < baseStart_1245869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245885 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1245885 : Nat := 118140960795 + 1245885 * 2 ^ 59
def prefixEnd_1245885 : Nat := 4983230072969 + 3 ^ 40 * 1245885 * 2
def baseEnd_1245885 : Nat := 213245948408987734302595

theorem tailTrace_1245885 : CollatzResearch.WordTrace tailWord_1245885 prefixEnd_1245885 213245948408987734302595 := by
  unfold tailWord_1245885
  simp only [CollatzResearch.WordTrace]
  refine ⟨45441159091378900062811109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30294106060919266708540739 45441159091378900062811109)
  ·
    refine ⟨8520217329633543761777083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45441159091378900062811109 8520217329633543761777083)
    ·
      refine ⟨12780325994450315642665625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8520217329633543761777083 12780325994450315642665625)
      ·
        refine ⟨9585244495837736731999219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12780325994450315642665625 9585244495837736731999219)
        ·
          refine ⟨14377866743756605097998829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9585244495837736731999219 14377866743756605097998829)
          ·
            refine ⟨5391700028908726911749561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14377866743756605097998829 5391700028908726911749561)
            ·
              refine ⟨4043775021681545183812171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5391700028908726911749561 4043775021681545183812171)
              ·
                refine ⟨6065662532522317775718257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043775021681545183812171 6065662532522317775718257)
                ·
                  refine ⟨4549246899391738331788693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6065662532522317775718257 4549246899391738331788693)
                  ·
                    refine ⟨213245948408987734302595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4549246899391738331788693 213245948408987734302595)
                    ·
                      rfl

theorem cell23_1245885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1245885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245885 prefixEnd_1245885 := by exact prefixLift 1245885
  have htrace : WordTrace (prefixWord ++ tailWord_1245885) baseStart_1245885 baseEnd_1245885 := by
    simpa [prefixWord, tailWord_1245885, baseEnd_1245885] using wordTrace_append hprefix tailTrace_1245885
  have hstable : (prefixWord ++ tailWord_1245885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245885).length < 2 ^ (prefixWord ++ tailWord_1245885).sum := by decide
  have hdescent : baseEnd_1245885 < baseStart_1245885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245886 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_1245886 : Nat := 118140960795 + 1245886 * 2 ^ 59
def prefixEnd_1245886 : Nat := 4983230072969 + 3 ^ 40 * 1245886 * 2
def baseEnd_1245886 : Nat := 639738358707617698995281

theorem tailTrace_1245886 : CollatzResearch.WordTrace tailWord_1245886 prefixEnd_1245886 639738358707617698995281 := by
  unfold tailWord_1245886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680149445546909654199689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30294130376250184822398341 5680149445546909654199689)
  ·
    refine ⟨4260112084160182240649767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5680149445546909654199689 4260112084160182240649767)
    ·
      refine ⟨6390168126240273360974651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4260112084160182240649767 6390168126240273360974651)
      ·
        refine ⟨9585252189360410041461977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390168126240273360974651 9585252189360410041461977)
        ·
          refine ⟨7188939142020307531096483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9585252189360410041461977 7188939142020307531096483)
          ·
            refine ⟨10783408713030461296644725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188939142020307531096483 10783408713030461296644725)
            ·
              refine ⟨1010944566846605746560443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10783408713030461296644725 1010944566846605746560443)
              ·
                refine ⟨1516416850269908619840665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010944566846605746560443 1516416850269908619840665)
                ·
                  refine ⟨1137312637702431464880499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1516416850269908619840665 1137312637702431464880499)
                  ·
                    refine ⟨1705968956553647197320749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137312637702431464880499 1705968956553647197320749)
                    ·
                      refine ⟨639738358707617698995281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1705968956553647197320749 639738358707617698995281)
                      ·
                        rfl

theorem cell23_1245886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_1245886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245886 prefixEnd_1245886 := by exact prefixLift 1245886
  have htrace : WordTrace (prefixWord ++ tailWord_1245886) baseStart_1245886 baseEnd_1245886 := by
    simpa [prefixWord, tailWord_1245886, baseEnd_1245886] using wordTrace_append hprefix tailTrace_1245886
  have hstable : (prefixWord ++ tailWord_1245886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245886).length < 2 ^ (prefixWord ++ tailWord_1245886).sum := by decide
  have hdescent : baseEnd_1245886 < baseStart_1245886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245942 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1245942 : Nat := 118140960795 + 1245942 * 2 ^ 59
def prefixEnd_1245942 : Nat := 4983230072969 + 3 ^ 40 * 1245942 * 2
def baseEnd_1245942 : Nat := 639767113624269479895023

theorem tailTrace_1245942 : CollatzResearch.WordTrace tailWord_1245942 prefixEnd_1245942 639767113624269479895023 := by
  unfold tailWord_1245942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840202378260774924852255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30295492034781599198424053 2840202378260774924852255)
  ·
    refine ⟨4260303567391162387278383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2840202378260774924852255 4260303567391162387278383)
    ·
      refine ⟨6390455351086743580917575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4260303567391162387278383 6390455351086743580917575)
      ·
        refine ⟨9585683026630115371376363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390455351086743580917575 9585683026630115371376363)
        ·
          refine ⟨14378524539945173057064545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9585683026630115371376363 14378524539945173057064545)
          ·
            refine ⟨10783893404958879792798409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14378524539945173057064545 10783893404958879792798409)
            ·
              refine ⟨8087920053719159844598807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10783893404958879792798409 8087920053719159844598807)
              ·
                refine ⟨12131880080578739766898211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8087920053719159844598807 12131880080578739766898211)
                ·
                  refine ⟨18197820120868109650347317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12131880080578739766898211 18197820120868109650347317)
                  ·
                    refine ⟨1706045636331385279720061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18197820120868109650347317 1706045636331385279720061)
                    ·
                      refine ⟨639767113624269479895023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706045636331385279720061 639767113624269479895023)
                      ·
                        rfl

theorem cell23_1245942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1245942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245942 prefixEnd_1245942 := by exact prefixLift 1245942
  have htrace : WordTrace (prefixWord ++ tailWord_1245942) baseStart_1245942 baseEnd_1245942 := by
    simpa [prefixWord, tailWord_1245942, baseEnd_1245942] using wordTrace_append hprefix tailTrace_1245942
  have hstable : (prefixWord ++ tailWord_1245942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245942).length < 2 ^ (prefixWord ++ tailWord_1245942).sum := by decide
  have hdescent : baseEnd_1245942 < baseStart_1245942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245962 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1245962 : Nat := 118140960795 + 1245962 * 2 ^ 59
def prefixEnd_1245962 : Nat := 4983230072969 + 3 ^ 40 * 1245962 * 2
def baseEnd_1245962 : Nat := 213259127745786467214977

theorem tailTrace_1245962 : CollatzResearch.WordTrace tailWord_1245962 prefixEnd_1245962 213259127745786467214977 := by
  unfold tailWord_1245962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11360991878024985553341035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30295978341399961475576093 11360991878024985553341035)
  ·
    refine ⟨17041487817037478330011553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11360991878024985553341035 17041487817037478330011553)
    ·
      refine ⟨12781115862778108747508665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17041487817037478330011553 12781115862778108747508665)
      ·
        refine ⟨9585836897083581560631499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12781115862778108747508665 9585836897083581560631499)
        ·
          refine ⟨14378755345625372340947249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9585836897083581560631499 14378755345625372340947249)
          ·
            refine ⟨10784066509219029255710437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14378755345625372340947249 10784066509219029255710437)
            ·
              refine ⟨2022012470478567985445707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10784066509219029255710437 2022012470478567985445707)
              ·
                refine ⟨3033018705717851978168561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022012470478567985445707 3033018705717851978168561)
                ·
                  refine ⟨2274764029288388983626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3033018705717851978168561 2274764029288388983626421)
                  ·
                    refine ⟨213259127745786467214977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2274764029288388983626421 213259127745786467214977)
                    ·
                      rfl

theorem cell23_1245962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1245962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245962 prefixEnd_1245962 := by exact prefixLift 1245962
  have htrace : WordTrace (prefixWord ++ tailWord_1245962) baseStart_1245962 baseEnd_1245962 := by
    simpa [prefixWord, tailWord_1245962, baseEnd_1245962] using wordTrace_append hprefix tailTrace_1245962
  have hstable : (prefixWord ++ tailWord_1245962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245962).length < 2 ^ (prefixWord ++ tailWord_1245962).sum := by decide
  have hdescent : baseEnd_1245962 < baseStart_1245962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245985 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1245985 : Nat := 118140960795 + 1245985 * 2 ^ 59
def prefixEnd_1245985 : Nat := 4983230072969 + 3 ^ 40 * 1245985 * 2
def baseEnd_1245985 : Nat := 639789193292412811657325

theorem tailTrace_1245985 : CollatzResearch.WordTrace tailWord_1245985 prefixEnd_1245985 639789193292412811657325 := by
  unfold tailWord_1245985
  simp only [CollatzResearch.WordTrace]
  refine ⟨45444806391016617141451409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30296537594011078094300939 45444806391016617141451409)
  ·
    refine ⟨34083604793262462856088557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45444806391016617141451409 34083604793262462856088557)
    ·
      refine ⟨12781351797473423571033209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34083604793262462856088557 12781351797473423571033209)
      ·
        refine ⟨9586013848105067678274907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12781351797473423571033209 9586013848105067678274907)
        ·
          refine ⟨14379020772157601517412361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586013848105067678274907 14379020772157601517412361)
          ·
            refine ⟨10784265579118201138059271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14379020772157601517412361 10784265579118201138059271)
            ·
              refine ⟨16176398368677301707088907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10784265579118201138059271 16176398368677301707088907)
              ·
                refine ⟨24264597553015952560633361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16176398368677301707088907 24264597553015952560633361)
                ·
                  refine ⟨18198448164761964420475021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24264597553015952560633361 18198448164761964420475021)
                  ·
                    refine ⟨6824418061785736657678133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18198448164761964420475021 6824418061785736657678133)
                    ·
                      refine ⟨639789193292412811657325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6824418061785736657678133 639789193292412811657325)
                      ·
                        rfl

theorem cell23_1245985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1245985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1245985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1245985 prefixEnd_1245985 := by exact prefixLift 1245985
  have htrace : WordTrace (prefixWord ++ tailWord_1245985) baseStart_1245985 baseEnd_1245985 := by
    simpa [prefixWord, tailWord_1245985, baseEnd_1245985] using wordTrace_append hprefix tailTrace_1245985
  have hstable : (prefixWord ++ tailWord_1245985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245985).length < 2 ^ (prefixWord ++ tailWord_1245985).sum := by decide
  have hdescent : baseEnd_1245985 < baseStart_1245985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246002 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1246002 : Nat := 118140960795 + 1246002 * 2 ^ 59
def prefixEnd_1246002 : Nat := 4983230072969 + 3 ^ 40 * 1246002 * 2
def baseEnd_1246002 : Nat := 639797922463539245144747

theorem tailTrace_1246002 : CollatzResearch.WordTrace tailWord_1246002 prefixEnd_1246002 639797922463539245144747 := by
  unfold tailWord_1246002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361356607988757261205065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30296950954636686029880173 11361356607988757261205065)
  ·
    refine ⟨8521017455991567945903799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11361356607988757261205065 8521017455991567945903799)
    ·
      refine ⟨12781526183987351918855699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8521017455991567945903799 12781526183987351918855699)
      ·
        refine ⟨19172289275981027878283549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12781526183987351918855699 19172289275981027878283549)
        ·
          refine ⟨7189608478492885454356331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19172289275981027878283549 7189608478492885454356331)
          ·
            refine ⟨10784412717739328181534497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189608478492885454356331 10784412717739328181534497)
            ·
              refine ⟨8088309538304496136150873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10784412717739328181534497 8088309538304496136150873)
              ·
                refine ⟨6066232153728372102113155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8088309538304496136150873 6066232153728372102113155)
                ·
                  refine ⟨9099348230592558153169733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066232153728372102113155 9099348230592558153169733)
                  ·
                    refine ⟨1706127793236104653719325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9099348230592558153169733 1706127793236104653719325)
                    ·
                      refine ⟨639797922463539245144747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706127793236104653719325 639797922463539245144747)
                      ·
                        rfl

theorem cell23_1246002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1246002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246002 prefixEnd_1246002 := by exact prefixLift 1246002
  have htrace : WordTrace (prefixWord ++ tailWord_1246002) baseStart_1246002 baseEnd_1246002 := by
    simpa [prefixWord, tailWord_1246002, baseEnd_1246002] using wordTrace_append hprefix tailTrace_1246002
  have hstable : (prefixWord ++ tailWord_1246002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246002).length < 2 ^ (prefixWord ++ tailWord_1246002).sum := by decide
  have hdescent : baseEnd_1246002 < baseStart_1246002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246039 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 6]
def baseStart_1246039 : Nat := 118140960795 + 1246039 * 2 ^ 59
def prefixEnd_1246039 : Nat := 4983230072969 + 3 ^ 40 * 1246039 * 2
def baseEnd_1246039 : Nat := 71090769027528400042453

theorem tailTrace_1246039 : CollatzResearch.WordTrace tailWord_1246039 prefixEnd_1246039 71090769027528400042453 := by
  unfold tailWord_1246039
  simp only [CollatzResearch.WordTrace]
  refine ⟨45446775932820984363917171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30297850621880656242611447 45446775932820984363917171)
  ·
    refine ⟨68170163899231476545875757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45446775932820984363917171 68170163899231476545875757)
    ·
      refine ⟨25563811462211803704703409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68170163899231476545875757 25563811462211803704703409)
      ·
        refine ⟨19172858596658852778527557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25563811462211803704703409 19172858596658852778527557)
        ·
          refine ⟨3594910986873534895973917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19172858596658852778527557 3594910986873534895973917)
          ·
            refine ⟨1348091620077575585990219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3594910986873534895973917 1348091620077575585990219)
            ·
              refine ⟨2022137430116363378985329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348091620077575585990219 2022137430116363378985329)
              ·
                refine ⟨1516603072587272534238997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022137430116363378985329 1516603072587272534238997)
                ·
                  refine ⟨71090769027528400042453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1516603072587272534238997 71090769027528400042453)
                  ·
                    rfl

theorem cell23_1246039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 6].length) (baseStart_1246039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246039 prefixEnd_1246039 := by exact prefixLift 1246039
  have htrace : WordTrace (prefixWord ++ tailWord_1246039) baseStart_1246039 baseEnd_1246039 := by
    simpa [prefixWord, tailWord_1246039, baseEnd_1246039] using wordTrace_append hprefix tailTrace_1246039
  have hstable : (prefixWord ++ tailWord_1246039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246039).length < 2 ^ (prefixWord ++ tailWord_1246039).sum := by decide
  have hdescent : baseEnd_1246039 < baseStart_1246039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246069 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1246069 : Nat := 118140960795 + 1246069 * 2 ^ 59
def prefixEnd_1246069 : Nat := 4983230072969 + 3 ^ 40 * 1246069 * 2
def baseEnd_1246069 : Nat := 213277441889130161002313

theorem tailTrace_1246069 : CollatzResearch.WordTrace tailWord_1246069 prefixEnd_1246069 213277441889130161002313 := by
  unfold tailWord_1246069
  simp only [CollatzResearch.WordTrace]
  refine ⟨45447870122712299487509261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30298580081808199658339507 45447870122712299487509261)
  ·
    refine ⟨17042951296017112307815973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45447870122712299487509261 17042951296017112307815973)
    ·
      refine ⟨3195553368003208557715495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17042951296017112307815973 3195553368003208557715495)
      ·
        refine ⟨4793330052004812836573243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195553368003208557715495 4793330052004812836573243)
        ·
          refine ⟨7189995078007219254859865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4793330052004812836573243 7189995078007219254859865)
          ·
            refine ⟨5392496308505414441144899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7189995078007219254859865 5392496308505414441144899)
            ·
              refine ⟨8088744462758121661717349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392496308505414441144899 8088744462758121661717349)
              ·
                refine ⟨1516639586767147811572003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8088744462758121661717349 1516639586767147811572003)
                ·
                  refine ⟨2274959380150721717358005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516639586767147811572003 2274959380150721717358005)
                  ·
                    refine ⟨213277441889130161002313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2274959380150721717358005 213277441889130161002313)
                    ·
                      rfl

theorem cell23_1246069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1246069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246069 prefixEnd_1246069 := by exact prefixLift 1246069
  have htrace : WordTrace (prefixWord ++ tailWord_1246069) baseStart_1246069 baseEnd_1246069 := by
    simpa [prefixWord, tailWord_1246069, baseEnd_1246069] using wordTrace_append hprefix tailTrace_1246069
  have hstable : (prefixWord ++ tailWord_1246069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246069).length < 2 ^ (prefixWord ++ tailWord_1246069).sum := by decide
  have hdescent : baseEnd_1246069 < baseStart_1246069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246089 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 4]
def baseStart_1246089 : Nat := 118140960795 + 1246089 * 2 ^ 59
def prefixEnd_1246089 : Nat := 4983230072969 + 3 ^ 40 * 1246089 * 2
def baseEnd_1246089 : Nat := 639842595280480404756847

theorem tailTrace_1246089 : CollatzResearch.WordTrace tailWord_1246089 prefixEnd_1246089 639842595280480404756847 := by
  unfold tailWord_1246089
  simp only [CollatzResearch.WordTrace]
  refine ⟨45448599582639842903237321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30299066388426561935491547 45448599582639842903237321)
  ·
    refine ⟨34086449686979882177427991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45448599582639842903237321 34086449686979882177427991)
    ·
      refine ⟨51129674530469823266141987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34086449686979882177427991 51129674530469823266141987)
      ·
        refine ⟨76694511795704734899212981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51129674530469823266141987 76694511795704734899212981)
        ·
          refine ⟨7190110480847318896801217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76694511795704734899212981 7190110480847318896801217)
          ·
            refine ⟨5392582860635489172600913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7190110480847318896801217 5392582860635489172600913)
            ·
              refine ⟨4044437145476616879450685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5392582860635489172600913 4044437145476616879450685)
              ·
                refine ⟨1516663929553731329794007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4044437145476616879450685 1516663929553731329794007)
                ·
                  refine ⟨2274995894330596994691011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516663929553731329794007 2274995894330596994691011)
                  ·
                    refine ⟨3412493841495895492036517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2274995894330596994691011 3412493841495895492036517)
                    ·
                      refine ⟨639842595280480404756847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3412493841495895492036517 639842595280480404756847)
                      ·
                        rfl

theorem cell23_1246089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_1246089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246089 prefixEnd_1246089 := by exact prefixLift 1246089
  have htrace : WordTrace (prefixWord ++ tailWord_1246089) baseStart_1246089 baseEnd_1246089 := by
    simpa [prefixWord, tailWord_1246089, baseEnd_1246089] using wordTrace_append hprefix tailTrace_1246089
  have hstable : (prefixWord ++ tailWord_1246089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246089).length < 2 ^ (prefixWord ++ tailWord_1246089).sum := by decide
  have hdescent : baseEnd_1246089 < baseStart_1246089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246092 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1246092 : Nat := 118140960795 + 1246092 * 2 ^ 59
def prefixEnd_1246092 : Nat := 4983230072969 + 3 ^ 40 * 1246092 * 2
def baseEnd_1246092 : Nat := 639844135722443893019333

theorem tailTrace_1246092 : CollatzResearch.WordTrace tailWord_1246092 prefixEnd_1246092 639844135722443893019333 := by
  unfold tailWord_1246092
  simp only [CollatzResearch.WordTrace]
  refine ⟨22724354500814487207798265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30299139334419316277064353 22724354500814487207798265)
  ·
    refine ⟨17043265875610865405848699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22724354500814487207798265 17043265875610865405848699)
    ·
      refine ⟨25564898813416298108773049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17043265875610865405848699 25564898813416298108773049)
      ·
        refine ⟨19173674110062223581579787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25564898813416298108773049 19173674110062223581579787)
        ·
          refine ⟨28760511165093335372369681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19173674110062223581579787 28760511165093335372369681)
          ·
            refine ⟨21570383373820001529277261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28760511165093335372369681 21570383373820001529277261)
            ·
              refine ⟨8088893765182500573478973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21570383373820001529277261 8088893765182500573478973)
              ·
                refine ⟨3033335161943437715054615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8088893765182500573478973 3033335161943437715054615)
                ·
                  refine ⟨4550002742915156572581923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033335161943437715054615 4550002742915156572581923)
                  ·
                    refine ⟨6825004114372734858872885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4550002742915156572581923 6825004114372734858872885)
                    ·
                      refine ⟨639844135722443893019333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6825004114372734858872885 639844135722443893019333)
                      ·
                        rfl

theorem cell23_1246092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1246092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246092 prefixEnd_1246092 := by exact prefixLift 1246092
  have htrace : WordTrace (prefixWord ++ tailWord_1246092) baseStart_1246092 baseEnd_1246092 := by
    simpa [prefixWord, tailWord_1246092, baseEnd_1246092] using wordTrace_append hprefix tailTrace_1246092
  have hstable : (prefixWord ++ tailWord_1246092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246092).length < 2 ^ (prefixWord ++ tailWord_1246092).sum := by decide
  have hdescent : baseEnd_1246092 < baseStart_1246092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246100 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1246100 : Nat := 118140960795 + 1246100 * 2 ^ 59
def prefixEnd_1246100 : Nat := 4983230072969 + 3 ^ 40 * 1246100 * 2
def baseEnd_1246100 : Nat := 639848243567679861719297

theorem tailTrace_1246100 : CollatzResearch.WordTrace tailWord_1246100 prefixEnd_1246100 639848243567679861719297 := by
  unfold tailWord_1246100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22724500392799995890943877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30299333857066661187925169 22724500392799995890943877)
  ·
    refine ⟨4260843823649999229551977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22724500392799995890943877 4260843823649999229551977)
    ·
      refine ⟨3195632867737499422163983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4260843823649999229551977 3195632867737499422163983)
      ·
        refine ⟨4793449301606249133245975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195632867737499422163983 4793449301606249133245975)
        ·
          refine ⟨7190173952409373699868963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4793449301606249133245975 7190173952409373699868963)
          ·
            refine ⟨10785260928614060549803445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7190173952409373699868963 10785260928614060549803445)
            ·
              refine ⟨1011118212057568176544073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10785260928614060549803445 1011118212057568176544073)
              ·
                refine ⟨758338659043176132408055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011118212057568176544073 758338659043176132408055)
                ·
                  refine ⟨1137507988564764198612083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758338659043176132408055 1137507988564764198612083)
                  ·
                    refine ⟨1706261982847146297918125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137507988564764198612083 1706261982847146297918125)
                    ·
                      refine ⟨639848243567679861719297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706261982847146297918125 639848243567679861719297)
                      ·
                        rfl

theorem cell23_1246100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1246100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246100 prefixEnd_1246100 := by exact prefixLift 1246100
  have htrace : WordTrace (prefixWord ++ tailWord_1246100) baseStart_1246100 baseEnd_1246100 := by
    simpa [prefixWord, tailWord_1246100, baseEnd_1246100] using wordTrace_append hprefix tailTrace_1246100
  have hstable : (prefixWord ++ tailWord_1246100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246100).length < 2 ^ (prefixWord ++ tailWord_1246100).sum := by decide
  have hdescent : baseEnd_1246100 < baseStart_1246100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246109 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1246109 : Nat := 118140960795 + 1246109 * 2 ^ 59
def prefixEnd_1246109 : Nat := 4983230072969 + 3 ^ 40 * 1246109 * 2
def baseEnd_1246109 : Nat := 639852864893570326506755

theorem tailTrace_1246109 : CollatzResearch.WordTrace tailWord_1246109 prefixEnd_1246109 639852864893570326506755 := by
  unfold tailWord_1246109
  simp only [CollatzResearch.WordTrace]
  refine ⟨45449329042567386318965381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30299552695044924212643587 45449329042567386318965381)
  ·
    refine ⟨8521749195481384934806009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45449329042567386318965381 8521749195481384934806009)
    ·
      refine ⟨6391311896611038701104507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8521749195481384934806009 6391311896611038701104507)
      ·
        refine ⟨9586967844916558051656761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391311896611038701104507 9586967844916558051656761)
        ·
          refine ⟨7190225883687418538742571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9586967844916558051656761 7190225883687418538742571)
          ·
            refine ⟨10785338825531127808113857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7190225883687418538742571 10785338825531127808113857)
            ·
              refine ⟨8089004119148345856085393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10785338825531127808113857 8089004119148345856085393)
              ·
                refine ⟨6066753089361259392064045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089004119148345856085393 6066753089361259392064045)
                ·
                  refine ⟨2275032408510472272024017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6066753089361259392064045 2275032408510472272024017)
                  ·
                    refine ⟨1706274306382854204018013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2275032408510472272024017 1706274306382854204018013)
                    ·
                      refine ⟨639852864893570326506755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706274306382854204018013 639852864893570326506755)
                      ·
                        rfl

theorem cell23_1246109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1246109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246109 prefixEnd_1246109 := by exact prefixLift 1246109
  have htrace : WordTrace (prefixWord ++ tailWord_1246109) baseStart_1246109 baseEnd_1246109 := by
    simpa [prefixWord, tailWord_1246109, baseEnd_1246109] using wordTrace_append hprefix tailTrace_1246109
  have hstable : (prefixWord ++ tailWord_1246109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246109).length < 2 ^ (prefixWord ++ tailWord_1246109).sum := by decide
  have hdescent : baseEnd_1246109 < baseStart_1246109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246173 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1246173 : Nat := 118140960795 + 1246173 * 2 ^ 59
def prefixEnd_1246173 : Nat := 4983230072969 + 3 ^ 40 * 1246173 * 2
def baseEnd_1246173 : Nat := 639885727655458076106461

theorem tailTrace_1246173 : CollatzResearch.WordTrace tailWord_1246173 prefixEnd_1246173 639885727655458076106461 := by
  unfold tailWord_1246173
  simp only [CollatzResearch.WordTrace]
  refine ⟨45451663314335525249295173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30301108876223683499530115 45451663314335525249295173)
  ·
    refine ⟨8522186871437910984242845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45451663314335525249295173 8522186871437910984242845)
    ·
      refine ⟨3195820076789216619091067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8522186871437910984242845 3195820076789216619091067)
      ·
        refine ⟨4793730115183824928636601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195820076789216619091067 4793730115183824928636601)
        ·
          refine ⟨3595297586387868696477451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4793730115183824928636601 3595297586387868696477451)
          ·
            refine ⟨5392946379581803044716177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595297586387868696477451 5392946379581803044716177)
            ·
              refine ⟨4044709784686352283537133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5392946379581803044716177 4044709784686352283537133)
              ·
                refine ⟨1516766169257382106326425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4044709784686352283537133 1516766169257382106326425)
                ·
                  refine ⟨1137574626943036579744819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1516766169257382106326425 1137574626943036579744819)
                  ·
                    refine ⟨1706361940414554869617229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137574626943036579744819 1706361940414554869617229)
                    ·
                      refine ⟨639885727655458076106461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706361940414554869617229 639885727655458076106461)
                      ·
                        rfl

theorem cell23_1246173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1246173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246173 prefixEnd_1246173 := by exact prefixLift 1246173
  have htrace : WordTrace (prefixWord ++ tailWord_1246173) baseStart_1246173 baseEnd_1246173 := by
    simpa [prefixWord, tailWord_1246173, baseEnd_1246173] using wordTrace_append hprefix tailTrace_1246173
  have hstable : (prefixWord ++ tailWord_1246173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246173).length < 2 ^ (prefixWord ++ tailWord_1246173).sum := by decide
  have hdescent : baseEnd_1246173 < baseStart_1246173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246192 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_1246192 : Nat := 118140960795 + 1246192 * 2 ^ 59
def prefixEnd_1246192 : Nat := 4983230072969 + 3 ^ 40 * 1246192 * 2
def baseEnd_1246192 : Nat := 639895483787893501768873

theorem tailTrace_1246192 : CollatzResearch.WordTrace tailWord_1246192 prefixEnd_1246192 639895483787893501768873 := by
  unfold tailWord_1246192
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726178150633345747118415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30301570867511127662824553 22726178150633345747118415)
  ·
    refine ⟨34089267225950018620677623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22726178150633345747118415 34089267225950018620677623)
    ·
      refine ⟨51133900838925027931016435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34089267225950018620677623 51133900838925027931016435)
      ·
        refine ⟨76700851258387541896524653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51133900838925027931016435 76700851258387541896524653)
        ·
          refine ⟨28762819221895328211196745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76700851258387541896524653 28762819221895328211196745)
          ·
            refine ⟨21572114416421496158397559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28762819221895328211196745 21572114416421496158397559)
            ·
              refine ⟨32358171624632244237596339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21572114416421496158397559 32358171624632244237596339)
              ·
                refine ⟨48537257436948366356394509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32358171624632244237596339 48537257436948366356394509)
                ·
                  refine ⟨18201471538855637383647941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48537257436948366356394509 18201471538855637383647941)
                  ·
                    refine ⟨3412775913535432009433989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18201471538855637383647941 3412775913535432009433989)
                    ·
                      refine ⟨639895483787893501768873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3412775913535432009433989 639895483787893501768873)
                      ·
                        rfl

theorem cell23_1246192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_1246192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246192 prefixEnd_1246192 := by exact prefixLift 1246192
  have htrace : WordTrace (prefixWord ++ tailWord_1246192) baseStart_1246192 baseEnd_1246192 := by
    simpa [prefixWord, tailWord_1246192, baseEnd_1246192] using wordTrace_append hprefix tailTrace_1246192
  have hstable : (prefixWord ++ tailWord_1246192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246192).length < 2 ^ (prefixWord ++ tailWord_1246192).sum := by decide
  have hdescent : baseEnd_1246192 < baseStart_1246192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246209 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1246209 : Nat := 118140960795 + 1246209 * 2 ^ 59
def prefixEnd_1246209 : Nat := 4983230072969 + 3 ^ 40 * 1246209 * 2
def baseEnd_1246209 : Nat := 639904212959019935256295

theorem tailTrace_1246209 : CollatzResearch.WordTrace tailWord_1246209 prefixEnd_1246209 639904212959019935256295 := by
  unfold tailWord_1246209
  simp only [CollatzResearch.WordTrace]
  refine ⟨45452976342205103397605681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30301984228136735598403787 45452976342205103397605681)
  ·
    refine ⟨34089732256653827548204261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45452976342205103397605681 34089732256653827548204261)
    ·
      refine ⟨6391824798122592665288299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34089732256653827548204261 6391824798122592665288299)
      ·
        refine ⟨9587737197183888997932449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391824798122592665288299 9587737197183888997932449)
        ·
          refine ⟨7190802897887916748449337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9587737197183888997932449 7190802897887916748449337)
          ·
            refine ⟨5393102173415937561337003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7190802897887916748449337 5393102173415937561337003)
            ·
              refine ⟨8089653260123906342005505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393102173415937561337003 8089653260123906342005505)
              ·
                refine ⟨6067239945092929756504129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089653260123906342005505 6067239945092929756504129)
                ·
                  refine ⟨4550429958819697317378097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067239945092929756504129 4550429958819697317378097)
                  ·
                    refine ⟨3412822469114772988033573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4550429958819697317378097 3412822469114772988033573)
                    ·
                      refine ⟨639904212959019935256295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3412822469114772988033573 639904212959019935256295)
                      ·
                        rfl

theorem cell23_1246209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1246209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246209 prefixEnd_1246209 := by exact prefixLift 1246209
  have htrace : WordTrace (prefixWord ++ tailWord_1246209) baseStart_1246209 baseEnd_1246209 := by
    simpa [prefixWord, tailWord_1246209, baseEnd_1246209] using wordTrace_append hprefix tailTrace_1246209
  have hstable : (prefixWord ++ tailWord_1246209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246209).length < 2 ^ (prefixWord ++ tailWord_1246209).sum := by decide
  have hdescent : baseEnd_1246209 < baseStart_1246209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246219 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 7]
def baseStart_1246219 : Nat := 118140960795 + 1246219 * 2 ^ 59
def prefixEnd_1246219 : Nat := 4983230072969 + 3 ^ 40 * 1246219 * 2
def baseEnd_1246219 : Nat := 71101038640618321792361

theorem tailTrace_1246219 : CollatzResearch.WordTrace tailWord_1246219 prefixEnd_1246219 71101038640618321792361 := by
  unfold tailWord_1246219
  simp only [CollatzResearch.WordTrace]
  refine ⟨45453341072168875105469711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30302227381445916736979807 45453341072168875105469711)
  ·
    refine ⟨68180011608253312658204567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45453341072168875105469711 68180011608253312658204567)
    ·
      refine ⟨102270017412379968987306851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68180011608253312658204567 102270017412379968987306851)
      ·
        refine ⟨153405026118569953480960277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102270017412379968987306851 153405026118569953480960277)
        ·
          refine ⟨7190860599307966569420013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153405026118569953480960277 7190860599307966569420013)
          ·
            refine ⟨2696572724740487463532505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7190860599307966569420013 2696572724740487463532505)
            ·
              refine ⟨2022429543555365597649379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696572724740487463532505 2022429543555365597649379)
              ·
                refine ⟨3033644315333048396474069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022429543555365597649379 3033644315333048396474069)
                ·
                  refine ⟨71101038640618321792361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3033644315333048396474069 71101038640618321792361)
                  ·
                    rfl

theorem cell23_1246219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 7].length) (baseStart_1246219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246219 prefixEnd_1246219 := by exact prefixLift 1246219
  have htrace : WordTrace (prefixWord ++ tailWord_1246219) baseStart_1246219 baseEnd_1246219 := by
    simpa [prefixWord, tailWord_1246219, baseEnd_1246219] using wordTrace_append hprefix tailTrace_1246219
  have hstable : (prefixWord ++ tailWord_1246219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246219).length < 2 ^ (prefixWord ++ tailWord_1246219).sum := by decide
  have hdescent : baseEnd_1246219 < baseStart_1246219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246270 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1246270 : Nat := 118140960795 + 1246270 * 2 ^ 59
def prefixEnd_1246270 : Nat := 4983230072969 + 3 ^ 40 * 1246270 * 2
def baseEnd_1246270 : Nat := 71103948364327132954835

theorem tailTrace_1246270 : CollatzResearch.WordTrace tailWord_1246270 prefixEnd_1246270 71103948364327132954835 := by
  unfold tailWord_1246270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681900149373013851947033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30303467463322740543717509 5681900149373013851947033)
  ·
    refine ⟨4261425112029760388960275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5681900149373013851947033 4261425112029760388960275)
    ·
      refine ⟨6392137668044640583440413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4261425112029760388960275 6392137668044640583440413)
      ·
        refine ⟨2397051625516740218790155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6392137668044640583440413 2397051625516740218790155)
        ·
          refine ⟨3595577438275110328185233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397051625516740218790155 3595577438275110328185233)
          ·
            refine ⟨2696683078706332746138925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3595577438275110328185233 2696683078706332746138925)
            ·
              refine ⟨1011256154514874779802097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2696683078706332746138925 1011256154514874779802097)
              ·
                refine ⟨758442115886156084851573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011256154514874779802097 758442115886156084851573)
                ·
                  refine ⟨71103948364327132954835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 758442115886156084851573 71103948364327132954835)
                  ·
                    rfl

theorem cell23_1246270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1246270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246270 prefixEnd_1246270 := by exact prefixLift 1246270
  have htrace : WordTrace (prefixWord ++ tailWord_1246270) baseStart_1246270 baseEnd_1246270 := by
    simpa [prefixWord, tailWord_1246270, baseEnd_1246270] using wordTrace_append hprefix tailTrace_1246270
  have hstable : (prefixWord ++ tailWord_1246270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246270).length < 2 ^ (prefixWord ++ tailWord_1246270).sum := by decide
  have hdescent : baseEnd_1246270 < baseStart_1246270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246286 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_1246286 : Nat := 118140960795 + 1246286 * 2 ^ 59
def prefixEnd_1246286 : Nat := 4983230072969 + 3 ^ 40 * 1246286 * 2
def baseEnd_1246286 : Nat := 639943750969416133993441

theorem tailTrace_1246286 : CollatzResearch.WordTrace tailWord_1246286 prefixEnd_1246286 639943750969416133993441 := by
  unfold tailWord_1246286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681973095365768193519839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30303856508617430365439141 5681973095365768193519839)
  ·
    refine ⟨8522959643048652290279759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5681973095365768193519839 8522959643048652290279759)
    ·
      refine ⟨12784439464572978435419639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522959643048652290279759 12784439464572978435419639)
      ·
        refine ⟨19176659196859467653129459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12784439464572978435419639 19176659196859467653129459)
        ·
          refine ⟨28764988795289201479694189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19176659196859467653129459 28764988795289201479694189)
          ·
            refine ⟨10786870798233450554885321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28764988795289201479694189 10786870798233450554885321)
            ·
              refine ⟨8090153098675087916163991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10786870798233450554885321 8090153098675087916163991)
              ·
                refine ⟨12135229648012631874245987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090153098675087916163991 12135229648012631874245987)
                ·
                  refine ⟨18202844472018947811368981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12135229648012631874245987 18202844472018947811368981)
                  ·
                    refine ⟨853258334625888178657921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18202844472018947811368981 853258334625888178657921)
                    ·
                      refine ⟨639943750969416133993441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853258334625888178657921 639943750969416133993441)
                      ·
                        rfl

theorem cell23_1246286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_1246286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246286 prefixEnd_1246286 := by exact prefixLift 1246286
  have htrace : WordTrace (prefixWord ++ tailWord_1246286) baseStart_1246286 baseEnd_1246286 := by
    simpa [prefixWord, tailWord_1246286, baseEnd_1246286] using wordTrace_append hprefix tailTrace_1246286
  have hstable : (prefixWord ++ tailWord_1246286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246286).length < 2 ^ (prefixWord ++ tailWord_1246286).sum := by decide
  have hdescent : baseEnd_1246286 < baseStart_1246286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246289 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_1246289 : Nat := 118140960795 + 1246289 * 2 ^ 59
def prefixEnd_1246289 : Nat := 4983230072969 + 3 ^ 40 * 1246289 * 2
def baseEnd_1246289 : Nat := 639945291411379622255927

theorem tailTrace_1246289 : CollatzResearch.WordTrace tailWord_1246289 prefixEnd_1246289 639945291411379622255927 := by
  unfold tailWord_1246289
  simp only [CollatzResearch.WordTrace]
  refine ⟨45455894181915277060517921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30303929454610184707011947 45455894181915277060517921)
  ·
    refine ⟨34091920636436457795388441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45455894181915277060517921 34091920636436457795388441)
    ·
      refine ⟨25568940477327343346541331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34091920636436457795388441 25568940477327343346541331)
      ·
        refine ⟨38353410715991015019811997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25568940477327343346541331 38353410715991015019811997)
        ·
          refine ⟨14382529018496630632429499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38353410715991015019811997 14382529018496630632429499)
          ·
            refine ⟨21573793527744945948644249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14382529018496630632429499 21573793527744945948644249)
            ·
              refine ⟨16180345145808709461483187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21573793527744945948644249 16180345145808709461483187)
              ·
                refine ⟨24270517718713064192224781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16180345145808709461483187 24270517718713064192224781)
                ·
                  refine ⟨9101444144517399072084293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24270517718713064192224781 9101444144517399072084293)
                  ·
                    refine ⟨1706520777097012326015805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9101444144517399072084293 1706520777097012326015805)
                    ·
                      refine ⟨639945291411379622255927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706520777097012326015805 639945291411379622255927)
                      ·
                        rfl

theorem cell23_1246289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_1246289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246289 prefixEnd_1246289 := by exact prefixLift 1246289
  have htrace : WordTrace (prefixWord ++ tailWord_1246289) baseStart_1246289 baseEnd_1246289 := by
    simpa [prefixWord, tailWord_1246289, baseEnd_1246289] using wordTrace_append hprefix tailTrace_1246289
  have hstable : (prefixWord ++ tailWord_1246289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246289).length < 2 ^ (prefixWord ++ tailWord_1246289).sum := by decide
  have hdescent : baseEnd_1246289 < baseStart_1246289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246339 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 5, 5]
def baseStart_1246339 : Nat := 118140960795 + 1246339 * 2 ^ 59
def prefixEnd_1246339 : Nat := 4983230072969 + 3 ^ 40 * 1246339 * 2
def baseEnd_1246339 : Nat := 213323655148034808876899

theorem tailTrace_1246339 : CollatzResearch.WordTrace tailWord_1246339 prefixEnd_1246339 213323655148034808876899 := by
  unfold tailWord_1246339
  simp only [CollatzResearch.WordTrace]
  refine ⟨45457717831734135599838071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30305145221156090399892047 45457717831734135599838071)
  ·
    refine ⟨68186576747601203399757107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45457717831734135599838071 68186576747601203399757107)
    ·
      refine ⟨102279865121401805099635661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68186576747601203399757107 102279865121401805099635661)
      ·
        refine ⟨38354949420525676912363373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102279865121401805099635661 38354949420525676912363373)
        ·
          refine ⟨14383106032697128842136265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38354949420525676912363373 14383106032697128842136265)
          ·
            refine ⟨10787329524522846631602199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14383106032697128842136265 10787329524522846631602199)
            ·
              refine ⟨16180994286784269947403299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10787329524522846631602199 16180994286784269947403299)
              ·
                refine ⟨24271491430176404921104949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16180994286784269947403299 24271491430176404921104949)
                ·
                  refine ⟨2275452321579037961353589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24271491430176404921104949 2275452321579037961353589)
                  ·
                    refine ⟨213323655148034808876899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2275452321579037961353589 213323655148034808876899)
                    ·
                      rfl

theorem cell23_1246339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 5].length) (baseStart_1246339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246339 prefixEnd_1246339 := by exact prefixLift 1246339
  have htrace : WordTrace (prefixWord ++ tailWord_1246339) baseStart_1246339 baseEnd_1246339 := by
    simpa [prefixWord, tailWord_1246339, baseEnd_1246339] using wordTrace_append hprefix tailTrace_1246339
  have hstable : (prefixWord ++ tailWord_1246339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246339).length < 2 ^ (prefixWord ++ tailWord_1246339).sum := by decide
  have hdescent : baseEnd_1246339 < baseStart_1246339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246373 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_1246373 : Nat := 118140960795 + 1246373 * 2 ^ 59
def prefixEnd_1246373 : Nat := 4983230072969 + 3 ^ 40 * 1246373 * 2
def baseEnd_1246373 : Nat := 213329474595452431201847

theorem tailTrace_1246373 : CollatzResearch.WordTrace tailWord_1246373 prefixEnd_1246373 213329474595452431201847 := by
  unfold tailWord_1246373
  simp only [CollatzResearch.WordTrace]
  refine ⟨45458957913610959406575773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30305971942407306271050515 45458957913610959406575773)
  ·
    refine ⟨17047109217604109777465915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45458957913610959406575773 17047109217604109777465915)
    ·
      refine ⟨25570663826406164666198873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17047109217604109777465915 25570663826406164666198873)
      ·
        refine ⟨19177997869804623499649155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25570663826406164666198873 19177997869804623499649155)
        ·
          refine ⟨28766996804706935249473733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19177997869804623499649155 28766996804706935249473733)
          ·
            refine ⟨5393811900882550359276325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28766996804706935249473733 5393811900882550359276325)
            ·
              refine ⟨1011339731415478192364311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5393811900882550359276325 1011339731415478192364311)
              ·
                refine ⟨1517009597123217288546467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011339731415478192364311 1517009597123217288546467)
                ·
                  refine ⟨2275514395684825932819701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517009597123217288546467 2275514395684825932819701)
                  ·
                    refine ⟨213329474595452431201847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2275514395684825932819701 213329474595452431201847)
                    ·
                      rfl

theorem cell23_1246373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_1246373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246373 prefixEnd_1246373 := by exact prefixLift 1246373
  have htrace : WordTrace (prefixWord ++ tailWord_1246373) baseStart_1246373 baseEnd_1246373 := by
    simpa [prefixWord, tailWord_1246373, baseEnd_1246373] using wordTrace_append hprefix tailTrace_1246373
  have hstable : (prefixWord ++ tailWord_1246373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246373).length < 2 ^ (prefixWord ++ tailWord_1246373).sum := by decide
  have hdescent : baseEnd_1246373 < baseStart_1246373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246396 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1246396 : Nat := 118140960795 + 1246396 * 2 ^ 59
def prefixEnd_1246396 : Nat := 4983230072969 + 3 ^ 40 * 1246396 * 2
def baseEnd_1246396 : Nat := 640000233841410703617935

theorem tailTrace_1246396 : CollatzResearch.WordTrace tailWord_1246396 prefixEnd_1246396 640000233841410703617935 := by
  unfold tailWord_1246396
  simp only [CollatzResearch.WordTrace]
  refine ⟨22729898396263817167331521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30306531195018422889775361 22729898396263817167331521)
  ·
    refine ⟨17047423797197862875498641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22729898396263817167331521 17047423797197862875498641)
    ·
      refine ⟨12785567847898397156623981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17047423797197862875498641 12785567847898397156623981)
      ·
        refine ⟨4794587942961898933733993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12785567847898397156623981 4794587942961898933733993)
        ·
          refine ⟨3595940957221424200300495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4794587942961898933733993 3595940957221424200300495)
          ·
            refine ⟨5393911435832136300450743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595940957221424200300495 5393911435832136300450743)
            ·
              refine ⟨8090867153748204450676115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393911435832136300450743 8090867153748204450676115)
              ·
                refine ⟨12136300730622306676014173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090867153748204450676115 12136300730622306676014173)
                ·
                  refine ⟨4551112773983365003505315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12136300730622306676014173 4551112773983365003505315)
                  ·
                    refine ⟨6826669160975047505257973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4551112773983365003505315 6826669160975047505257973)
                    ·
                      refine ⟨640000233841410703617935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6826669160975047505257973 640000233841410703617935)
                      ·
                        rfl

theorem cell23_1246396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1246396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246396 prefixEnd_1246396 := by exact prefixLift 1246396
  have htrace : WordTrace (prefixWord ++ tailWord_1246396) baseStart_1246396 baseEnd_1246396 := by
    simpa [prefixWord, tailWord_1246396, baseEnd_1246396] using wordTrace_append hprefix tailTrace_1246396
  have hstable : (prefixWord ++ tailWord_1246396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246396).length < 2 ^ (prefixWord ++ tailWord_1246396).sum := by decide
  have hdescent : baseEnd_1246396 < baseStart_1246396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246410 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_1246410 : Nat := 118140960795 + 1246410 * 2 ^ 59
def prefixEnd_1246410 : Nat := 4983230072969 + 3 ^ 40 * 1246410 * 2
def baseEnd_1246410 : Nat := 640007422570573648842871

theorem tailTrace_1246410 : CollatzResearch.WordTrace tailWord_1246410 prefixEnd_1246410 640007422570573648842871 := by
  unfold tailWord_1246410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11365076853619228681418171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30306871609651276483781789 11365076853619228681418171)
  ·
    refine ⟨17047615280428843022127257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11365076853619228681418171 17047615280428843022127257)
    ·
      refine ⟨12785711460321632266595443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17047615280428843022127257 12785711460321632266595443)
      ·
        refine ⟨19178567190482448399893165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12785711460321632266595443 19178567190482448399893165)
        ·
          refine ⟨7191962696430918149959937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19178567190482448399893165 7191962696430918149959937)
          ·
            refine ⟨5393972022323188612469953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7191962696430918149959937 5393972022323188612469953)
            ·
              refine ⟨4045479016742391459352465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393972022323188612469953 4045479016742391459352465)
              ·
                refine ⟨3034109262556793594514349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4045479016742391459352465 3034109262556793594514349)
                ·
                  refine ⟨1137790973458797597942881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3034109262556793594514349 1137790973458797597942881)
                  ·
                    refine ⟨853343230094098198457161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1137790973458797597942881 853343230094098198457161)
                    ·
                      refine ⟨640007422570573648842871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853343230094098198457161 640007422570573648842871)
                      ·
                        rfl

theorem cell23_1246410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_1246410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246410 prefixEnd_1246410 := by exact prefixLift 1246410
  have htrace : WordTrace (prefixWord ++ tailWord_1246410) baseStart_1246410 baseEnd_1246410 := by
    simpa [prefixWord, tailWord_1246410, baseEnd_1246410] using wordTrace_append hprefix tailTrace_1246410
  have hstable : (prefixWord ++ tailWord_1246410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246410).length < 2 ^ (prefixWord ++ tailWord_1246410).sum := by decide
  have hdescent : baseEnd_1246410 < baseStart_1246410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246426 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1246426 : Nat := 118140960795 + 1246426 * 2 ^ 59
def prefixEnd_1246426 : Nat := 4983230072969 + 3 ^ 40 * 1246426 * 2
def baseEnd_1246426 : Nat := 640015638261045586242797

theorem tailTrace_1246426 : CollatzResearch.WordTrace tailWord_1246426 prefixEnd_1246426 640015638261045586242797 := by
  unfold tailWord_1246426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11365222745604737364563783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30307260654945966305503421 11365222745604737364563783)
  ·
    refine ⟨17047834118407106046845675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11365222745604737364563783 17047834118407106046845675)
    ·
      refine ⟨25571751177610659070268513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17047834118407106046845675 25571751177610659070268513)
      ·
        refine ⟨19178813383207994302701385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25571751177610659070268513 19178813383207994302701385)
        ·
          refine ⟨14384110037405995727026039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19178813383207994302701385 14384110037405995727026039)
          ·
            refine ⟨21576165056108993590539059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14384110037405995727026039 21576165056108993590539059)
            ·
              refine ⟨32364247584163490385808589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21576165056108993590539059 32364247584163490385808589)
              ·
                refine ⟨12136592844061308894678221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32364247584163490385808589 12136592844061308894678221)
                ·
                  refine ⟨4551222316522990835504333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12136592844061308894678221 4551222316522990835504333)
                  ·
                    refine ⟨1706708368696121563314125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4551222316522990835504333 1706708368696121563314125)
                    ·
                      refine ⟨640015638261045586242797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706708368696121563314125 640015638261045586242797)
                      ·
                        rfl

theorem cell23_1246426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1246426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246426 prefixEnd_1246426 := by exact prefixLift 1246426
  have htrace : WordTrace (prefixWord ++ tailWord_1246426) baseStart_1246426 baseEnd_1246426 := by
    simpa [prefixWord, tailWord_1246426, baseEnd_1246426] using wordTrace_append hprefix tailTrace_1246426
  have hstable : (prefixWord ++ tailWord_1246426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246426).length < 2 ^ (prefixWord ++ tailWord_1246426).sum := by decide
  have hdescent : baseEnd_1246426 < baseStart_1246426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246443 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 3]
def baseStart_1246443 : Nat := 118140960795 + 1246443 * 2 ^ 59
def prefixEnd_1246443 : Nat := 4983230072969 + 3 ^ 40 * 1246443 * 2
def baseEnd_1246443 : Nat := 640024367432172019730219

theorem tailTrace_1246443 : CollatzResearch.WordTrace tailWord_1246443 prefixEnd_1246443 640024367432172019730219 := by
  unfold tailWord_1246443
  simp only [CollatzResearch.WordTrace]
  refine ⟨45461511023357361361623983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30307674015571574241082655 45461511023357361361623983)
  ·
    refine ⟨68192266535036042042435975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45461511023357361361623983 68192266535036042042435975)
    ·
      refine ⟨102288399802554063063653963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68192266535036042042435975 102288399802554063063653963)
      ·
        refine ⟨153432599703831094595480945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102288399802554063063653963 153432599703831094595480945)
        ·
          refine ⟨115074449777873320946610709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153432599703831094595480945 115074449777873320946610709)
          ·
            refine ⟨5394114833337811919372377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115074449777873320946610709 5394114833337811919372377)
            ·
              refine ⟨4045586125003358939529283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394114833337811919372377 4045586125003358939529283)
              ·
                refine ⟨6068379187505038409293925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045586125003358939529283 6068379187505038409293925)
                ·
                  refine ⟨1137821097657194701742611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6068379187505038409293925 1137821097657194701742611)
                  ·
                    refine ⟨1706731646485792052613917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137821097657194701742611 1706731646485792052613917)
                    ·
                      refine ⟨640024367432172019730219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1706731646485792052613917 640024367432172019730219)
                      ·
                        rfl

theorem cell23_1246443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 3].length) (baseStart_1246443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246443 prefixEnd_1246443 := by exact prefixLift 1246443
  have htrace : WordTrace (prefixWord ++ tailWord_1246443) baseStart_1246443 baseEnd_1246443 := by
    simpa [prefixWord, tailWord_1246443, baseEnd_1246443] using wordTrace_append hprefix tailTrace_1246443
  have hstable : (prefixWord ++ tailWord_1246443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246443).length < 2 ^ (prefixWord ++ tailWord_1246443).sum := by decide
  have hdescent : baseEnd_1246443 < baseStart_1246443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246444 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 1, 2, 2]
def baseStart_1246444 : Nat := 118140960795 + 1246444 * 2 ^ 59
def prefixEnd_1246444 : Nat := 4983230072969 + 3 ^ 40 * 1246444 * 2
def baseEnd_1246444 : Nat := 640024880912826515817715

theorem tailTrace_1246444 : CollatzResearch.WordTrace tailWord_1246444 prefixEnd_1246444 640024880912826515817715 := by
  unfold tailWord_1246444
  simp only [CollatzResearch.WordTrace]
  refine ⟨22730773748176869266205193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30307698330902492354940257 22730773748176869266205193)
  ·
    refine ⟨17048080311132651949653895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22730773748176869266205193 17048080311132651949653895)
    ·
      refine ⟨25572120466698977924480843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17048080311132651949653895 25572120466698977924480843)
      ·
        refine ⟨38358180700048466886721265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25572120466698977924480843 38358180700048466886721265)
        ·
          refine ⟨28768635525036350165040949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38358180700048466886721265 28768635525036350165040949)
          ·
            refine ⟨2697059580472157827972589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28768635525036350165040949 2697059580472157827972589)
            ·
              refine ⟨1011397342677059185489721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2697059580472157827972589 1011397342677059185489721)
              ·
                refine ⟨758548007007794389117291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011397342677059185489721 758548007007794389117291)
                ·
                  refine ⟨1137822010511691583675937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758548007007794389117291 1137822010511691583675937)
                  ·
                    refine ⟨853366507883768687756953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1137822010511691583675937 853366507883768687756953)
                    ·
                      refine ⟨640024880912826515817715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853366507883768687756953 640024880912826515817715)
                      ·
                        rfl

theorem cell23_1246444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_1246444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246444 prefixEnd_1246444 := by exact prefixLift 1246444
  have htrace : WordTrace (prefixWord ++ tailWord_1246444) baseStart_1246444 baseEnd_1246444 := by
    simpa [prefixWord, tailWord_1246444, baseEnd_1246444] using wordTrace_append hprefix tailTrace_1246444
  have hstable : (prefixWord ++ tailWord_1246444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246444).length < 2 ^ (prefixWord ++ tailWord_1246444).sum := by decide
  have hdescent : baseEnd_1246444 < baseStart_1246444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246487 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 1, 3, 2]
def baseStart_1246487 : Nat := 118140960795 + 1246487 * 2 ^ 59
def prefixEnd_1246487 : Nat := 4983230072969 + 3 ^ 40 * 1246487 * 2
def baseEnd_1246487 : Nat := 640046960580969847580017

theorem tailTrace_1246487 : CollatzResearch.WordTrace tailWord_1246487 prefixEnd_1246487 640046960580969847580017 := by
  unfold tailWord_1246487
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463115835197956876225715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30308743890131971250817143 45463115835197956876225715)
  ·
    refine ⟨68194673752796935314338573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45463115835197956876225715 68194673752796935314338573)
    ·
      refine ⟨25573002657298850742876965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68194673752796935314338573 25573002657298850742876965)
      ·
        refine ⟨4794937998243534514289431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25573002657298850742876965 4794937998243534514289431)
        ·
          refine ⟨7192406997365301771434147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4794937998243534514289431 7192406997365301771434147)
          ·
            refine ⟨10788610496047952657151221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7192406997365301771434147 10788610496047952657151221)
            ·
              refine ⟨1011432234004495561607927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10788610496047952657151221 1011432234004495561607927)
              ·
                refine ⟨1517148351006743342411891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011432234004495561607927 1517148351006743342411891)
                ·
                  refine ⟨2275722526510115013617837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517148351006743342411891 2275722526510115013617837)
                  ·
                    refine ⟨853395947441293130106689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2275722526510115013617837 853395947441293130106689)
                    ·
                      refine ⟨640046960580969847580017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853395947441293130106689 640046960580969847580017)
                      ·
                        rfl

theorem cell23_1246487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_1246487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246487 prefixEnd_1246487 := by exact prefixLift 1246487
  have htrace : WordTrace (prefixWord ++ tailWord_1246487) baseStart_1246487 baseEnd_1246487 := by
    simpa [prefixWord, tailWord_1246487, baseEnd_1246487] using wordTrace_append hprefix tailTrace_1246487
  have hstable : (prefixWord ++ tailWord_1246487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246487).length < 2 ^ (prefixWord ++ tailWord_1246487).sum := by decide
  have hdescent : baseEnd_1246487 < baseStart_1246487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246513 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1246513 : Nat := 118140960795 + 1246513 * 2 ^ 59
def prefixEnd_1246513 : Nat := 4983230072969 + 3 ^ 40 * 1246513 * 2
def baseEnd_1246513 : Nat := 640060311077986745854897

theorem tailTrace_1246513 : CollatzResearch.WordTrace tailWord_1246513 prefixEnd_1246513 640060311077986745854897 := by
  unfold tailWord_1246513
  simp only [CollatzResearch.WordTrace]
  refine ⟨45464064133103763316672193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30309376088735842211114795 45464064133103763316672193)
  ·
    refine ⟨34098048099827822487504145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45464064133103763316672193 34098048099827822487504145)
    ·
      refine ⟨25573536074870866865628109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34098048099827822487504145 25573536074870866865628109)
      ·
        refine ⟨9590076028076575074610541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25573536074870866865628109 9590076028076575074610541)
        ·
          refine ⟨3596278510528715652978953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9590076028076575074610541 3596278510528715652978953)
          ·
            refine ⟨2697208882896536739734215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3596278510528715652978953 2697208882896536739734215)
            ·
              refine ⟨4045813324344805109601323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697208882896536739734215 4045813324344805109601323)
              ·
                refine ⟨6068719986517207664401985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045813324344805109601323 6068719986517207664401985)
                ·
                  refine ⟨4551539989887905748301489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6068719986517207664401985 4551539989887905748301489)
                  ·
                    refine ⟨3413654992415929311226117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551539989887905748301489 3413654992415929311226117)
                    ·
                      refine ⟨640060311077986745854897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3413654992415929311226117 640060311077986745854897)
                      ·
                        rfl

theorem cell23_1246513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1246513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246513 prefixEnd_1246513 := by exact prefixLift 1246513
  have htrace : WordTrace (prefixWord ++ tailWord_1246513) baseStart_1246513 baseEnd_1246513 := by
    simpa [prefixWord, tailWord_1246513, baseEnd_1246513] using wordTrace_append hprefix tailTrace_1246513
  have hstable : (prefixWord ++ tailWord_1246513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246513).length < 2 ^ (prefixWord ++ tailWord_1246513).sum := by decide
  have hdescent : baseEnd_1246513 < baseStart_1246513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246517 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_1246517 : Nat := 118140960795 + 1246517 * 2 ^ 59
def prefixEnd_1246517 : Nat := 4983230072969 + 3 ^ 40 * 1246517 * 2
def baseEnd_1246517 : Nat := 640062365000604730204879

theorem tailTrace_1246517 : CollatzResearch.WordTrace tailWord_1246517 prefixEnd_1246517 640062365000604730204879 := by
  unfold tailWord_1246517
  simp only [CollatzResearch.WordTrace]
  refine ⟨45464210025089271999817805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30309473350059514666545203 45464210025089271999817805)
  ·
    refine ⟨17049078759408476999931677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45464210025089271999817805 17049078759408476999931677)
    ·
      refine ⟨6393404534778178874974379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17049078759408476999931677 6393404534778178874974379)
      ·
        refine ⟨9590106802167268312461569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6393404534778178874974379 9590106802167268312461569)
        ·
          refine ⟨7192580101625451234346177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9590106802167268312461569 7192580101625451234346177)
          ·
            refine ⟨5394435076219088425759633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7192580101625451234346177 5394435076219088425759633)
            ·
              refine ⟨4045826307164316319319725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394435076219088425759633 4045826307164316319319725)
              ·
                refine ⟨1517184865186618619744897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4045826307164316319319725 1517184865186618619744897)
                ·
                  refine ⟨1137888648889963964808673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517184865186618619744897 1137888648889963964808673)
                  ·
                    refine ⟨853416486667472973606505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1137888648889963964808673 853416486667472973606505)
                    ·
                      refine ⟨640062365000604730204879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853416486667472973606505 640062365000604730204879)
                      ·
                        rfl

theorem cell23_1246517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_1246517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246517 prefixEnd_1246517 := by exact prefixLift 1246517
  have htrace : WordTrace (prefixWord ++ tailWord_1246517) baseStart_1246517 baseEnd_1246517 := by
    simpa [prefixWord, tailWord_1246517, baseEnd_1246517] using wordTrace_append hprefix tailTrace_1246517
  have hstable : (prefixWord ++ tailWord_1246517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246517).length < 2 ^ (prefixWord ++ tailWord_1246517).sum := by decide
  have hdescent : baseEnd_1246517 < baseStart_1246517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246540 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 5]
def baseStart_1246540 : Nat := 118140960795 + 1246540 * 2 ^ 59
def prefixEnd_1246540 : Nat := 4983230072969 + 3 ^ 40 * 1246540 * 2
def baseEnd_1246540 : Nat := 71119352783962015579697

theorem tailTrace_1246540 : CollatzResearch.WordTrace tailWord_1246540 prefixEnd_1246540 71119352783962015579697 := by
  unfold tailWord_1246540
  simp only [CollatzResearch.WordTrace]
  refine ⟨22732524452002973463952537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30310032602670631285270049 22732524452002973463952537)
  ·
    refine ⟨17049393339002230097964403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22732524452002973463952537 17049393339002230097964403)
    ·
      refine ⟨25574090008503345146946605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17049393339002230097964403 25574090008503345146946605)
      ·
        refine ⟨9590283753188754430104977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25574090008503345146946605 9590283753188754430104977)
        ·
          refine ⟨7192712814891565822578733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9590283753188754430104977 7192712814891565822578733)
          ·
            refine ⟨2697267305584337183467025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7192712814891565822578733 2697267305584337183467025)
            ·
              refine ⟨2022950479188252887600269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697267305584337183467025 2022950479188252887600269)
              ·
                refine ⟨758606429695594832850101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2022950479188252887600269 758606429695594832850101)
                ·
                  refine ⟨71119352783962015579697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 758606429695594832850101 71119352783962015579697)
                  ·
                    rfl

theorem cell23_1246540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_1246540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246540 prefixEnd_1246540 := by exact prefixLift 1246540
  have htrace : WordTrace (prefixWord ++ tailWord_1246540) baseStart_1246540 baseEnd_1246540 := by
    simpa [prefixWord, tailWord_1246540, baseEnd_1246540] using wordTrace_append hprefix tailTrace_1246540
  have hstable : (prefixWord ++ tailWord_1246540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246540).length < 2 ^ (prefixWord ++ tailWord_1246540).sum := by decide
  have hdescent : baseEnd_1246540 < baseStart_1246540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246573 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1246573 : Nat := 118140960795 + 1246573 * 2 ^ 59
def prefixEnd_1246573 : Nat := 4983230072969 + 3 ^ 40 * 1246573 * 2
def baseEnd_1246573 : Nat := 640091119917256511104621

theorem tailTrace_1246573 : CollatzResearch.WordTrace tailWord_1246573 prefixEnd_1246573 640091119917256511104621 := by
  unfold tailWord_1246573
  simp only [CollatzResearch.WordTrace]
  refine ⟨45466252512886393563856373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30310835008590929042570915 45466252512886393563856373)
  ·
    refine ⟨4262461173083099396611535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45466252512886393563856373 4262461173083099396611535)
    ·
      refine ⟨6393691759624649094917303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262461173083099396611535 6393691759624649094917303)
      ·
        refine ⟨9590537639436973642375955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6393691759624649094917303 9590537639436973642375955)
        ·
          refine ⟨14385806459155460463563933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9590537639436973642375955 14385806459155460463563933)
          ·
            refine ⟨5394677422183297673836475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14385806459155460463563933 5394677422183297673836475)
            ·
              refine ⟨8092016133274946510754713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394677422183297673836475 8092016133274946510754713)
              ·
                refine ⟨6069012099956209883066035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8092016133274946510754713 6069012099956209883066035)
                ·
                  refine ⟨9103518149934314824599053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6069012099956209883066035 9103518149934314824599053)
                  ·
                    refine ⟨3413819306225368059224645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9103518149934314824599053 3413819306225368059224645)
                    ·
                      refine ⟨640091119917256511104621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3413819306225368059224645 640091119917256511104621)
                      ·
                        rfl

theorem cell23_1246573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1246573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246573 prefixEnd_1246573 := by exact prefixLift 1246573
  have htrace : WordTrace (prefixWord ++ tailWord_1246573) baseStart_1246573 baseEnd_1246573 := by
    simpa [prefixWord, tailWord_1246573, baseEnd_1246573] using wordTrace_append hprefix tailTrace_1246573
  have hstable : (prefixWord ++ tailWord_1246573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246573).length < 2 ^ (prefixWord ++ tailWord_1246573).sum := by decide
  have hdescent : baseEnd_1246573 < baseStart_1246573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246583 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 3, 4]
def baseStart_1246583 : Nat := 118140960795 + 1246583 * 2 ^ 59
def prefixEnd_1246583 : Nat := 4983230072969 + 3 ^ 40 * 1246583 * 2
def baseEnd_1246583 : Nat := 213365418241267157326525

theorem tailTrace_1246583 : CollatzResearch.WordTrace tailWord_1246583 prefixEnd_1246583 213365418241267157326525 := by
  unfold tailWord_1246583
  simp only [CollatzResearch.WordTrace]
  refine ⟨45466617242850165271720403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30311078161900110181146935 45466617242850165271720403)
  ·
    refine ⟨68199925864275247907580605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45466617242850165271720403 68199925864275247907580605)
    ·
      refine ⟨25574972199103217965342727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68199925864275247907580605 25574972199103217965342727)
      ·
        refine ⟨38362458298654826948014091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25574972199103217965342727 38362458298654826948014091)
        ·
          refine ⟨57543687447982240422021137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38362458298654826948014091 57543687447982240422021137)
          ·
            refine ⟨43157765585986680316515853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57543687447982240422021137 43157765585986680316515853)
            ·
              refine ⟨16184162094745005118693445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43157765585986680316515853 16184162094745005118693445)
              ·
                refine ⟨3034530392764688459755021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16184162094745005118693445 3034530392764688459755021)
                ·
                  refine ⟨1137948897286758172408133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3034530392764688459755021 1137948897286758172408133)
                  ·
                    refine ⟨213365418241267157326525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1137948897286758172408133 213365418241267157326525)
                    ·
                      rfl

theorem cell23_1246583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_1246583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246583 prefixEnd_1246583 := by exact prefixLift 1246583
  have htrace : WordTrace (prefixWord ++ tailWord_1246583) baseStart_1246583 baseEnd_1246583 := by
    simpa [prefixWord, tailWord_1246583, baseEnd_1246583] using wordTrace_append hprefix tailTrace_1246583
  have hstable : (prefixWord ++ tailWord_1246583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246583).length < 2 ^ (prefixWord ++ tailWord_1246583).sum := by decide
  have hdescent : baseEnd_1246583 < baseStart_1246583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246586 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1246586 : Nat := 118140960795 + 1246586 * 2 ^ 59
def prefixEnd_1246586 : Nat := 4983230072969 + 3 ^ 40 * 1246586 * 2
def baseEnd_1246586 : Nat := 640097795165764960242061

theorem tailTrace_1246586 : CollatzResearch.WordTrace tailWord_1246586 prefixEnd_1246586 640097795165764960242061 := by
  unfold tailWord_1246586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11366681665459824196019903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30311151107892864522719741 11366681665459824196019903)
  ·
    refine ⟨17050022498189736294029855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11366681665459824196019903 17050022498189736294029855)
    ·
      refine ⟨25575033747284604441044783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17050022498189736294029855 25575033747284604441044783)
      ·
        refine ⟨38362550620926906661567175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25575033747284604441044783 38362550620926906661567175)
        ·
          refine ⟨57543825931390359992350763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38362550620926906661567175 57543825931390359992350763)
          ·
            refine ⟨86315738897085539988526145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57543825931390359992350763 86315738897085539988526145)
            ·
              refine ⟨64736804172814154991394609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86315738897085539988526145 64736804172814154991394609)
              ·
                refine ⟨48552603129610616243545957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64736804172814154991394609 48552603129610616243545957)
                ·
                  refine ⟨9103613086801990545664867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48552603129610616243545957 9103613086801990545664867)
                  ·
                    refine ⟨13655419630202985818497301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9103613086801990545664867 13655419630202985818497301)
                    ·
                      refine ⟨640097795165764960242061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13655419630202985818497301 640097795165764960242061)
                      ·
                        rfl

theorem cell23_1246586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1246586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246586 prefixEnd_1246586 := by exact prefixLift 1246586
  have htrace : WordTrace (prefixWord ++ tailWord_1246586) baseStart_1246586 baseEnd_1246586 := by
    simpa [prefixWord, tailWord_1246586, baseEnd_1246586] using wordTrace_append hprefix tailTrace_1246586
  have hstable : (prefixWord ++ tailWord_1246586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246586).length < 2 ^ (prefixWord ++ tailWord_1246586).sum := by decide
  have hdescent : baseEnd_1246586 < baseStart_1246586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246701 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1246701 : Nat := 118140960795 + 1246701 * 2 ^ 59
def prefixEnd_1246701 : Nat := 4983230072969 + 3 ^ 40 * 1246701 * 2
def baseEnd_1246701 : Nat := 640156845441032010304033

theorem tailTrace_1246701 : CollatzResearch.WordTrace tailWord_1246701 prefixEnd_1246701 640156845441032010304033 := by
  unfold tailWord_1246701
  simp only [CollatzResearch.WordTrace]
  refine ⟨45470921056422671424515957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30313947370948447616343971 45470921056422671424515957)
  ·
    refine ⟨4262898849039625446048371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45470921056422671424515957 4262898849039625446048371)
    ·
      refine ⟨6394348273559438169072557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262898849039625446048371 6394348273559438169072557)
      ·
        refine ⟨2397880602584789313402209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6394348273559438169072557 2397880602584789313402209)
        ·
          refine ⟨1798410451938591985051657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397880602584789313402209 1798410451938591985051657)
          ·
            refine ⟨1348807838953943988788743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798410451938591985051657 1348807838953943988788743)
            ·
              refine ⟨2023211758430915983183115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348807838953943988788743 2023211758430915983183115)
              ·
                refine ⟨3034817637646373974774673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023211758430915983183115 3034817637646373974774673)
                ·
                  refine ⟨2276113228234780481081005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034817637646373974774673 2276113228234780481081005)
                  ·
                    refine ⟨853542460588042680405377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276113228234780481081005 853542460588042680405377)
                    ·
                      refine ⟨640156845441032010304033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853542460588042680405377 640156845441032010304033)
                      ·
                        rfl

theorem cell23_1246701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1246701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246701 prefixEnd_1246701 := by exact prefixLift 1246701
  have htrace : WordTrace (prefixWord ++ tailWord_1246701) baseStart_1246701 baseEnd_1246701 := by
    simpa [prefixWord, tailWord_1246701, baseEnd_1246701] using wordTrace_append hprefix tailTrace_1246701
  have hstable : (prefixWord ++ tailWord_1246701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246701).length < 2 ^ (prefixWord ++ tailWord_1246701).sum := by decide
  have hdescent : baseEnd_1246701 < baseStart_1246701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246717 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_1246717 : Nat := 118140960795 + 1246717 * 2 ^ 59
def prefixEnd_1246717 : Nat := 4983230072969 + 3 ^ 40 * 1246717 * 2
def baseEnd_1246717 : Nat := 640165061131503947703959

theorem tailTrace_1246717 : CollatzResearch.WordTrace tailWord_1246717 prefixEnd_1246717 640165061131503947703959 := by
  unfold tailWord_1246717
  simp only [CollatzResearch.WordTrace]
  refine ⟨45471504624364706157098405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30314336416243137438065603 45471504624364706157098405)
  ·
    refine ⟨8525907117068382404455951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45471504624364706157098405 8525907117068382404455951)
    ·
      refine ⟨12788860675602573606683927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8525907117068382404455951 12788860675602573606683927)
      ·
        refine ⟨19183291013403860410025891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12788860675602573606683927 19183291013403860410025891)
        ·
          refine ⟨28774936520105790615038837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19183291013403860410025891 28774936520105790615038837)
          ·
            refine ⟨2697650298759917870159891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28774936520105790615038837 2697650298759917870159891)
            ·
              refine ⟨4046475448139876805239837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697650298759917870159891 4046475448139876805239837)
              ·
                refine ⟨1517428293052453801964939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4046475448139876805239837 1517428293052453801964939)
                ·
                  refine ⟨2276142439578680702947409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517428293052453801964939 2276142439578680702947409)
                  ·
                    refine ⟨1707106829684010527210557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276142439578680702947409 1707106829684010527210557)
                    ·
                      refine ⟨640165061131503947703959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1707106829684010527210557 640165061131503947703959)
                      ·
                        rfl

theorem cell23_1246717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_1246717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246717 prefixEnd_1246717 := by exact prefixLift 1246717
  have htrace : WordTrace (prefixWord ++ tailWord_1246717) baseStart_1246717 baseEnd_1246717 := by
    simpa [prefixWord, tailWord_1246717, baseEnd_1246717] using wordTrace_append hprefix tailTrace_1246717
  have hstable : (prefixWord ++ tailWord_1246717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246717).length < 2 ^ (prefixWord ++ tailWord_1246717).sum := by decide
  have hdescent : baseEnd_1246717 < baseStart_1246717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246744 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 1, 2, 4]
def baseStart_1246744 : Nat := 118140960795 + 1246744 * 2 ^ 59
def prefixEnd_1246744 : Nat := 4983230072969 + 3 ^ 40 * 1246744 * 2
def baseEnd_1246744 : Nat := 640178925109175342066335

theorem tailTrace_1246744 : CollatzResearch.WordTrace tailWord_1246744 prefixEnd_1246744 640178925109175342066335 := by
  unfold tailWord_1246744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22736244697633444884165643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30314992930177926512220857 22736244697633444884165643)
  ·
    refine ⟨34104367046450167326248465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22736244697633444884165643 34104367046450167326248465)
    ·
      refine ⟨25578275284837625494686349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34104367046450167326248465 25578275284837625494686349)
      ·
        refine ⟨9591853231814109560507381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25578275284837625494686349 9591853231814109560507381)
        ·
          refine ⟨899236240482572771297567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9591853231814109560507381 899236240482572771297567)
          ·
            refine ⟨1348854360723859156946351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899236240482572771297567 1348854360723859156946351)
            ·
              refine ⟨2023281541085788735419527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348854360723859156946351 2023281541085788735419527)
              ·
                refine ⟨3034922311628683103129291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023281541085788735419527 3034922311628683103129291)
                ·
                  refine ⟨4552383467443024654693937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034922311628683103129291 4552383467443024654693937)
                  ·
                    refine ⟨3414287600582268491020453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4552383467443024654693937 3414287600582268491020453)
                    ·
                      refine ⟨640178925109175342066335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3414287600582268491020453 640178925109175342066335)
                      ·
                        rfl

theorem cell23_1246744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_1246744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246744 prefixEnd_1246744 := by exact prefixLift 1246744
  have htrace : WordTrace (prefixWord ++ tailWord_1246744) baseStart_1246744 baseEnd_1246744 := by
    simpa [prefixWord, tailWord_1246744, baseEnd_1246744] using wordTrace_append hprefix tailTrace_1246744
  have hstable : (prefixWord ++ tailWord_1246744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246744).length < 2 ^ (prefixWord ++ tailWord_1246744).sum := by decide
  have hdescent : baseEnd_1246744 < baseStart_1246744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246838 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1246838 : Nat := 118140960795 + 1246838 * 2 ^ 59
def prefixEnd_1246838 : Nat := 4983230072969 + 3 ^ 40 * 1246838 * 2
def baseEnd_1246838 : Nat := 640227192290697974290903

theorem tailTrace_1246838 : CollatzResearch.WordTrace tailWord_1246838 prefixEnd_1246838 640227192290697974290903 := by
  unfold tailWord_1246838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842244866057896488890823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30317278571284229214835445 2842244866057896488890823)
  ·
    refine ⟨4263367299086844733336235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2842244866057896488890823 4263367299086844733336235)
    ·
      refine ⟨6395050948630267100004353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4263367299086844733336235 6395050948630267100004353)
      ·
        refine ⟨4796288211472700325003265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6395050948630267100004353 4796288211472700325003265)
        ·
          refine ⟨3597216158604525243752449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4796288211472700325003265 3597216158604525243752449)
          ·
            refine ⟨2697912118953393932814337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3597216158604525243752449 2697912118953393932814337)
            ·
              refine ⟨2023434089215045449610753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697912118953393932814337 2023434089215045449610753)
              ·
                refine ⟨1517575566911284087208065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023434089215045449610753 1517575566911284087208065)
                ·
                  refine ⟨1138181675183463065406049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517575566911284087208065 1138181675183463065406049)
                  ·
                    refine ⟨853636256387597299054537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1138181675183463065406049 853636256387597299054537)
                    ·
                      refine ⟨640227192290697974290903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853636256387597299054537 640227192290697974290903)
                      ·
                        rfl

theorem cell23_1246838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1246838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246838 prefixEnd_1246838 := by exact prefixLift 1246838
  have htrace : WordTrace (prefixWord ++ tailWord_1246838) baseStart_1246838 baseEnd_1246838 := by
    simpa [prefixWord, tailWord_1246838, baseEnd_1246838] using wordTrace_append hprefix tailTrace_1246838
  have hstable : (prefixWord ++ tailWord_1246838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246838).length < 2 ^ (prefixWord ++ tailWord_1246838).sum := by decide
  have hdescent : baseEnd_1246838 < baseStart_1246838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246860 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1246860 : Nat := 118140960795 + 1246860 * 2 ^ 59
def prefixEnd_1246860 : Nat := 4983230072969 + 3 ^ 40 * 1246860 * 2
def baseEnd_1246860 : Nat := 640238488865096888215801

theorem tailTrace_1246860 : CollatzResearch.WordTrace tailWord_1246860 prefixEnd_1246860 640238488865096888215801 := by
  unfold tailWord_1246860
  simp only [CollatzResearch.WordTrace]
  refine ⟨22738360131423320789777017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30317813508564427719702689 22738360131423320789777017)
  ·
    refine ⟨17053770098567490592332763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22738360131423320789777017 17053770098567490592332763)
    ·
      refine ⟨25580655147851235888499145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053770098567490592332763 25580655147851235888499145)
      ·
        refine ⟨19185491360888426916374359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25580655147851235888499145 19185491360888426916374359)
        ·
          refine ⟨28778237041332640374561539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19185491360888426916374359 28778237041332640374561539)
          ·
            refine ⟨43167355561998960561842309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28778237041332640374561539 43167355561998960561842309)
            ·
              refine ⟨8093879167874805105345433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43167355561998960561842309 8093879167874805105345433)
              ·
                refine ⟨6070409375906103829009075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8093879167874805105345433 6070409375906103829009075)
                ·
                  refine ⟨9105614063859155743513613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6070409375906103829009075 9105614063859155743513613)
                  ·
                    refine ⟨3414605273947183403817605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9105614063859155743513613 3414605273947183403817605)
                    ·
                      refine ⟨640238488865096888215801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3414605273947183403817605 640238488865096888215801)
                      ·
                        rfl

theorem cell23_1246860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1246860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246860 prefixEnd_1246860 := by exact prefixLift 1246860
  have htrace : WordTrace (prefixWord ++ tailWord_1246860) baseStart_1246860 baseEnd_1246860 := by
    simpa [prefixWord, tailWord_1246860, baseEnd_1246860] using wordTrace_append hprefix tailTrace_1246860
  have hstable : (prefixWord ++ tailWord_1246860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246860).length < 2 ^ (prefixWord ++ tailWord_1246860).sum := by decide
  have hdescent : baseEnd_1246860 < baseStart_1246860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246877 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_1246877 : Nat := 118140960795 + 1246877 * 2 ^ 59
def prefixEnd_1246877 : Nat := 4983230072969 + 3 ^ 40 * 1246877 * 2
def baseEnd_1246877 : Nat := 640247218036223321703223

theorem tailTrace_1246877 : CollatzResearch.WordTrace tailWord_1246877 prefixEnd_1246877 640247218036223321703223 := by
  unfold tailWord_1246877
  simp only [CollatzResearch.WordTrace]
  refine ⟨45477340303785053482922885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30318226869190035655281923 45477340303785053482922885)
  ·
    refine ⟨8527001306959697528048041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45477340303785053482922885 8527001306959697528048041)
    ·
      refine ⟨6395250980219773146036031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8527001306959697528048041 6395250980219773146036031)
      ·
        refine ⟨9592876470329659719054047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6395250980219773146036031 9592876470329659719054047)
        ·
          refine ⟨14389314705494489578581071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9592876470329659719054047 14389314705494489578581071)
          ·
            refine ⟨21583972058241734367871607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14389314705494489578581071 21583972058241734367871607)
            ·
              refine ⟨32375958087362601551807411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21583972058241734367871607 32375958087362601551807411)
              ·
                refine ⟨48563937131043902327711117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32375958087362601551807411 48563937131043902327711117)
                ·
                  refine ⟨18211476424141463372891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48563937131043902327711117 18211476424141463372891669)
                  ·
                    refine ⟨853662957381631095604297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18211476424141463372891669 853662957381631095604297)
                    ·
                      refine ⟨640247218036223321703223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853662957381631095604297 640247218036223321703223)
                      ·
                        rfl

theorem cell23_1246877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_1246877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246877 prefixEnd_1246877 := by exact prefixLift 1246877
  have htrace : WordTrace (prefixWord ++ tailWord_1246877) baseStart_1246877 baseEnd_1246877 := by
    simpa [prefixWord, tailWord_1246877, baseEnd_1246877] using wordTrace_append hprefix tailTrace_1246877
  have hstable : (prefixWord ++ tailWord_1246877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246877).length < 2 ^ (prefixWord ++ tailWord_1246877).sum := by decide
  have hdescent : baseEnd_1246877 < baseStart_1246877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246920 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1246920 : Nat := 118140960795 + 1246920 * 2 ^ 59
def prefixEnd_1246920 : Nat := 4983230072969 + 3 ^ 40 * 1246920 * 2
def baseEnd_1246920 : Nat := 640269297704366653465525

theorem tailTrace_1246920 : CollatzResearch.WordTrace tailWord_1246920 prefixEnd_1246920 640269297704366653465525 := by
  unfold tailWord_1246920
  simp only [CollatzResearch.WordTrace]
  refine ⟨22739454321314635913369107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30319272428419514551158809 22739454321314635913369107)
  ·
    refine ⟨34109181481971953870053661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22739454321314635913369107 34109181481971953870053661)
    ·
      refine ⟨12790943055739482701270123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34109181481971953870053661 12790943055739482701270123)
      ·
        refine ⟨19186414583609224051905185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12790943055739482701270123 19186414583609224051905185)
        ·
          refine ⟨14389810937706918038928889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19186414583609224051905185 14389810937706918038928889)
          ·
            refine ⟨10792358203280188529196667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14389810937706918038928889 10792358203280188529196667)
            ·
              refine ⟨16188537304920282793795001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10792358203280188529196667 16188537304920282793795001)
              ·
                refine ⟨12141402978690212095346251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16188537304920282793795001 12141402978690212095346251)
                ·
                  refine ⟨18212104468035318143019377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12141402978690212095346251 18212104468035318143019377)
                  ·
                    refine ⟨13659078351026488607264533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18212104468035318143019377 13659078351026488607264533)
                    ·
                      refine ⟨640269297704366653465525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13659078351026488607264533 640269297704366653465525)
                      ·
                        rfl

theorem cell23_1246920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1246920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246920 prefixEnd_1246920 := by exact prefixLift 1246920
  have htrace : WordTrace (prefixWord ++ tailWord_1246920) baseStart_1246920 baseEnd_1246920 := by
    simpa [prefixWord, tailWord_1246920, baseEnd_1246920] using wordTrace_append hprefix tailTrace_1246920
  have hstable : (prefixWord ++ tailWord_1246920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246920).length < 2 ^ (prefixWord ++ tailWord_1246920).sum := by decide
  have hdescent : baseEnd_1246920 < baseStart_1246920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246954 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_1246954 : Nat := 118140960795 + 1246954 * 2 ^ 59
def prefixEnd_1246954 : Nat := 4983230072969 + 3 ^ 40 * 1246954 * 2
def baseEnd_1246954 : Nat := 640286756046619520440369

theorem tailTrace_1246954 : CollatzResearch.WordTrace tailWord_1246954 prefixEnd_1246954 640286756046619520440369 := by
  unfold tailWord_1246954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11370037181126523908368979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30320099149670730422317277 11370037181126523908368979)
  ·
    refine ⟨17055055771689785862553469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11370037181126523908368979 17055055771689785862553469)
    ·
      refine ⟨6395645914383669698457551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17055055771689785862553469 6395645914383669698457551)
      ·
        refine ⟨9593468871575504547686327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6395645914383669698457551 9593468871575504547686327)
        ·
          refine ⟨14390203307363256821529491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9593468871575504547686327 14390203307363256821529491)
          ·
            refine ⟨21585304961044885232294237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14390203307363256821529491 21585304961044885232294237)
            ·
              refine ⟨8094489360391831962110339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21585304961044885232294237 8094489360391831962110339)
              ·
                refine ⟨12141734040587747943165509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094489360391831962110339 12141734040587747943165509)
                ·
                  refine ⟨2276575132610202739343533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12141734040587747943165509 2276575132610202739343533)
                  ·
                    refine ⟨853715674728826027253825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276575132610202739343533 853715674728826027253825)
                    ·
                      refine ⟨640286756046619520440369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 853715674728826027253825 640286756046619520440369)
                      ·
                        rfl

theorem cell23_1246954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_1246954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246954 prefixEnd_1246954 := by exact prefixLift 1246954
  have htrace : WordTrace (prefixWord ++ tailWord_1246954) baseStart_1246954 baseEnd_1246954 := by
    simpa [prefixWord, tailWord_1246954, baseEnd_1246954] using wordTrace_append hprefix tailTrace_1246954
  have hstable : (prefixWord ++ tailWord_1246954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246954).length < 2 ^ (prefixWord ++ tailWord_1246954).sum := by decide
  have hdescent : baseEnd_1246954 < baseStart_1246954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246960 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_1246960 : Nat := 118140960795 + 1246960 * 2 ^ 59
def prefixEnd_1246960 : Nat := 4983230072969 + 3 ^ 40 * 1246960 * 2
def baseEnd_1246960 : Nat := 213429945643515498988447

theorem tailTrace_1246960 : CollatzResearch.WordTrace tailWord_1246960 prefixEnd_1246960 213429945643515498988447 := by
  unfold tailWord_1246960
  simp only [CollatzResearch.WordTrace]
  refine ⟨22740183781242179329097167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30320245041656239105462889 22740183781242179329097167)
  ·
    refine ⟨34110275671863268993645751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22740183781242179329097167 34110275671863268993645751)
    ·
      refine ⟨51165413507794903490468627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34110275671863268993645751 51165413507794903490468627)
      ·
        refine ⟨76748120261692355235702941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51165413507794903490468627 76748120261692355235702941)
        ·
          refine ⟨28780545098134633213388603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76748120261692355235702941 28780545098134633213388603)
          ·
            refine ⟨43170817647201949820082905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28780545098134633213388603 43170817647201949820082905)
            ·
              refine ⟨32378113235401462365062179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43170817647201949820082905 32378113235401462365062179)
              ·
                refine ⟨48567169853102193547593269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32378113235401462365062179 48567169853102193547593269)
                ·
                  refine ⟨4553172173728330645086869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48567169853102193547593269 4553172173728330645086869)
                  ·
                    refine ⟨213429945643515498988447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4553172173728330645086869 213429945643515498988447)
                    ·
                      rfl

theorem cell23_1246960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_1246960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246960 prefixEnd_1246960 := by exact prefixLift 1246960
  have htrace : WordTrace (prefixWord ++ tailWord_1246960) baseStart_1246960 baseEnd_1246960 := by
    simpa [prefixWord, tailWord_1246960, baseEnd_1246960] using wordTrace_append hprefix tailTrace_1246960
  have hstable : (prefixWord ++ tailWord_1246960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246960).length < 2 ^ (prefixWord ++ tailWord_1246960).sum := by decide
  have hdescent : baseEnd_1246960 < baseStart_1246960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246961 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_1246961 : Nat := 118140960795 + 1246961 * 2 ^ 59
def prefixEnd_1246961 : Nat := 4983230072969 + 3 ^ 40 * 1246961 * 2
def baseEnd_1246961 : Nat := 640290350411200993052837

theorem tailTrace_1246961 : CollatzResearch.WordTrace tailWord_1246961 prefixEnd_1246961 640290350411200993052837 := by
  unfold tailWord_1246961
  simp only [CollatzResearch.WordTrace]
  refine ⟨45480404035480735828980737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30320269356987157219320491 45480404035480735828980737)
  ·
    refine ⟨34110303026610551871735553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45480404035480735828980737 34110303026610551871735553)
    ·
      refine ⟨25582727269957913903801665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34110303026610551871735553 25582727269957913903801665)
      ·
        refine ⟨19187045452468435427851249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25582727269957913903801665 19187045452468435427851249)
        ·
          refine ⟨14390284089351326570888437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19187045452468435427851249 14390284089351326570888437)
          ·
            refine ⟨1349089133376686866020791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14390284089351326570888437 1349089133376686866020791)
            ·
              refine ⟨2023633700065030299031187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349089133376686866020791 2023633700065030299031187)
              ·
                refine ⟨3035450550097545448546781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023633700065030299031187 3035450550097545448546781)
                ·
                  refine ⟨1138293956286579543205043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3035450550097545448546781 1138293956286579543205043)
                  ·
                    refine ⟨1707440934429869314807565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138293956286579543205043 1707440934429869314807565)
                    ·
                      refine ⟨640290350411200993052837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1707440934429869314807565 640290350411200993052837)
                      ·
                        rfl

theorem cell23_1246961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_1246961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246961 prefixEnd_1246961 := by exact prefixLift 1246961
  have htrace : WordTrace (prefixWord ++ tailWord_1246961) baseStart_1246961 baseEnd_1246961 := by
    simpa [prefixWord, tailWord_1246961, baseEnd_1246961] using wordTrace_append hprefix tailTrace_1246961
  have hstable : (prefixWord ++ tailWord_1246961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246961).length < 2 ^ (prefixWord ++ tailWord_1246961).sum := by decide
  have hdescent : baseEnd_1246961 < baseStart_1246961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246994 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1246994 : Nat := 118140960795 + 1246994 * 2 ^ 59
def prefixEnd_1246994 : Nat := 4983230072969 + 3 ^ 40 * 1246994 * 2
def baseEnd_1246994 : Nat := 213435765090933121313395

theorem tailTrace_1246994 : CollatzResearch.WordTrace tailWord_1246994 prefixEnd_1246994 213435765090933121313395 := by
  unfold tailWord_1246994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11370401911090295616233009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30321071762907454976621357 11370401911090295616233009)
  ·
    refine ⟨8527801433317721712174757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11370401911090295616233009 8527801433317721712174757)
    ·
      refine ⟨1598962768747072821032767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8527801433317721712174757 1598962768747072821032767)
      ·
        refine ⟨2398444153120609231549151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598962768747072821032767 2398444153120609231549151)
        ·
          refine ⟨3597666229680913847323727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398444153120609231549151 3597666229680913847323727)
          ·
            refine ⟨5396499344521370770985591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597666229680913847323727 5396499344521370770985591)
            ·
              refine ⟨8094749016782056156478387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396499344521370770985591 8094749016782056156478387)
              ·
                refine ⟨12142123525173084234717581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094749016782056156478387 12142123525173084234717581)
                ·
                  refine ⟨4553296321939906588019093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12142123525173084234717581 4553296321939906588019093)
                  ·
                    refine ⟨213435765090933121313395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4553296321939906588019093 213435765090933121313395)
                    ·
                      rfl

theorem cell23_1246994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1246994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246994 prefixEnd_1246994 := by exact prefixLift 1246994
  have htrace : WordTrace (prefixWord ++ tailWord_1246994) baseStart_1246994 baseEnd_1246994 := by
    simpa [prefixWord, tailWord_1246994, baseEnd_1246994] using wordTrace_append hprefix tailTrace_1246994
  have hstable : (prefixWord ++ tailWord_1246994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246994).length < 2 ^ (prefixWord ++ tailWord_1246994).sum := by decide
  have hdescent : baseEnd_1246994 < baseStart_1246994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246997 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1246997 : Nat := 118140960795 + 1246997 * 2 ^ 59
def prefixEnd_1246997 : Nat := 4983230072969 + 3 ^ 40 * 1246997 * 2
def baseEnd_1246997 : Nat := 640308835714762852202671

theorem tailTrace_1246997 : CollatzResearch.WordTrace tailWord_1246997 prefixEnd_1246997 640308835714762852202671 := by
  unfold tailWord_1246997
  simp only [CollatzResearch.WordTrace]
  refine ⟨45481717063350313977291245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30321144708900209318194163 45481717063350313977291245)
  ·
    refine ⟨17055643898756367741484217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45481717063350313977291245 17055643898756367741484217)
    ·
      refine ⟨12791732924067275806113163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17055643898756367741484217 12791732924067275806113163)
      ·
        refine ⟨19187599386100913709169745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12791732924067275806113163 19187599386100913709169745)
        ·
          refine ⟨14390699539575685281877309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19187599386100913709169745 14390699539575685281877309)
          ·
            refine ⟨5396512327340881980703991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14390699539575685281877309 5396512327340881980703991)
            ·
              refine ⟨8094768491011322971055987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396512327340881980703991 8094768491011322971055987)
              ·
                refine ⟨12142152736516984456583981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094768491011322971055987 12142152736516984456583981)
                ·
                  refine ⟨4553307276193869171218993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12142152736516984456583981 4553307276193869171218993)
                  ·
                    refine ⟨3414980457145401878414245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4553307276193869171218993 3414980457145401878414245)
                    ·
                      refine ⟨640308835714762852202671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3414980457145401878414245 640308835714762852202671)
                      ·
                        rfl

theorem cell23_1246997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1246997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1246997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1246997 prefixEnd_1246997 := by exact prefixLift 1246997
  have htrace : WordTrace (prefixWord ++ tailWord_1246997) baseStart_1246997 baseEnd_1246997 := by
    simpa [prefixWord, tailWord_1246997, baseEnd_1246997] using wordTrace_append hprefix tailTrace_1246997
  have hstable : (prefixWord ++ tailWord_1246997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246997).length < 2 ^ (prefixWord ++ tailWord_1246997).sum := by decide
  have hdescent : baseEnd_1246997 < baseStart_1246997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247034 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_1247034 : Nat := 118140960795 + 1247034 * 2 ^ 59
def prefixEnd_1247034 : Nat := 4983230072969 + 3 ^ 40 * 1247034 * 2
def baseEnd_1247034 : Nat := 640327834498979207440001

theorem tailTrace_1247034 : CollatzResearch.WordTrace tailWord_1247034 prefixEnd_1247034 640327834498979207440001 := by
  unfold tailWord_1247034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11370766641054067324097039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30322044376144179530925437 11370766641054067324097039)
  ·
    refine ⟨17056149961581100986145559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11370766641054067324097039 17056149961581100986145559)
    ·
      refine ⟨25584224942371651479218339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17056149961581100986145559 25584224942371651479218339)
      ·
        refine ⟨38376337413557477218827509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25584224942371651479218339 38376337413557477218827509)
        ·
          refine ⟨3597781632521013489265079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38376337413557477218827509 3597781632521013489265079)
          ·
            refine ⟨5396672448781520233897619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597781632521013489265079 5396672448781520233897619)
            ·
              refine ⟨8095008673172280350846429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396672448781520233897619 8095008673172280350846429)
              ·
                refine ⟨3035628252439605131567411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8095008673172280350846429 3035628252439605131567411)
                ·
                  refine ⟨4553442378659407697351117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035628252439605131567411 4553442378659407697351117)
                  ·
                    refine ⟨1707540891997277886506669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4553442378659407697351117 1707540891997277886506669)
                    ·
                      refine ⟨640327834498979207440001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1707540891997277886506669 640327834498979207440001)
                      ·
                        rfl

theorem cell23_1247034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_1247034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247034 prefixEnd_1247034 := by exact prefixLift 1247034
  have htrace : WordTrace (prefixWord ++ tailWord_1247034) baseStart_1247034 baseEnd_1247034 := by
    simpa [prefixWord, tailWord_1247034, baseEnd_1247034] using wordTrace_append hprefix tailTrace_1247034
  have hstable : (prefixWord ++ tailWord_1247034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247034).length < 2 ^ (prefixWord ++ tailWord_1247034).sum := by decide
  have hdescent : baseEnd_1247034 < baseStart_1247034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247068 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1247068 : Nat := 118140960795 + 1247068 * 2 ^ 59
def prefixEnd_1247068 : Nat := 4983230072969 + 3 ^ 40 * 1247068 * 2
def baseEnd_1247068 : Nat := 640345292841232074414845

theorem tailTrace_1247068 : CollatzResearch.WordTrace tailWord_1247068 prefixEnd_1247068 640345292841232074414845 := by
  unfold tailWord_1247068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22742153323046546551562929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30322871097395395402083905 22742153323046546551562929)
  ·
    refine ⟨17056614992284909913672197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22742153323046546551562929 17056614992284909913672197)
    ·
      refine ⟨3198115311053420608813537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17056614992284909913672197 3198115311053420608813537)
      ·
        refine ⟨2398586483290065456610153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3198115311053420608813537 2398586483290065456610153)
        ·
          refine ⟨1798939862467549092457615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398586483290065456610153 1798939862467549092457615)
          ·
            refine ⟨2698409793701323638686423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798939862467549092457615 2698409793701323638686423)
            ·
              refine ⟨4047614690551985458029635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698409793701323638686423 4047614690551985458029635)
              ·
                refine ⟨6071422035827978187044453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047614690551985458029635 6071422035827978187044453)
                ·
                  refine ⟨1138391631717745910070835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6071422035827978187044453 1138391631717745910070835)
                  ·
                    refine ⟨1707587447576618865106253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138391631717745910070835 1707587447576618865106253)
                    ·
                      refine ⟨640345292841232074414845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1707587447576618865106253 640345292841232074414845)
                      ·
                        rfl

theorem cell23_1247068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1247068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247068 prefixEnd_1247068 := by exact prefixLift 1247068
  have htrace : WordTrace (prefixWord ++ tailWord_1247068) baseStart_1247068 baseEnd_1247068 := by
    simpa [prefixWord, tailWord_1247068, baseEnd_1247068] using wordTrace_append hprefix tailTrace_1247068
  have hstable : (prefixWord ++ tailWord_1247068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247068).length < 2 ^ (prefixWord ++ tailWord_1247068).sum := by decide
  have hdescent : baseEnd_1247068 < baseStart_1247068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247077 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1247077 : Nat := 118140960795 + 1247077 * 2 ^ 59
def prefixEnd_1247077 : Nat := 4983230072969 + 3 ^ 40 * 1247077 * 2
def baseEnd_1247077 : Nat := 640349914167122539202303

theorem tailTrace_1247077 : CollatzResearch.WordTrace tailWord_1247077 prefixEnd_1247077 640349914167122539202303 := by
  unfold tailWord_1247077
  simp only [CollatzResearch.WordTrace]
  refine ⟨45484634903060487640203485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30323089935373658426802323 45484634903060487640203485)
  ·
    refine ⟨17056738088647682865076307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45484634903060487640203485 17056738088647682865076307)
    ·
      refine ⟨25585107132971524297614461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17056738088647682865076307 25585107132971524297614461)
      ·
        refine ⟨9594415174864321611605423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25585107132971524297614461 9594415174864321611605423)
        ·
          refine ⟨14391622762296482417408135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9594415174864321611605423 14391622762296482417408135)
          ·
            refine ⟨21587434143444723626112203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14391622762296482417408135 21587434143444723626112203)
            ·
              refine ⟨32381151215167085439168305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21587434143444723626112203 32381151215167085439168305)
              ·
                refine ⟨24285863411375314079376229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32381151215167085439168305 24285863411375314079376229)
                ·
                  refine ⟨4553599389632871389883043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24285863411375314079376229 4553599389632871389883043)
                  ·
                    refine ⟨6830399084449307084824565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4553599389632871389883043 6830399084449307084824565)
                    ·
                      refine ⟨640349914167122539202303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6830399084449307084824565 640349914167122539202303)
                      ·
                        rfl

theorem cell23_1247077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1247077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247077 prefixEnd_1247077 := by exact prefixLift 1247077
  have htrace : WordTrace (prefixWord ++ tailWord_1247077) baseStart_1247077 baseEnd_1247077 := by
    simpa [prefixWord, tailWord_1247077, baseEnd_1247077] using wordTrace_append hprefix tailTrace_1247077
  have hstable : (prefixWord ++ tailWord_1247077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247077).length < 2 ^ (prefixWord ++ tailWord_1247077).sum := by decide
  have hdescent : baseEnd_1247077 < baseStart_1247077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247097 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 7]
def baseStart_1247097 : Nat := 118140960795 + 1247097 * 2 ^ 59
def prefixEnd_1247097 : Nat := 4983230072969 + 3 ^ 40 * 1247097 * 2
def baseEnd_1247097 : Nat := 71151131531134717883579

theorem tailTrace_1247097 : CollatzResearch.WordTrace tailWord_1247097 prefixEnd_1247097 71151131531134717883579 := by
  unfold tailWord_1247097
  simp only [CollatzResearch.WordTrace]
  refine ⟨45485364362988031055931545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30323576241992020703954363 45485364362988031055931545)
  ·
    refine ⟨34114023272241023291948659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45485364362988031055931545 34114023272241023291948659)
    ·
      refine ⟨51171034908361534937922989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34114023272241023291948659 51171034908361534937922989)
      ·
        refine ⟨19189138090635575601721121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51171034908361534937922989 19189138090635575601721121)
        ·
          refine ⟨14391853567976681701290841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19189138090635575601721121 14391853567976681701290841)
          ·
            refine ⟨10793890175982511275968131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14391853567976681701290841 10793890175982511275968131)
            ·
              refine ⟨16190835263973766913952197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10793890175982511275968131 16190835263973766913952197)
              ·
                refine ⟨3035781611995081296366037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16190835263973766913952197 3035781611995081296366037)
                ·
                  refine ⟨71151131531134717883579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3035781611995081296366037 71151131531134717883579)
                  ·
                    rfl

theorem cell23_1247097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_1247097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247097 prefixEnd_1247097 := by exact prefixLift 1247097
  have htrace : WordTrace (prefixWord ++ tailWord_1247097) baseStart_1247097 baseEnd_1247097 := by
    simpa [prefixWord, tailWord_1247097, baseEnd_1247097] using wordTrace_append hprefix tailTrace_1247097
  have hstable : (prefixWord ++ tailWord_1247097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247097).length < 2 ^ (prefixWord ++ tailWord_1247097).sum := by decide
  have hdescent : baseEnd_1247097 < baseStart_1247097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247177 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_1247177 : Nat := 118140960795 + 1247177 * 2 ^ 59
def prefixEnd_1247177 : Nat := 4983230072969 + 3 ^ 40 * 1247177 * 2
def baseEnd_1247177 : Nat := 640401262232572147951843

theorem tailTrace_1247177 : CollatzResearch.WordTrace tailWord_1247177 prefixEnd_1247177 640401262232572147951843 := by
  unfold tailWord_1247177
  simp only [CollatzResearch.WordTrace]
  refine ⟨45488282202698204718843785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30325521468465469812562523 45488282202698204718843785)
  ·
    refine ⟨34116211652023653539132839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45488282202698204718843785 34116211652023653539132839)
    ·
      refine ⟨51174317478035480308699259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34116211652023653539132839 51174317478035480308699259)
      ·
        refine ⟨76761476217053220463048889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51174317478035480308699259 76761476217053220463048889)
        ·
          refine ⟨57571107162789915347286667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76761476217053220463048889 57571107162789915347286667)
          ·
            refine ⟨86356660744184873020930001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57571107162789915347286667 86356660744184873020930001)
            ·
              refine ⟨64767495558138654765697501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86356660744184873020930001 64767495558138654765697501)
              ·
                refine ⟨24287810834301995537136563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64767495558138654765697501 24287810834301995537136563)
                ·
                  refine ⟨36431716251452993305704845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24287810834301995537136563 36431716251452993305704845)
                  ·
                    refine ⟨13661893594294872489639317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36431716251452993305704845 13661893594294872489639317)
                    ·
                      refine ⟨640401262232572147951843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13661893594294872489639317 640401262232572147951843)
                      ·
                        rfl

theorem cell23_1247177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_1247177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247177 prefixEnd_1247177 := by exact prefixLift 1247177
  have htrace : WordTrace (prefixWord ++ tailWord_1247177) baseStart_1247177 baseEnd_1247177 := by
    simpa [prefixWord, tailWord_1247177, baseEnd_1247177] using wordTrace_append hprefix tailTrace_1247177
  have hstable : (prefixWord ++ tailWord_1247177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247177).length < 2 ^ (prefixWord ++ tailWord_1247177).sum := by decide
  have hdescent : baseEnd_1247177 < baseStart_1247177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247204 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 6]
def baseStart_1247204 : Nat := 118140960795 + 1247204 * 2 ^ 59
def prefixEnd_1247204 : Nat := 4983230072969 + 3 ^ 40 * 1247204 * 2
def baseEnd_1247204 : Nat := 71157236245582615812691

theorem tailTrace_1247204 : CollatzResearch.WordTrace tailWord_1247204 prefixEnd_1247204 71157236245582615812691 := by
  unfold tailWord_1247204
  simp only [CollatzResearch.WordTrace]
  refine ⟨22744633486800194165038333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30326177982400258886717777 22744633486800194165038333)
  ·
    refine ⟨8529237557550072811889375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22744633486800194165038333 8529237557550072811889375)
    ·
      refine ⟨12793856336325109217834063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8529237557550072811889375 12793856336325109217834063)
      ·
        refine ⟨19190784504487663826751095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12793856336325109217834063 19190784504487663826751095)
        ·
          refine ⟨28786176756731495740126643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19190784504487663826751095 28786176756731495740126643)
          ·
            refine ⟨43179265135097243610189965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28786176756731495740126643 43179265135097243610189965)
            ·
              refine ⟨16192224425661466353821237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43179265135097243610189965 16192224425661466353821237)
              ·
                refine ⟨1518021039905762470670741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16192224425661466353821237 1518021039905762470670741)
                ·
                  refine ⟨71157236245582615812691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1518021039905762470670741 71157236245582615812691)
                  ·
                    rfl

theorem cell23_1247204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_1247204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247204 prefixEnd_1247204 := by exact prefixLift 1247204
  have htrace : WordTrace (prefixWord ++ tailWord_1247204) baseStart_1247204 baseEnd_1247204 := by
    simpa [prefixWord, tailWord_1247204, baseEnd_1247204] using wordTrace_append hprefix tailTrace_1247204
  have hstable : (prefixWord ++ tailWord_1247204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247204).length < 2 ^ (prefixWord ++ tailWord_1247204).sum := by decide
  have hdescent : baseEnd_1247204 < baseStart_1247204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247281 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 4, 4]
def baseStart_1247281 : Nat := 118140960795 + 1247281 * 2 ^ 59
def prefixEnd_1247281 : Nat := 4983230072969 + 3 ^ 40 * 1247281 * 2
def baseEnd_1247281 : Nat := 213484888073546580350455

theorem tailTrace_1247281 : CollatzResearch.WordTrace tailWord_1247281 prefixEnd_1247281 213484888073546580350455 := by
  unfold tailWord_1247281
  simp only [CollatzResearch.WordTrace]
  refine ⟨45492075394321430480629697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30328050262880953653753131 45492075394321430480629697)
  ·
    refine ⟨34119056545741072860472273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45492075394321430480629697 34119056545741072860472273)
    ·
      refine ⟨25589292409305804645354205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34119056545741072860472273 25589292409305804645354205)
      ·
        refine ⟨9595984653489676742007827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25589292409305804645354205 9595984653489676742007827)
        ·
          refine ⟨14393976980234515113011741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9595984653489676742007827 14393976980234515113011741)
          ·
            refine ⟨5397741367587943167379403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14393976980234515113011741 5397741367587943167379403)
            ·
              refine ⟨8096612051381914751069105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397741367587943167379403 8096612051381914751069105)
              ·
                refine ⟨6072459038536436063301829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096612051381914751069105 6072459038536436063301829)
                ·
                  refine ⟨1138586069725581761869093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6072459038536436063301829 1138586069725581761869093)
                  ·
                    refine ⟨213484888073546580350455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1138586069725581761869093 213484888073546580350455)
                    ·
                      rfl

theorem cell23_1247281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_1247281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247281 prefixEnd_1247281 := by exact prefixLift 1247281
  have htrace : WordTrace (prefixWord ++ tailWord_1247281) baseStart_1247281 baseEnd_1247281 := by
    simpa [prefixWord, tailWord_1247281, baseEnd_1247281] using wordTrace_append hprefix tailTrace_1247281
  have hstable : (prefixWord ++ tailWord_1247281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247281).length < 2 ^ (prefixWord ++ tailWord_1247281).sum := by decide
  have hdescent : baseEnd_1247281 < baseStart_1247281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247282 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_1247282 : Nat := 118140960795 + 1247282 * 2 ^ 59
def prefixEnd_1247282 : Nat := 4983230072969 + 3 ^ 40 * 1247282 * 2
def baseEnd_1247282 : Nat := 640455177701294237138861

theorem tailTrace_1247282 : CollatzResearch.WordTrace tailWord_1247282 prefixEnd_1247282 640455177701294237138861 := by
  unfold tailWord_1247282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373027966829451912854025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30328074578211871767610733 11373027966829451912854025)
  ·
    refine ⟨8529770975122088934640519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11373027966829451912854025 8529770975122088934640519)
    ·
      refine ⟨12794656462683133401960779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8529770975122088934640519 12794656462683133401960779)
      ·
        refine ⟨19191984694024700102941169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12794656462683133401960779 19191984694024700102941169)
        ·
          refine ⟨14393988520518525077205877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19191984694024700102941169 14393988520518525077205877)
          ·
            refine ⟨1349436423798611725988051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14393988520518525077205877 1349436423798611725988051)
            ·
              refine ⟨2024154635697917588982077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349436423798611725988051 2024154635697917588982077)
              ·
                refine ⟨759057988386719095868279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2024154635697917588982077 759057988386719095868279)
                ·
                  refine ⟨1138586982580078643802419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759057988386719095868279 1138586982580078643802419)
                  ·
                    refine ⟨1707880473870117965703629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138586982580078643802419 1707880473870117965703629)
                    ·
                      refine ⟨640455177701294237138861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1707880473870117965703629 640455177701294237138861)
                      ·
                        rfl

theorem cell23_1247282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_1247282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247282 prefixEnd_1247282 := by exact prefixLift 1247282
  have htrace : WordTrace (prefixWord ++ tailWord_1247282) baseStart_1247282 baseEnd_1247282 := by
    simpa [prefixWord, tailWord_1247282, baseEnd_1247282] using wordTrace_append hprefix tailTrace_1247282
  have hstable : (prefixWord ++ tailWord_1247282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247282).length < 2 ^ (prefixWord ++ tailWord_1247282).sum := by decide
  have hdescent : baseEnd_1247282 < baseStart_1247282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247321 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_1247321 : Nat := 118140960795 + 1247321 * 2 ^ 59
def prefixEnd_1247321 : Nat := 4983230072969 + 3 ^ 40 * 1247321 * 2
def baseEnd_1247321 : Nat := 640475203446819584551181

theorem tailTrace_1247321 : CollatzResearch.WordTrace tailWord_1247321 prefixEnd_1247321 640475203446819584551181 := by
  unfold tailWord_1247321
  simp only [CollatzResearch.WordTrace]
  refine ⟨45493534314176517312085817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30329022876117678208057211 45493534314176517312085817)
  ·
    refine ⟨34120150735632387984064363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45493534314176517312085817 34120150735632387984064363)
    ·
      refine ⟨51180226103448581976096545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34120150735632387984064363 51180226103448581976096545)
      ·
        refine ⟨38385169577586436482072409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51180226103448581976096545 38385169577586436482072409)
        ·
          refine ⟨28788877183189827361554307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38385169577586436482072409 28788877183189827361554307)
          ·
            refine ⟨43183315774784741042331461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28788877183189827361554307 43183315774784741042331461)
            ·
              refine ⟨8096871707772138945437149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43183315774784741042331461 8096871707772138945437149)
              ·
                refine ⟨3036326890414552104538931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8096871707772138945437149 3036326890414552104538931)
                ·
                  refine ⟨4554490335621828156808397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036326890414552104538931 4554490335621828156808397)
                  ·
                    refine ⟨1707933875858185558803149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4554490335621828156808397 1707933875858185558803149)
                    ·
                      refine ⟨640475203446819584551181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1707933875858185558803149 640475203446819584551181)
                      ·
                        rfl

theorem cell23_1247321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_1247321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247321 prefixEnd_1247321 := by exact prefixLift 1247321
  have htrace : WordTrace (prefixWord ++ tailWord_1247321) baseStart_1247321 baseEnd_1247321 := by
    simpa [prefixWord, tailWord_1247321, baseEnd_1247321] using wordTrace_append hprefix tailTrace_1247321
  have hstable : (prefixWord ++ tailWord_1247321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247321).length < 2 ^ (prefixWord ++ tailWord_1247321).sum := by decide
  have hdescent : baseEnd_1247321 < baseStart_1247321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247325 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1247325 : Nat := 118140960795 + 1247325 * 2 ^ 59
def prefixEnd_1247325 : Nat := 4983230072969 + 3 ^ 40 * 1247325 * 2
def baseEnd_1247325 : Nat := 640477257369437568901163

theorem tailTrace_1247325 : CollatzResearch.WordTrace tailWord_1247325 prefixEnd_1247325 640477257369437568901163 := by
  unfold tailWord_1247325
  simp only [CollatzResearch.WordTrace]
  refine ⟨45493680206162025995231429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30329120137441350663487619 45493680206162025995231429)
  ·
    refine ⟨8530065038655379874105893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45493680206162025995231429 8530065038655379874105893)
    ·
      refine ⟨1599387194747883726394855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8530065038655379874105893 1599387194747883726394855)
      ·
        refine ⟨2399080792121825589592283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599387194747883726394855 2399080792121825589592283)
        ·
          refine ⟨3598621188182738384388425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399080792121825589592283 3598621188182738384388425)
          ·
            refine ⟨2698965891137053788291319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3598621188182738384388425 2698965891137053788291319)
            ·
              refine ⟨4048448836705580682436979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698965891137053788291319 4048448836705580682436979)
              ·
                refine ⟨6072673255058371023655469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048448836705580682436979 6072673255058371023655469)
                ·
                  refine ⟨2277252470646889133870801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6072673255058371023655469 2277252470646889133870801)
                  ·
                    refine ⟨1707939352985166850403101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277252470646889133870801 1707939352985166850403101)
                    ·
                      refine ⟨640477257369437568901163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1707939352985166850403101 640477257369437568901163)
                      ·
                        rfl

theorem cell23_1247325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1247325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247325 prefixEnd_1247325 := by exact prefixLift 1247325
  have htrace : WordTrace (prefixWord ++ tailWord_1247325) baseStart_1247325 baseEnd_1247325 := by
    simpa [prefixWord, tailWord_1247325, baseEnd_1247325] using wordTrace_append hprefix tailTrace_1247325
  have hstable : (prefixWord ++ tailWord_1247325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247325).length < 2 ^ (prefixWord ++ tailWord_1247325).sum := by decide
  have hdescent : baseEnd_1247325 < baseStart_1247325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247354 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_1247354 : Nat := 118140960795 + 1247354 * 2 ^ 59
def prefixEnd_1247354 : Nat := 4983230072969 + 3 ^ 40 * 1247354 * 2
def baseEnd_1247354 : Nat := 213497382769472651812843

theorem tailTrace_1247354 : CollatzResearch.WordTrace tailWord_1247354 prefixEnd_1247354 213497382769472651812843 := by
  unfold tailWord_1247354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373684480764240987009279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30329825282037975965358077 11373684480764240987009279)
  ·
    refine ⟨17060526721146361480513919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373684480764240987009279 17060526721146361480513919)
    ·
      refine ⟨25590790081719542220770879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17060526721146361480513919 25590790081719542220770879)
      ·
        refine ⟨38386185122579313331156319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25590790081719542220770879 38386185122579313331156319)
        ·
          refine ⟨57579277683868969996734479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38386185122579313331156319 57579277683868969996734479)
          ·
            refine ⟨86368916525803454995101719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57579277683868969996734479 86368916525803454995101719)
            ·
              refine ⟨129553374788705182492652579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86368916525803454995101719 129553374788705182492652579)
              ·
                refine ⟨194330062183057773738978869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129553374788705182492652579 194330062183057773738978869)
                ·
                  refine ⟨18218443329661666288029269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194330062183057773738978869 18218443329661666288029269)
                  ·
                    refine ⟨213497382769472651812843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18218443329661666288029269 213497382769472651812843)
                    ·
                      rfl

theorem cell23_1247354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_1247354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247354 prefixEnd_1247354 := by exact prefixLift 1247354
  have htrace : WordTrace (prefixWord ++ tailWord_1247354) baseStart_1247354 baseEnd_1247354 := by
    simpa [prefixWord, tailWord_1247354, baseEnd_1247354] using wordTrace_append hprefix tailTrace_1247354
  have hstable : (prefixWord ++ tailWord_1247354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247354).length < 2 ^ (prefixWord ++ tailWord_1247354).sum := by decide
  have hdescent : baseEnd_1247354 < baseStart_1247354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247381 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1247381 : Nat := 118140960795 + 1247381 * 2 ^ 59
def prefixEnd_1247381 : Nat := 4983230072969 + 3 ^ 40 * 1247381 * 2
def baseEnd_1247381 : Nat := 640506012286089349800905

theorem tailTrace_1247381 : CollatzResearch.WordTrace tailWord_1247381 prefixEnd_1247381 640506012286089349800905 := by
  unfold tailWord_1247381
  simp only [CollatzResearch.WordTrace]
  refine ⟨45495722693959147559269997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30330481795972765039513331 45495722693959147559269997)
  ·
    refine ⟨17060896010234680334726249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45495722693959147559269997 17060896010234680334726249)
    ·
      refine ⟨12795672007676010251044687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17060896010234680334726249 12795672007676010251044687)
      ·
        refine ⟨19193508011514015376567031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12795672007676010251044687 19193508011514015376567031)
        ·
          refine ⟨28790262017271023064850547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19193508011514015376567031 28790262017271023064850547)
          ·
            refine ⟨43185393025906534597275821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28790262017271023064850547 43185393025906534597275821)
            ·
              refine ⟨16194522384714950473978433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43185393025906534597275821 16194522384714950473978433)
              ·
                refine ⟨12145891788536212855483825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16194522384714950473978433 12145891788536212855483825)
                ·
                  refine ⟨9109418841402159641612869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12145891788536212855483825 9109418841402159641612869)
                  ·
                    refine ⟨1708016032762904932802413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9109418841402159641612869 1708016032762904932802413)
                    ·
                      refine ⟨640506012286089349800905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708016032762904932802413 640506012286089349800905)
                      ·
                        rfl

theorem cell23_1247381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1247381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247381 prefixEnd_1247381 := by exact prefixLift 1247381
  have htrace : WordTrace (prefixWord ++ tailWord_1247381) baseStart_1247381 baseEnd_1247381 := by
    simpa [prefixWord, tailWord_1247381, baseEnd_1247381] using wordTrace_append hprefix tailTrace_1247381
  have hstable : (prefixWord ++ tailWord_1247381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247381).length < 2 ^ (prefixWord ++ tailWord_1247381).sum := by decide
  have hdescent : baseEnd_1247381 < baseStart_1247381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247406 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1247406 : Nat := 118140960795 + 1247406 * 2 ^ 59
def prefixEnd_1247406 : Nat := 4983230072969 + 3 ^ 40 * 1247406 * 2
def baseEnd_1247406 : Nat := 640518849302451751988291

theorem tailTrace_1247406 : CollatzResearch.WordTrace tailWord_1247406 prefixEnd_1247406 640518849302451751988291 := by
  unfold tailWord_1247406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687079314858572103616259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30331089679245717885953381 5687079314858572103616259)
  ·
    refine ⟨8530618972287858155424389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5687079314858572103616259 8530618972287858155424389)
    ·
      refine ⟨1599491057303973404142073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8530618972287858155424389 1599491057303973404142073)
      ·
        refine ⟨1199618292977980053106555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599491057303973404142073 1199618292977980053106555)
        ·
          refine ⟨1799427439466970079659833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199618292977980053106555 1799427439466970079659833)
          ·
            refine ⟨1349570579600227559744875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1799427439466970079659833 1349570579600227559744875)
            ·
              refine ⟨2024355869400341339617313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349570579600227559744875 2024355869400341339617313)
              ·
                refine ⟨1518266902050256004712985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024355869400341339617313 1518266902050256004712985)
                ·
                  refine ⟨1138700176537692003534739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1518266902050256004712985 1138700176537692003534739)
                  ·
                    refine ⟨1708050264806538005302109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138700176537692003534739 1708050264806538005302109)
                    ·
                      refine ⟨640518849302451751988291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708050264806538005302109 640518849302451751988291)
                      ·
                        rfl

theorem cell23_1247406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1247406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247406 prefixEnd_1247406 := by exact prefixLift 1247406
  have htrace : WordTrace (prefixWord ++ tailWord_1247406) baseStart_1247406 baseEnd_1247406 := by
    simpa [prefixWord, tailWord_1247406, baseEnd_1247406] using wordTrace_append hprefix tailTrace_1247406
  have hstable : (prefixWord ++ tailWord_1247406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247406).length < 2 ^ (prefixWord ++ tailWord_1247406).sum := by decide
  have hdescent : baseEnd_1247406 < baseStart_1247406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247418 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_1247418 : Nat := 118140960795 + 1247418 * 2 ^ 59
def prefixEnd_1247418 : Nat := 4983230072969 + 3 ^ 40 * 1247418 * 2
def baseEnd_1247418 : Nat := 71169445674478411670915

theorem tailTrace_1247418 : CollatzResearch.WordTrace tailWord_1247418 prefixEnd_1247418 71169445674478411670915 := by
  unfold tailWord_1247418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11374268048706275719591727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30331381463216735252244605 11374268048706275719591727)
  ·
    refine ⟨17061402073059413579387591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11374268048706275719591727 17061402073059413579387591)
    ·
      refine ⟨25592103109589120369081387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17061402073059413579387591 25592103109589120369081387)
      ·
        refine ⟨38388154664383680553622081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25592103109589120369081387 38388154664383680553622081)
        ·
          refine ⟨28791115998287760415216561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38388154664383680553622081 28791115998287760415216561)
          ·
            refine ⟨21593336998715820311412421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28791115998287760415216561 21593336998715820311412421)
            ·
              refine ⟨4048750687259216308389829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21593336998715820311412421 4048750687259216308389829)
              ·
                refine ⟨759140753861103057823093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4048750687259216308389829 759140753861103057823093)
                ·
                  refine ⟨71169445674478411670915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 759140753861103057823093 71169445674478411670915)
                  ·
                    rfl

theorem cell23_1247418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_1247418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247418 prefixEnd_1247418 := by exact prefixLift 1247418
  have htrace : WordTrace (prefixWord ++ tailWord_1247418) baseStart_1247418 baseEnd_1247418 := by
    simpa [prefixWord, tailWord_1247418, baseEnd_1247418] using wordTrace_append hprefix tailTrace_1247418
  have hstable : (prefixWord ++ tailWord_1247418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247418).length < 2 ^ (prefixWord ++ tailWord_1247418).sum := by decide
  have hdescent : baseEnd_1247418 < baseStart_1247418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247468 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1247468 : Nat := 118140960795 + 1247468 * 2 ^ 59
def prefixEnd_1247468 : Nat := 4983230072969 + 3 ^ 40 * 1247468 * 2
def baseEnd_1247468 : Nat := 640550685103030509413005

theorem tailTrace_1247468 : CollatzResearch.WordTrace tailWord_1247468 prefixEnd_1247468 640550685103030509413005 := by
  unfold tailWord_1247468
  simp only [CollatzResearch.WordTrace]
  refine ⟨22749447922321980708843529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30332597229762640945124705 22749447922321980708843529)
  ·
    refine ⟨17062085941741485531632647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22749447922321980708843529 17062085941741485531632647)
    ·
      refine ⟨25593128912612228297448971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17062085941741485531632647 25593128912612228297448971)
      ·
        refine ⟨38389693368918342446173457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25593128912612228297448971 38389693368918342446173457)
        ·
          refine ⟨28792270026688756834630093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38389693368918342446173457 28792270026688756834630093)
          ·
            refine ⟨10797101260008283812986285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28792270026688756834630093 10797101260008283812986285)
            ·
              refine ⟨4048912972503106429869857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10797101260008283812986285 4048912972503106429869857)
              ·
                refine ⟨3036684729377329822402393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048912972503106429869857 3036684729377329822402393)
                ·
                  refine ⟨2277513547032997366801795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036684729377329822402393 2277513547032997366801795)
                  ·
                    refine ⟨3416270320549496050202693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2277513547032997366801795 3416270320549496050202693)
                    ·
                      refine ⟨640550685103030509413005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3416270320549496050202693 640550685103030509413005)
                      ·
                        rfl

theorem cell23_1247468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1247468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247468 prefixEnd_1247468 := by exact prefixLift 1247468
  have htrace : WordTrace (prefixWord ++ tailWord_1247468) baseStart_1247468 baseEnd_1247468 := by
    simpa [prefixWord, tailWord_1247468, baseEnd_1247468] using wordTrace_append hprefix tailTrace_1247468
  have hstable : (prefixWord ++ tailWord_1247468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247468).length < 2 ^ (prefixWord ++ tailWord_1247468).sum := by decide
  have hdescent : baseEnd_1247468 < baseStart_1247468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247481 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1247481 : Nat := 118140960795 + 1247481 * 2 ^ 59
def prefixEnd_1247481 : Nat := 4983230072969 + 3 ^ 40 * 1247481 * 2
def baseEnd_1247481 : Nat := 640557360351538958550445

theorem tailTrace_1247481 : CollatzResearch.WordTrace tailWord_1247481 prefixEnd_1247481 640557360351538958550445 := by
  unfold tailWord_1247481
  simp only [CollatzResearch.WordTrace]
  refine ⟨45499369993596864637910297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30332913329064576425273531 45499369993596864637910297)
  ·
    refine ⟨34124527495197648478432723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45499369993596864637910297 34124527495197648478432723)
    ·
      refine ⟨51186791242796472717649085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34124527495197648478432723 51186791242796472717649085)
      ·
        refine ⟨19195046716048677269118407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51186791242796472717649085 19195046716048677269118407)
        ·
          refine ⟨28792570074073015903677611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19195046716048677269118407 28792570074073015903677611)
          ·
            refine ⟨43188855111109523855516417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28792570074073015903677611 43188855111109523855516417)
            ·
              refine ⟨32391641333332142891637313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43188855111109523855516417 32391641333332142891637313)
              ·
                refine ⟨24293730999999107168727985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32391641333332142891637313 24293730999999107168727985)
                ·
                  refine ⟨18220298249999330376545989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24293730999999107168727985 18220298249999330376545989)
                  ·
                    refine ⟨3416305921874874445602373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18220298249999330376545989 3416305921874874445602373)
                    ·
                      refine ⟨640557360351538958550445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3416305921874874445602373 640557360351538958550445)
                      ·
                        rfl

theorem cell23_1247481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1247481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247481 prefixEnd_1247481 := by exact prefixLift 1247481
  have htrace : WordTrace (prefixWord ++ tailWord_1247481) baseStart_1247481 baseEnd_1247481 := by
    simpa [prefixWord, tailWord_1247481, baseEnd_1247481] using wordTrace_append hprefix tailTrace_1247481
  have hstable : (prefixWord ++ tailWord_1247481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247481).length < 2 ^ (prefixWord ++ tailWord_1247481).sum := by decide
  have hdescent : baseEnd_1247481 < baseStart_1247481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247505 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_1247505 : Nat := 118140960795 + 1247505 * 2 ^ 59
def prefixEnd_1247505 : Nat := 4983230072969 + 3 ^ 40 * 1247505 * 2
def baseEnd_1247505 : Nat := 640569683887246864650335

theorem tailTrace_1247505 : CollatzResearch.WordTrace tailWord_1247505 prefixEnd_1247505 640569683887246864650335 := by
  unfold tailWord_1247505
  simp only [CollatzResearch.WordTrace]
  refine ⟨45500245345509916736783969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30333496897006611157855979 45500245345509916736783969)
  ·
    refine ⟨34125184009132437552587977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45500245345509916736783969 34125184009132437552587977)
    ·
      refine ⟨25593888006849328164440983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34125184009132437552587977 25593888006849328164440983)
      ·
        refine ⟨38390832010273992246661475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25593888006849328164440983 38390832010273992246661475)
        ·
          refine ⟨57586248015410988369992213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38390832010273992246661475 57586248015410988369992213)
          ·
            refine ⟨2699355375722390079843385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57586248015410988369992213 2699355375722390079843385)
            ·
              refine ⟨2024516531791792559882539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699355375722390079843385 2024516531791792559882539)
              ·
                refine ⟨3036774797687688839823809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024516531791792559882539 3036774797687688839823809)
                ·
                  refine ⟨2277581098265766629867857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036774797687688839823809 2277581098265766629867857)
                  ·
                    refine ⟨1708185823699324972400893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277581098265766629867857 1708185823699324972400893)
                    ·
                      refine ⟨640569683887246864650335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708185823699324972400893 640569683887246864650335)
                      ·
                        rfl

theorem cell23_1247505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_1247505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247505 prefixEnd_1247505 := by exact prefixLift 1247505
  have htrace : WordTrace (prefixWord ++ tailWord_1247505) baseStart_1247505 baseEnd_1247505 := by
    simpa [prefixWord, tailWord_1247505, baseEnd_1247505] using wordTrace_append hprefix tailTrace_1247505
  have hstable : (prefixWord ++ tailWord_1247505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247505).length < 2 ^ (prefixWord ++ tailWord_1247505).sum := by decide
  have hdescent : baseEnd_1247505 < baseStart_1247505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247525 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 6]
def baseStart_1247525 : Nat := 118140960795 + 1247525 * 2 ^ 59
def prefixEnd_1247525 : Nat := 4983230072969 + 3 ^ 40 * 1247525 * 2
def baseEnd_1247525 : Nat := 71175550388926309600027

theorem tailTrace_1247525 : CollatzResearch.WordTrace tailWord_1247525 prefixEnd_1247525 71175550388926309600027 := by
  unfold tailWord_1247525
  simp only [CollatzResearch.WordTrace]
  refine ⟨45500974805437460152512029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30333983203624973435008019 45500974805437460152512029)
  ·
    refine ⟨17062865552039047557192011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45500974805437460152512029 17062865552039047557192011)
    ·
      refine ⟨25594298328058571335788017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17062865552039047557192011 25594298328058571335788017)
      ·
        refine ⟨19195723746043928501841013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25594298328058571335788017 19195723746043928501841013)
        ·
          refine ⟨1799599101191618297047595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19195723746043928501841013 1799599101191618297047595)
          ·
            refine ⟨2699398651787427445571393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799599101191618297047595 2699398651787427445571393)
            ·
              refine ⟨2024548988840570584178545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699398651787427445571393 2024548988840570584178545)
              ·
                refine ⟨1518411741630427938133909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024548988840570584178545 1518411741630427938133909)
                ·
                  refine ⟨71175550388926309600027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1518411741630427938133909 71175550388926309600027)
                  ·
                    rfl

theorem cell23_1247525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_1247525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247525 prefixEnd_1247525 := by exact prefixLift 1247525
  have htrace : WordTrace (prefixWord ++ tailWord_1247525) baseStart_1247525 baseEnd_1247525 := by
    simpa [prefixWord, tailWord_1247525, baseEnd_1247525] using wordTrace_append hprefix tailTrace_1247525
  have hstable : (prefixWord ++ tailWord_1247525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247525).length < 2 ^ (prefixWord ++ tailWord_1247525).sum := by decide
  have hdescent : baseEnd_1247525 < baseStart_1247525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247556 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1247556 : Nat := 118140960795 + 1247556 * 2 ^ 59
def prefixEnd_1247556 : Nat := 4983230072969 + 3 ^ 40 * 1247556 * 2
def baseEnd_1247556 : Nat := 640595871400626165112601

theorem tailTrace_1247556 : CollatzResearch.WordTrace tailWord_1247556 prefixEnd_1247556 640595871400626165112601 := by
  unfold tailWord_1247556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22751052734162576223445261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30334736978883434964593681 22751052734162576223445261)
  ·
    refine ⟨8531644775310966083791973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22751052734162576223445261 8531644775310966083791973)
    ·
      refine ⟨1599683395370806140710995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8531644775310966083791973 1599683395370806140710995)
      ·
        refine ⟨2399525093056209211066493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599683395370806140710995 2399525093056209211066493)
        ·
          refine ⟨899821909896078454149935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2399525093056209211066493 899821909896078454149935)
          ·
            refine ⟨1349732864844117681224903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899821909896078454149935 1349732864844117681224903)
            ·
              refine ⟨2024599297266176521837355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349732864844117681224903 2024599297266176521837355)
              ·
                refine ⟨3036898945899264782756033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024599297266176521837355 3036898945899264782756033)
                ·
                  refine ⟨2277674209424448587067025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036898945899264782756033 2277674209424448587067025)
                  ·
                    refine ⟨1708255657068336440300269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277674209424448587067025 1708255657068336440300269)
                    ·
                      refine ⟨640595871400626165112601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708255657068336440300269 640595871400626165112601)
                      ·
                        rfl

theorem cell23_1247556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1247556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247556 prefixEnd_1247556 := by exact prefixLift 1247556
  have htrace : WordTrace (prefixWord ++ tailWord_1247556) baseStart_1247556 baseEnd_1247556 := by
    simpa [prefixWord, tailWord_1247556, baseEnd_1247556] using wordTrace_append hprefix tailTrace_1247556
  have hstable : (prefixWord ++ tailWord_1247556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247556).length < 2 ^ (prefixWord ++ tailWord_1247556).sum := by decide
  have hdescent : baseEnd_1247556 < baseStart_1247556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247568 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_1247568 : Nat := 118140960795 + 1247568 * 2 ^ 59
def prefixEnd_1247568 : Nat := 4983230072969 + 3 ^ 40 * 1247568 * 2
def baseEnd_1247568 : Nat := 213534011056160039387515

theorem tailTrace_1247568 : CollatzResearch.WordTrace tailWord_1247568 prefixEnd_1247568 213534011056160039387515 := by
  unfold tailWord_1247568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22751271572140839248163679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30335028762854452330884905 22751271572140839248163679)
  ·
    refine ⟨34126907358211258872245519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22751271572140839248163679 34126907358211258872245519)
    ·
      refine ⟨51190361037316888308368279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34126907358211258872245519 51190361037316888308368279)
      ·
        refine ⟨76785541555975332462552419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51190361037316888308368279 76785541555975332462552419)
        ·
          refine ⟨115178312333962998693828629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76785541555975332462552419 115178312333962998693828629)
          ·
            refine ⟨5398983390654515563773217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115178312333962998693828629 5398983390654515563773217)
            ·
              refine ⟨4049237542990886672829913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5398983390654515563773217 4049237542990886672829913)
              ·
                refine ⟨3036928157243165004622435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4049237542990886672829913 3036928157243165004622435)
                ·
                  refine ⟨4555392235864747506933653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036928157243165004622435 4555392235864747506933653)
                  ·
                    refine ⟨213534011056160039387515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4555392235864747506933653 213534011056160039387515)
                    ·
                      rfl

theorem cell23_1247568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_1247568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247568 prefixEnd_1247568 := by exact prefixLift 1247568
  have htrace : WordTrace (prefixWord ++ tailWord_1247568) baseStart_1247568 baseEnd_1247568 := by
    simpa [prefixWord, tailWord_1247568, baseEnd_1247568] using wordTrace_append hprefix tailTrace_1247568
  have hstable : (prefixWord ++ tailWord_1247568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247568).length < 2 ^ (prefixWord ++ tailWord_1247568).sum := by decide
  have hdescent : baseEnd_1247568 < baseStart_1247568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247569 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 1, 1, 3]
def baseStart_1247569 : Nat := 118140960795 + 1247569 * 2 ^ 59
def prefixEnd_1247569 : Nat := 4983230072969 + 3 ^ 40 * 1247569 * 2
def baseEnd_1247569 : Nat := 640602546649134614250041

theorem tailTrace_1247569 : CollatzResearch.WordTrace tailWord_1247569 prefixEnd_1247569 640602546649134614250041 := by
  unfold tailWord_1247569
  simp only [CollatzResearch.WordTrace]
  refine ⟨45502579617278055667113761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30335053078185370444742507 45502579617278055667113761)
  ·
    refine ⟨34126934712958541750335321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45502579617278055667113761 34126934712958541750335321)
    ·
      refine ⟨25595201034718906312751491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34126934712958541750335321 25595201034718906312751491)
      ·
        refine ⟨38392801552078359469127237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25595201034718906312751491 38392801552078359469127237)
        ·
          refine ⟨7198650291014692400461357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38392801552078359469127237 7198650291014692400461357)
          ·
            refine ⟨2699493859130509650173009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7198650291014692400461357 2699493859130509650173009)
            ·
              refine ⟨2024620394347882237629757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699493859130509650173009 2024620394347882237629757)
              ·
                refine ⟨759232647880455839111159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2024620394347882237629757 759232647880455839111159)
                ·
                  refine ⟨1138848971820683758666739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759232647880455839111159 1138848971820683758666739)
                  ·
                    refine ⟨1708273457731025638000109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138848971820683758666739 1708273457731025638000109)
                    ·
                      refine ⟨640602546649134614250041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708273457731025638000109 640602546649134614250041)
                      ·
                        rfl

theorem cell23_1247569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_1247569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247569 prefixEnd_1247569 := by exact prefixLift 1247569
  have htrace : WordTrace (prefixWord ++ tailWord_1247569) baseStart_1247569 baseEnd_1247569 := by
    simpa [prefixWord, tailWord_1247569, baseEnd_1247569] using wordTrace_append hprefix tailTrace_1247569
  have hstable : (prefixWord ++ tailWord_1247569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247569).length < 2 ^ (prefixWord ++ tailWord_1247569).sum := by decide
  have hdescent : baseEnd_1247569 < baseStart_1247569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247572 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_1247572 : Nat := 118140960795 + 1247572 * 2 ^ 59
def prefixEnd_1247572 : Nat := 4983230072969 + 3 ^ 40 * 1247572 * 2
def baseEnd_1247572 : Nat := 213534695697032700837509

theorem tailTrace_1247572 : CollatzResearch.WordTrace tailWord_1247572 prefixEnd_1247572 213534695697032700837509 := by
  unfold tailWord_1247572
  simp only [CollatzResearch.WordTrace]
  refine ⟨22751344518133593589736485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30335126024178124786315313 22751344518133593589736485)
  ·
    refine ⟨4265877097150048798075591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22751344518133593589736485 4265877097150048798075591)
    ·
      refine ⟨6398815645725073197113387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4265877097150048798075591 6398815645725073197113387)
      ·
        refine ⟨9598223468587609795670081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398815645725073197113387 9598223468587609795670081)
        ·
          refine ⟨7198667601440707346752561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9598223468587609795670081 7198667601440707346752561)
          ·
            refine ⟨5399000701080530510064421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198667601440707346752561 5399000701080530510064421)
            ·
              refine ⟨1012312631452599470637079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5399000701080530510064421 1012312631452599470637079)
              ·
                refine ⟨1518468947178899205955619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012312631452599470637079 1518468947178899205955619)
                ·
                  refine ⟨2277703420768348808933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518468947178899205955619 2277703420768348808933429)
                  ·
                    refine ⟨213534695697032700837509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2277703420768348808933429 213534695697032700837509)
                    ·
                      rfl

theorem cell23_1247572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_1247572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247572 prefixEnd_1247572 := by exact prefixLift 1247572
  have htrace : WordTrace (prefixWord ++ tailWord_1247572) baseStart_1247572 baseEnd_1247572 := by
    simpa [prefixWord, tailWord_1247572, baseEnd_1247572] using wordTrace_append hprefix tailTrace_1247572
  have hstable : (prefixWord ++ tailWord_1247572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247572).length < 2 ^ (prefixWord ++ tailWord_1247572).sum := by decide
  have hdescent : baseEnd_1247572 < baseStart_1247572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247575 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_1247575 : Nat := 118140960795 + 1247575 * 2 ^ 59
def prefixEnd_1247575 : Nat := 4983230072969 + 3 ^ 40 * 1247575 * 2
def baseEnd_1247575 : Nat := 640605627533061590775013

theorem tailTrace_1247575 : CollatzResearch.WordTrace tailWord_1247575 prefixEnd_1247575 640605627533061590775013 := by
  unfold tailWord_1247575
  simp only [CollatzResearch.WordTrace]
  refine ⟨45502798455256318691832179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30335198970170879127888119 45502798455256318691832179)
  ·
    refine ⟨68254197682884478037748269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45502798455256318691832179 68254197682884478037748269)
    ·
      refine ⟨25595324131081679264155601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68254197682884478037748269 25595324131081679264155601)
      ·
        refine ⟨19196493098311259448116701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25595324131081679264155601 19196493098311259448116701)
        ·
          refine ⟨7198684911866722293043763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19196493098311259448116701 7198684911866722293043763)
          ·
            refine ⟨10798027367800083439565645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198684911866722293043763 10798027367800083439565645)
            ·
              refine ⟨4049260262925031289837117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10798027367800083439565645 4049260262925031289837117)
              ·
                refine ⟨1518472598596886733688919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4049260262925031289837117 1518472598596886733688919)
                ·
                  refine ⟨2277708897895330100533379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518472598596886733688919 2277708897895330100533379)
                  ·
                    refine ⟨3416563346842995150800069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2277708897895330100533379 3416563346842995150800069)
                    ·
                      refine ⟨640605627533061590775013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3416563346842995150800069 640605627533061590775013)
                      ·
                        rfl

theorem cell23_1247575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_1247575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247575 prefixEnd_1247575 := by exact prefixLift 1247575
  have htrace : WordTrace (prefixWord ++ tailWord_1247575) baseStart_1247575 baseEnd_1247575 := by
    simpa [prefixWord, tailWord_1247575, baseEnd_1247575] using wordTrace_append hprefix tailTrace_1247575
  have hstable : (prefixWord ++ tailWord_1247575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247575).length < 2 ^ (prefixWord ++ tailWord_1247575).sum := by decide
  have hdescent : baseEnd_1247575 < baseStart_1247575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247578 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1247578 : Nat := 118140960795 + 1247578 * 2 ^ 59
def prefixEnd_1247578 : Nat := 4983230072969 + 3 ^ 40 * 1247578 * 2
def baseEnd_1247578 : Nat := 640607167975025079037499

theorem tailTrace_1247578 : CollatzResearch.WordTrace tailWord_1247578 prefixEnd_1247578 640607167975025079037499 := by
  unfold tailWord_1247578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11375726968561362551047847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30335271916163633469460925 11375726968561362551047847)
  ·
    refine ⟨17063590452842043826571771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11375726968561362551047847 17063590452842043826571771)
    ·
      refine ⟨25595385679263065739857657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17063590452842043826571771 25595385679263065739857657)
      ·
        refine ⟨19196539259447299304893243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25595385679263065739857657 19196539259447299304893243)
        ·
          refine ⟨28794808889170948957339865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19196539259447299304893243 28794808889170948957339865)
          ·
            refine ⟨21596106666878211718004899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28794808889170948957339865 21596106666878211718004899)
            ·
              refine ⟨32394160000317317577007349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21596106666878211718004899 32394160000317317577007349)
              ·
                refine ⟨3036952500029748522844439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32394160000317317577007349 3036952500029748522844439)
                ·
                  refine ⟨4555428750044622784266659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036952500029748522844439 4555428750044622784266659)
                  ·
                    refine ⟨6833143125066934176399989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4555428750044622784266659 6833143125066934176399989)
                    ·
                      refine ⟨640607167975025079037499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6833143125066934176399989 640607167975025079037499)
                      ·
                        rfl

theorem cell23_1247578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1247578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247578 prefixEnd_1247578 := by exact prefixLift 1247578
  have htrace : WordTrace (prefixWord ++ tailWord_1247578) baseStart_1247578 baseEnd_1247578 := by
    simpa [prefixWord, tailWord_1247578, baseEnd_1247578] using wordTrace_append hprefix tailTrace_1247578
  have hstable : (prefixWord ++ tailWord_1247578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247578).length < 2 ^ (prefixWord ++ tailWord_1247578).sum := by decide
  have hdescent : baseEnd_1247578 < baseStart_1247578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247588 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1247588 : Nat := 118140960795 + 1247588 * 2 ^ 59
def prefixEnd_1247588 : Nat := 4983230072969 + 3 ^ 40 * 1247588 * 2
def baseEnd_1247588 : Nat := 640612302781570039912453

theorem tailTrace_1247588 : CollatzResearch.WordTrace tailWord_1247588 prefixEnd_1247588 640612302781570039912453 := by
  unfold tailWord_1247588
  simp only [CollatzResearch.WordTrace]
  refine ⟨22751636302104610956027709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30335515069472814608036945 22751636302104610956027709)
  ·
    refine ⟨8531863613289229108510391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22751636302104610956027709 8531863613289229108510391)
    ·
      refine ⟨12797795419933843662765587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8531863613289229108510391 12797795419933843662765587)
      ·
        refine ⟨19196693129900765494148381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12797795419933843662765587 19196693129900765494148381)
        ·
          refine ⟨7198759923712787060305643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19196693129900765494148381 7198759923712787060305643)
          ·
            refine ⟨10798139885569180590458465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198759923712787060305643 10798139885569180590458465)
            ·
              refine ⟨8098604914176885442843849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10798139885569180590458465 8098604914176885442843849)
              ·
                refine ⟨6073953685632664082132887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8098604914176885442843849 6073953685632664082132887)
                ·
                  refine ⟨9110930528448996123199331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6073953685632664082132887 9110930528448996123199331)
                  ·
                    refine ⟨13666395792673494184798997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9110930528448996123199331 13666395792673494184798997)
                    ·
                      refine ⟨640612302781570039912453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13666395792673494184798997 640612302781570039912453)
                      ·
                        rfl

theorem cell23_1247588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1247588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247588 prefixEnd_1247588 := by exact prefixLift 1247588
  have htrace : WordTrace (prefixWord ++ tailWord_1247588) baseStart_1247588 baseEnd_1247588 := by
    simpa [prefixWord, tailWord_1247588, baseEnd_1247588] using wordTrace_append hprefix tailTrace_1247588
  have hstable : (prefixWord ++ tailWord_1247588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247588).length < 2 ^ (prefixWord ++ tailWord_1247588).sum := by decide
  have hdescent : baseEnd_1247588 < baseStart_1247588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247605 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1247605 : Nat := 118140960795 + 1247605 * 2 ^ 59
def prefixEnd_1247605 : Nat := 4983230072969 + 3 ^ 40 * 1247605 * 2
def baseEnd_1247605 : Nat := 640621031952696473399875

theorem tailTrace_1247605 : CollatzResearch.WordTrace tailWord_1247605 prefixEnd_1247605 640621031952696473399875 := by
  unfold tailWord_1247605
  simp only [CollatzResearch.WordTrace]
  refine ⟨45503892645147633815424269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30335928430098422543616179 45503892645147633815424269)
  ·
    refine ⟨17063959741930362680784101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45503892645147633815424269 17063959741930362680784101)
    ·
      refine ⟨3199492451611943002647019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17063959741930362680784101 3199492451611943002647019)
      ·
        refine ⟨4799238677417914503970529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199492451611943002647019 4799238677417914503970529)
        ·
          refine ⟨3599429008063435877977897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4799238677417914503970529 3599429008063435877977897)
          ·
            refine ⟨2699571756047576908483423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3599429008063435877977897 2699571756047576908483423)
            ·
              refine ⟨4049357634071365362725135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699571756047576908483423 4049357634071365362725135)
              ·
                refine ⟨6074036451107048044087703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049357634071365362725135 6074036451107048044087703)
                ·
                  refine ⟨9111054676660572066131555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6074036451107048044087703 9111054676660572066131555)
                  ·
                    refine ⟨13666582014990858099197333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9111054676660572066131555 13666582014990858099197333)
                    ·
                      refine ⟨640621031952696473399875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13666582014990858099197333 640621031952696473399875)
                      ·
                        rfl

theorem cell23_1247605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1247605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247605 prefixEnd_1247605 := by exact prefixLift 1247605
  have htrace : WordTrace (prefixWord ++ tailWord_1247605) baseStart_1247605 baseEnd_1247605 := by
    simpa [prefixWord, tailWord_1247605, baseEnd_1247605] using wordTrace_append hprefix tailTrace_1247605
  have hstable : (prefixWord ++ tailWord_1247605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247605).length < 2 ^ (prefixWord ++ tailWord_1247605).sum := by decide
  have hdescent : baseEnd_1247605 < baseStart_1247605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247642 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1247642 : Nat := 118140960795 + 1247642 * 2 ^ 59
def prefixEnd_1247642 : Nat := 4983230072969 + 3 ^ 40 * 1247642 * 2
def baseEnd_1247642 : Nat := 640640030736912828637205

theorem tailTrace_1247642 : CollatzResearch.WordTrace tailWord_1247642 prefixEnd_1247642 640640030736912828637205 := by
  unfold tailWord_1247642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11376310536503397283630295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30336828097342392756347453 11376310536503397283630295)
  ·
    refine ⟨17064465804755095925445443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11376310536503397283630295 17064465804755095925445443)
    ·
      refine ⟨25596698707132643888168165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17064465804755095925445443 25596698707132643888168165)
      ·
        refine ⟨4799381007587370729031531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25596698707132643888168165 4799381007587370729031531)
        ·
          refine ⟨7199071511381056093547297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799381007587370729031531 7199071511381056093547297)
          ·
            refine ⟨5399303633535792070160473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7199071511381056093547297 5399303633535792070160473)
            ·
              refine ⟨4049477725151844052620355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5399303633535792070160473 4049477725151844052620355)
              ·
                refine ⟨6074216587727766078930533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049477725151844052620355 6074216587727766078930533)
                ·
                  refine ⟨1138915610198956139799475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6074216587727766078930533 1138915610198956139799475)
                  ·
                    refine ⟨1708373415298434209699213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138915610198956139799475 1708373415298434209699213)
                    ·
                      refine ⟨640640030736912828637205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708373415298434209699213 640640030736912828637205)
                      ·
                        rfl

theorem cell23_1247642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1247642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247642 prefixEnd_1247642 := by exact prefixLift 1247642
  have htrace : WordTrace (prefixWord ++ tailWord_1247642) baseStart_1247642 baseEnd_1247642 := by
    simpa [prefixWord, tailWord_1247642, baseEnd_1247642] using wordTrace_append hprefix tailTrace_1247642
  have hstable : (prefixWord ++ tailWord_1247642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247642).length < 2 ^ (prefixWord ++ tailWord_1247642).sum := by decide
  have hdescent : baseEnd_1247642 < baseStart_1247642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247669 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_1247669 : Nat := 118140960795 + 1247669 * 2 ^ 59
def prefixEnd_1247669 : Nat := 4983230072969 + 3 ^ 40 * 1247669 * 2
def baseEnd_1247669 : Nat := 640653894714584222999581

theorem tailTrace_1247669 : CollatzResearch.WordTrace tailWord_1247669 prefixEnd_1247669 640653894714584222999581 := by
  unfold tailWord_1247669
  simp only [CollatzResearch.WordTrace]
  refine ⟨45506226916915772745754061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30337484611277181830502707 45506226916915772745754061)
  ·
    refine ⟨17064835093843414779657773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45506226916915772745754061 17064835093843414779657773)
    ·
      refine ⟨6399313160191280542371665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17064835093843414779657773 6399313160191280542371665)
      ·
        refine ⟨4799484870143460406778749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6399313160191280542371665 4799484870143460406778749)
        ·
          refine ⟨1799806826303797652542031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4799484870143460406778749 1799806826303797652542031)
          ·
            refine ⟨2699710239455696478813047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799806826303797652542031 2699710239455696478813047)
            ·
              refine ⟨4049565359183544718219571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699710239455696478813047 4049565359183544718219571)
              ·
                refine ⟨6074348038775317077329357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049565359183544718219571 6074348038775317077329357)
                ·
                  refine ⟨2277880514540743903998509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6074348038775317077329357 2277880514540743903998509)
                  ·
                    refine ⟨854205192952778963999441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277880514540743903998509 854205192952778963999441)
                    ·
                      refine ⟨640653894714584222999581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854205192952778963999441 640653894714584222999581)
                      ·
                        rfl

theorem cell23_1247669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_1247669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247669 prefixEnd_1247669 := by exact prefixLift 1247669
  have htrace : WordTrace (prefixWord ++ tailWord_1247669) baseStart_1247669 baseEnd_1247669 := by
    simpa [prefixWord, tailWord_1247669, baseEnd_1247669] using wordTrace_append hprefix tailTrace_1247669
  have hstable : (prefixWord ++ tailWord_1247669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247669).length < 2 ^ (prefixWord ++ tailWord_1247669).sum := by decide
  have hdescent : baseEnd_1247669 < baseStart_1247669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247702 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1247702 : Nat := 118140960795 + 1247702 * 2 ^ 59
def prefixEnd_1247702 : Nat := 4983230072969 + 3 ^ 40 * 1247702 * 2
def baseEnd_1247702 : Nat := 640670839576182593886929

theorem tailTrace_1247702 : CollatzResearch.WordTrace tailWord_1247702 prefixEnd_1247702 640670839576182593886929 := by
  unfold tailWord_1247702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844214407862263711356585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30338287017197479587803573 2844214407862263711356585)
  ·
    refine ⟨2133160805896697783517439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2844214407862263711356585 2133160805896697783517439)
    ·
      refine ⟨3199741208845046675276159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133160805896697783517439 3199741208845046675276159)
      ·
        refine ⟨4799611813267570012914239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199741208845046675276159 4799611813267570012914239)
        ·
          refine ⟨7199417719901355019371359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799611813267570012914239 7199417719901355019371359)
          ·
            refine ⟨10799126579852032529057039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7199417719901355019371359 10799126579852032529057039)
            ·
              refine ⟨16198689869778048793585559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10799126579852032529057039 16198689869778048793585559)
              ·
                refine ⟨24298034804667073190378339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16198689869778048793585559 24298034804667073190378339)
                ·
                  refine ⟨36447052207000609785567509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24298034804667073190378339 36447052207000609785567509)
                  ·
                    refine ⟨1708455572203153583698477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36447052207000609785567509 1708455572203153583698477)
                    ·
                      refine ⟨640670839576182593886929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708455572203153583698477 640670839576182593886929)
                      ·
                        rfl

theorem cell23_1247702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1247702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247702 prefixEnd_1247702 := by exact prefixLift 1247702
  have htrace : WordTrace (prefixWord ++ tailWord_1247702) baseStart_1247702 baseEnd_1247702 := by
    simpa [prefixWord, tailWord_1247702, baseEnd_1247702] using wordTrace_append hprefix tailTrace_1247702
  have hstable : (prefixWord ++ tailWord_1247702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247702).length < 2 ^ (prefixWord ++ tailWord_1247702).sum := by decide
  have hdescent : baseEnd_1247702 < baseStart_1247702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247750 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1247750 : Nat := 118140960795 + 1247750 * 2 ^ 59
def prefixEnd_1247750 : Nat := 4983230072969 + 3 ^ 40 * 1247750 * 2
def baseEnd_1247750 : Nat := 640695486647598406086709

theorem tailTrace_1247750 : CollatzResearch.WordTrace tailWord_1247750 prefixEnd_1247750 640695486647598406086709 := by
  unfold tailWord_1247750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422161913425697611857897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30339454153081549052968469 1422161913425697611857897)
  ·
    refine ⟨1066621435069273208893423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1422161913425697611857897 1066621435069273208893423)
    ·
      refine ⟨1599932152603909813340135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066621435069273208893423 1599932152603909813340135)
      ·
        refine ⟨2399898228905864720010203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599932152603909813340135 2399898228905864720010203)
        ·
          refine ⟨3599847343358797080015305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399898228905864720010203 3599847343358797080015305)
          ·
            refine ⟨2699885507519097810011479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3599847343358797080015305 2699885507519097810011479)
            ·
              refine ⟨4049828261278646715017219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699885507519097810011479 4049828261278646715017219)
              ·
                refine ⟨6074742391917970072525829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049828261278646715017219 6074742391917970072525829)
                ·
                  refine ⟨1139014198484619388598593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6074742391917970072525829 1139014198484619388598593)
                  ·
                    refine ⟨854260648863464541448945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139014198484619388598593 854260648863464541448945)
                    ·
                      refine ⟨640695486647598406086709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854260648863464541448945 640695486647598406086709)
                      ·
                        rfl

theorem cell23_1247750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1247750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247750 prefixEnd_1247750 := by exact prefixLift 1247750
  have htrace : WordTrace (prefixWord ++ tailWord_1247750) baseStart_1247750 baseEnd_1247750 := by
    simpa [prefixWord, tailWord_1247750, baseEnd_1247750] using wordTrace_append hprefix tailTrace_1247750
  have hstable : (prefixWord ++ tailWord_1247750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247750).length < 2 ^ (prefixWord ++ tailWord_1247750).sum := by decide
  have hdescent : baseEnd_1247750 < baseStart_1247750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
